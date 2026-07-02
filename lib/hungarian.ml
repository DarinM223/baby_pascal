let pp_cost ~num_rows ~num_cols fmt cost =
  let open Format in
  pp_open_box fmt 0;
  pp_print_string fmt "[";
  for r = 0 to num_rows - 1 do
    pp_open_box fmt 0;
    pp_print_string fmt "[";
    for c = 0 to num_cols - 1 do
      let e = cost.((r * num_cols) + c) in
      pp_print_int fmt e;
      if c <> num_cols - 1 then pp_print_string fmt ", "
    done;
    pp_print_string fmt "]";
    pp_close_box fmt ();
    if r <> num_rows - 1 then pp_print_string fmt ", "
  done;
  pp_print_string fmt "]";
  pp_close_box fmt ()

let pp_assignment ~regs fmt assignment =
  for r = 0 to Array.length assignment - 1 do
    Format.fprintf fmt "%a <- %a\n" X86.Target.pp_reg regs.(r) X86.Target.pp_reg
      regs.(assignment.(r))
  done

(** Goes from minimum cost matching to maximum cost matching *)
let min_to_max_cost ?max_cost cost =
  let max_cost =
    match max_cost with
    | Some max -> max
    | None -> Array.fold_left Int.max 0 cost
  in
  Array.iteri (fun i cost_value -> cost.(i) <- max_cost - cost_value) cost

(** Hungarian algorithm, does perfect matching only *)
let solve ~cost ~num_rows ~num_cols =
  let no_exist = -1 in
  (* The row of a marked zero in a column *)
  let col_mate = Array.make num_rows no_exist in
  (* The column of a marked zero in a row *)
  let row_mate = Array.make num_cols no_exist in
  let unchosen_row = Array.make num_rows 0 in
  let row_dec = Array.make num_rows 0 in
  let col_inc = Array.make num_cols 0 in
  let parent_row = Array.make num_cols no_exist in
  (* The purpose of the slack is to track how close unvisited nodes
     are to being added to the optimal assignment path *)
  (* For each column j, slack[j] is the minimum slack value across all currently explored rows *)
  let slack = Array.make num_cols Int.max_int in
  (* Stores the row index i that produced the minimum slack for column j *)
  let slack_row = Array.make num_cols 0 in

  (* Subtract the minimum cost from each column *)
  for c = 0 to num_cols - 1 do
    let col_minimum =
      let min = ref cost.((0 * num_cols) + c) in
      for r = 1 to num_rows - 1 do
        if cost.((r * num_cols) + c) < !min then
          min := cost.((r * num_cols) + c)
      done;
      !min
    in
    if col_minimum <> 0 then begin
      for r = 0 to num_rows - 1 do
        cost.((r * num_cols) + c) <- cost.((r * num_cols) + c) - col_minimum
      done
    end
  done;
  (* Subtract the minimum cost from each row and mark zeros *)
  let unmatched = ref 0 in
  for r = 0 to num_rows - 1 do
    let row_minimum =
      let min = ref cost.((r * num_cols) + 0) in
      for c = 1 to num_cols - 1 do
        if cost.((r * num_cols) + c) < !min then
          min := cost.((r * num_cols) + c)
      done;
      !min
    in
    row_dec.(r) <- row_minimum;
    let exception RowDone in
    try
      for c = 0 to num_cols - 1 do
        if cost.((r * num_cols) + c) = row_minimum && row_mate.(c) = no_exist
        then begin
          col_mate.(r) <- c;
          row_mate.(c) <- r;
          raise RowDone
        end
      done;
      unchosen_row.(!unmatched) <- r;
      incr unmatched
    with RowDone -> ()
  done;
  let exception Done in
  begin try
    if !unmatched = 0 then raise Done;
    let t = ref !unmatched in
    while true do
      let q = ref 0 in
      (* Find an unassigned zero *)
      let exception FoundUnassignedZero of int * int in
      try
        while true do
          (* Go over unmarked rows, setting initial slack per column
             to the minimum cost value *)
          while !q < !t do
            let r = unchosen_row.(!q) in
            let dec = row_dec.(r) in
            for c = 0 to num_cols - 1 do
              if slack.(c) <> 0 then begin
                let del = cost.((r * num_cols) + c) - dec + col_inc.(c) in
                if del < slack.(c) then
                  if del = 0 then begin
                    if row_mate.(c) = no_exist then
                      raise (FoundUnassignedZero (r, c));
                    (* Add assigned zero to augmenting path *)
                    slack.(c) <- 0;
                    parent_row.(c) <- r;
                    unchosen_row.(!t) <- row_mate.(c);
                    incr t
                  end
                  else begin
                    slack.(c) <- del;
                    slack_row.(c) <- r
                  end
              end
            done;
            incr q
          done;
          (* Get the minimum slack across all columns *)
          let slack_minimum =
            let s = ref Int.max_int in
            for c = 0 to num_cols - 1 do
              if slack.(c) <> 0 && slack.(c) < !s then s := slack.(c)
            done;
            !s
          in
          (* Decrease unchosen rows by slack minimum *)
          for q = 0 to !t - 1 do
            row_dec.(unchosen_row.(q)) <-
              row_dec.(unchosen_row.(q)) + slack_minimum
          done;
          (* Increase chosen columns by slack minimum and
             check for newly uncovered zeros *)
          for c = 0 to num_cols - 1 do
            if slack.(c) <> 0 then begin
              slack.(c) <- slack.(c) - slack_minimum;
              if slack.(c) = 0 then
                let r = slack_row.(c) in
                if row_mate.(c) = no_exist then begin
                  (* Since we are going to break out of the loop,
                     finish canceling out the row decrease on the other columns
                     in the tree by incrementing them by the slack minimum *)
                  for j = c + 1 to num_cols - 1 do
                    if slack.(j) = 0 then
                      col_inc.(j) <- col_inc.(j) + slack_minimum
                  done;
                  raise (FoundUnassignedZero (r, c))
                end
                else begin
                  (* Move slack edge into augmenting path, and uncover assigned row *)
                  parent_row.(c) <- r;
                  unchosen_row.(!t) <- row_mate.(c);
                  incr t
                end
            end
            else
              (* Column is in the alternating tree (slack = 0)
                 Cancel out row decrease by increasing the column by minimum slack *)
              col_inc.(c) <- col_inc.(c) + slack_minimum
          done
        done
      with FoundUnassignedZero (r, c) ->
        (* Walk the parent links rematching the assignments to include
           the augmenting path with the found uncovered zero *)
        let r, c = (ref r, ref c) in
        let exception FinishedRematching in
        begin try
          while true do
            let j = col_mate.(!r) in
            col_mate.(!r) <- !c;
            row_mate.(!c) <- !r;
            if j = no_exist then raise FinishedRematching;
            r := parent_row.(j);
            c := j
          done
        with FinishedRematching -> ()
        end;
        decr unmatched;
        if !unmatched = 0 then raise Done;
        (* Reset state for next round *)
        Array.fill parent_row 0 num_cols no_exist;
        Array.fill slack 0 num_cols Int.max_int;
        t := 0;
        for r = 0 to num_rows - 1 do
          if col_mate.(r) = no_exist then begin
            unchosen_row.(!t) <- r;
            incr t
          end
        done
    done
  with Done -> ()
  end;
  col_mate
