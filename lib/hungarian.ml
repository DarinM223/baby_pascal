type t = {
  num_rows : int;
  num_cols : int;
  cost : int array;
}

let solve ({ cost; num_rows; num_cols; _ } : t) =
  let col_mate = Array.make num_rows 0 in
  let row_mate = Array.make num_cols 0 in
  let unchosen_row = Array.make num_rows 0 in
  let row_dec = Array.make num_rows 0 in
  let _col_inc = Array.make num_cols 0 in

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
        if cost.((r * num_cols) + c) = row_minimum && row_mate.(c) = 0 then begin
          col_mate.(r) <- c;
          row_mate.(c) <- r;
          raise RowDone
        end
      done;
      unchosen_row.(!unmatched) <- r;
      incr unmatched
    with RowDone -> ()
  done;
  failwith "unimplemented"
