open Baby_pascal

let input_files = ref []
let speclist = []
let usage_msg = ""
let anon_fn filename = input_files := filename :: !input_files
let () = Arg.parse speclist anon_fn usage_msg
let process_file filename =
  match Parse.parse_file filename with
  | Some program ->
    let program = Compile.compile program in
    let out = open_out (Format.sprintf "%s.s" (Filename.basename filename)) in
    Compile.write_file out program
  | None -> Format.printf "Error parsing file\n"
let () = List.iter process_file !input_files
