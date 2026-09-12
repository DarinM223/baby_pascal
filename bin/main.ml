open Baby_pascal

type isa =
  | X86_64
  | AARCH64

let input_files = ref []
let isa = ref X86_64
let speclist =
  [
    ("-x86", Arg.Unit (fun () -> isa := X86_64), "Set ISA to X86_64");
    ("-x86_64", Arg.Unit (fun () -> isa := X86_64), "Set ISA to X86_64");
    ("-arm", Arg.Unit (fun () -> isa := AARCH64), "Set ISA to AARCH64");
    ("-arm64", Arg.Unit (fun () -> isa := AARCH64), "Set ISA to AARCH64");
    ("-aarch64", Arg.Unit (fun () -> isa := AARCH64), "Set ISA to AARCH64");
  ]
let usage_msg = ""
let anon_fn filename = input_files := filename :: !input_files
let () = Arg.parse speclist anon_fn usage_msg
let process_file filename =
  match Parse.parse_file filename with
  | Some program ->
    begin match !isa with
    | X86_64 ->
      let program = Compile.X86.compile program in
      let out = open_out (Format.sprintf "%s.s" (Filename.basename filename)) in
      Compile.X86.write_file out program;
      flush out;
      close_out out
    | AARCH64 -> failwith "AARCH64 not supported yet"
    end
  | None -> Format.printf "Error parsing file\n"
let () =
  let debug =
    match Sys.getenv_opt "DEBUG" with
    | Some s when String.trim s = "1" -> true
    | _ -> false
  in
  if debug then begin
    Logs.set_reporter (Logs_fmt.reporter ());
    Logs.set_level (Some Logs.Debug)
  end;
  List.iter process_file !input_files
