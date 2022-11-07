(* ***************************************************** *)
(*                                                       *)
(*                      Mini-Macle                       *)
(*                                                       *)
(*           Loïc Sylvestre, Sorbonne Université         *)
(* ***************************************************** *)

let flag_no_propagation = ref false ;;
let flag_typ_each_step = ref true ;;

(* pretty printing config *)
type out = Ast | Anf | Inl | Nrm | Prop | Ren | HSML | No_dep | Flat | VHDL

let out_sieve : (out,unit) Hashtbl.t =
  Hashtbl.create 10

let add_output o () =
  Hashtbl.add out_sieve o ()

let clear_output o () =
  Hashtbl.remove out_sieve Anf

let show_all () =
  List.iter (fun o -> add_output o ())
    [Ast ; Anf ; Inl ; Nrm ; Prop ; Ren ; HSML ; No_dep ; Flat ; VHDL]

let clear_all () =
  Hashtbl.clear out_sieve

(* files to process *)
let inputs = ref ([] : string list)

let add_file f = inputs := !inputs @ [f]

(* main config *)
let () =
 Arg.parse [
      ("-ast",     Arg.Unit (add_output Ast),      "enable pretty printing of source code");
      ("-no-ast",  Arg.Unit (clear_output Ast),    "disable pretty printing of source code");
      ("-anf",     Arg.Unit (add_output Anf),      "enable pretty printing of ANF form");
      ("-no-anf",  Arg.Unit (clear_output Anf),    "disable pretty printing of ANF form");
      ("-inl",     Arg.Unit (add_output Inl),      "enable pretty printing of inlined code");
      ("-no-inl",  Arg.Unit (clear_output Inl),    "disable pretty printing of inlined code");
      ("-nrm",     Arg.Unit (add_output Nrm),      "enable pretty printing of normalized code");
      ("-no-nrm",  Arg.Unit (clear_output Nrm),    "disable pretty printing of normalized code");
      ("-prop",    Arg.Unit (add_output Prop),     "enable pretty printing of code after propagation of pure expression");
      ("-no-prop", Arg.Unit (clear_output Prop),   "disable pretty printing of code after propagation of pure expression");
      ("-ren",     Arg.Unit (add_output Ren),      "enable pretty printing of code after renaming");
      ("-no-ren",  Arg.Unit (clear_output Ren),    "disable pretty printing of code after renaming");
      ("-hsml",    Arg.Unit (add_output HSML),     "enable pretty printing of HSML intermediate code");
      ("-hsml",    Arg.Unit (clear_output HSML),   "disable pretty printing of HSML intermediate code");
      ("-dep",     Arg.Unit (add_output No_dep),   "enable pretty printing of HSML code after removing of data dependencies");
      ("-no-dep",  Arg.Unit (clear_output No_dep), "disable pretty printing of HSML code after removing of data dependencies");
      ("-flat",    Arg.Unit (add_output Flat),     "enable pretty printing of flat HSML code");
      ("-no-flat", Arg.Unit (clear_output Flat),   "disable pretty printing of flat HSML code");
      ("-vhdl",    Arg.Unit (add_output VHDL),     "enable pretty printing of VHDL generated code");
      ("-no-vhdl", Arg.Unit (clear_output VHDL),   "disable pretty printing of VHDL generated code");
      ("-all",     Arg.Unit show_all,              "enable pretty printing of all compilation steps");
      ("-clear",   Arg.Unit clear_all,             "disable all pretty printing (default)");
      ("-step-ty", Arg.Clear flag_typ_each_step,   "enable systematic type checking at each compilation step (default)");
      ("-no-step-ty", Arg.Clear flag_typ_each_step, "disable systematic type checking at each compilation step");
    ]

      add_file "Usage:\n  ./maclec file"

(** pretty printer for Macle abstract syntax tree  *)
module PP = Print_syntax.Make(Macle)(Const)

(** Macle type checker *)
module Type_checker = Typing.MakeTyping(Const)(Macle)

  
(* type checking or pretty printer at each compilation step *)
let step ?(pp_ci=PP.pp_ci) lvl ci =
  if !flag_typ_each_step then Type_checker.typing_ci [] ci;
  let open Format in
  let fmt = std_formatter in
  if Hashtbl.mem out_sieve lvl then
    (pp_ci fmt ci;
    Prelude.Errors.(emph blue fmt "\n(* ************************************ *)\n");
    pp_print_flush fmt ())


(** compile Macle to VHDL *)
let compile ?(result="ml_return") ?(start="ml_start") ?(rdy="ml_rdy") fmt ci = 
  let open Compile in

  (* type check the source code *)
  Type_checker.typing_ci [] ci; 

  (step Ast ci);

  let ty_circuit = Macle.ty_of ci.e in

  (* collapsing to a simpler language *)
  let ci = {ci with e = Anf.anf ci.e } in
  let ci = {ci with e = let n = Const.Type.arity ty_circuit in
                        Anf.eta_expansion_anf n ci.e } in
  (step Anf ci); 

  let ci = {ci with e = Inl.inl ci.e } in   (step Inl ci);   
  let ci = {ci with e = Norm.nrm ci.e } in  (step Nrm ci); 

  (* optimisation *)
  let ci = {
    ci with e = if !flag_no_propagation 
                then ci.e 
                else Propagation.propagation ci.e
  } in 
  (step Prop ci);

  (* renaming *)
  let reserved_names = ci.x ::List.map fst ci.inputs@List.map fst ci.outputs@List.map fst ci.signals in
  let ci = {ci with e = Renaming.rename_exp ~reserved_names ci.e} in
  (step Ren ci);

  (* translation to an hierarchical-automata based language *)
  let ci = Translate_to_automata.translate_main ~start ~result ~rdy ci in
  (step HSML ci);

  (* supress data dependencies *)
  let ci = Supress_data_dependencies.propagation_ci ci in
  (step No_dep ci);

  (* flat the hierarchical structure *)
  let ci = Flattening.flat_ci ci in
  (step Flat ci);

  (* ensure that transformations preserve types of the source program.
     monomorphize if needed *)
  Type_checker.typing_ci [] ci;

  (* translation to a textual VHDL code *)
  ToVhdl.pp_ci fmt ci;
  Format.fprintf fmt "@.";

  (step ~pp_ci:ToVhdl.pp_ci VHDL ci)


(** *************************************** **)

let () =
  List.iter (fun filepath ->
    let filepath = Sys.argv.(1) in
    let circuit = 
      let ic = open_in filepath in (try
        (* Lexing *)
        let lexbuf = Lexing.from_channel ic in 
        (* Parsing *)
        let ast = Parser.exp_end Lexer.token lexbuf in
        close_in ic;
        ast
      with e -> close_in_noerr ic; raise e) 
    in
    let name_out = "gen/rtl/"^Filename.(remove_extension (basename filepath))^".vhdl" in
    let oc = open_out @@ name_out in (try
    let fmt = Format.formatter_of_out_channel oc in 
    (* Compiling *)
    (compile fmt circuit);
    close_out oc with e -> close_out_noerr oc; raise e)) !inputs

