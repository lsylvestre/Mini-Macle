%{
    open Prelude
    open Errors
    module M = Macle
    open Macle
    module C = Const

let tvar_environment =
  let h = Hashtbl.create 16 in
  (fun x ->
    if Hashtbl.mem h x then Hashtbl.find h x else
    let v = C.Const.Type.new_tvar() in
    Hashtbl.add h x v;
    v) ;;

let parse_simple_ty loc x =
  match x with
 | "unit" -> C.Const.Type.tunit_
 | "bool" -> C.Const.Type.tbool_
 | "int" -> C.Const.Type.tint_
 | x ->
    let msg = "Unbound type constructor "^x in
    syntax_error ~msg loc

let error_type_constructor_arity name ~has ~expects loc =
  let msg = Printf.sprintf
              "The type constructor %s expects %d argument(s),\n\
              but is here applied to %d argument(s)"
            name expects has in
  syntax_error ~msg loc
%}

%token LPAREN RPAREN BEGIN END COMMA PIPE_PIPE EQ EQEQ SEMICOL COL
%token FUN
%token PIPE LEFT_ARROW
%token LET REC AND IN IF THEN ELSE
%token MATCH WITH WILDCARD
%token <string> IDENT UP_IDENT QUOTE_TVAR
%token <bool> BOOL_LIT
%token <int> INT_LIT
%token PLUS MINUS TIMES LT LE GT GE NEQ NOT MOD DIV PARALLEL_AND
%token CIRCUIT
%token EOF
%token SEMI_SEMI
%token BANG COLONEQ
%token LBRACKET RBRACKET COLCOL
%token DOT RIGHT_ARROW
%token TO_PACKET OF_PACKET
%token TYPE OF
%token RAISE FAILURE INVALID_ARG
%token FOR TO DO DONE
%token <string> STRING_LIT
%token TILDE SHARP QUESTION_MARK
%token SIZE SIGNAL PACKET AUTOMATON CONTINUE INPUT OUTPUT
%token SHARP_LBRACKET_PIPE PIPE_RBRACKET
%token PAR

/* The precedences must be listed from low to high. */

%left PAR
%nonassoc IN
%nonassoc SEMICOL
%nonassoc LET
%left     COMMA
%left     LT LE GT GE NEQ EQ EQEQ
%left     PLUS MINUS
%left     TIMES
%right    DIV MOD
%nonassoc DOT
%nonassoc TILDE BANG BEGIN BOOL_LIT LBRACKET IDENT LPAREN

%start <Macle.circuit> exp_end
%%

exp_end:
| CIRCUIT x=ident xs=ident* EQ ii=inputs oo=outputs e=exp SEMI_SEMI? EOF
    { let e = List.fold_right (fun x e -> M.fun_ ~loc:$loc x e) xs e in
      {x;inputs=ii;outputs=oo;signals=[];e} }
/*| cs=circuit+ SEMI_SEMI
  { List.fold_right (fun (x,e,loc) e' -> let_ ~loc [x,e] e') cs @@
    List.fold_right (fun (x,_,_) e ->
               seq_ (output_ ~loc:$loc x)
               (seq_ (app_ (app_ (const_ ~loc:$loc @@ Const.parse_prim "output_set") (var_ x))
                         (var_ x)) e)) cs
     (const_ ~loc:$loc @@ Const.unit_) }*/

inputs:
| { [] }
| INPUT bs=separated_nonempty_list(COMMA,ident_ty_annot_opt) SEMICOL
  { bs }

outputs:
| { [] }
| OUTPUT bs=separated_nonempty_list(COMMA,ident_ty_annot_opt) SEMICOL
  { bs }


/*circuit:
| CIRCUIT b=binding { let (x,e) = b in x,e,$loc }*/


exp:
| e1=lexp SEMICOL e2=exp { M.seq_ ~loc:$loc e1 e2 }
| e=lexp { e }

lexp:
| FUN p=ident_ty_annot_opt_paren RIGHT_ARROW e=exp
    { let x,ty = p in M.fun_ ~ty ~loc:$loc x e }
| LET bs=separated_nonempty_list(AND,binding) IN e=exp
    { M.let_ ~loc:$loc bs e }

| LET REC bs=separated_nonempty_list(AND,binding) IN e=exp
    { M.letrec_ ~loc:$loc bs e }
| AUTOMATON PIPE? ts=separated_nonempty_list(PIPE,transition) IN e=exp
    { M.automaton_ ~loc:$loc ts e }
| AUTOMATON IN e=exp
    { M.automaton_ ~loc:$loc [] e }
| SIGNAL x=ident ty=binding_annot_eq e1=exp IN e2=exp
    { let se = M.app_ ~loc:$loc
          (M.const_ ~loc:$loc @@ C.Const.parse_prim "signal_create") e1
      in
      C.Const.Type.unify ~loc:$loc C.Const.Type.(tsignal_ ty) (M.ty_of se);
      M.let_ ~loc:$loc [x,se] e2 }
| IF e1=exp THEN e2=lexp ELSE e3=lexp
    { M.if_ ~loc:$loc e1 e2 e3 }
| IF e1=exp THEN e2=lexp
    { M.if_ ~loc:$loc e1 e2 (M.const_ ~loc:$loc @@ C.Const.unit_) }
| TILDE ex=aexp LEFT_ARROW e=app
    { match ex with
      | M.Var x,_ -> M.set_ ~loc:$loc `Sig x e
      | _ -> syntax_error ~msg:"signal name expected" $loc }
| QUESTION_MARK ex=aexp LEFT_ARROW e=app
    { match ex with
      | M.Var x,_ -> M.set_ ~loc:$loc `Out x e
      | _ -> syntax_error ~msg:"output name expected" $loc }
| e=ctors { e }
| e=app { e }

app:
| e1=app e2=aexp
    { M.app_ ~loc:$loc e1 e2 }
| SIZE n=INT_LIT { M.const_ ~loc:$loc @@ C.Const.size_ n }
| CONTINUE q=ident { M.continue_ ~loc:$loc @@ q }
| e1=app p=binop e2=lexp
    { M.app_ ~loc:$loc
        (M.app_ ~loc:$loc (M.const_ ~loc:$loc @@ C.Const.parse_prim p) e1) e2 }
| e1=aexp PAR e2=aexp
    { M.par_ ~loc:$loc e1 e2 }
| e=aexp
    { e }


aexp:
| LPAREN p=op RPAREN
    { M.const_ ~loc:$loc @@ C.Const.parse_prim p }
| LPAREN RPAREN
    { M.const_ ~loc:$loc @@ C.Const.unit_ }
| n=INT_LIT
    { M.const_ ~loc:$loc @@ C.Const.int_ n }
| b=BOOL_LIT
    { M.const_ ~loc:$loc @@ C.Const.bool_ b }
| x=IDENT
    { match C.Const.parse_prim_opt x with
      | Some c -> M.const_ ~loc:$loc c
      | None ->
         M.var_ ~loc:$loc x }
| BANG e=aexp
    { M.app_ ~loc:$loc (M.const_ ~loc:$loc @@ C.Const.parse_prim "!") e }
| TILDE ex=aexp
    { match ex with
      | Var x,_ -> M.get_ ~loc:$loc `Sig x
      | _ -> syntax_error ~msg:"signal name expected" $loc }
| QUESTION_MARK ex=aexp
    { match ex with
      | Var x,_ -> M.get_ ~loc:$loc `In x
      | _ -> syntax_error ~msg:"input name expected" $loc }
| LPAREN e=exp RPAREN
    { e }

ctors:
| c=UP_IDENT
    { M.cstor_ ~loc:$loc c [] }
| c=UP_IDENT e=exp
    { M.cstor_ ~loc:$loc c [e] }
| c=UP_IDENT LPAREN es=separated_nonempty_list(COMMA,exp) RPAREN 
    { M.cstor_ ~loc:$loc c es }

op:
| p=binop {p}
| BANG { "!" }

%inline binop:
| PLUS  { "+" }
| MINUS { "-" }
| TIMES { "*" }
| DIV   { "/" }
| MOD   { "mod" }
| LT    { "<" }
| GT    { ">" }
| LE    { "<=" }
| GE    { ">=" }
| EQEQ  { "==" }
| PARALLEL_AND { "&&." }
| NEQ   { "!=" }
| COLONEQ { ":=" }

ident:
| e=aexp
   { match e with
     | Var x,_ -> x
     | _ -> syntax_error ~msg:"identifier expected" $loc }

transition:
| q=ident RIGHT_ARROW e=exp { q,e }

binding:
| x=ident EQ e=exp { x,e }
| f=fun_binding { f }
| x=ident ty=binding_annot_eq e=exp {
    C.Const.Type.unify ~loc:$loc ty (ty_of e);
    (x,e) }

fun_binding:
| x=ident ps=ident_ty_annot_opt_paren+ ty=binding_annot_eq e=exp
  { C.Const.Type.unify ~loc:$loc ty (M.ty_of e);
    x,List.fold_right (fun p e ->
        match p with
        | x,ty_opt -> M.fun_ ~loc:$loc ~ty:ty_opt x e) ps e  }

ident_ty_annot_opt_paren:
| LPAREN p=ident_ty_annot_opt_paren RPAREN { p }
| p=ident_ty_annot_opt { p }

binding_annot_eq:
| COL ty=ty EQ { ty }
| EQ { C.Const.Type.new_tvar() }

ident_ty_annot_opt:
| x=ident { x,C.Const.Type.new_tvar() }
| x=ident COL ty=ty { x,ty }

ty:
| ty=app_ty_ctor {ty}
| t1=aty RIGHT_ARROW t2=ty {  C.Const.Type.tfun_ t1 t2 }
| ty=aty {ty}

aty:
| LPAREN t=ty RPAREN { t }
| x=QUOTE_TVAR {
  let v = tvar_environment x
  in v }
| x=IDENT
   { parse_simple_ty $loc x }

app_ty_ctor_aux:
| k=sig_in_or_out {[],k}
| t=ty p=app_ty_ctor_aux { let (ts,k) = p in ((t::ts),k)}

app_ty_ctor:
| p=app_ty_ctor_aux
   {
     let (rts,k) = p in
     let ts = List.rev rts in
     match k,ts with
     | `Sig,[t] -> C.Const.Type.tsignal_ t
     | `In,[t] -> C.Const.Type.tinput_ t
     | `Out,[t] -> C.Const.Type.toutput_ t
     | _ ->
       error_type_constructor_arity
         (match k with
          | `Sig -> "signal"
          | `In -> "input"
          | `Out -> "output")
         ~has:(List.length ts) ~expects:1 $loc }

sig_in_or_out:
| SIGNAL { `Sig }
| INPUT { `In }
| OUTPUT { `Out }

