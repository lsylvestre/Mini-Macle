open Prelude
open Syntax
open Const

type ident = string

module type TYPING = sig
  type exp
  type ty
  val type_exp : (ident * ty) list -> exp -> ty
end


module MakeTyping
   (C:CONST)
   (M:MACLE with type const = C.t and type ty = C.Type.ty) = struct
  type exp = M.exp
  module T = C.Type
  type ty = T.ty

  module Env = Map.Make(String)

  exception Should_be_non_expansive of ident * loc
  exception Unbound_value of (ident * loc)
  exception Unbound_state of (ident * loc)
  exception Unbound_constructor of (ident * loc)
  exception Bad_arity_constructor of (ident * int * int * loc)

  let non_expansive e =
    let exception Expansive in
    let rec aux e =
      match M.desc_of e with
      | Var _ | Const _ | Fun _ | Get _ -> ()
      | Set _ -> (* seems to be safe *)
          ()
      | Cstor(_,es) ->
          List.iter aux es
      | App _ ->
          (match M.uncurry e with
          | ((M.Const c),_),es ->
             if C.is_pure c then List.iter aux es else
             raise Expansive
          | _ -> raise Expansive)
      | If(e1,e2,e3) ->
          aux e1; aux e2; aux e3
      | Let(bs,e)
      | Letrec(bs,e) ->
          List.iter (fun (_,e) -> aux e) bs; aux e
      | Seq(e1,e2) -> aux e1; aux e2
      | Match(e,cases) ->
          aux e;
          List.iter (fun (_,e) -> aux e) cases
      | _ -> raise Expansive
    in try aux e; true with Expansive -> false

  let typ_var v x env loc =
    (try T.unify ~loc v (T.instance (Env.find x env)) with
     | Not_found -> raise (Unbound_value (x,loc)))

  let rec typ_exp stts ctors env e : unit =

    let unify t1 t2 = T.unify ~loc:(M.loc_of e) t1 t2 in

    let v = M.ty_of e in
    match M.desc_of e with
    | Const c ->
        unify v (T.instance (T.const_typing c))
    | Var x ->
        typ_var v x env (M.loc_of e)
    | Cstor(c,es) ->
        let tys,t = try List.assoc c ctors with
                    | Not_found -> raise (Unbound_constructor (c,M.loc_of e)) in

        if List.compare_lengths es tys <> 0 then
           raise (Bad_arity_constructor (c,List.length es, List.length tys, M.loc_of e));

        List.iter2 (fun e ty -> typ_exp stts ctors env e; unify (M.ty_of e) ty) es tys;
        unify v (T.instance t)
    | If(e1,e2,e3) ->
        typ_exp stts ctors env e1;
        unify (M.ty_of e1) (T.tbool_);
        typ_exp stts ctors env e2;
        typ_exp stts ctors env e3;
        unify (M.ty_of e2) (M.ty_of e3);
        unify v (M.ty_of e2)
    | Fun(x,e) ->
        let w = T.new_tvar() in
        typ_exp stts ctors (Env.add x (T.trivial_scheme w) env) e;
        unify (T.tfun_ w (M.ty_of e)) v
    | Let(bs,e) ->
        List.iter (fun (_,e) -> typ_exp stts ctors env e) bs;
        let env' = List.fold_left (fun env (x,e) ->
                      let t = M.ty_of e in
                      Env.add x (if non_expansive e then T.generalize (Env.bindings env) t
                         else T.trivial_scheme t) env) env bs in
        typ_exp stts ctors env' e;
        unify v (M.ty_of e)
    | Letrec(bs,e) ->
        let env' = List.fold_left (fun env (x,e) ->
                      Env.add x (T.trivial_scheme @@ T.new_tvar()) env) env bs in
        List.iter (fun (_,e) -> typ_exp stts ctors env' e) bs;
        typ_exp stts ctors env' e;
        unify v (M.ty_of e)
    | App(e1,e2) ->
        typ_exp stts ctors env e1;
        typ_exp stts ctors env e2;
        unify (M.ty_of e1) (T.tfun_ (M.ty_of e2) v)
    | Get(m,x) ->
        let w = match m with `Sig -> T.tsignal_ v | `In -> T.tinput_ v in
        typ_var w x env (M.loc_of e)
    | Set(m,x,e') ->
        typ_exp stts ctors env e';
        let u = M.ty_of e' in
        let w = match m with `Sig -> T.tsignal_ u | `Out  -> T.toutput_ u in
        typ_var w x env (M.loc_of e);
        unify v T.tunit_
    | Seq(e1,e2) ->
        typ_exp stts ctors env e1;
        if not (T.is_unit (M.ty_of e1)) then
          Printf.printf "Warning 10: this expression should have type unit.";
        typ_exp stts ctors env e2;
        unify (M.ty_of e2) v
    | Automaton(ts,e) ->
        let stts' = List.map fst ts @ stts in
        List.iter (fun (_,e) -> typ_exp stts' ctors env e;
                                unify (M.ty_of e) T.tunit_) ts;
        typ_exp stts' ctors env e;
        unify (M.ty_of e) v
    | Continue q ->
        if not (List.mem q stts) then
           raise (Unbound_state (q,M.loc_of e));
        unify (M.ty_of e) v
    | Par(e1,e2) ->
        typ_exp stts ctors env e1;
        typ_exp stts ctors env e2;
        unify v T.tunit_;
        unify (M.ty_of e2) T.tunit_
    | Match _ -> assert false (* todo *)

  let init_ctors =
    ["None",([],        T.generalize [] @@ T.tcstor_ "option" [T.new_tvar()]);
     "Some",([T.tint_], T.generalize [] @@ T.tcstor_ "option" [T.new_tvar()]);
    ]

  exception Not_a_basic_type of [
               `Ci of ident | `Arg of int
               | `Exp | `In of ident | `Out of ident] * ty * loc
  exception Ill_kinded of [`Exp | `Var of ident] * ty * loc

  let check_kind e =
    let check_ty z e =
      let ty = M.ty_of e in
      if not @@ T.well_kinded ty then
        raise (Ill_kinded (z,ty,M.loc_of e))
    in
    let f e =
      match M.desc_of e with
      | Set (m,x,e0) ->
        if not (T.basic_type (M.ty_of e0)) then
          let tx = (match m with
                  | `Sig -> T.tsignal_
                  | `Out  -> T.toutput_) (M.ty_of e0)
          in
          raise (Ill_kinded (`Var x,tx,M.loc_of e))
      | Let(bs,_) ->
          List.iter (fun (x,e) -> check_ty (`Var x) e) bs
      | _ ->
        check_ty `Exp e
    in
    M.iter f e



  let rec typing_ci initial_env ci =
    let open M in
    let open Format in
    try

      (*  (too restrictive)

          if not (non_expansive ci.e) then
          raise (Should_be_non_expansive(ci.x,loc_of ci.e)); *)

      let env0 = List.fold_left (fun env (x,t) ->
          Env.add x t env) Env.empty
          ((List.map (fun (x,t) -> x,T.trivial_scheme t) @@
            ( (List.map (fun (x,t) -> x,T.tinput_ t) ci.inputs) @
              (List.map (fun (x,t) -> x,T.toutput_ t) ci.outputs) @
              (List.map (fun (x,e) -> x,M.ty_of e) ci.signals)
            )) @ initial_env)
      in

      typ_exp [] init_ctors env0 ci.e;

      (* check that the type of the circuit is a basic type *)
      (match T.get_type (ty_of ci.e) with
       | `TVar | `TInt | `TBool | `TUnit  -> ()
       | `TFun (ts,t) ->
           if not (T.basic_type t) then
             raise (Not_a_basic_type(`Ci ci.x,M.ty_of ci.e,M.loc_of ci.e));
         List.iteri (fun i t -> if not (T.basic_type t) then
                        raise (Not_a_basic_type(`Arg i,t,M.loc_of ci.e))) ts
       | (`TSig _ | `TIn _ | `TOut _) ->
         (raise (Not_a_basic_type(`Ci ci.x,M.ty_of ci.e,M.loc_of ci.e));)
      );

      let check_basics m l =
          List.iter (fun (x,t) ->
            if not (T.basic_type t) then
              raise (Not_a_basic_type(m x,t,M.loc_of ci.e))) l in
 
      (* check that inputs/outputs have basic types *)
      check_basics (fun x -> `In x) ci.inputs;
      check_basics (fun x -> `Out x) ci.outputs;


      (* check well-kindness of types of all subexpression *)
      check_kind ci.e;

    with
    | T.Cannot_unify(t1,t2,loc) ->
        let open Errors in
        error loc @@ fun fmt ->
        fprintf fmt
          "This expression has type %a but an expression was expected of type %a"
        (emph_pp red T.print_ty) t1
          (emph_pp green T.print_ty) t2
    | Unbound_value (x,loc) ->
        Errors.error loc @@ fun fmt ->
          fprintf fmt "Unbound value %s" x
    | Should_be_non_expansive (x,loc) ->
        Errors.error loc @@ fun fmt ->
          fprintf fmt "circuit %s should be non expansive" x
    | Not_a_basic_type (z,t,loc) ->
        let open Errors in
        error loc @@ fun fmt ->
          fprintf fmt
            "%s has type %a but it should have a basic type"
            (match z with
             | `In x -> "input "^x
             | `Out x -> "output "^x
             | `Exp -> "expression"
             | `Arg i -> "argument "^string_of_int i
             | `Ci x -> "return value of circuit "^x)
          (emph_pp red T.print_ty) t
    | Ill_kinded (z,t,loc) ->
        let open Errors in
        error loc @@ fun fmt ->
          fprintf fmt
            "%s has type %a which is ill kinded"
            (match z with
             | `Exp -> "This expression"
             | `Var x -> "name "^x)
          (emph_pp red T.print_ty) t
end

