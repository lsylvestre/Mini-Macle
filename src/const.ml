open Prelude

module type CONST = sig
  type t

  val pp_const : Format.formatter -> t -> unit
  val pp_appc : t -> Format.formatter -> (Format.formatter -> 'a -> unit) -> 'a list -> unit option
  val unit_ : t
  val bool_ : bool -> t
  val int_ : int -> t
  val parallel_and_ : t
  val parse_prim_opt : ident -> t option
  val parse_prim : ident -> t

  val signal_create : t
  val signal_create_uninitialized : t
  val output_create_uninitialized : t

  val size_ : int -> t

  val is_seq : t -> bool
  val is_pure : t -> bool
  val is_sig_creation : t -> bool

  module Type : sig

    type ty

    val as_const_opt : ty -> [> `TInt | `TBool | `TUnit ] option

    type scheme
    val new_tvar : unit -> ty
    val tfun_ : ty -> ty -> ty
    val is_fun : ty -> bool
    val is_unit : ty -> bool
    val is_signal : ty -> bool
    val get_type : ty -> ([> `TVar | `TInt | `TBool | `TUnit | `TFun of ty list * ty
                          | `TSig of 'a | `TIn of 'a | `TOut of 'a] as 'a)
    val arity : ty -> int
    val tunit_ : ty
    val tbool_ : ty
    val tint_ : ty
    val tsize_ : int -> ty
    val toutput_ : ty -> ty
    val tsignal_ : ty -> ty
    val tinput_ : ty -> ty
    val tcstor_ : ident -> ty list -> ty
    val trivial_scheme : ty -> scheme

    exception Cannot_unify of ty * ty * loc

    val unify : ?loc:loc -> ty -> ty -> unit
    val instance : scheme -> ty
    val const_typing : t -> scheme
    type env = (ident * scheme) list
    val generalize : env -> ty -> scheme

    val basic_type : ty -> bool
    val well_kinded : ty -> bool

    val print_ty : Format.formatter -> ty -> unit
  end

  val const_to_macle_runtime : t ->
            [ `Bool of bool
            | `Int of int
            | `Unit
            | `Instantaneous of string
            | `PacketCreate
            | `PacketGet
            | `PacketSet
            | `SigCreate ]
end

module type PATTERN = sig
  type t = private
  | PVar of ident
  | PWildcard
  | PTuple of t list
  | PCstor of ident * t list
end




module Const : CONST = struct
  type t =
    | Bool of bool
    | Int of int
    | Unit
    | Prim of prim
    | Size of int
  and prim = Add | Sub | Mul | Div | Mod | Eq | Neq | Lt | Gt | Le | Ge
  | Parallel_and
  | Signal_create_uninitialized | Output_create_uninitialized
  | Signal_create | Packet_create | Packet_get | Packet_set
  let unit_ = Unit
  let bool_ b = Bool b
  let int_ n = Int n
  let parallel_and_ = Prim Parallel_and
  let size_ n = Size n

  let signal_create = Prim Signal_create
  let signal_create_uninitialized = Prim Signal_create_uninitialized
  let output_create_uninitialized = Prim Output_create_uninitialized
  let parse_prim_opt p =
    let exception Ident in
    try
      Some (Prim
            (match p with
            | "+" -> Add
            | "-" -> Sub
            | "*" -> Mul
            | "/" -> Div
            | "mod" -> Mod
            | "==" -> Eq
            | "!=" -> Neq
            | "<" -> Lt
            | ">" -> Gt
            | "<=" -> Le
            | ">=" -> Ge
            | "&&." -> Parallel_and
            | "signal_create_uninitialized" -> Signal_create_uninitialized
            | "output_create_uninitialized" -> Output_create_uninitialized
            | "signal_create" -> Signal_create
            | "packet_create" -> Packet_create
            | "packet_get" -> Packet_get
            | "packet_set" -> Packet_set
            | x -> raise Ident))
    with Ident -> None

  let parse_prim x =
    match parse_prim_opt x with
    | None -> invalid_arg ("Const.parse_prim: "^x)
    | Some c -> c

  let is_pure c =
    match c with
    | Unit | Int _ | Bool _ | Size _ -> true
    | Prim(Add|Sub|Mul|Div|Mod|Lt|Gt|Le|Ge|Eq|Neq) -> true
    | Prim(Packet_create|Packet_get) -> true
    | _ -> false

  let is_sig_creation c =
    match c with
    | Prim(Signal_create|Signal_create_uninitialized) -> true
    | _ -> false
;;
  (* take more than 1 cycle to be applyed *)
  let is_seq c =
    (not (is_pure c)) &&
      (match c with
       | Prim(Signal_create|Signal_create_uninitialized) -> false
       | _ -> true)



  module Type = struct

    type ty =
    | TVar of tvar ref
    | TFun of ty * ty
    | TTuple of ty list
    | TConst of tconst
    | TCstor of ident * ty list
    | TSize of int

    and type_variable = tvar ref

    and tvar =
      V of int
    | T of ty
    and tconst = TInt | TBool | TUnit

    let as_const_opt = function
    | TConst TInt -> Some `TInt
    | TConst TBool -> Some `TBool
    | TConst TUnit -> Some `TUnit
    | _ -> None

    module Vs = Set.Make(Int)

    type scheme = Forall of (Vs.t * ty)

    let new_tvar = let c = ref 0 in fun () -> incr c; TVar(ref (V !c))

    let tunit_ = TConst TUnit
    let tbool_ = TConst TBool
    let tint_ = TConst TInt
    let tpair_ t1 t2 = TCstor("*",[t1;t2])
    let tref_ t = TCstor("ref",[t])
    let tarray_ t = TCstor("array",[t])
    let tsize_ n = TSize n
    let tsignal_ t = TCstor("signal",[t])
    let tpacket_ t z = TCstor("packet",[t;z])
    let toutput_ t = TCstor("output",[t])
    let tinput_ t = TCstor("input",[t])
    let tcstor_ x tys = TCstor(x,tys)

    let trivial_scheme t = Forall(Vs.empty,t)
    let tfun_ t1 t2 = TFun(t1,t2)
    
    let rec is_fun = function
    | TVar {contents=T t} -> is_fun t
    | TFun _ -> true 
    | _ -> false
    
    let rec is_unit = function
    | TVar {contents=T t} -> is_unit t
    | TConst TUnit -> true 
    | _ -> false
  
    let rec is_signal = function
    | TVar {contents=T t} -> is_signal t
    | TCstor("signal",_) -> true 
    | _ -> false
    
    let rec get_type t =
      match t with
      | TVar{contents=T t} -> get_type t
      | TVar _ -> `TVar
      | TConst TUnit -> `TUnit
      | TFun _ ->
          let rec loop acc = function
          | TFun(t1,t2) -> loop (t1::acc) t2
          | t' -> `TFun (List.rev acc, t')
          in loop [] t
      | TConst TBool -> `TBool
      | TConst TInt -> `TInt
      | TCstor("signal",[t]) -> `TSig (get_type t)
      | TCstor("input",[t]) -> `TIn (get_type t)
      | TCstor("output",[t]) -> `TOut (get_type t)
      | _ -> assert false (* ill-formed type *)

  let arity t =
    match get_type t with
    | `TFun (ts,_) -> List.length ts
    | _ -> 0

  let rec canon ty =
    match ty with
    | TVar({contents=T ty'} as v) ->
        let ty2 = canon ty' in
        v := T ty2; ty2
    | TVar{contents=V _} ->
        ty
    | TFun(ty1,ty2) ->
        TFun (canon ty1, canon ty2)
    | TTuple tys ->
        TTuple(List.map canon tys)
    | TCstor(c,tys) ->
        TCstor(c,List.map canon tys)
    | _ -> ty


  let rec occur v ty =
    let exception Found in
    let rec f = function
    | TVar {contents=V v'} ->
        if v = v' then raise Found
    | TVar {contents=T ty} -> f ty
    | TFun(ty1,ty2) ->
        f ty1;f ty2
    | TTuple tys
    | TCstor(_,tys) ->
       List.iter f tys
    | TConst _ | TSize _ -> ()
  in try f ty; false with Found -> true

let rec print_ty fmt ty =
  let open Format in
  match canon ty with
  | TConst TInt -> fprintf fmt "int"
  | TConst TBool -> fprintf fmt "bool"
  | TConst TUnit -> fprintf fmt "unit"
  | TCstor (t,[]) -> fprintf fmt "%s" t
  | TCstor (t,[ty]) -> fprintf fmt "%a %s" print_ty ty t
  | TCstor (t,tys) ->
      fprintf fmt "(";
      pp_print_list
        ~pp_sep:(fun fmt () -> fprintf fmt ", ")
        print_ty fmt tys;
      fprintf fmt ") %s" t;
  | TVar{contents=V n} ->
      fprintf fmt "'a%d" n
  | TVar{contents=T t} ->
      fprintf fmt "%a" print_ty t
  | TFun(t1,t2) ->
      fprintf fmt "(%a -> %a)" print_ty t1 print_ty t2
  | TSize n ->
      fprintf fmt "'size_%d" n
  | TTuple _ -> assert false (*todo*)

  exception Cannot_unify of ty * ty * loc

  let unify ?(loc=dloc) t1 t2 =

    let cannot_unify t1 t2 =
      raise (Cannot_unify(t1,t2,loc)) in

    let rec unify_types t1 t2 =
      let t1 = canon t1 and t2 = canon t2 in
      let unify_list tys1 tys2 =
        if List.compare_lengths tys1 tys2 <> 0 then
            cannot_unify t1 t2;
        List.iter2 unify_types tys1 tys2
      in
      match t1,t2 with
      | TConst c1,TConst c2 -> if c1 <> c2 then cannot_unify t1 t2;
      | TTuple tys1, TTuple tys2 ->
         unify_list tys1 tys2
      | TCstor(c1,tys1),TCstor(c2,tys2) ->
          if c1 <> c2 then cannot_unify t1 t2;
          unify_list tys1 tys2
      | TFun(t1,t1'),TFun(t2,t2') ->
         unify_types t1 t2;
         unify_types t1' t2'
      | TSize n, TSize m ->
         if n <> m then cannot_unify t1 t2;
      | TVar {contents=(V n)},
        TVar ({contents=V m} as v) ->
          if n = m then () else v := T t1
      | TVar ({contents=T t1'}),
        TVar ({contents=T t2'}) ->
           unify_types t1' t2'
      | TVar ({contents=T t'} as v),t
      | t,TVar ({contents=T t'} as v) ->
           v := T t;
           unify_types t' t
      | TVar ({contents=V n} as v),t
      | t,TVar ({contents=V n} as v) ->
          if occur n t then cannot_unify t1 t2;
          v := T t
      | _ -> cannot_unify t1 t2
    in unify_types t1 t2



  let vars_of_type (t:ty) : Vs.t =
    let rec vars s = function
    | TConst _ | TSize _ -> s
    | TTuple ts | TCstor(_,ts) ->
       List.fold_left vars s ts
    | TVar vt ->
         (match !vt with
             V n ->
               Vs.add n s
           | T ty ->
               vars s ty)
    | TFun (ty1,ty2) ->
          vars (vars s ty1) ty2
     in
     vars Vs.empty t ;;

  let free_vars_of_type (bv,t) =
    Vs.diff (vars_of_type t) bv

  let instance (Forall(vs,ty)) =
    let unknowns = Hashtbl.create (Vs.cardinal vs) in
    Vs.iter (fun n -> Hashtbl.add unknowns n (new_tvar())) vs;
     let rec instance = function
       TVar {contents=(V n)} as t ->
          (try Hashtbl.find unknowns n with Not_found -> t)
     | TVar {contents=(T t)} ->
         instance t
     | (TConst _ | TSize _) as t ->
         t
     | TTuple ts ->
         TTuple(List.map instance ts)
     | TCstor(c,ts) ->
         TCstor(c,List.map instance ts)
     | TFun (t1,t2) ->
         TFun (instance t1, instance t2)
     (* | TSize _ as t -> t *)
     in
       instance ty

  let free_vars_of_type_env l =
    List.fold_left (fun vs (x,Forall (v,t)) ->
                    Vs.union vs (free_vars_of_type (v,t)) )
      Vs.empty l

      type env = (ident * scheme) list

  let generalize r ty =
    let fvg = free_vars_of_type_env r in
    Forall(free_vars_of_type (fvg,ty),ty)

  let tvar_a = TVar (ref (V (-1)))
  let tvar_b = TVar (ref (V (-2)))
  let tvar_z = TVar (ref (V (-3)))

  let id = function
  | TVar {contents=V n} -> n
  | _ -> assert false

  let forall vs t =
    Forall(Vs.(of_list vs),t)

  (* typing environnement for constants *)
  let const_typing = function
  | Prim (Add|Mul|Sub|Div|Mod) -> forall [] @@ tfun_ tint_ (tfun_ tint_ tint_)
  | Prim (Lt|Gt|Le|Ge) -> forall [] @@ tfun_ tint_ (tfun_ tint_ tbool_)
  | Prim (Eq|Neq) -> forall [id tvar_a] @@ tfun_ tvar_a (tfun_ tvar_a tbool_)
  | Prim(Parallel_and) -> forall [] @@ tfun_ tbool_ (tfun_ tbool_ tbool_)
  | Prim (Signal_create) -> forall [id tvar_a] @@ tfun_ tvar_a (tsignal_ tvar_a)
  | Prim (Signal_create_uninitialized) -> forall [id tvar_a] @@ tfun_ tunit_ (tsignal_ tvar_a)
  | Prim (Output_create_uninitialized) -> forall [id tvar_a] @@ tfun_ tunit_ (toutput_ tvar_a)
  | Prim (Packet_create) ->
      forall [id tvar_a;id tvar_z] @@ tfun_ tvar_z (tfun_ tvar_a (tpacket_ tvar_a tvar_z))
  | Prim (Packet_get) ->
      forall [id tvar_a;id tvar_z] @@ tfun_ (tpacket_ tvar_a tvar_z) (tfun_ tint_ tvar_a)
  | Prim (Packet_set) ->
      forall [id tvar_a;id tvar_z] @@ tfun_ (tpacket_ tvar_a tvar_z) (tfun_ tint_ (tfun_ tvar_a tunit_))
  | Int _ -> forall [] tint_
  | Bool _ -> forall [] tbool_
  | Unit -> forall [] tunit_
  | Size n -> forall [] (tsize_ n)

  let rec basic_type t =
    match t with
    | TConst _ | TVar{contents=V _} -> true
    | TVar{contents=T t} -> basic_type t
    | _ -> false

  let rec well_kinded t =
    match t with
    | TVar{contents=T t} -> well_kinded t
    | TConst _ | TVar {contents=V _}
    | TSize _ | TFun _ -> true
    | TTuple ts -> List.for_all well_kinded ts
    | TCstor("signal",[t])
    | TCstor("input",[t])
    | TCstor("output",[t]) ->
        basic_type t
    | _ -> assert false (* todo *)

  end

  (** pretty printer for constants *)
  let pp_const fmt = function
  | Bool b -> Format.fprintf fmt "%b" b
  | Int n -> Format.fprintf fmt "%d" n
  | Unit -> Format.fprintf fmt "()"
  | Prim p ->
      Format.fprintf fmt "%s"
      (match p with
      | Add -> "+"
      | Sub -> "-"
      | Mul -> "*"
      | Div -> "/"
      | Mod -> "mod"
      | Eq -> "=="
      | Neq -> "!="
      | Lt -> "<"
      | Gt -> ">"
      | Le -> "<="
      | Ge -> ">="
      | Parallel_and -> "&&."
      | Signal_create_uninitialized -> "signal_create_uninitialized"
      | Output_create_uninitialized -> "output_create_uninitialized"
      | Signal_create -> "signal_create"
      | Packet_create -> "packet_create"
      | Packet_get -> "packet_get"
      | Packet_set -> "packet_set")
  | Size n ->
      Format.fprintf fmt "%n" n

  let binop = function
  | Prim(Add|Sub|Mul|Div|Mod|Eq|Neq|Lt|Le|Gt|Ge|Parallel_and) -> true
  | _ -> false;;

  let some_unit = Some ()

  let pp_appc c fmt pp_exp es =
    let exception Partial in
    try
      (match c,es with
      | c,[e1;e2] when binop c ->
         Format.fprintf fmt "%a %a %a" pp_exp e1 pp_const c pp_exp e2
      | c,[_] when binop c ->
        (* todo : couper ? why ?? *)
        Format.fprintf fmt "@[<hov>(%a) " pp_const c;
        Format.pp_print_list
              ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
              pp_exp fmt es;
        Format.fprintf fmt "@]"
      | _ -> raise Partial) ; some_unit
  with Partial -> None

  let const_to_macle_runtime = function
  | Bool b -> `Bool b
  | Int n -> `Int n
  | Unit -> `Unit
  | Size _ -> assert false (*todo*)
  | Prim p ->
      (match p with
      | Add -> `Instantaneous "macle_add"
      | Sub -> `Instantaneous "macle_sub"
      | Mul -> `Instantaneous "macle_mul"
      | Div -> `Instantaneous "macle_div"
      | Mod -> `Instantaneous "macle_mod"
      | Eq -> `Instantaneous "macle_eq"
      | Neq -> `Instantaneous "macle_neq"
      | Lt -> `Instantaneous "macle_lt"
      | Gt -> `Instantaneous "macle_gt"
      | Le -> `Instantaneous "macle_le"
      | Ge -> `Instantaneous "macle_ge"
      | Parallel_and -> `Instantaneous "macle_and"
      | Signal_create_uninitialized -> `SigCreate
      | Output_create_uninitialized -> `SigCreate
      | Signal_create -> `SigCreate
      | Packet_create -> `PacketCreate
      | Packet_get -> `PacketGet
      | Packet_set -> `PacketSet)

end


include Const




(* todo *)
module Pattern : PATTERN = struct
  type t =
  | PVar of ident
  | PWildcard
  | PTuple of t list
  | PCstor of ident * t list
end
