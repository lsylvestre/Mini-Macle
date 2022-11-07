open Prelude


module type MACLE = sig
  type ty
  type const
  type pattern

  type prog = decl list
  and decl = TDef of ident * tdef | Ci of circuit
  and tdef = Sum of (ident * ty) list
  and circuit = {
    x:ident;
    inputs:(ident * ty) list;
    outputs:(ident * ty) list;
    signals:(ident * exp) list;
    e:exp
  }
  and exp = exp_desc * deco

  and exp_desc =
    private
    | Var of ident
    | Const of const
    | Cstor of ident * exp list
    | Fun of ident * exp
    | App of exp * exp
    | Let of (ident * exp) list * exp
    | Letrec of (ident * exp) list * exp
    | If of exp * exp * exp
    | Match of exp * (pattern * exp) list
    | Seq of exp * exp
    | Get of [`In  | `Sig] * ident
    | Set of [`Out | `Sig] * ident * exp
    | Automaton of (ident * exp) list * exp
    | Continue of ident
    | Par of exp * exp

  (** [deco] is a box that contains information of type and position
     of each subexpression *)
  and deco

  val desc_of : exp -> exp_desc
  val ty_of : exp -> ty
  val loc_of : exp -> loc

  (** [var_ ~ty:t x] constructs #[(x : t)] *)
  val var_ : ?loc:loc -> ?ty:ty -> ident -> exp
  (** [const_ ~ty:t c] constructs #[(c : t)] *)
  val const_ : ?loc:loc -> ?ty:ty -> const -> exp
  val cstor_ : ?loc:loc -> ?ty:ty -> ident -> exp list -> exp
  
  (** [fun_ ~ty:t x e] constructs #[fun (x : t) -> e] *)
  val fun_ : ?loc:loc -> ?ty:ty -> ident -> exp -> exp
  val app_ : ?loc:loc -> exp -> exp -> exp
  val let_ : ?loc:loc -> (ident * exp) list -> exp -> exp
  val letrec_ : ?loc:loc -> (ident * exp) list -> exp -> exp
  val if_ : ?loc:loc -> exp -> exp -> exp -> exp
  val seq_ : ?loc:loc ->  exp -> exp -> exp

  (* derivated constructs *)
  val app_list_ : ?loc:loc -> exp -> exp list -> exp
  val call_ : ?loc:loc -> const -> exp list -> exp
  val seq_list_ : ?loc:loc -> exp list -> after:exp -> exp

  (** [get_ ~ty:t `In x] constructs #[?(x:t)].
      [get_ ~ty:t `Sig x] constructs #[~(x:t)] *)
  val get_ : ?loc:loc -> ?ty:ty -> [`In | `Sig] -> ident -> exp
  (** [set_ ~ty:t `Out x e] constructs #[?(x:t) <- e].
      [set_ ~ty:t `Sig x e] constructs #[~(x:t) <- e] *)
  val set_ : ?loc:loc -> [`Out | `Sig] -> ident -> exp -> exp

  val match_ : ?loc:loc -> exp -> (pattern * exp) list -> exp
  val automaton_ : ?loc:loc -> (ident * exp) list -> exp -> exp
  val continue_ : ?loc:loc -> ?ty:ty -> ident -> exp
  val par_ : ?loc:loc -> exp -> exp -> exp

  val split_fun : exp -> (ident * ty) list * exp
  val uncurry : exp -> exp * exp list
  val eta_expansion : int -> exp -> exp

  val iter : (exp -> unit) -> exp -> unit

end



module type CONFIG = sig

  type ty

  val new_tvar : unit -> ty

  exception Cannot_unify of ty * ty * loc

  val unify : ?loc:loc -> ty -> ty -> unit
  val tfun_ : ty -> ty -> ty
  val is_fun : ty -> bool
  val tunit_ : ty
  val tinput_ : ty -> ty
  val toutput_ : ty -> ty
  val tsignal_ : ty -> ty

  type const
  type pattern

end

module Make (P : CONFIG)
  : (MACLE with
     type ty = P.ty and
     type const = P.const and
     type pattern = P.pattern) = struct

  include P

  type prog = decl list
  and decl = TDef of ident * tdef | Ci of circuit
  and tdef = Sum of (ident * ty) list

  and circuit = {
    x:ident;
    inputs:(ident * ty) list;
    outputs:(ident * ty) list;
    signals:(ident * exp) list;
    e:exp
  }

  and exp = exp_desc * deco

  and exp_desc =
    | Var of ident
    | Const of const
    | Cstor of ident * exp list
    | Fun of ident * exp
    | App of exp * exp
    | Let of (ident * exp) list * exp
    | Letrec of (ident * exp) list * exp
    | If of exp * exp * exp
    | Match of exp * (pattern * exp) list
    | Seq of exp * exp
    | Get of [`In  | `Sig] * ident
    | Set of [`Out | `Sig] * ident * exp
    | Automaton of (ident * exp) list * exp
    | Continue of ident
    | Par of exp * exp

  and deco = (ty * loc)

  let desc_of (desc,_) = desc
  let deco_of (_,deco) = deco
  let loc_of (_,(_,loc)) = loc
  let ty_of (_,(ty,_)) = ty
  let exp ?(loc=dloc) ?(ty=new_tvar()) de =
    de, (ty, loc)

  (* smart constructors *)

  let var_ ?loc ?ty x = exp ?loc ?ty @@ Var x

  let const_ ?loc ?ty c = exp ?loc ?ty @@ Const c

  let cstor_ ?loc ?ty x es = exp ?loc ?ty @@ Cstor(x,es)

  let fun_ ?loc ?(ty=new_tvar()) x e =
    exp ?loc ~ty:(tfun_ ty (ty_of e)) @@ Fun(x,e)

  let app_ ?loc e1 e2 =
    let v = new_tvar() in
    (* unify (ty_of e1) (tfun_ (ty_of e2) v); *)
    exp ?loc ~ty:v @@ App(e1,e2)

  let if_ ?loc e1 e2 e3 =
    exp ?loc ~ty:(ty_of e2) @@ If(e1,e2,e3)

  let let_ ?loc bs e =
    match bs with
    | [] -> e
    | _ -> exp ?loc ~ty:(ty_of e) @@ Let(bs,e)

  let letrec_ ?loc bs e =
    match bs with
    | [] -> e
    | _ -> exp ?loc ~ty:(ty_of e) @@ Letrec(bs,e)

  let seq_ ?loc e1 e2 =
    exp ?loc ~ty:(ty_of e2) @@ Seq(e1,e2)

  let get_ ?loc ?ty mode x =
    exp ?loc ?ty @@ Get(mode,x)

  let set_ ?loc mode x e =
    exp ?loc ~ty:tunit_ @@ Set(mode,x,e)

  let match_ ?(loc=dloc) e cases =
    match cases with
    | [] -> invalid_arg "match_"
    | _ -> exp ~loc @@ Match(e,cases)

  let automaton_ ?loc ts e =
    match ts with
    | [] -> e
    | _ -> exp ?loc ~ty:(ty_of e) @@ Automaton(ts,e)

  let continue_ ?loc ?ty q = exp ?loc ?ty @@ Continue q

  let par_ ?loc e1 e2 = exp ?loc ~ty:tunit_ @@ Par(e1,e2)


  let app_list_ ?loc e es =
    List.fold_left app_ e es

  let call_ ?loc c es =
    app_list_ ?loc (const_ c) es

  let seq_list_ ?loc es ~after:e =
    List.fold_left (fun acc e -> seq_ e acc) e es

  let split_fun e =
    let rec loop xs e =
      match desc_of e, ty_of e with
      | Fun (x,e),t ->
          let w = new_tvar() in
          (try
             unify ~loc:(loc_of e) t (tfun_ w (ty_of e))
           with Cannot_unify _ -> assert false);
          loop ((x,w)::xs) e
      | _ ->
          List.rev xs,e
    in loop [] e

  let uncurry e =
    let rec loop aas e =
      match desc_of e with
      | App (e,a) -> loop (a::aas) e
      | _ -> e, (*List.rev *)aas
    in loop [] e

  let eta_expansion n e =
    let xs = List.init n (fun _ -> Prelude.gensym ~prefix:"eta" ()) in
    let fe = List.fold_right fun_ xs e in
    List.fold_right (fun x e -> app_ e (var_ x)) (List.rev xs) fe

  let iter f e =
    let rec i e =
      f e;
      match (desc_of e) with
      | Const _ | Var _ -> ()
      | Fun(_,e) ->
          i e
      | App(e,_) ->
          i e
      | If(e1,e2,e3) ->
          i e1; i e2; i e3
      | Let(bs,e)
      | Letrec(bs,e)
      | Automaton(bs,e) ->
          List.iter (fun (_,e) -> i e) bs; i e
      | Seq(e1,e2) ->
          i e1; i e2
      | Get _ -> ()
      | Set(_,_,e) ->
          i e
      | Continue _ -> ()
      | Par(e1,e2) ->
          i e1; i e2
      | Match(e,cases) ->
          i e; List.iter (fun (_,e) -> i e) cases
      | Cstor(_,es) ->
          List.iter i es
    in i e

end







