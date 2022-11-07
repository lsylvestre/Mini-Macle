let flag_print_ty_annot = ref false

(** Macle pretty printer *)
module Make (M:Syntax.MACLE)(C:Const.CONST with type t = M.const and type Type.ty = M.ty) = struct
  open M
  open Format
  let pp_ident fmt x = fprintf fmt "%s" x

  (** [is_aexp e] return [true] if the expression [e]
      never needs to be parenthesized *)
  let is_aexp e = match desc_of e with
  | Var _ | Const _ -> true
  | _ -> false

  (** [is_a_seq e] return [true] if [e] is a sequence [(e1; e2)] *)
  let is_a_seq e = match desc_of e with
    | Seq _ -> true
    | _ -> false

  (** [paren ~is_par:b fmt pp] put parenthesis around pretty printer [pp] *)
  let paren ~is_par fmt pp =
    if is_par then begin
      fprintf fmt "(";
      pp fmt;
      fprintf fmt ")"
    end else pp fmt

  let ty_annot_binding ?(is_par=false) x fmt ty =
    if !flag_print_ty_annot then
      paren ~is_par fmt (fun fmt ->
        fprintf fmt "%a : %a" pp_ident x C.Type.print_ty ty)
    else pp_ident fmt x


  (** pretty printer for expressions *)
  let pp_exp fmt e =
    let rec pp_exp ~is_par fmt e =
      paren ~is_par:(not (is_aexp e) && is_par) fmt @@ fun fmt ->
        match desc_of e with
        | Var x ->
            pp_ident fmt x
        | Const c ->
            C.pp_const fmt c
        | Cstor (x,[]) ->
            pp_ident fmt x
        | Cstor (x,es) ->
            pp_ident fmt x;
            fprintf fmt "(";
            pp_print_list
              ~pp_sep:(fun fmt () -> fprintf fmt ", ")
              (pp_exp ~is_par:false) fmt es;
            fprintf fmt ")"
        | Fun (x,e0) ->
            fprintf fmt "@[<hov 2>fun ";
              (let v = C.Type.new_tvar() in
              C.Type.unify ~loc:(M.loc_of e) (M.ty_of e) (C.Type.tfun_ v (M.ty_of e0));
              ty_annot_binding ~is_par:true x fmt v);
              fprintf fmt " -> @,%a@,@]"
              (pp_exp ~is_par:false) e0
        | App(e1,e2) ->
            let e0,es = uncurry e in
            if (match desc_of e0 with
                | Const c ->
                    (C.pp_appc c fmt (pp_exp ~is_par:true) es) = None
                | _ -> true) then
            let is_app = match desc_of e1 with
            | App _ -> true | _ -> false in
            fprintf fmt "@[<v>%a %a@]"
              (pp_exp ~is_par:(not is_app)) e1
              (pp_exp ~is_par:true) e2
        | If(e1,e2,e3) ->
            fprintf fmt "@[<v>if %a then %a else @,%a@]"
              (pp_exp ~is_par:false) e1
              (pp_exp ~is_par:true) e2
              (pp_exp ~is_par:(is_a_seq e3)) e3
        | Let(bs,e) ->
            pp_let ~is_par ~is_rec:false fmt bs e
        | Letrec(bs,e) ->
            pp_let ~is_par ~is_rec:true fmt bs e
        | Seq(e1,e2) ->
            fprintf fmt "@[<hov>%a; @,%a@]"
              (pp_exp ~is_par:true) e1
              (pp_exp ~is_par:false) e2
        | Get(m,x) ->
            fprintf fmt "@[<hov>%s%a@]"
              (match m with `In -> "?" | `Sig -> "~")
              pp_ident x
        | Set(m,x,e) ->
            fprintf fmt "@[<hov>%s%a <- %a@]"
              (match m with `Out -> "?" | `Sig -> "~")
              pp_ident x
              (pp_exp ~is_par:false) e
        | Automaton(ts,e) ->
            fprintf fmt "@[<v>automaton";
            List.iter (fun (q,e) -> fprintf fmt "@,| %a -> %a"
                                       pp_ident q
                                       (pp_exp ~is_par:false) e) ts;
            fprintf fmt "@,in %a@]" (pp_exp ~is_par:false) e;
       | Continue q ->
            fprintf fmt "@[<hov>continue %a@]" pp_ident q
       | Par(e1,e2) ->
            fprintf fmt "@[<v 4>(%a //@, %a)@,@]"
              (pp_exp ~is_par:true) e1
              (pp_exp ~is_par:true) e2
       | Match _ -> assert false (*todo*)
  and pp_let ~is_par ~is_rec fmt bs e =
    fprintf fmt "@[<v>let ";
    if is_rec then fprintf fmt "rec ";
    pp_print_list
      ~pp_sep:(fun fmt () -> fprintf fmt "@,and ")
      (fun fmt (x,e) ->
        ty_annot_binding x fmt (M.ty_of e);
        fprintf fmt " =";
        (if is_rec then fprintf fmt "@," else fprintf fmt " ");
        fprintf fmt "@[<v>%a@]"
          (pp_exp ~is_par:false) e) fmt bs;
    fprintf fmt " in@,@]%a" (pp_exp ~is_par:false) e

  in pp_exp ~is_par:false fmt e

  let pp_ci fmt {x;inputs=ii;outputs=oo;signals;e} =
    fprintf fmt "@[<v 2>circuit %a =@," pp_ident x;

    (match ii with
    | [] -> ()
    | _ ->
       fprintf fmt "input ";
       pp_print_list
          ~pp_sep:(fun fmt () -> fprintf fmt ", ")
          (fun fmt (x,t) -> ty_annot_binding x fmt t) fmt ii;
       fprintf fmt ";@,");

    (match oo with
    | [] -> ()
    | _ ->
       fprintf fmt "output ";
       pp_print_list
          ~pp_sep:(fun fmt () -> fprintf fmt ", ")
          (fun fmt (x,t) -> ty_annot_binding x fmt t) fmt oo;
       fprintf fmt ";@,");

    List.iter (fun (x,e) ->
        fprintf fmt "signal %a = %a in@,"
          (ty_annot_binding x) (C.Type.tsignal_ (M.ty_of e))
          pp_exp e) signals;

    pp_exp fmt e;
    fprintf fmt "@]"

end

