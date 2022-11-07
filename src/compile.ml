open Const
open Prelude

module M = Macle

let list_map_snd f l =
  List.map (fun (a,b) -> (a,f b)) l


module Anf = struct
  open M

  let is_atom e =
    match desc_of e with
    | Var _ | Const _ | Fun _ -> true
    | _ -> false

  let tmpsym () = gensym ~prefix:"tmp" ()

  (** [anf e] translates [e] in ANF form *)
  let rec anf e =
    match desc_of e with
    | Var _ | Const _ ->
        e
    | Fun(x,e) ->
        fun_ x (anf e)
    | Cstor(x,es) ->
        let bs = List.map (fun e -> tmpsym(),e) es in
      let_ bs (cstor_ x (List.map (fun (x,_) -> var_ x) bs))
    | App(e1,e2) ->
        let x = tmpsym() in
        let_ [x, anf e2] (app_ (anf e1) (var_ x))
    | Let(bs,e) ->
        let_ (list_map_snd anf bs) (anf e)
    | Letrec(bs,e) ->
        letrec_ (list_map_snd anf bs) (anf e)
    | If(e1,e2,e3) ->
        let x = tmpsym() in
        let_ [x, anf e1] (if_ (var_ x) (anf e2) (anf e3))
    | Seq(e1,e2) ->
        seq_ (anf e1) (anf e2)
    | Get _ ->
        e
    | Set(m,x,e) ->
        let y = tmpsym() in
        let_ [y, anf e] (set_ m x (var_ y))
    | Match(e,cases) ->
      let x = tmpsym() in
      let_ [x, anf e]
        (match_ (var_ x) (list_map_snd anf cases))
    | Automaton(ts,e) ->
        automaton_ (list_map_snd anf ts) (anf e)
    | Continue _ ->
        e
    | Par(e1,e2) ->
          par_ (anf e1) (anf e2)

  let eta_expansion_anf n e =
    let rec eta n e =
      if n <= 0 then e else
        match desc_of e with
        | Fun _ ->
            eta (n-1) e
        | Var _ | Const _ | App _ ->
            eta_expansion n e
        | ( Cstor _ | Get _ | Set _
          | Automaton _ | Continue _ | Par _) ->
            assert false (* impossible *)
        | Let(bs,e) ->
            let_ bs (eta n e)
        | Letrec(bs,e) ->
            letrec_ bs (eta n e)
        | If(a,e1,e2) ->
            if_ a (eta n e1)
                  (eta n e2)
        | Seq(e1,e2) ->
            seq_ e1 (eta n e2)
        | Match(a,cases) ->
          match_ a (list_map_snd (eta n) cases)
    in eta n e

  end


module Beta_reduction = struct
  open Anf
  open M
  let app bs e =
    (* if List.not (is_atom ax) then invalid_arg "beta_reduce" else *)
    let rec subst e =
      match desc_of e with
      | Var x ->
        (match List.assoc_opt x bs with
         | Some a -> a
         | None -> e)
      | Const _ -> e
      | Cstor(x,es) ->
          cstor_ x (List.map subst es)
      | Fun(x,e0) ->
          (match List.assoc_opt x bs with
           | Some _ -> e
           | None -> fun_ x (subst e0))
      | App(e,a) ->
           app_ (subst e) (subst a)
      | Let(bs',e) ->
          let_ (list_map_snd subst bs')
            (subst e)
      | Letrec(bs',e) ->
          if List.exists (* à revoir *) (fun (x,_) ->
               List.mem_assoc x bs) bs' then e else
          letrec_ (list_map_snd subst bs')
            (subst e)
      | If(a,e1,e2) ->
          if_ (subst a) (subst e1) (subst e2)
      | Seq(e1,e2) ->
          seq_ (subst e1) (subst e2)
      | Get (m,x) ->
          let x' = match List.assoc_opt x bs with
                   | Some (Var y,_) -> y
                   | Some _ -> failwith "beta-reduce err 1"
                   | None -> x in
          get_ m x'
      | Set(m,x,e) ->
          let x' = match List.assoc_opt x bs with
                   | Some (Var y,_) -> y
                   | Some _ -> failwith "beta-reduce err 2"
                   | None -> x in
          set_ m x' (subst e)
      | Automaton(ts,e) ->
          automaton_ (list_map_snd subst ts) (subst e)
      | Continue q ->
         (match List.assoc_opt q bs with
           | Some a -> a
           | None -> e)
      | Par(e1,e2) ->
          par_ (subst e1) (subst e2)
      | Match(e,cases) ->
          assert false (*todo*)
      in subst e
end

module Inl = struct
  open M
  module A = Anf
  module S = Beta_reduction

  let rec inl e =
    match desc_of e with
    (* atoms are unchanged *)
    | Var _ | Const _ -> e
    | Cstor(c,es) ->
       cstor_ c (List.map inl es)
    | Fun(x,e) -> fun_ x (inl e)
    (* functions are applied when possible *)
    | App(e,a) ->
        let e' = inl e in
        (match desc_of e' with
         | Fun(x,e0) ->
            inl @@ S.app [x,a] e0
         | Seq(e1,e2) ->
            inl @@ seq_ e1 (app_ e2 a)
         | Let(bs,e2) ->
            inl @@ let_ bs (app_ e2 a)
         | _ -> app_ e' a)
    | If(a,e1,e2) ->
        if_ a (inl e1) (inl e2)
    (* atoms are propagated (constant and copy propagation + inlining) *)
    | Let(bs,e) ->
        let bs = list_map_snd inl bs in
        let bsa,bse = List.partition (fun (_,ei) -> A.is_atom ei) bs in
        if List.length bse > 1 && List.for_all (fun (_,ei) -> not (Const.Type.is_fun (* or is_sig *)(M.ty_of ei))) bse then
          (let_ bse @@ inl (S.app bsa e))
        else
          let rec loop bs_ok bse e =
          match bse with
          | [] -> List.fold_left (fun e bs -> let_ bs e) e (List.rev bs_ok)
          (* | (xi,ei,false)::bs -> M.let_ [xi,ei] (loop bs e) *)
          | (xi,ei)::bs ->
             (match desc_of ei with
             | Var _ | Const _ | Fun _ | Cstor _ | App _ | Continue _
             | Get _ | Set _ | Par _ ->
                loop ([xi,ei]::bs_ok) bs e
             | Let(bs',e') ->
                 loop (bs'::[xi,e']::bs_ok) bs e
             | Automaton(ts,e') ->
                 (loop ([xi,e']::bs_ok) bs (automaton_ ts e))
             | Letrec(bs',e') ->
                 letrec_ bs' @@
                 loop ([xi,e']::bs_ok) bs e
             | If(a,e1,e2) ->
                 (* General case : duplicating the continuation.
                    It is a safe maniere to proceed in the general case
                    (nottably in presence of hiher-order-functions or
                     functions parameterized by signals)
                    but it doubles the size of the expression. *)
                 if_ a (loop ([xi,e1]::bs_ok) bs e)
                       (loop ([xi,e2]::bs_ok) bs e)
             | Seq(e1,e2) ->
                 seq_ e1 (loop ([xi,e2]::bs_ok) bs e)
             | _ -> assert false)
           in (loop [] bse (inl @@ S.app bsa e))
    | Letrec(bs,e) ->
        let bs' = list_map_snd inl bs in
        let theta = List.map (fun (x,e) ->
            x,(letrec_ bs' (var_ x))) bs' in
        (S.app theta e)
    | Seq(e1,e2) ->
        seq_ (inl e1) (inl e2)
    | Get _ -> e
    | Set(x,m,a) ->
       set_ x m (inl a)
    | Automaton(ts,e) ->
        automaton_ (list_map_snd inl ts) (inl e)
    | Continue _ -> e
    | Par(e1,e2) ->
      par_ (inl e1) (inl e2)
    | Match _ -> assert false (* todo *)
end



module Norm = struct
  open M

  module S = Beta_reduction

  let rec nrm e =
    match desc_of e with
    | Var _ | Const _ | Cstor _ -> e
    | Fun(x,e) ->
        fun_ x (nrm e)
    (* functions are applied when possible *)
    | App(e,a) ->
        let e' = nrm e in
        (match desc_of e' with
         | Fun(x,e0) ->
             nrm @@ S.app [x,a] e0
         | Let(bs,e0) ->
            let_ bs (nrm (app_ e0 a))
         | Letrec(bs,e0) ->
            letrec_ bs (nrm (app_ e0 a))
         | If(a',e1,e2) ->
            if_ a' (nrm (app_ e1 a)) (nrm (app_ e2 a))
         | _ -> app_ e' a)
    | If(a,e1,e2) ->
        if_ a (nrm e1) (nrm e2)
    (* atoms are propaged (constant and copy propagation + inlining) *)
    | Let(bs,e) ->
        let_ (list_map_snd nrm bs) @@ nrm e
    | Letrec(bs,e) ->
        letrec_ (list_map_snd nrm bs) @@ nrm e
    | Seq(e1,e2) ->
        seq_ (nrm e1) (nrm e2)
    | Get _ -> e
    | Set(x,m,a) ->
       set_ x m (nrm a)
    | Automaton(ts,e) ->
        automaton_ (list_map_snd nrm ts) (nrm e)
    | Continue _ -> e
    | Par(e1,e2) ->
        par_ (nrm e1) (nrm e2)
    | Match _ -> assert false (* todo *)
end


module Renaming = struct
  open M

  module Env = Map.Make(String)

  let gensym =
    let h = Hashtbl.create 100 in
    fun x ->
      let y = if Hashtbl.mem h x then
                gensym ~prefix:x ()
              else x in
      Hashtbl.add h y (); y

  let ren_ident r x =
    match Env.find_opt x r with
    | Some y -> y
    | None -> x (* warning ? *)

  let rec rename r e =
    match desc_of e with
    | Const _ -> e
    | Var x -> var_ ~ty:(ty_of e) (ren_ident r x)
    | Cstor(x,es) ->
        cstor_ x (List.map (rename r) es)
    | Fun(x,e) ->
        let x' = gensym x  in
        fun_ x' (rename (Env.add x x' r) e)
    (* functions are applied when possible *)
    | App(e,a) ->
        app_ (rename r e) (rename r a)
    | If(a,e1,e2) ->
        if_ (rename r a) (rename r e1) (rename r e2)
    (* atoms are propaged (constant and copy propagation + inlining) *)
    | Let(bs,e) ->
        let r' = List.fold_left (fun r (x,_) -> Env.add x (gensym x) r) r bs in
        let bs' = List.map (fun (x,e) -> ren_ident r' x, rename r e) bs in
        let_ bs' (rename r' e)
    | Letrec(bs,e) ->
        let r' = List.fold_left (fun r (x,_) -> Env.add x (gensym x) r) r bs in
        let bs' = List.map (fun (x,e) -> ren_ident r' x, rename r' e) bs in
        letrec_ bs' (rename r' e)
    | Seq(e1,e2) ->
        seq_ (rename r e1) (rename r e2)
    | Get (m,x) ->
        get_ m (ren_ident r x)
    | Set(m,x,e) ->
        set_ m (ren_ident r x) (rename r e)
    | Automaton(ts,e) ->
        let r' = List.fold_left (fun r (q,_) -> Env.add q (gensym q) r) r ts in
        let ts' = List.map (fun (q,e) -> ren_ident r' q, rename r' e) ts in
        automaton_ ts' (rename r' e)
    | Continue q ->
        continue_ (ren_ident r q)
    | Par(e1,e2) ->
        par_ (rename r e1) (rename r e2)
    | Match _ -> assert false (* todo *)
  let rename_exp ~reserved_names e =
    (* TODO : fix reserved_names *)
    (* let env = List.fold_left (fun env x ->
                                 Env.add x ("ml_"^x) env)
                Env.empty reserved_names in *)
    rename Env.empty e
end



module Translate_to_automata = struct

  module S = Beta_reduction

  open M

  let sig_create x e e' =
    M.let_ [x,M.app_ (M.const_ (Const.signal_create)) e] e'

  let sig_create_uninitialized x e' =
    M.let_ [x,M.app_ (M.const_ (Const.signal_create_uninitialized))
                               (M.const_ Const.unit_)] e'
  let out_create_uninitialized x e' =
    M.let_ [x,M.app_ (M.const_ (Const.output_create_uninitialized))
                               (M.const_ Const.unit_)] e'

  let assign_continue ~is_master result e idle =
    match result with
    | "_" -> (continue_ idle)
    | _ -> seq_ (set_ (if is_master then `Out else `Sig) result e) (continue_ idle)

  let assign_then ~as_output x e e' =
    seq_ (set_ (if as_output then `Out else `Sig) x e) e'

  let is_seq ?(const_criterion=Const.is_seq) e =
    let exception Seq in
    let f e =
      match desc_of e with
      | Let _ | Letrec _ | Automaton _ -> raise Seq
      | Const c -> if const_criterion c then raise Seq
      | _ -> () in
    try M.iter f e; false with Seq -> true

  let rec translate ~is_master result idle args r e =
    (* if not (is_seq e) then assign_continue result e idle else *)
    match desc_of e with
    | Const _ ->
       assign_continue ~is_master result e idle
    | Var x ->
       assign_continue ~is_master result (get_ `Sig x) idle
    | Fun _ -> assert false
    | If(a,e1,e2) ->
       if_ (translate_noseq args a)
           (translate ~is_master result idle args r e1)
           (translate ~is_master result idle args r e2)
    | Let([x,e1],e2) ->
        if (let e0,_ = uncurry e1 in
            match desc_of e0 with
            | Const c -> (Const.is_sig_creation c)
            | _ -> false) then
          M.let_ [x, e1] (translate ~is_master result idle args r e2)
        else if not (is_seq e) then
          M.let_ [x, M.app_ (M.const_ (Const.signal_create))
                    (translate_noseq args e1)]
            (translate ~is_master result idle (x::args) r e2)
        else
          let q = gensym ~prefix:"q" () in
          let_ [x,app_ (const_ Const.signal_create_uninitialized)
                       (const_ Const.unit_)] @@
          let args_plus_x = x::args in
          automaton_ [q,(translate ~is_master result idle args_plus_x r e2)]
            (* it is also [args_plus_x] since x is the destination (signal) to set *)
            (translate ~is_master:false x q args_plus_x r e1)
    | Let(bs,e) ->
        let xs = List.map fst bs in
        let args' = xs@args in

        let sync_signals = List.map (fun _ ->
            gensym ~prefix:"start" (), gensym ~prefix:"rdy" ()
          ) xs
        in

        List.fold_right (fun (start_i,rdy_i) e ->
                          sig_create start_i (const_ @@ Const.bool_ false) @@
                          sig_create_uninitialized rdy_i e)
          sync_signals @@

        let ps = List.rev @@
                 List.map2 (fun (x,e) (start_i,rdy_i) ->
                           translate_fsm_sync
                             ~is_master:false ~start:start_i ~rdy:rdy_i
                             ~result:x (start_i::rdy_i::args') e)
                    bs
                    sync_signals
        in
        (* synchro *)
        let main =
          let q_start_true = gensym ~prefix:"q_start_true" () in
          let q_start_false = gensym ~prefix:"q_start_false" () in
          let q_wait_rdy = gensym ~prefix:"q_wait_rdy" () in

          let set_all_then_continue l v q =
            let es = List.rev_map (fun x -> set_ `Sig x v) l in
            seq_list_ es ~after:(continue_ q)
          in
          automaton_ [q_start_true,
                          set_all_then_continue (List.map fst sync_signals)
                                                (const_ @@ Const.bool_ true)
                                                q_start_false;
                      q_start_false,
                        set_all_then_continue (List.map fst sync_signals)
                                                (const_ @@ Const.bool_ false)
                                                q_wait_rdy;
                      q_wait_rdy,
                        if_ (call_ Const.parallel_and_
                                   (List.map (fun (_,rdy_i) ->
                                      get_ `Sig rdy_i) sync_signals))
                            (translate ~is_master result idle args' r e)
                            (continue_ q_wait_rdy) ]
                (continue_ q_start_true)
        in
        List.fold_right (fun (x,_) e ->
          sig_create_uninitialized x e) bs @@
        (List.fold_left par_ main ps)
    | Letrec(bs,e) ->
       let bs' = List.map (fun (q,e) -> q,split_fun e) bs in
       let r' = (List.map (fun (x,(xs,_)) -> x,(List.map fst xs)) bs')@r in
       let vars = List.concat (List.map (fun (_,(xs,_)) -> xs) bs') in
       List.fold_right (fun (x,t) e -> M.let_ [x,
                     M.app_ (M.const_ (Const.signal_create_uninitialized)) (M.const_ Const.unit_)] e) vars @@
       automaton_ (List.map (fun (q,(xs,e)) ->
                       let args' = List.map fst xs @ args in
                        q,translate ~is_master result idle args' r' e) bs') @@
       translate ~is_master result idle args r' e
    | App _ ->
       let (e0,es) = uncurry e in
       (match desc_of e0,List.map (translate_noseq args) es with
       | Const c,vs ->
            let e' = List.fold_left app_ e0 vs in
            assign_continue ~is_master result e' idle
       | Var q,vs -> (match List.assoc_opt q r with
                      | None -> assert false
                      | Some ys -> List.fold_right2 (assign_then ~as_output:false) ys vs (continue_ q))
       | _ ->
         assert false (* ANF form, and no more #[fun x -> e] *)
      )
    | Seq(e1,e2) ->
       if not (is_seq e1) then
         seq_ (translate_noseq args e1) (translate ~is_master result idle args r e2)
       else
         let q = gensym ~prefix:"q" () in
         automaton_ [q,translate ~is_master result idle args r e2]
           (translate ~is_master "_" q args r e1)
    | Get _ ->
        assign_continue ~is_master result e idle
    | Set _ ->
        seq_
          (translate_noseq args e)
          (continue_ idle)  (* ah bon ?? *)
    | Automaton(ts,e) ->
       automaton_
         (list_map_snd (translate ~is_master result idle args r) ts)
         (translate ~is_master result idle args r e)
    | Continue _ ->
         e
    | Par(e1,e2) ->
        par_
          (translate ~is_master result idle args r e1)
          (translate_fsm ~is_master:false ~result:"_" args e2)
    | ( Cstor _
      | Match _) -> assert false (* already expanded *)

   (* pas besoin de resultat (poubelle) *)
   and translate_noseq args e =
    match desc_of e with
    | Get _ -> e
    | Set(m,x,e) -> translate_noseq_to m x args e
    | Var x -> if List.mem x args then get_ `Sig x else e
    | Const _ -> e
    | App(e,a) -> app_ (translate_noseq args e) (translate_noseq args a)
    | If(a,e1,e2) -> if_ a (translate_noseq args e1) (translate_noseq args e2)
    | Let(bs,e) -> let_ (list_map_snd (translate_noseq args) bs) (translate_noseq args e)
    | Seq _ -> e
    | Par(e1,e2) -> (* besoin ? *)
        par_ (translate_noseq args e1) (translate_noseq args e2)
    | ( Cstor _
      | Fun _
      | Letrec _
      | Match _
      | Automaton _
      | Continue _) -> assert false

   and translate_noseq_to mode result args e =
    match desc_of e with
    | Get _ | Var _ | Const _ | App _ | If _ ->
        set_ mode result (translate_noseq args e)
    | Let(bs,e) -> let_ bs (translate_noseq_to mode result args e)
    | Set(m,x,e) -> translate_noseq_to m x args e
    | Seq(e1,e2) -> seq_ (translate_noseq_to mode result args e1)
                         (translate_noseq_to mode result args e2)
    | Par(e1,e2) ->
        par_ (translate_noseq args e1)
             (translate_noseq args e2)
    | _ -> translate_fsm_sync ~is_master:true ~start:"ml_start" ~rdy:"ml_rdy" ~result args e (* à paramétrer *)

   and translate_fsm ~is_master ~result args e =
      let idle = gensym ~prefix:"idle" () in
      automaton_ [idle,translate ~is_master result idle args [] e] (continue_ idle)

  and translate_fsm_sync ~is_master ~start ~rdy ~result args e =
      let idle = gensym ~prefix:"idle" () in
      automaton_ [idle, if_ (get_ (if is_master then `In else `Sig) start)
                           (seq_ (set_ (if is_master then `Out else `Sig) rdy (const_ @@ Const.bool_ false))
                                 (translate ~is_master result idle args [] e))
                           (seq_ (set_ (if is_master then `Out else `Sig) rdy (const_ @@ Const.bool_ true))
                                 (continue_ idle))] (continue_ idle)

let no_need_to_translate e : bool =
        let open M in
        let exception Need in
        let f e =
          match desc_of e with
          | Cstor _ | Fun _ | Letrec _ | Match _ | Let _ -> raise Need
          | _ -> () in
        try M.iter f e; true with Need -> false


  let translate_main ~start ~result ~rdy ci =

    let argument i = "ml_arg"^string_of_int (i+1) in

    let add_reserved_name_no_dup x t_inferred l =
      match List.assoc_opt x l with
      | Some t_from_src_code -> (try Const.Type.unify t_inferred t_from_src_code with
                    | Const.Type.Cannot_unify _ ->
                        let open Errors in
                        error dloc @@ fun fmt ->
                          Format.fprintf fmt
                            "reserved name %s must have type %a" x
                          (emph_pp green Const.Type.print_ty) t_inferred
                  ) ; l
      | None -> (x,t_inferred)::l in

    let xs,e0 = split_fun ci.e in
    let ci = {ci with inputs =List.mapi (fun i (_,t) -> argument i, t) xs@ ci.inputs;
              e=if xs = [] then e0 else
              (S.app (List.mapi (fun i (x,_) -> x,get_ `In (argument i)) xs) e0)} in

    let ci = {ci with outputs = add_reserved_name_no_dup result (M.ty_of ci.e) ci.outputs } in

    if not (is_seq ci.e) then
      {ci with e = translate_noseq_to `Out result [] ci.e }
    else if no_need_to_translate ci.e then
       (* i.e. no ML constructs *)
       {ci with e = if is_seq ci.e
                    then seq_ (set_ `Out result (const_ Const.unit_)) ci.e
                    else set_ `Out result ci.e} else

     let inputs = add_reserved_name_no_dup start Const.Type.tbool_ ci.inputs in
      let outputs = add_reserved_name_no_dup rdy Const.Type.tbool_ ci.outputs in

     let e = translate_fsm_sync ~is_master:true ~start ~rdy ~result [] ci.e in
     { ci with inputs;outputs; e}

   end

module Propagation = struct
  open M

  let propageable (_,e) =
    let exception Found in
    let rec is_pure e =
      match desc_of e with
      | Fun _ | Letrec _ | Automaton _ | Continue _ | Par _
        -> raise Found
      | Const c -> if not (Const.is_pure c) then raise Found (* todo (?) *)
      | _ -> ()
    in
    try M.iter is_pure e; true with Found -> false


  let propagation e =
    let module B = Map.Make(String) in
    let rec prop r e =
      match desc_of e with
      | Var x -> (match B.find_opt x r with
                  | None -> e
                  | Some e' -> e')
      | Const _ -> e
      | Fun(x,e') ->
         fun_ x (prop r e')
      | If(a,e1,e2) ->
         if_ (prop r a) (prop r e1) (prop r e2)
      | App(e1,e2) ->
         app_ (prop r e1) (prop r e2)
      | Seq(e1,e2) ->
         seq_ (prop r e1) (prop r e2)
      | Letrec(bs,e0) ->
         let r' = List.fold_right (fun (x,_) r -> B.remove x r) bs r in
         letrec_ (list_map_snd (prop r') bs) (prop r' e0)
      | Let(bs,e0) ->
         let r' = List.fold_right (fun (x,_) r -> B.remove x r) bs r in
         let bs' = list_map_snd (prop r) bs in
         let bsa,bse = List.partition propageable bs' in

         let_ bse @@ (prop (List.fold_right (fun (x,e) r -> B.add x e r) bsa r') e0)
      | Automaton(ts,e0) ->
         let r' = List.fold_right (fun (x,_) r -> B.remove x r) ts r in
         automaton_ (list_map_snd (prop r') ts) (prop r' e0)
      | Get _ -> e
      | Set (m,x,e) ->
          set_ m x (prop r e)
      | Continue _ ->
         e
      | Par(e1,e2) ->
         par_ (prop r e1) (prop r e2)
      | (Cstor (_, _) | Match (_, _)) -> assert false (* already expanded *)
    in prop B.empty e
end





module Flattening = struct

  open M

  let rec flat e =
    match desc_of e with
    | Const _ | Var _ | App _ -> [],[],e
    | Automaton(ts,e) ->
        let w = list_map_snd flat ts in
        let ts = List.concat @@ List.map (fun (q,(ts,_,e)) -> (q,e)::ts) w in
        let ps = List.concat @@ List.map (fun (_,(_,ps,_)) -> ps) w in
        let ts',ps',e' = flat e in
        ts@ts',ps@ps',e'
    | If(a,e1,e2) ->
       let ts1,ps1,e1' = flat e1 in
       let ts2,ps2,e2' = flat e2 in
       ts1@ts2,ps1@ps2, if_ a e1' e2'
    | Let([x,a],e) ->
       flat e
    | Seq(e1,e2) ->
       (* let ts1,e1' = flat e1 in
       let ts2,e2' = flat e2 in
       (* ts1@ts2,seq_ e1' e2' *)
       let ts = ts1@ts2 in *)
       (match desc_of e1 with
       | Seq(e3,e4) -> flat @@ seq_ e3 (seq_ e4 e2)
       | If(a,e3,e4) -> flat @@ if_ a (seq_ e3 e2) (seq_ e4 e2)
       | _ -> 
         let ts1,ps1,e1' = flat e1 in
         let ts2,ps2,e2' = flat e2 in
         ts1@ts2,ps1@ps2,seq_ e1' e2')
    | Par(e1,e2) -> 
       let ts1,ps1,e1' = flat e1 in
       let ts2,ps2,e2' = flat e2 in
       ts1,(automaton_ ts2 e2')::ps1@ps2,e1' 
    | _ -> 
       (* when all sub-expressions are in ANF *)
       [],[],e
  
  let signals e =
    (* must preserve the order of the signal declarations *)
    let r = ref [] in
    let f = function
    | Let(bs,e),_ ->
      List.iter (fun ((xi,ei) as b) ->
       match uncurry ei with
       | (Const c,_),_ ->
         if c = Const.signal_create || c = Const.signal_create_uninitialized then
           r := b::!r
       | _ -> ()) bs
    | _ -> ()
    in
    M.iter  f e;
    List.rev !r
  

  let flat_ci ci =
    let ts,ps,e' = flat ci.e in
    let r = signals ci.e in
    let e'' = List.fold_left par_ (automaton_ ts e') ps in
    (* let e'' = List.fold_right (fun (x,a) e -> let_ [x,a] e) r e' in *)
    {ci with e = e'' ; 
     signals= r}
end



(** rewrite (e1;e2) to remove data dependencies (for signals and outputs). 
 for instance, [(~x <- ~x + 1; ~x <- ~x * 2; ?o <- ~x)]
 is rewritten as follow: [(?o <- (~x + 1) * 2; ~x <- (~x + 1) * 2)]
*)
module Supress_data_dependencies = struct
  open M

  module Env = Map.Make(String)

  let ren x e r genv =
    match Env.find_opt x (Env.fold (*ici, détécter les écriture en //*) Env.add r genv) with
    | Some e -> e
         (* (match uncurry e with
         | (Const c, _),vs ->
             (match Const.const_to_macle_runtime c,vs with
              | `SigGet,[e] -> e
              | _ -> e)
           | _ -> e) *)
    | None -> e


  let assign_then x e e' =
    seq_ (set_ `Sig x e) e'


  let app_multi_ e es =
    List.fold_left (fun ei e -> app_ e ei) e es 

  let end_by r e =
    Env.fold (fun x a e -> assign_then x a e) r e

  let force_end ~before r =
    match Env.min_binding_opt r with
    | None -> 
       before
    | Some (x,e) -> 
       seq_ before (end_by (Env.remove x r) (set_ `Sig x e))

  let rec propagation ?(genv=Env.empty) e =
    let rec prop r e =
    match desc_of e with
    | Const _ -> e
    | Var x -> e
    | Continue x -> 
        end_by r (ren x (continue_ x) r genv)
    | App(e1,e2) ->
        app_ (prop r e1) (prop r e2)
    | Get (`In,_) -> e
    | Get (_,x) -> ren x e r genv
    (* | Set (`Sig,x,e') -> force_end (Env.add x (prop r e') r) *)
    | Set (`Sig,x,e') ->
       set_ `Sig x @@ (prop r e')
        (* mettre à jour x, puis ... *)
    | Set (`Out,x,e') -> 
        force_end ~before:(set_ `Out x (prop r e')) r
    | Automaton(ts,e) ->
        automaton_ (list_map_snd (prop r) ts) (prop r e)
    | If(a,e1,e2) ->
       if_ (prop r a) (prop r e1) (prop r e2)
    | Let(bs,e) ->
       (* signal declaration. 
          The default value does not be pushed into the environnement r.
          It is the value at the begining of the program (reset) and not
          at the begining of each clock cycle. *)
       let_ bs (prop r e)
    | Seq((If(e1,e2,e3),_),e4) ->
       prop r (if_ e1 (seq_ e2 e4) (seq_ e3 e4))
    | Seq((Seq(e1,e2),_),e3) ->
       prop r (seq_ e1 (seq_ e2 e3)) 
    | Seq(e1,((Const _,_) as e2))
    | Seq(e1,(Par((Const _,_),_),_ as e2)) ->
        seq_ (prop r e1) e2
    | Seq((Set(`Sig,x,e1),_),e2) ->
      (prop (Env.add x (prop r e1) r) e2)
    | Seq(e1,e2) ->
       seq_ (prop r e1) (prop r e2)
    | Par(e1,e2) ->
       let f e r0 = if not (Translate_to_automata.is_seq e) then  (* is_seq au sens : pas d'automates *)
         let q = gensym ~prefix:"q" () in automaton_ [q,prop Env.empty e] (end_by r0 @@ continue_ q) 
        else (prop Env.empty e)
       in par_ (f e1 r) (f e2 Env.empty)
    | ( Cstor _ 
      | Fun _
      | Letrec _
      | Match _) -> assert false  (* already expanded *)
  in prop Env.empty e

  let propagation_ci ci =
    let e' = propagation ci.e in
    {ci with e = e'}
end

module ToVhdl = struct
   open M
   open Format

   let reset = "reset"
   let clock = "clock"


   let rec pp_simple_exp i fmt e =
    match desc_of e with
    | Const c -> 
        (match Const.const_to_macle_runtime c with
        | `Unit -> fprintf fmt "macle_unit"
        | `Bool b -> if b then fprintf fmt "macle_true" else
                    fprintf fmt "macle_false" 
        | `Int n -> fprintf fmt "macle_int(%d)" n
        | _ -> assert false)
    | Var x -> fprintf fmt "%s" x
    | Get(_,x) ->
       fprintf fmt "%s" x
    | App _ ->
        let e0,vs = uncurry e in
        (match desc_of e0 with
        | Const c -> 
           (match Const.const_to_macle_runtime c,vs with
           | `Instantaneous op,vs ->
               fprintf fmt "@[<v 2>%s(" op;
               pp_print_list
                  ~pp_sep:(fun fmt () -> fprintf fmt ",")
                 (pp_exp i) fmt vs;
              fprintf fmt ")@]"
           | _ -> assert false)
        | _ -> assert false)
    | _ -> assert false
   
   and pp_exp i fmt e =
    match desc_of e with
    | Const _ | Var _ | Get _ | App _ ->
       pp_simple_exp i fmt e
    | Set(_,x,e) ->
       fprintf fmt "@[<v 2>%s <= %a;@]" x (pp_exp i) e
    | Automaton(ts,e) ->
        fprintf fmt "@[<v>@[<v 2>process(%s,%s) begin@," reset clock;
        fprintf fmt "@[<v 2>if %s = '1' then@," reset;
        pp_exp i fmt e;
        fprintf fmt "@]@,";
        fprintf fmt "@[<v 2>elsif rising_edge(%s) then@," clock;
        fprintf fmt "@[<v 2>case state%d is@," i;
        pp_print_list
            ~pp_sep:(fun fmt () -> fprintf fmt "@,")
            (fun fmt (q,e) ->
              fprintf fmt "@[<v 2>when %s =>@,%a@]" q (pp_exp i) e) fmt ts;
        fprintf fmt "@]@,end case;@]@,";
        fprintf fmt "end if;@]@,";
        fprintf fmt "@]end process;@,@]"
    | If(a,e1,e2) ->
       fprintf fmt "@[<v 2>if %a = macle_true then@,%a@]@,@[<v 2>else@,%a@]@,end if;"
        (pp_exp i) a
        (pp_exp i) e1
        (pp_exp i) e2
    | Seq(e1,e2) ->
       fprintf fmt "@[<v>%a@,%a@]"
          (pp_exp i) e1
          (pp_exp i) e2
    | Continue q ->
        fprintf fmt "@[<v>state%d <= %s;@]" i q
    | Par(e1,e2) -> 
       fprintf fmt "@[<v>%a@,@,%a@]" (pp_exp i) e1 (pp_exp (i+1)) e2
    | _ -> 
       assert false
  
  let pp_ident fmt x =
    fprintf fmt "%s" x

  let rec pp_exp_concurrent fmt e =
  match desc_of e with
   | Const _ | App _ | Get _ -> pp_simple_exp 0 fmt e
  (*
    | Let(_,e) -> pp_exp_concurrent i fmt e*)
  | Set(m,x,e) -> 
     pp_stat_concurrent fmt x e
  | Seq(e1,e2) ->
      fprintf fmt "%a@,%a" 
        pp_exp_concurrent e1
        pp_exp_concurrent e2
  | If(e1,e2,e3) -> fprintf fmt "macle_if(@[<v>%a,@,%a,@,%a)@]"
       pp_exp_concurrent e1
       pp_exp_concurrent e2
       pp_exp_concurrent e3
  | _ -> 
    assert false 

  and pp_stat_concurrent fmt result e =
    match desc_of e with
    | Const _ | App _ | Get _ | If _ -> 
       fprintf fmt "%a <= %a;" pp_ident result pp_exp_concurrent e
    | Set(_,x,e) ->
       fprintf fmt "%a <= %a;" pp_ident x pp_exp_concurrent e
    | _ -> assert false

  let pp_exp_main i fmt e =
    if not (Translate_to_automata.is_seq e) then 
       pp_exp_concurrent fmt e else
    pp_exp i fmt e


  let rec ty_vhdl = function
  | `TUnit -> "unit"
  | `TBool -> "bool"
  | `TInt -> "int"
  | `TVar -> "value"
  | `TOut t | `TSig t | `TIn t -> ty_vhdl t
  | _ -> assert false

  let rec pp_ty_vhdl fmt t = 
    fprintf fmt "%s" (ty_vhdl @@ Const.Type.get_type t)

  let par_list e =
    let rec aux acc e = 
     match desc_of e with
     | Par(e1,e2) -> aux (e2::acc) e1
     | _ -> e::acc
   in aux [] e

   let pp_ci fmt {x;e;inputs;outputs;signals} =
      fprintf fmt "@[<v>library ieee;@,";
      fprintf fmt "use ieee.std_logic_1164.all;@,";
      fprintf fmt "use ieee.numeric_std.all;@,@,";
      fprintf fmt "use work.macle_runtime.all;@,@,";
      fprintf fmt "@[<v 2>entity %a is@," pp_ident x;
      fprintf fmt "port(@[<v 0>";
      fprintf fmt "signal %a : in std_logic;@," pp_ident clock;
      fprintf fmt "signal %a : in std_logic" pp_ident reset;

      List.iter (fun (x,t) -> 
                    fprintf fmt ";@,signal %a : in %a" 
                        pp_ident x pp_ty_vhdl t) inputs;

      List.iter (fun (x,t) -> 
                    fprintf fmt ";@,signal %a : out %a" 
                        pp_ident x pp_ty_vhdl t) outputs;

      fprintf fmt ");@]@]@,";
      fprintf fmt "end entity;@,@,";
      fprintf fmt "@[<v 2>architecture rtl of %a is@," pp_ident x;
     
      List.iter (fun (x,e) -> 
                    fprintf fmt "signal %a : %a;@," 
                        pp_ident x 
                        pp_ty_vhdl (Const.Type.tsignal_ (M.ty_of e))
                  ) signals;


      let ps = par_list e in
      List.iteri (fun i e ->
         match e with 
         | (Automaton(ts,_),_) ->
             fprintf fmt "type t_state%d is (" i;
             pp_print_list
                      ~pp_sep:(fun fmt () -> fprintf fmt ",")
                     (fun fmt (q,_) -> pp_ident fmt q) fmt ts;
             fprintf fmt ");@,";
             fprintf fmt "signal state%d: t_state%d;@," i i
        | _ -> ()) ps;

      fprintf fmt "@]@,@[<v 2>begin@,";

      List.iteri (fun i e -> pp_exp_main i fmt e) ps;

      fprintf fmt "@,@]@,";
      fprintf fmt "end architecture;@,@]"
  

end
