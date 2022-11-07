open Prelude
open Syntax
open Const

include Make(
  struct
    type const = Const.t
    type pattern = Pattern.t

    module T = Const.Type

    type ty = T.ty

    exception Cannot_unify of ty * ty * loc

    let unify = T.unify
    let new_tvar = T.new_tvar
    let tunit_ = T.tunit_
    let tsignal_ = T.tsignal_
    let toutput_ = T.toutput_
    let tinput_ = T.tinput_
    let tfun_ = T.tfun_
    let is_fun = T.is_fun

  end)
