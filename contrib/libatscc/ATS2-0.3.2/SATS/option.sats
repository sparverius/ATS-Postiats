(*
** libatscc-common
*)

(* ****** ****** *)

(*
staload "./../basics.sats"
*)

(* ****** ****** *)
//
castfn
Option_vt2t
  {a:t0p}{b:bool}
  (Option_vt(INV(a), b)):<> Option(a, b)
//
(* ****** ****** *)
//
fun
Option_some
  {a:t0p}
  (x0: a): Option(a, true) = "mac#%"
fun
Option_none
  {a:t0p}
  ((*void*)): Option(a, false) = "mac#%"
//
(* ****** ****** *)
//
fun
Option_unsome
  {a:t0p}
  (opt: Option(a, true)): (a) = "mac#%"
//
(* ****** ****** *)
//
fun
Option_is_some
  {a:t0p}{b:bool}
  (opt: Option(a, b)): Bool(b) = "mac#%"
fun
Option_is_none
  {a:t0p}{b:bool}
  (opt: Option(a, b)): Bool(~b) = "mac#%"
//
overload is_some with Option_is_some
overload is_none with Option_is_none
//
overload .is_some with Option_is_some
overload .is_none with Option_is_none
//
(* ****** ****** *)

(* end of [option.sats] *)
