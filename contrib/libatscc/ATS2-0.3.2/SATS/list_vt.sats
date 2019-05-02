(*
** libatscc-common
*)

(* ****** ****** *)

(*
staload "./../basics.sats"
*)

(* ****** ****** *)
//
fun{}
List_vt_is_nil
  {a:vt0p}{n:int}
  (xs: !List_vt(a, n)): Bool(n==0)
fun{}
List_vt_is_cons
  {a:vt0p}{n:int}
  (xs: !List_vt(a, n)): Bool(n > 0)
//
overload iseqz with List_vt_is_nil of 100
overload isneqz with List_vt_is_cons of 100
//
(* ****** ****** *)
//
fun
List_vt_length
  {a:vt0p}{n:int}
  (xs: !List_vt(INV(a), n)): Int(n) = "mac#%"
//
overload length with List_vt_length of 100
//
(* ****** ****** *)
//
fun
List_vt_snoc
  {a:vt0p}{n:int}
  (xs: List_vt(INV(a), n), x0: a): List_vt(a, n+1) = "mac#%"
//
fun
List_vt_extend
  {a:vt0p}{n:int}
  (xs: List_vt(INV(a), n), x0: a): List_vt(a, n+1) = "mac#%"
//
(* ****** ****** *)
//
fun
List_vt_append
  {a:vt0p}{i,j:int}
  (List_vt(INV(a), i), List_vt(a, j)): List_vt(a, i+j)= "mac#%"
//
overload + with List_vt_append of 100 // infix
//
(* ****** ****** *)
//
fun
List_vt_reverse
  {a:vt0p}{n:int}
  (List_vt(INV(a), n)): List_vt(a, n) = "mac#%"
//
fun
List_vt_reverse_append
  {a:vt0p}{i,j:int}
  (List_vt(INV(a), i), List_vt(a, j)): List_vt(a, i+j) = "mac#%"
//
overload reverse with List_vt_reverse of 100
overload revappend with List_vt_reverse_append of 100
//
(* ****** ****** *)

(* end of [list_vt.sats] *)
