(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2010-2015 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
**
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
**
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* Author: Hongwei Xi *)
(* Start time: Feburary, 2012 *)
(* Authoremail: gmhwxiATgmailDOTcom *)

(* ****** ****** *)

(*
** Source:
** $PATSHOME/prelude/DATS/CODEGEN/List.atxt
** Time of generation: Fri Jan 11 08:42:04 2019
*)

(* ****** ****** *)
//
staload
UN = "prelude/SATS/unsafe.sats"
staload
_(*anon*) = "prelude/DATS/unsafe.dats"
//
(* ****** ****** *)

abstype
List0_(a:t@ype+) = List0(a)

(* ****** ****** *)

primplmnt
lemma_List_param(xs) =
(
//
case+ xs of
| List_nil _ => () | List_cons _ => ()
//
) (* lemma_List_param *)

(* ****** ****** *)
//
implement
{a}(*tmp*)
List_tuple_0() = List_nil()
//
implement
{a}(*tmp*)
List_tuple_1(x0) = $list{a}(x0)
implement
{a}(*tmp*)
List_tuple_2(x0, x1) = $list{a}(x0, x1)
implement
{a}(*tmp*)
List_tuple_3(x0, x1, x2) = $list{a}(x0, x1, x2)
//
implement
{a}(*tmp*)
List_tuple_4
(x0, x1, x2, x3) = $list{a}(x0, x1, x2, x3)
implement
{a}(*tmp*)
List_tuple_5
(x0, x1, x2, x3, x4) = $list{a}(x0, x1, x2, x3, x4)
implement
{a}(*tmp*)
List_tuple_6
(x0, x1, x2, x3, x4, x5) = $list{a}(x0, x1, x2, x3, x4, x5)
//
(* ****** ****** *)
//
implement
{x}(*tmp*)
List_make_sing(x) =
List_vt_cons{x}(x, List_vt_nil())
implement
{x}(*tmp*)
List_make_pair(x1, x2) =
List_vt_cons{x}(x1, List_vt_cons{x}(x2, List_vt_nil()))
//
(* ****** ****** *)

implement
{x}(*tmp*)
List_make_elt
  {n} (n, x) = let
//
fun loop
  {i:nat | i <= n} .<i>.
(
  i: Int i, x: x, res: List_vt(x, n-i)
) :<> List_vt(x, n) =
(
  if (i > 0)
    then loop(pred(i), x, List_vt_cons(x, res)) else res
  // end of [if]
) // end of [loop]
//
in
  loop(n, x, List_vt_nil())
end // end of [List_make_elt]

(* ****** ****** *)

implement
{}(*tmp*)
List_make_intrange
  {l0,r} (l0, r) = let
//
typedef elt = intBtw(l0, r)
vtypedef res(l:int) = List_vt(elt, r-l)
//
fun
loop
{
  l:int
| l0 <= l; l <= r
} .<r-l>.
(
  l: Int l, r: Int r
, res: &ptr? >> res(l)
) :<!wrt> void =
(
//
if
(l < r)
then let
  val () = res :=
    List_vt_cons{elt}{0}(l, _)
  val+List_vt_cons(_, res1) = res
  val () = loop(l+1, r, res1)
  prval ((*folded*)) = fold@(res)
in
  // nothing
end else (res := List_vt_nil())
//
) (* end of [loop] *)
//
var res: ptr
val ((*void*)) = $effmask_wrt(loop(l0, r, res))
//
in
  res
end // end of [List_make_intrange]

(* ****** ****** *)

implement
{a}(*tmp*)
List_make_array
  {n}(A, n0) = let
//
prval() = lemma_array_param(A)
//
vtypedef res(n:int) = List_vt(a, n)
//
fun
loop
{l:addr}
{n:nat} .<n>.
(
  pf: !array_v(a, l, n) >> array_v(a?!, l, n)
| p0: ptr l
, n0: Size_t n
, res: &ptr? >> res(n)
) :<!wrt> void = (
//
if
(n0 > 0)
then let
  prval
  (
    pf1, pf2
  ) = array_v_uncons{a}(pf)
//
  val () = res :=
    List_vt_cons{a}{0}(_, _)
  // end of [val]
  val+List_vt_cons(x, res1) = res
//
  val () = x := !p0
  val p1 = ptr1_succ<a>(p0)
  val () =
    loop(pf2 | p1, pred(n0), res1)
  // end of [val]
  prval () =
    pf := array_v_cons{a?!}(pf1, pf2)
  // end of [prval]
  prval ((*folded*)) = fold@ (res)
in
  // nothing
end // end of [then]
else let
  prval () = array_v_unnil(pf)
  prval () = pf := array_v_nil()
in
  res := List_vt_nil((*void*))
end // end of [else]
//
) (* end of [loop] *)
//
var
res: ptr // uninitialized
//
val ((*void*)) =
  loop(view@(A) | addr@(A), n0, res)
//
in
  res
end // end of [List_make_array]

(* ****** ****** *)

implement
{a}(*tmp*)
List_make_arrpsz
  {n}(ASZ) = let
//
var
asz: size_t
//
val A0 =
arrpsz_get_ptrsize
  (ASZ, asz)
//
val p0 = arrayptr2ptr(A0)
//
prval
pfarr = arrayptr_takeout(A0)
val res = List_make_array(!p0, asz)
prval() = arrayptr_addback(pfarr | A0)
//
in
//
let val () = arrayptr_free(A0) in res end
//
end // end of [List_make_arrpsz]

(* ****** ****** *)
//
implement
{a}(*tmp*)
print_List(xs) =
  fprint_List<a>(stdout_ref, xs)
implement
{a}(*tmp*)
prerr_List(xs) =
  fprint_List<a>(stderr_ref, xs)
//
(* ****** ****** *)
//
implement
{}(*tmp*)
fprint_List$sep
  (out) = fprint_string(out, ", ")
// end of [fprint_List$sep]
//
implement
{a}(*tmp*)
fprint_List(out, xs) = let
//
implement(env)
List_iforeach$fwork<a><env>
  (i, x, env) = let
  val () =
  if i > 0
    then fprint_List$sep<(*none*)>(out)
  // end of [if]
  // end of [val]
in
  fprint_val<a>(out, x)
end // end of [List_iforeach$fwork]
//
val _(*len*) = List_iforeach<a>(xs)
//
in
  // nothing
end // end of [fprint_List]
//
implement
{a}(*tmp*)
fprint_List_sep
  (out, xs, sep) = let
//
implement
fprint_List$sep<(*none*)>
  (out) = fprint_string(out, sep)
//
in
  fprint_List<a>(out, xs)
end // end of [fprint_List_sep]
//
(* ****** ****** *)
(*
//
// HX-2012-05:
// Compiling this can be a great challenge!
//
*)
implement
{a}(*tmp*)
fprint_ListList_sep
  (out, xss, sep1, sep2) = let
//
implement
fprint_val<List0_(a)>
  (out, xs) = let
  val xs = $UN.cast{List0(a)}(xs)
in
  fprint_List_sep<a>(out, xs, sep2)
end // end of [fprint_val]
//
in
//
fprint_List_sep<List0_(a)>
  (out, $UN.cast{List_1(List0_(a))}(xss), sep1)
//
end // end of [fprint_ListList_sep]

(* ****** ****** *)

implement
{}(*tmp*)
List_is_nil(xs) =
  case+ xs of List_nil() => true | _ =>> false
// end of [List_is_nil]

implement
{}(*tmp*)
List_is_cons(xs) =
  case+ xs of List_cons _ => true | _ =>> false
// end of [List_is_cons]

implement
{x}(*tmp*)
List_is_sing (xs) =
  case+ xs of List_sing(x) => true | _ =>> false
// end of [List_is_sing]
implement
{x}(*tmp*)
List_isnot_sing (xs) =
  case+ xs of List_sing(x) => false | _ =>> true
// end of [List_isnot_sing]

implement
{x}(*tmp*)
List_is_pair(xs) =
  case+ xs of List_pair(x1, x2) => true | _ =>> false
// end of [List_is_pair]
implement
{x}(*tmp*)
List_isnot_pair(xs) =
  case+ xs of List_pair(x1, x2) => false | _ =>> true
// end of [List_isnot_pair]

(* ****** ****** *)

implement
{x}(*tmp*)
List_head (xs) =
  let val+List_cons(x, _) = xs in x end
// end of [List_head]
implement
{x}(*tmp*)
List_tail (xs) =
  let val+List_cons(_, xs) = xs in xs end
// end of [List_tail]
implement
{x}(*tmp*)
List_last(xs) = let
//
fun
loop
(
  xs: List1(x)
): (x) = let
  val+List_cons(x, xs) = xs
in
  case+ xs of
  | List_cons _ => loop(xs) | List_nil _ => x
end // end of [loop]
//
in
  $effmask_all(loop(xs))
end // end of [List_last]

(* ****** ****** *)

implement
{x}(*tmp*)
List_head_exn (xs) =
(
case+ xs of
| List_cons(x, _) => x | _ => $raise ListSubscriptExn()
) (* end of [List_head_exn] *)

implement
{x}(*tmp*)
List_tail_exn (xs) =
(
case+ xs of
| List_cons(_, xs) => xs | _ => $raise ListSubscriptExn()
) (* end of [List_tail_exn] *)

implement
{x}(*tmp*)
List_last_exn (xs) =
(
case+ xs of
| List_cons _ => List_last(xs) | _ => $raise ListSubscriptExn()
) (* end of [List_last_exn] *)

(* ****** ****** *)

implement
{a}(*tmp*)
List_nth(xs, i) = let
//
fun
loop
{n,i:nat | i < n} .<i>.
(
  xs: List(a, n), i: Int i
) :<> a =
  if i > 0 then let
    val+List_cons(_, xs) = xs in loop(xs, pred(i))
  end else List_head<a>(xs)
//
in
  loop(xs, i)
end // end of [List_nth]

implement
{a}(*tmp*)
List_nth_opt(xs, i) = let
//
fun loop
  {n:nat} .<n>.
(
  xs: List(a, n), i: intGte(0)
) :<> Option_vt_1(a) =
(
case+ xs of
| List_nil() => None1_vt()
| List_cons(x, xs) =>
    if i = 0 then Some1_vt(x) else loop(xs, pred(i))
  // end of [List_vt_cons]
) (* end of [loop] *)
//
prval() = lemma_List_param (xs)
//
in
  loop(xs, i)
end // end of [List_nth_opt]

(* ****** ****** *)

implement
{a}(*tmp*)
List_get_at(xs, i) = List_nth<a>(xs, i)
implement
{a}(*tmp*)
List_get_at_opt(xs, i) = List_nth_opt<a>(xs, i)

(* ****** ****** *)

implement
{a}(*tmp*)
List_fset_at
  (xs, i, x_new) = let
//
val
(
xs1, xs2
) =
$effmask_wrt
  (List_split_at<a>(xs, i))
//
val+List_cons(x_old, xs2) = xs2
val xs2 = List_cons{a}(x_new, xs2)
//
in
  $effmask_wrt(List_append1_vt<a>(xs1, xs2))
end // ed of [List_fset_at]

(* ****** ****** *)

implement
{a}(*tmp*)
List_fexch_at
  (xs, i, x_new) = let
val
(
xs1, xs2
) =
$effmask_wrt
  (List_split_at<a>(xs, i))
//
val+List_cons(x_old, xs2) = xs2
val xs2 = List_cons{a}(x_new, xs2)
//
in
  ($effmask_wrt(List_append1_vt<a>(xs1, xs2)), x_old)
end // ed of [List_fexch_at]

(* ****** ****** *)

implement
{a}(*tmp*)
List_insert_at
  (xs, i, x) = let
//
fun loop{n:int}
  {i:nat | i <= n} .<i>.
(
  xs: List(a, n)
, i: Int i, x: a
, res: &ptr? >> List(a, n+1)
) :<!wrt> void =
//
if
i > 0
then let
  val+List_cons(x1, xs1) = xs
  val () = res :=
    List_cons{a}{0}(x1, _(*?*))
  val+List_cons
    (_, res1) = res // res1 = res.1
  val () = loop(xs1, i-1, x, res1)
  prval ((*folded*)) = fold@ (res)
in
  // nothing
end // end of [then]
else res := List_cons(x, xs)
//
var
res: ptr
val () =
  $effmask_wrt(loop(xs, i, x, res))
//
in
  res
end // end of [List_insert_at]

(* ****** ****** *)

implement
{a}(*tmp*)
List_remove_at
  (xs, i) = let
//
var x0: a // uninitized
//
in
  $effmask_wrt(List_takeout_at(xs, i, x0))
end // end of [List_remove_at]

(* ****** ****** *)

implement
{a}(*tmp*)
List_takeout_at
  (xs, i, x0) = let
//
fun loop{n:int}
  {i:nat | i < n} .<i>.
(
  xs: List(a, n)
, i: Int i, x0: &a? >> a
, res: &ptr? >> List(a, n-1)
) :<!wrt> void = let
//
val+List_cons(x, xs) = xs
//
in
//
if i > 0 then let
  val () =
    res :=
    List_cons{a}{0}(x, _(*?*))
  // end of [val]
  val+List_cons
    (_, res1) = res // res1 = res.1
  val () = loop(xs, i-1, x0, res1)
  prval ((*folded*)) = fold@ (res)
in
  // nothing
end else let
  val () = x0 := x; val () = res := xs
in
  // nothing
end // end of [if]
//
end // end of [loop]
//
var res: ptr?
val () = loop(xs, i, x0, res)
//
in
  res
end // end of [List_takeout_at]

(* ****** ****** *)

implement
{x}(*tmp*)
List_length(xs) = let
//
prval() = lemma_List_param (xs)
//
fun
loop
{i,j:nat} .<i>.
(
xs: List(x, i), j: Int j
) :<> Int(i+j) = (
//
case+ xs of
| List_cons(_, xs) => loop(xs, j+1) | _ =>> j
//
) (* end of [loop] *)
//
in
  loop(xs, 0)
end // end of [List_length]

(* ****** ****** *)
//
implement
{x}(*tmp*)
List_length_gte
  (xs, n2) =
  (List_length_compare<x>(xs, n2) >= 0)
//
implement
{x}(*tmp*)
List_length_compare
  (xs, n2) =
  loop(xs, n2) where
{
//
fun
loop
{i:nat;j:int} .<i>.
(xs: List(x, i), j: Int j) :<> Int(sgn(i-j)) =
(
if
(j < 0)
then 1 else
(
case+ xs of
| List_cons
    (_, xs) => loop(xs, j-1)
  // List_cons
| _ (*List_nil*) =>> (if j = 0 then 0 else ~1)
)
) (* end of [loop] *)
//
prval() = lemma_List_param(xs)
//
} (* end of [List_length_compare] *)
//
(* ****** ****** *)

implement
{x}(*tmp*)
List_copy
  (xs) = res where {
//
prval() =
  lemma_List_param(xs)
//
vtypedef res = List0_vt(x)
//
fun loop
  {n:nat} .<n>.
(
  xs: List(x, n)
, res: &res? >> List_vt(x, n)
) :<!wrt> void = let
in
//
case+ xs of
| List_cons
    (x, xs) => let
    val () = res :=
      List_vt_cons{x}{0}(x, _(*?*))
    val+List_vt_cons
      (_, res1) = res // res1 = res.1
    val () = loop(xs, res1)
    prval ((*folded*)) = fold@ (res)
  in
    // nothing
  end // end of [cons]
| List_nil() => res := List_vt_nil()
//
end // end of [loop]
//
var res: res? ; val () = loop(xs, res)
//
} // end of [List_copy]

(* ****** ****** *)

implement
{a}(*tmp*)
List_append
  {m,n} (xs, ys) = let
//
val ys =
__cast(ys) where
{
  extern
  castfn
  __cast(ys: List(a, n)):<> List_vt(a, n)
} // end of [where] // end of [val]
in
//
$effmask_wrt
  (List_of_List_vt(List_append2_vt(xs, ys)))
//
end // end of [List_append]

implement
{a}(*tmp*)
List_append1_vt
  {m,n} (xs, ys) = let
//
val ys =
__cast(ys) where
{
  extern
  castfn
  __cast(ys: List(a, n)):<> List_vt(a, n)
} (* end of [val] *)
//
in
  List_of_List_vt(List_vt_append(xs, ys))
end // end of [List_append1_vt]

implement
{a}(*tmp*)
List_append2_vt
  {m,n} (xs, ys) = let
//
prval() = lemma_List_param (xs)
prval() = lemma_List_vt_param (ys)
//
fun
loop
{m:nat} .<m>.
(
  xs: List(a, m)
, ys: List_vt(a, n)
, res: &ptr? >> List_vt(a, m+n)
) :<!wrt> void =
  case+ xs of
  | List_nil
      () => (res := ys)
    // List_nil
  | List_cons
      (x, xs) => let
      val () = res :=
        List_vt_cons{a}{0}(x, _(*?*))
      val+List_vt_cons
        (_, res1) = res // res1 = res.1
      val () = loop(xs, ys, res1)
      prval ((*folded*)) = fold@ (res)
    in
      // nothing
    end // end of [List_cons]
// end of [loop]
var res: ptr // uninitialized
val () = loop(xs, ys, res)
//
in
  res
end // end of [List_append2_vt]

(* ****** ****** *)
//
implement
{a}(*tmp*)
List_extend(xs, y) =
(
  List_append2_vt<a>(xs, List_vt_sing(y))
) (* end of [List_extend] *)
//
(* ****** ****** *)

implement
{a}(*tmp*)
mul_int_List
{m,n}(m, xs) =
loop{m,0}
(
m, xs, List_vt_nil
) where
{
//
prval() = lemma_List_param(xs)
//
fun
loop
{i,j:nat} .<i>.
(
i0: Int(i)
,
xs: List(a, n)
,
res: List_vt(a, j*n)
) :<!wrt> List_vt(a, (i+j)*n) =
if
(i0 = 0)
then
(
  res where
{
  prval
  EQINT() = eqint_make{i,0}()
}
) (* end of [then] *)
else
(
  loop{i-1,j+1}(i0-1, xs, List_append2_vt<a>(xs, res))
) (* end of [else] *)
//
} (* end of [mul_int_List] *)

(* ****** ****** *)

implement
{x}(*tmp*)
List_reverse (xs) =
(
  List_reverse_append2_vt<x>(xs, List_vt_nil)
) // end of [List_reverse]

(* ****** ****** *)

implement
{a}(*tmp*)
List_reverse_append
  {m,n} (xs, ys) = let
//
val ys =
__cast(ys) where
{
  extern
  castfn __cast(ys: List(a, n)):<> List_vt(a, n)
} // end of [where] // end of [val]
//
in
//
$effmask_wrt
(
  List_of_List_vt(List_reverse_append2_vt<a>(xs, ys))
) (* end of [$effmask_wrt] *)
//
end // end of [List_reverse_append]

implement
{a}(*tmp*)
List_reverse_append1_vt
  {m,n} (xs, ys) = let
//
prval() =
lemma_List_vt_param(xs)
//
prval() = lemma_List_param(ys)
//
fun
loop{m,n:nat} .<m>.
(
  xs: List_vt(a, m), ys: List(a, n)
) :<!wrt> List(a, m+n) = let
in
//
case+ xs of
| ~List_vt_nil
    ((*void*)) => ys
  // end of [List_vt_nil]
| @List_vt_cons
    (x, xs1) => let
    val xs1_ = xs1
    val ys =
    __cast(ys) where
    {
      extern
      castfn
      __cast(ys: List(a, n)):<> List_vt(a, n)
    } (* end of [val] *)
    val () = (xs1 := ys)
    prval ((*folded*)) = fold@ (xs)
  in
    loop(xs1_, List_of_List_vt{a}(xs))
  end // end of [List_vt_cons]
//
end // end of [loop]
//
in
  loop(xs, ys)
end // end of [List_reverse_append1_vt]

implement
{a}(*tmp*)
List_reverse_append2_vt
  (xs, ys) = let
//
prval() = lemma_List_param(xs)
prval() = lemma_List_vt_param(ys)
//
fun loop
  {m,n:nat} .<m>.
(
  xs: List(a, m), ys: List_vt(a, n)
) :<!wrt> List_vt(a, m+n) =
(
case+ xs of
| List_nil
    () => ys
  // end of [List_nil]
| List_cons
    (x, xs) => loop(xs, List_vt_cons{a}(x, ys))
  // end of [List_cons]
) (* end of [loop] *)
//
in
  loop(xs, ys)
end // end of [List_reverse_append2_vt]

(* ****** ****** *)

(*
implement
{a}(*tmp*)
List_concat(xss) = let
//
typedef T = List(a)
//
prval() = lemma_List_param(xss)
//
fun
aux{n:nat} .<n>.
(
  xs0: T
, xss: List(T, n)
) :<!wrt> List0_vt(a) = let
//
prval() = lemma_List_param(xs0)
//
in
  case+ xss of
  | List_nil
      () => List_copy(xs0)
    // end of [List_nil]
  | List_cons
      (xs, xss) => let
      val res = aux(xs, xss)
      val ys0 = List_copy<a>(xs0)
    in
      List_vt_append<a>(ys0, res)
    end // end of [List_cons]
end // end of [aux]
//
in
//
case+ xss of
| List_nil
     () => List_vt_nil()
  // List_nil
| List_cons
    (xs, xss) => aux (xs, xss)
  // List_cons
//
end // end of [List_concat]
*)

(* ****** ****** *)

implement
{x}(*tmp*)
List_concat(xss) = let
//
typedef xs = List_1(x)
//
prval() = lemma_List_param(xss)
//
fnx
aux1
{n1:nat} .<n1,0>.
(
  xss: List(xs, n1)
, res: &ptr? >> List0_vt(x)
) :<!wrt> void =
(
case+ xss of
| List_nil() =>
  (res := List_vt_nil())
| List_cons(xs0, xss) => let
    prval() =
      lemma_List_param(xs0) in aux2(xs0, xss, res)
    // end of [val]
  end // end of [List_cons]
)
and
aux2
{n1,n2:nat} .<n1,n2+1>.
(
  xs0: List(x, n2)
, xss: List(xs, n1)
, res: &ptr? >> List0_vt(x)
) :<!wrt> void = let
in
  case+ xs0 of
  | List_nil() =>
    aux1(xss, res)
  | List_cons(x0, xs1) =>
    {
      val () =
      (
        res :=
        List_vt_cons{x}{0}(x0, _)
      ) (* end of [val] *)
      val+List_vt_cons(_, res1) = res
      val ((*void*)) = aux2(xs1, xss, res1)
      prval ((*folded*)) = fold@(res)
    }
end // end of [aux2]
//
in
//
  let var res: ptr in aux1(xss, res); res end
//
end // end of [List_concat]

(* ****** ****** *)

implement
{a}(*tmp*)
List_take (xs, i) = let
//
fun
loop
{n:int}
{i:nat | i <= n} .<i>.
(
  xs: List(a, n), i: Int i
, res: &ptr? >> List_vt(a, i)
) :<!wrt> void =
  if i > 0 then let
    val+List_cons(x, xs) = xs
    val () = res :=
      List_vt_cons{a}{0}(x, _(*?*))
    val+List_vt_cons
      (_, res1) = res // res1 = res.1
    val () = loop(xs, i-1, res1)
    val ((*folded*)) = fold@ (res)
  in
    // nothing
  end else (res := List_vt_nil())
// end of [loop]
//
var res: ptr
val () = loop(xs, i, res)
//
in
  res
end // end of [List_take]

implement
{a}(*tmp*)
List_take_exn
  {n}{i} (xs, i) = let
//
prval() = lemma_List_param(xs)
//
fun loop
  {n:nat}
  {i:nat} .<i>. (
  xs: List(a, n), i: Int i
, res: &ptr? >> List_vt(a, j)
) :<!wrt> #[
  j:nat | (i <= n && i == j) || (i > n && n == j)
] Bool (i <= n) = let
//
in
//
if i > 0
then let
in
//
case+ xs of
| List_cons
    (x, xs1) =>
    ans where {
//
    val ((*void*)) =
    res :=
    List_vt_cons{a}{0}(x, _)
//
    val+
    List_vt_cons(_, res1) = res
    val ans = loop(xs1, i-1, res1)
//
    prval ((*folded*)) = fold@ (res)
//
  } (* end of [List_cons] *)
| List_nil() => let
    val ((*void*)) =
    res := List_vt_nil() in false(*fail*)
  end // end of [List_nil]
//
end // end of [then]
else let
  val () = res := List_vt_nil() in true(*succ*)
end // end of [else]
// end of [if]
//
end // end of [loop] 
//   
var res: ptr
val ans = loop{n}{i}(xs, i, res)
//
in
//
if ans
then res // i <= n && length (res) == i
else let
  val () = List_vt_free<a>(res) in $raise ListSubscriptExn()
end // end of [if]
//
end (* end of [List_take_exn] *)

(* ****** ****** *)

implement
{a}(*tmp*)
List_drop (xs, i) = let
//
fun loop
  {n:int}
  {i:nat | i <= n} .<i>.
  (xs: List(a, n), i: Int i):<> List(a, n-i) =
  if i > 0 then let
    val+List_cons(_, xs) = xs in loop(xs, i-1)
  end else xs // end of [if]
//
in
  loop(xs, i)
end // end of [List_drop]

implement
{a}(*tmp*)
List_drop_exn
  (xs, i) = let
//
prval() = lemma_List_param(xs)
//
fun
loop
{n:nat}{i:nat} .<i>.
(
  xs: List(a, n), i: Int i
) :<!exn> [i <= n] List(a, n-i) =
  if i > 0 then (
    case+ xs of
    | List_nil
        () => $raise ListSubscriptExn()
      // List_nil
    | List_cons(_, xs) => loop(xs, i-1)
  ) else (xs) // end of [if]
//
in
  loop(xs, i)
end // end of [List_drop_exn]

(* ****** ****** *)

implement
{x}(*tmp*)
List_split_at
  (xs, i) = let
//
fun
loop
{n:int}
{i:nat | i <= n} .<n>.
(
  xs: List(x, n), i: Int i
, res: &ptr? >> List_vt(x, i)
) :<!wrt> List(x, n-i) =
(
if i > 0
  then let
    val+List_cons(x, xs) = xs
    val () =
      res := List_vt_cons{x}{0}(x, _)
    // end of [val]
    val+List_vt_cons(_, res1) = res
    val xs2 = loop(xs, i-1, res1)
    prval ((*folded*)) = fold@ (res)
  in
    xs2
  end // end of [then]
  else let
    val () = res := List_vt_nil() in xs
  end // end of [else]
// end of [if]
)
//
var res: ptr
val xs2 = loop(xs, i, res)
//
in
  (res, xs2)
end // end of [List_split_at]

(* ****** ****** *)

implement
{x}(*tmp*)
List_exists
  (xs) = loop(xs) where
{
//
fun
loop :
$d2ctype(List_exists<x>) = lam(xs) =>
//
case+ xs of
| List_nil() => false
| List_cons(x, xs) =>
    if List_exists$pred<x>(x) then true else loop(xs)
  // end of [List_cons]
//
} (* end of [List_exists] *)

(* ****** ****** *)

implement
{x}(*tmp*)
List_forall
  (xs) = loop(xs) where
{
fun
loop :
$d2ctype(List_forall<x>) = lam(xs) =>
//
case+ xs of
| List_nil() => true
| List_cons(x, xs) =>
    if List_forall$pred<x>(x) then loop(xs) else false
  // end of [List_cons]
//
} (* end of [List_forall] *)

(* ****** ****** *)

implement
{x}(*tmp*)
List_equal
(
  xs1, xs2
) = loop(xs1, xs2) where
{
fun
loop :
$d2ctype
(
  List_equal<x>
) = lam(xs1, xs2) =>
//
case+ xs1 of
| List_nil((*void*)) =>
  ( case+ xs2 of
    | List_nil _ => true
    | List_cons _ => false
  ) // end of [List_nil]
| List_cons(x1, xs1) =>
  ( case+ xs2 of
    | List_nil() => false
    | List_cons(x2, xs2) => let
        val test =
          List_equal$eqfn<x>(x1, x2)
        // end of [val]
      in
        if test then loop(xs1, xs2) else false
      end // end of [List_cons]
  ) (* end of [List_cons] *)
//
} (* end of [List_equal] *)

implement
{a}(*tmp*)
List_equal$eqfn = gequal_val_val<a>

(* ****** ****** *)

implement
{x}(*tmp*)
List_compare
(
  xs1, xs2
) = loop(xs1, xs2) where
{
fun
loop :
$d2ctype
(
  List_compare<x>
) = lam(xs1, xs2) =>
//
case+ xs1 of
| List_nil((*void*)) =>
  ( case+ xs2 of
    | List_nil _ => 0
    | List_cons _ => ~1
  ) // end of [List_nil]
| List_cons(x1, xs1) =>
  ( case+ xs2 of
    | List_nil() => (1)
    | List_cons(x2, xs2) => let
        val test =
          List_compare$cmpfn<x>(x1, x2)
        // end of [val]
      in
        if test = 0 then loop(xs1, xs2) else test
      end // end of [List_cons]
  ) (* end of [List_cons] *)
//
} (* end of [List_compare] *)

implement
{a}(*tmp*)
List_compare$cmpfn = gcompare_val_val<a>

(* ****** ****** *)

implement
{x}(*tmp*)
List_find
  {n}(xs, x0) = let
//
prval() = lemma_List_param(xs)
//
fun
loop
{ i:nat
| i <= n
} .<n-i>.
(
  xs: List(x, n-i)
, i: Int(i), x0: &x? >> opt(x, i >= 0)
) :<!wrt> #[i:int | i < n] Int(i) =
(
case+ xs of
| List_nil() =>
  (
    opt_none(x0); ~1
  ) (* List_nil *)
| List_cons(x, xs) =>
  (
    if List_find$pred<x>(x)
      then (x0 := x; opt_some(x0); i) else loop(xs, i+1, x0)
    // end of [if]
  ) (* List_cons *)
) (* end of [loop] *)
//
in
  loop(xs, 0, x0)
end // end of [List_find]

(* ****** ****** *)

implement
{x}(*tmp*)
List_find_exn
  (xs) = loop(xs) where
{
//
fun
loop :
$d2ctype(List_find_exn<x>) = lam(xs) =>
//
case+ xs of
| List_nil() =>
    $raise NotFoundExn()
| List_cons(x, xs) =>
    if List_find$pred<x>(x) then x else loop(xs)
//
} (* end of [List_find_exn] *)

implement
{x}(*tmp*)
List_find_opt
  (xs) = loop(xs) where
{
//
fun
loop :
$d2ctype(List_find_opt<x>) = lam(xs) =>
//
case+ xs of
| List_nil() =>
    None1_vt((*void*))
| List_cons(x, xs) =>
    if List_find$pred<x>(x) then Some1_vt{x}(x) else loop(xs)
//
} (* end of [List_find_opt] *)

(* ****** ****** *)

implement
{key}(*tmp*)
List_assoc$eqfn = gequal_val_val<key>

implement
{key,itm}
List_assoc
  (kxs, k0, x0) = let
//
fun loop
(
  kxs: List_1 @(key, itm)
, k0: key, x0: &itm? >> opt(itm, b)
) : #[b:bool] Bool(b) =
(
  case+ kxs of
  | List_cons
      (kx, kxs) => let
      val iseq =
      List_assoc$eqfn<key>(k0, kx.0)
    in
      if iseq
        then let
          val () = x0 := kx.1
          prval () = opt_some{itm}(x0)
        in
          true
        end // end of [then]
        else loop(kxs, k0, x0)
      // end of [if]
    end // end of [List_cons]
  | List_nil((*void*)) =>
      let prval() = opt_none{itm}(x0) in false end 
    // end of [List_nil]
) (* end of [loop] *)
//
in
  $effmask_all (loop(kxs, k0, x0))
end // end of [List_assoc]

(* ****** ****** *)

implement
{key,itm}
List_assoc_exn
  (kxs, k0) = let
  var x0: itm?
  val ans = List_assoc<key,itm>(kxs, k0, x0)
in
//
if ans
  then let
    prval() = opt_unsome{itm}(x0) in x0
  end // end of [then]
  else let
    prval() = opt_unnone{itm}(x0) in $raise NotFoundExn()
  end // end of [else]
//
end // end of [List_assoc_exn]

(* ****** ****** *)

implement
{key,itm}
List_assoc_opt
  (kxs, k0) = let
  var x0: itm?
  val ans = List_assoc<key,itm>(kxs, k0, x0)
in
//
if ans
  then let
    prval() = opt_unsome{itm}(x0) in Some1_vt{itm}(x0)
  end // end of [then]
  else let
    prval() = opt_unnone{itm}(x0) in None1_vt((*void*))
  end // end of [else]
//
end // end of [List_assoc_opt]

(* ****** ****** *)

implement
{x}(*tmp*)
List_filter{n}(xs) = let
//
prval() = lemma_List_param(xs)
//
fun
loop
{n:nat} .<n>.
(
  xs: List(x, n)
, res: &ptr? >> ListLte_vt(x, n)
) : void = (
//
case+ xs of
| List_nil
  (
    // argless
  ) => (res := List_vt_nil)
| List_cons
    (x, xs) => let
    val test = List_filter$pred<x>(x)
  in
    case+ test of
    | true => () where
      {
        val () = res :=
          List_vt_cons{x}{0}(x, _(*?*))
        val+List_vt_cons
          (_, res1) = res // res1 = res.1
        val () = loop(xs, res1)
        prval ((*folded*)) = fold@ (res)
      } (* end of [true] *)
    | false => loop(xs, res)
  end // end of [List_cons]
//
) (* end of [loop] *)
//
var res: ptr
val () = loop(xs, res)
//
in
  res(*ListLte_vt(x, n)*)
end // end of [List_filter]

(* ****** ****** *)

implement
{x}(*tmp*)
List_labelize
  (xs) = res where {
//
typedef ix = @(int, x)
//
prval() = lemma_List_param(xs)
//
fun
loop
{n:nat} .<n>.
(
  xs: List(x, n), i: int
, res: &ptr? >> List_vt(ix, n)
) :<!wrt> void = let
in
//
case+ xs of
| List_nil
    () =>
    (res := List_vt_nil)
  // end of [List_nil]
| List_cons
    (x, xs) => () where
  {
    val () =
    res :=
    List_vt_cons{ix}{0}(_, _)
    val+
    List_vt_cons(ix, res1) = res
    val () = ix.0 := i and () = ix.1 := x
    val () = loop(xs, i+1, res1)
    prval ((*folded*)) = fold@ (res)
  } (* end of [List_cons] *)
//
end // end of [loop]
//
var res: ptr ; val () = loop(xs, 0, res)
//
} // end of [List_labelize]

(* ****** ****** *)

implement
{x}(*tmp*)
List_app(xs) = let
//
prval() = lemma_List_param(xs)
//
fun
loop{n:nat} .<n>. (xs: List(x, n)): void =
(
case+ xs of
| List_nil() => ()
| List_cons(x, xs) => (List_app$fwork(x); loop(xs))
) (* end of [loop] *)
//
in
  loop(xs)
end // end of [List_app]

(* ****** ****** *)

implement
{x}{y}(*tmp*)
List_map{n}(xs) = let
//
prval() = lemma_List_param(xs)
//
fun
loop
{n:nat} .<n>.
(
  xs: List(x, n)
, res: &ptr? >> List_vt(y, n)
) : void = (
  case+ xs of
  | List_nil
      ((*void*)) =>
      (res := List_vt_nil)
    // List_nil
  | List_cons(x, xs) => let
      val y =
        List_map$fopr<x><y>(x)
      val () = res :=
        List_vt_cons{y}{0}(y, _(*?*))
      val+List_vt_cons
        (_, res1) = res // res1 = res.1
      val () = loop(xs, res1)
      prval ((*folded*)) = fold@ (res)
    in
      // nothing
    end // end of [List_cons]
) // end of [loop]
//
var res: ptr
val () = loop(xs, res)
//
in
  res(*List_vt(y, n)*)
end // end of [List_map]

(* ****** ****** *)

(*
implement
{x}{y}(*tmp*)
List_map_funenv
  {v}{vt}{n}{fe}
  (pfv | xs, f, env) = let
//
prval() =
  lemma_List_param(xs)
//
vtypedef ys = List0_vt(y)
//
fun
loop
{n:nat} .<n>.
(
  pfv: !v
| xs: List(x, n)
, f: (!v | x, !vt) -<fun,fe> y
, env: !vt
, res: &ys? >> List_vt(y, n)
) :<!wrt,fe> void = let
in
//
case+ xs of
| List_nil
    () => (res := List_vt_nil())
  // List_nil
| List_cons
    (x, xs) => let
    val y = f (pfv | x, env)
    val () = res :=
      List_vt_cons{y}{0}(y, _(*?*))
    val+List_vt_cons
      (_, res1) = res // res1 = res.1
    val () = loop(pfv | xs, f, env, res1)
    prval ((*folded*)) = fold@ (res)
  in
    (*nothing*)
  end // end of [List_vt_cons]
//
end // end of [loop]
//
var res: ys // uninitialized
val () = loop(pfv | xs, f, env, res)
//
in
  res(*List_vt(y,n)*)
end // end of [List_map_funenv]
*)

(* ****** ****** *)

implement
{x}{y}
List_imap{n}(xs) = let
//
prval() = lemma_List_param(xs)
//
fun loop
  {n:nat}{i:nat} .<n>.
(
  xs: List(x, n), i: Int(i)
, res: &ptr? >> List_vt(y, n)
) : void = (
  case+ xs of
  | List_nil
      () => (res := List_vt_nil)
    // List_nil
  | List_cons
      (x, xs) => let
      val y =
        List_imap$fopr<x><y>(i, x)
      val () = res :=
        List_vt_cons{y}{0}(y, _(*?*))
      val+List_vt_cons
        (_, res1) = res // res1 = res.1
      val () = loop(xs, i+1, res1)
      prval ((*void*)) = fold@ (res)
    in
      // nothing
    end // end of [List_cons]
) // end of [loop]
//
var res: ptr
val () = loop(xs, 0, res)
//
in
  res(*List_vt(y, n)*)
end // end of [List_imap]

(* ****** ****** *)

implement
{x}{y}
List_mapopt{n}(xs) = let
//
prval() = lemma_List_param(xs)
//
fun
loop
{n:nat} .<n>.
(
  xs: List(x, n)
, res: &ptr? >> ListLte_vt(y, n)
) : void = let
in
//
case+ xs of
| List_nil
    () =>
    (res := List_vt_nil)
  // List_nil
| List_cons(x, xs) => let
    val opt =
      List_mapopt$fopr<x><y>(x)
    // end of [val]
  in
    case+ opt of
    | ~Some1_vt(y) => let
        val () = res :=
          List_vt_cons{y}{0}(y, _(*?*))
        val+List_vt_cons
          (_, res1) = res // res1 = res.1
        val () = loop(xs, res1)
        prval ((*folded*)) = fold@ (res)
      in
        // nothing
      end // end of [Some_vt]
    | ~None1_vt((*void*)) => loop(xs, res)
  end // end of [List_cons]
//
end // end of [loop]
//
var res: ptr
val () = loop(xs, res)
//
in
  res(*ListLte_vt(y, n)*)
end // end of [List_mapopt]

(* ****** ****** *)

(*
implement
{x}{y}(*tmp*)
List_mapopt_funenv
  {v}{vt}{n}{fe}
  (pfv | xs, f0, env) = let
//
prval() =
  lemma_List_param(xs)
//
vtypedef ys = List0_vt(y)
//
fun
loop
{n:nat} .<n>.
(
  pfv: !v
| xs: List(x, n)
, f0: (!v | x, !vt) -<fun,fe> Option_vt(y)
, env: !vt
, res: &ys? >> ListLte_vt(y, n)
) :<!wrt,fe> void = let
in
//
case+ xs of
| List_nil
    () =>
    (res := List_vt_nil())
  // end of [List_nil]
| List_cons
    (x, xs) => let
    val opt = f0(pfv | x, env)
  in
    case+ opt of
    | ~None_vt() =>
      (
        loop(pfv | xs, f0, env, res)
      ) (* end of [None_vt] *)
    | ~Some_vt(y) => let
        val () = res :=
          List_vt_cons{y}{0}(y, _(*?*))
        val+List_vt_cons
          (_, res1) = res // res1 = res.1
        val () = loop(pfv | xs, f0, env, res1)
        prval ((*folded*)) = fold@ (res)
      in
        (*nothing*)
      end // end of [Some_vt]
  end // end of [List_vt_cons]
//
end // end of [loop]
//
var res: ys // uninitialized
val () = loop(pfv | xs, f0, env, res)
//
in
  res(*ListLte_vt(y,n)*)
end // end of [List_mapopt_funenv]
*)

(* ****** ****** *)

implement
{x1,x2}{y}
List_map2
  {n1,n2}(xs1, xs2) = let
//
prval() = lemma_List_param(xs1)
prval() = lemma_List_param(xs2)
//
fun
loop{n1,n2:nat}
(
  xs1: List(x1, n1)
, xs2: List(x2, n2)
, res: &ptr? >> List_vt(y, min(n1,n2))
) : void = let
in
//
case+ (xs1, xs2) of
| (List_cons(x1, xs1),
   List_cons(x2, xs2)) =>
  {
    val y =
    List_map2$fopr<x1,x2><y>(x1, x2)
    val () =
      res := List_vt_cons{y}{0}(y, _)
    val+List_vt_cons(_, res1) = res
    val ((*void*)) = loop(xs1, xs2, res1)
    prval ((*folded*)) = fold@ (res)
  } (* end of [cons, cons] *)
| (_, _) =>> (res := List_vt_nil((*void*)))
//
end // end of [loop]
//
var res: ptr
val ((*void*)) = loop(xs1, xs2, res)
//
in
  res
end // end of [List_map2]

(* ****** ****** *)

implement
{x}(*tmp*)
List_tabulate
  (n) = let
//
fun loop
  {n:int}
  {i:nat | i <= n}
  .<n-i>. (
  n: Int n, i: Int i
, res: &ptr? >> List_vt(x, n-i)
) : void =
  if n > i then let
    val x =
      List_tabulate$fopr<x>(i)
    val () = res :=
      List_vt_cons{x}{0}(x, _(*?*))
    val+List_vt_cons
      (_, res1) = res // res1 = res.1
    val () = loop(n, succ(i), res1)
    prval ((*folded*)) = fold@ (res)
  in
    // nothing
  end else (res := List_vt_nil)
//
in
//
let var res: ptr; val () = loop(n, 0, res) in res end
//
end // end of [List_tabulate]

(* ****** ****** *)

implement
{x,y}
List_zip
  (xs, ys) = let
//
typedef xy = @(x, y)
//
implement
List_zipwith$fopr<x,y><xy>(x, y) = @(x, y)
//
in
  $effmask_all(List_zipwith<x,y><xy>(xs, ys))
end // end of [List_zip]

implement
{x,y}{xy}
List_zipwith
(
  xs, ys
) = res where
{
//
prval() = lemma_List_param(xs)
prval() = lemma_List_param(ys)
//
fun
loop
{m,n:nat} .<m>.
(
  xs: List(x, m)
, ys: List(y, n)
, res: &ptr? >> List_vt(xy, min(m,n))
) : void = (
//
case+ xs of
| List_nil() =>
    (res := List_vt_nil)
  // List_nil
| List_cons(x, xs) =>
  (
  case+ ys of
  | List_nil() =>
      (res := List_vt_nil)
    // List_nil
  | List_cons
      (y, ys) =>
      fold@(res) where
    {
      val xy =
        List_zipwith$fopr<x,y><xy>(x, y)
      // end of [val]
      val () = res :=
        List_vt_cons{xy}{0}(xy, _(*res*))
      val+List_vt_cons
        (xy, res1) = res // res1 = res.1
      val ((*tailrec*)) = loop(xs, ys, res1)
    } (* end of [List_cons] *)
  ) // end of [List_cons]
//
) (* end of [loop] *)
//
var res: ptr
val ((*void*)) = loop(xs, ys, res)
//
} (* end of [List_zipwith] *)

(* ****** ****** *)

implement
{x,y}
List_cross
  (xs, ys) = let
//
typedef xy = @(x, y)
//
implement
List_crosswith$fopr<x,y><xy>(x, y) = @(x, y)
//
in
  $effmask_all (List_crosswith<x,y><xy>(xs, ys))
end // end of [List_cross]

implement
{x,y}{xy}
List_crosswith
  (xs, ys) = let
//
prval() = lemma_List_param(xs)
prval() = lemma_List_param(ys)
//
fnx
loop1
{m,n:nat} .<m,0,0>.
(
  xs: List(x, m)
, ys: List(y, n)
, res: &ptr? >> List_vt(xy, m*n)
) : void = let
in
  case+ xs of
  | List_cons
      (x, xs) =>
      loop2(xs, ys, x, ys, res)
    // List_cons
  | List_nil() => (res := List_vt_nil())
end // end of [loop1]

and
loop2
{m,n,n2:nat} .<m,n2,1>.
(
  xs: List(x, m)
, ys: List(y, n)
, x: x, ys2: List(y, n2)
, res: &ptr? >> List_vt(xy, m*n+n2)
) : void = let
in
//
case+ ys2 of
| List_cons
    (y, ys2) => let
    val xy = 
      List_crosswith$fopr<x,y><xy>
        (x, y)
      // List_crosswith$fopr
    // end of [val]
    val () = res :=
      List_vt_cons{xy}{0}(xy, _(*?*))
    val+List_vt_cons (_, res1) = res
    val () = loop2(xs, ys, x, ys2, res1)
    prval () = mul_gte_gte_gte{m,n}()
  in
    fold@ (res) // nothing
  end // end of [List_cons]
| List_nil() => loop1(xs, ys, res)
//
end // end of [loop2]
//
in
//
let var res: ptr; val () = loop1(xs, ys, res) in res end
//
end // end of [List_crosswith]

(* ****** ****** *)

implement
{x}(*tmp*)
List_foreach(xs) = let
//
var env: void = () in List_foreach_env<x><void>(xs, env)
//
end // end of [List_foreach]

(* ****** ****** *)

implement
{x}{env}
List_foreach_env
  (xs, env) = let
//
prval() = lemma_List_param(xs)
//
fun
loop
{n:nat} .<n>.
(
  xs: List(x, n), env: &env
) : void = let
in
//
case+ xs of
| List_nil() => ()
| List_cons(x, xs) => let
    val test =
      List_foreach$cont<x><env>(x, env)
    // end of [val]
  in
    if test then let
      val () =
      List_foreach$fwork<x><env>(x, env)
    in
      loop(xs, env)
    end else () // end of [if]
  end // end of [List_cons]
//
end // end of [loop]
//
in
  loop(xs, env)
end // end of [List_foreach_env]

(* ****** ****** *)
//
implement
{x}{env}
List_foreach$cont(x, env) = true
//
(* ****** ****** *)

implement
{x}(*tmp*)
List_foreach_funenv
  {v}{vt}{fe}
  (pfv | xs, f0, env) = let
//
prval() = lemma_List_param(xs)
//
fun
loop{n:nat} .<n>.
(
  pfv: !v
| xs: List(x, n)
, f0: (!v | x, !vt) -<fun,fe> void
, env: !vt
) :<fe> void =
(
  case+ xs of
  | List_nil() => ()
  | List_cons(x, xs) => let
      val () = f0(pfv | x, env) in loop(pfv | xs, f0, env)
    end // end of [List_cons]
) (* end of [loop] *)
//
in
  loop(pfv | xs, f0, env)
end // end of [List_foreach_funenv]

(* ****** ****** *)

implement
{x,y}(*tmp*)
List_foreach2(xs, ys) = let
  var env: void = () in List_foreach2_env<x,y><void>(xs, ys, env)
end // end of [List_foreach2]

implement
{x,y}{env}
List_foreach2_env
  (xs, ys, env) = let
//
prval() = lemma_List_param(xs)
prval() = lemma_List_param(ys)
//
fun loop
  {m,n:nat} .<m>. (
  xs: List(x, m), ys: List(y, n), env: &env
) : void = let
in
//
case+ xs of
| List_nil() => ()
| List_cons(x, xs) => (
  case+ ys of
  | List_nil() => ()
  | List_cons(y, ys) => let
      val test =
        List_foreach2$cont<x,y><env>(x, y, env)
      // end of [val]
    in
      if test then let
        val () = List_foreach2$fwork<x,y><env>(x, y, env)
      in
        loop(xs, ys, env)
      end else () // end of [if]
    end // end of [List_cons]
  ) (* end of [List_cons] *)
//
end // end of [loop]
//
in
  loop(xs, ys, env)
end // end of [List_foreach2_env]

(* ****** ****** *)
//
implement
{x,y}{env}
List_foreach2$cont(x, y, env) = true
//
(* ****** ****** *)

implement
{x}(*tmp*)
List_iforeach
  (xs) = let
  var env: void = ()
in
  List_iforeach_env<x><void>(xs, env)
end // end of [List_iforeach]

implement
{x}{env}
List_iforeach_env
  (xs, env) = let
//
prval() = lemma_List_param(xs)
//
fun
loop
{n:nat}{i:nat} .<n>.
(
  i: Int i, xs: List(x, n), env: &env
) : intBtwe(i,n+i) = (
//
case+ xs of
| List_nil() => (i)
| List_cons(x, xs) => let
    val test =
      List_iforeach$cont<x><env>(i, x, env)
    // end of [test]
  in
    if test then let
      val () = List_iforeach$fwork<x><env>(i, x, env)
    in
      loop(succ(i), xs, env)
    end else (i) // end of [if]
  end // end of [List_cons]
//
) (* end of [loop] *)
//
in
  loop(0, xs, env)
end // end of [List_iforeach_env]

(* ****** ****** *)

implement
{x}{env}(*tmp*)
List_iforeach$cont(i, x, env) = true

(* ****** ****** *)

implement
{x}(*tmp*)
List_iforeach_funenv
  {v}{vt}{n}{fe}
(
  pfv | xs, fwork, env
) = let
//
prval() = lemma_List_param(xs)
//
fun
loop
{ i:nat
| i <= n
} .<n-i>.
(
  pfv: !v
| i: Int i
, xs: List(x, n-i)
, fwork: (!v | natLt(n), x, !vt) -<fun,fe> void
, env: !vt
) :<fe> Int n = (
//
case+ xs of
| List_nil() => i
| List_cons(x, xs) => let
    val () = fwork (pfv | i, x, env) in loop(pfv | i+1, xs, fwork, env)
  end // end of [List_cons]
) (* end of [loop] *)
//
in
  loop(pfv | 0, xs, fwork, env)
end // end of [List_iforeach_funenv]

(* ****** ****** *)

implement
{x,y}(*tmp*)
List_iforeach2
  (xs, ys) = let
  var env: void = ()
in
  List_iforeach2_env<x,y><void>(xs, ys, env)
end // end of [List_iforeach2]

implement
{x,y}{env}
List_iforeach2_env
  (xs, ys, env) = let
//
prval() = lemma_List_param(xs)
prval() = lemma_List_param(ys)
//
fun loop
  {m,n:nat}{i:nat} .<m>.
(
  i: Int i, xs: List(x, m), ys: List(y, n), env: &env
) : intBtwe(i, min(m,n)+i) = let
in
//
case+ xs of
| List_nil() => i // the number of processed elements
| List_cons(x, xs) => (
  case+ ys of
  | List_nil() => (i)
  | List_cons(y, ys) => let
      val test =
        List_iforeach2$cont<x,y><env>(i, x, y, env)
      // end of [val]
    in
      if test
        then let
          val ((*void*)) =
            List_iforeach2$fwork<x,y><env>(i, x, y, env)
          // end of [val]
        in
          loop(succ(i), xs, ys, env)
        end // end of [then]
        else (i) // end of [else]
    end // end of [List_cons]
  ) (* end of [List_cons] *)
//
end // end of [loop]
//
in
  loop(0, xs, ys, env)
end // end of [List_iforeach2_env]

(* ****** ****** *)

implement
{x,y}{env}
List_iforeach2$cont(i, x, y, env) = true

(* ****** ****** *)

implement
{res}{x}
List_foldleft
  (xs, ini) = let
//
prval() = lemma_List_param(xs)
//
fun loop
  {n:nat} .<n>.
(
  xs: List(x, n), res: res
) : res =
  case+ xs of
  | List_nil() => res
  | List_cons(x, xs) => let
      val res =
        List_foldleft$fopr<res><x>(res, x)
      // end of [val]
    in
      loop(xs, res)
    end // end of [List_cons]
// end of [loop]
//
in
  loop(xs, ini)
end // end of [List_foldleft]

(* ****** ****** *)

implement
{x}{res}
List_foldright
  (xs, snk) = let
//
prval() =
lemma_List_param(xs)
//
fun aux
  {n:nat} .<n>.
(
  xs: List(x, n), res: res
) : res =
  case+ xs of
  | List_nil() => res
  | List_cons(x, xs) =>
      List_foldright$fopr<x><res>(x, aux(xs, res))
    // end of [List_cons]
// end of [aux]
//
in
  aux (xs, snk)
end // end of [List_foldright]

(* ****** ****** *)

implement
{a}(*tmp*)
List_is_ordered
  (xs) = let
//
fun
loop
(
x0: a, xs: List_1(a)
) : bool =
(
//
case+ xs of
| List_nil() => true
| List_cons(x1, xs) => let
    val
    sgn =
    gcompare_val_val<a>(x0, x1)
  in
    if sgn <= 0
      then loop(x1, xs) else false
    // end of [if]
  end // end of [List_cons]
//
) (* end of [loop] *)
//
in
  case+ xs of
  | List_nil() => true
  | List_cons(x0, xs) => loop(x0, xs)
end // end of [List_is_ordered]
  
(* ****** ****** *)

implement
{a}(*tmp*)
List_mergesort$cmp
  (x1, x2) = gcompare_val_val<a>(x1, x2)
// end of [List_mergesort$cmp]

implement
{a}(*tmp*)
List_mergesort
  (xs) = let
//
implement
List_vt_mergesort$cmp<a>
  (x1, x2) =
  List_mergesort$cmp<a>(x1, x2)
//
in
//
let val xs =
  List_copy<a>(xs) in List_vt_mergesort<a>(xs)
end // end of [let]
//
end // end of [List_mergesort]

(* ****** ****** *)

implement
{a}(*tmp*)
List_mergesort_fun
  (xs, cmp) = let
//
implement
{a2}(*tmp*)
List_mergesort$cmp
  (x1, x2) = let
//
typedef
cmp2 = cmpval(a2)
//
val cmp2 = $UN.cast{cmp2}(cmp) in cmp2(x1, x2)
//
end // end of [List_mergesort$cmp]
//
in
  List_mergesort<a>(xs)
end // end of [List_mergesort_fun]

implement
{a}(*tmp*)
List_mergesort_cloref
  (xs, cmp) = let
//
implement
{a2}(*tmp*)
List_mergesort$cmp
  (x1, x2) = let
//
typedef
cmp2 = (a2, a2) -<cloref> int
//
val cmp2 =
  $UN.cast{cmp2}(cmp) in cmp2 (x1, x2)
//
end // end of [List_mergesort$cmp]
//
in
  List_mergesort<a>(xs)
end // end of [List_mergesort_cloref]

(* ****** ****** *)

implement
{a}(*tmp*)
List_quicksort$cmp
  (x1, x2) = gcompare_val_val<a>(x1, x2)
// end of [List_quicksort$cmp]

implement
{a}(*tmp*)
List_quicksort
  (xs) = let
//
implement
List_vt_quicksort$cmp<a>
  (x1, x2) =
  List_quicksort$cmp<a>(x1, x2)
//
in
//
let val xs =
  List_copy<a>(xs) in List_vt_quicksort<a>(xs)
end // end of [let]
//
end // end of [List_quicksort]

(* ****** ****** *)

implement
{a}(*tmp*)
List_quicksort_fun
  (xs, cmp) = let
//
implement
{a2}(*tmp*)
List_quicksort$cmp
  (x1, x2) = let
//
typedef
cmp2 = cmpval(a2)
//
val cmp2 = $UN.cast{cmp2}(cmp) in cmp2(x1, x2)
//
end // end of [List_quicksort$cmp]
//
in
  List_quicksort<a>(xs)
end // end of [List_quicksort_fun]

implement
{a}(*tmp*)
List_quicksort_cloref
  (xs, cmp) = let
//
implement
{a2}(*tmp*)
List_quicksort$cmp
  (x1, x2) = let
//
typedef
cmp2 = (a2, a2) -<cloref> int
//
val cmp2 = $UN.cast{cmp2}(cmp) in cmp2(x1, x2)
//
end // end of [List_quicksort$cmp]
//
in
  List_quicksort<a>(xs)
end // end of [List_quicksort_cloref]

(* ****** ****** *)

implement
{a}(*tmp*)
streamize_List_elt
  (xs) = let
//
fun
auxmain
(
  xs: List_1(a)
) : stream_vt(a) = $ldelay
(
  case+ xs of
  | List_nil() => stream_vt_nil()
  | List_cons(x, xs) => stream_vt_cons(x, auxmain(xs))
) : stream_vt_con(a) // $ldelay
//
in
  $effmask_all(auxmain(xs))
end // end of [streamize_List_elt]

(* ****** ****** *)

implement
{a}(*tmp*)
streamize_List_choose2
  (xs) = let
//
typedef a2 = @(a, a)
//
fun
auxmain
(
  xs: List_1(a)
) : stream_vt(a2) = $ldelay
(
  case+ xs of
  | List_nil() => stream_vt_nil()
  | List_cons(x, xs) => !(auxmain2(x, xs))
) : stream_vt_con(@(a, a)) // $ldelay
//
and
auxmain2
(
  x0: a, xs: List_1(a)
) : stream_vt(a2) = $ldelay
(
  case+ xs of
  | List_nil() => !(auxmain(xs))
  | List_cons(x, xs) => stream_vt_cons((x0, x), auxmain2(x0, xs))
) : stream_vt_con(@(a, a)) // $ldelay
//
in
  $effmask_all(auxmain(xs))
end // end of [streamize_List_choose2]

(* ****** ****** *)

implement
{a,b}(*tmp*)
streamize_List_zip
  (xs, ys) = let
//
fun
auxmain
(
  xs: List_1(a)
, ys: List_1(b)
) : stream_vt(@(a, b)) = $ldelay
(
case+ xs of
| List_nil() =>
    stream_vt_nil()
  // end of [List_nil]
| List_cons(x, xs) =>
  (
    case+ ys of
    | List_nil() => stream_vt_nil()
    | List_cons(y, ys) => stream_vt_cons((x, y), auxmain(xs, ys))
  ) (* end of [List_cons] *)
) : stream_vt_con(@(a, b)) // auxmain
//
in
  $effmask_all(auxmain(xs, ys))
end // end of [streamize_List_zip]

(* ****** ****** *)

implement
{a,b}(*tmp*)
streamize_List_cross
  (xs, ys) = let
//
fun
auxone
(
  x0: a
, ys: List_1(b)
) : stream_vt(@(a, b)) = $ldelay
(
case+ ys of
| List_nil() =>
    stream_vt_nil()
  // end of [List_nil]
| List_cons(y, ys) =>
    stream_vt_cons((x0, y), auxone(x0, ys))
) : stream_vt_con(@(a, b))
//
fun
auxmain
(
  xs: List_1(a)
, ys: List_1(b)
) : stream_vt(@(a, b)) = $ldelay
(
case+ xs of
| List_nil() =>
    stream_vt_nil()
  // end of [List_nil]
| List_cons(x0, xs) =>
    !(stream_vt_append(auxone(x0, ys), auxmain(xs, ys)))
) : stream_vt_con(@(a, b))
//
in
  $effmask_all(auxmain(xs, ys))
end // end of [streamize_List_cross]

(* ****** ****** *)

(* end of [List.dats] *)
