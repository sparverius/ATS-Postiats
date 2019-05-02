(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-2015 Hongwei Xi, ATS Trustful Software, Inc.
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

(*
**
** Functional mset based on ordered lists
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: May 18, 2011
**
*)

(* ****** ****** *)
//
// HX-2015-09: ported to ATS/Postitats from ATS/Anairiats
//
(* ****** ****** *)

#define
ATS_PACKNAME "ATSLIB.libats.funmset_listord"
#define
ATS_DYNLOADFLAG 0 // no need for dynloading at run-time
#define
ATS_EXTERN_PREFIX "atslib_" // prefix for external names

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "libats/SATS/funmset_listord.sats"

(* ****** ****** *)
//
#include "./SHARE/funmset.hats" // code reuse
//
(* ****** ****** *)

assume
mset_type (a: t0p) = List0 @(intGt(0), a)

(* ****** ****** *)
//
// HX:
// A mset is represented as a sorted list in descending order;
// note that descending order is chosen to faciliate set comparison
//
(* ****** ****** *)

implement
{}(*tmp*)
funmset_nil () = List_nil()
implement
{}(*tmp*)
funmset_make_nil () = List_nil()

(* ****** ****** *)
//
implement
{a}(*tmp*)
funmset_sing
  (x) = List_cons((1, x), List_nil)
implement
{a}(*tmp*)
funmset_make_sing
  (x) = List_cons((1, x), List_nil)
//
(* ****** ****** *)

implement
{a}(*tmp*)
funmset_make_list
  (xs) = let
//
fun
loop1
(
  xs: List_vt_1(a)
) : mset(a) =
(
case+ xs of
| ~Nil_vt() => List_nil()
| ~Cons_vt(x, xs) => loop2(xs, x, 1, List_nil)
) (* end of [loop1] *)
//
and
loop2
(
  xs: List_vt_1(a), x0: a, n: intGt(0), res: mset(a)
) : mset(a) =
(
case+ xs of
| ~Nil_vt() =>
    List_cons ((n, x0), res)
  // end of [List_nil]
| ~Cons_vt(x1, xs) => let
    val sgn = compare_elt_elt<a> (x0, x1)
  in
    if sgn = 0
      then loop2(xs, x0, n+1, res)
      else loop2(xs, x1, 1, List_cons ((n, x0), res))
    // end of [if]
  end // end of [List_cons]
)
//
implement
List_mergesort$cmp<a>
  (x1, x2) = compare_elt_elt<a> (x1, x2)
//
in
  $effmask_all(loop1(List_mergesort(xs)))
end // end of [funmset_make_list]

(* ****** ****** *)
//
implement
{}(*tmp*)
funmset_is_nil(nxs) = List_is_nil(nxs)
implement
{}(*tmp*)
funmset_isnot_nil(nxs) = List_is_cons(nxs)
//
(* ****** ****** *)

implement
{a}(*tmp*)
funmset_size(nxs) = let
//
fun
loop
(
  nxs: List0 @(intGt(0), a), res: size_t
) : size_t =
(
case+ nxs of
| List_nil
    ((*void*)) => res
| List_cons
    ((n, x), nxs) => loop (nxs, res+i2sz(n))
  // end of [List_cons]
)
//
in
  $effmask_all(loop(nxs, i2sz(0)))
end // end of [funmset_size]

(* ****** ****** *)
//
implement
{a}(*tmp*)
funmset_is_member
  (nxs, x0) = funmset_get_ntime(nxs, x0) > 0
implement
{a}(*tmp*)
funmset_isnot_member
  (nxs, x0) = funmset_get_ntime(nxs, x0) = 0
//
(* ****** ****** *)

implement
{a}(*tmp*)
funmset_get_ntime
  (nxs, x0) = let
//
fun
loop
(
  nxs: List0 @(intGt(0), a), x0: a
) : intGte(0) =
(
case+ nxs of
| List_nil
    ((*void*)) => 0
| List_cons
    ((n, x), nxs) => let
    val sgn = compare_elt_elt<a> (x0, x)
  in
    if sgn < 0
      then loop(nxs, x0) else (if sgn > 0 then 0 else n)
    // end of [if]
  end // end of [List_cons]
) (* end of [loop] *)
//
in
  loop(nxs, x0)
end // end of [funmset_get_ntime]

(* ****** ****** *)

implement
{a}(*tmp*)
funmset_insert2
  (nxs, n0, x0) = let
//
typedef nx = @(intGt(0), a)
//
fun
loop
(
  nxs: List_1(nx)
, nbef: &int? >> intGte(0)
) : List0 nx =
(
//
case+ nxs of
| List_nil() => let
    val () = nbef := 0
  in
    List_cons((n0, x0), List_nil)
  end // end of [List_nil]
| List_cons
    (nx, nxs2) => let
    val x1 = nx.1
    val sgn =
      compare_elt_elt<a> (x0, nx.1)
    // end of [val]
  in
    if sgn < 0
      then List_cons(nx, loop(nxs2, nbef))
      else (
        if sgn > 0
          then (nbef := 0; List_cons((n0, x0), nxs))
          else (nbef := nx.0; List_cons((nbef+n0, x1), nxs2))
        // end of [if]
      ) (* end of [else] *)
    // end of [if]
  end // end of [List_cons]
) (* end of [loop] *)
//
var nbef: int // uninitized
//
in
  nxs := loop(nxs, nbef); nbef
end // end of [funmset_insert2]

(* ****** ****** *)

implement
{a}(*tmp*)
funmset_remove2
  (nxs, n0, x0) = let
//
typedef nx = @(intGt(0), a)
//
fun
loop
(
  nxs: List_1(nx), nbef: &int? >> intGte(0)
) : List0 nx =
(
//
case+ nxs of
| List_nil() =>
  (
    nbef := 0; List_nil()
  ) // end of [List_nil]
| List_cons
    (nx, nxs2) => let
    val x1 = nx.1
    val sgn =
      compare_elt_elt<a> (x0, nx.1)
    // end of [val]
  in
    if sgn < 0
      then List_cons(nx, loop(nxs2, nbef))
      else (
        if sgn > 0
          then (nbef := 0; nxs)
          else let
            val () = nbef := nx.0
          in
            if n0 <= nbef
              then nxs2 else List_cons((n0-nbef, nx.1), nxs2)
            // end of [if]
          end // end of [else]
        // end of [if]
      ) (* end of [else] *)
    // end of [if]
  end // end of [List_cons]
) (* end of [loop] *)
//
var nbef: int // uninitized
//
in
  nxs := loop(nxs, nbef); nbef
end // end of [funmset_remove2]

(* ****** ****** *)

implement
{a}(*tmp*)
funmset_union
  (nxs, nys) = let
//
typedef nx = (intGt(0), a)
//
prval () = lemma_List_param(nxs)
prval () = lemma_List_param(nys)
//
fun
union
(
  nxs: List0(nx)
, nys: List0(nx)
) : List0(nx) = (
//
case+
(nxs, nys) of
// case+
| (List_nil(), _) => nys
| (_, List_nil()) => nxs
| (List_cons(nx, nxs2),
   List_cons(ny, nys2)) => let
   val x = nx.1
   and y = ny.1
   val sgn = compare_elt_elt<a> (x, y)
 in
   if sgn < 0
     then List_cons(ny, union(nxs, nys2))
     else (
       if sgn > 0
         then List_cons(nx, union(nxs2, nys))
         else List_cons((nx.0+ny.0, x), union(nxs2, nys2))
       // end of [if]
     ) (* end of [if] *)
   // end of [if]
 end // end of [cons, cons]
//
) (* end of [union] *)
//
in
  union(nxs, nys)
end // end of [funmset_union]

(* ****** ****** *)

implement
{a}(*tmp*)
funmset_intersect
  (nxs, nys) = let
//
typedef nx = (intGt(0), a)
//
prval () = lemma_List_param(nxs)
prval () = lemma_List_param(nys)
//
fun
intersect
(
  nxs: List0(nx)
, nys: List0(nx)
) : List0(nx) = (
//
case+
(nxs, nys) of
// case+
| (List_nil(), _) => List_nil()
| (_, List_nil()) => List_nil()
| (List_cons(nx, nxs2),
   List_cons(ny, nys2)) => let
   val x = nx.1
   and y = ny.1
   val sgn = compare_elt_elt<a> (x, y)
 in
   if sgn < 0
     then intersect(nxs, nys2)
     else (
       if sgn > 0
         then intersect(nxs2, nys)
         else List_cons((min(nx.0,ny.0), x), intersect(nxs2, nys2))
       // end of [if]
     ) (* end of [if] *)
   // end of [if]
 end // end of [cons, cons]
//
) (* end of [intersect] *)
//
in
  intersect(nxs, nys)
end // end of [funmset_intersect]

(* ****** ****** *)

implement
{a}{env}
funmset_foreach_env
  (nxs, env) = let
//
fun
loop:
$d2ctype
(
  funmset_foreach_env<a><env>
) =
lam(nxs, env) =>
(
case+ nxs of
| List_nil
    ((*void*)) => ()
| List_cons
    ((n, x), nxs) => let
    val () = funmset_foreach$fwork(n, x, env)
  in
    loop(nxs, env)
  end // end of [List_cons]
)
//
in
  loop(nxs, env)
end // end of [funmset_foreach_env]

(* ****** ****** *)

(* end of [funmset_listord.dats] *)
