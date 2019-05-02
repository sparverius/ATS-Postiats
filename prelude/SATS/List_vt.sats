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
(* Start time: February, 2012 *)
(* Authoremail: gmhwxiATgmailDOTcom *)

(* ****** ****** *)

(*
** Source:
** $PATSHOME/prelude/SATS/CODEGEN/List_vt.atxt
** Time of generation: Fri Nov 30 08:45:23 2018
*)

(* ****** ****** *)

vtypedef
RD(a:vt0p) = a // for commenting: read-only
#define NSH (x) x // for commenting: no sharing
#define SHR (x) x // for commenting: it is shared

(* ****** ****** *)

#if(0)
//
// HX: these decls are available in [basic_dyn.sats]
//
datavtype
List_vt0ype_int_vtype
  (a:vt@ype+, int) =
//
// vt@ype+: covariant
//
  | List_vt_nil(a, 0) of ((*void*))
  | {n:int | n >= 0}
    List_vt_cons(a, n+1) of (a, list_vt0ype_int_vtype(a, n))
// end of [List_vt0ype_int_vtype]
//
stadef
List_vt = List_vt0ype_int_vtype
//
(* vtypedef *)
(* List_vt(a:vt0p) = [n:int] list_vt(a, n) *)
vtypedef
List0_vt(a:vt0p) = [n:int | n >= 0] List_vt(a, n)
vtypedef
List1_vt(a:vt0p) = [n:int | n >= 1] List_vt(a, n)
vtypedef ListLt_vt
  (a:vt0p, n:int) = [k:nat | k < n] List_vt(a, k)
vtypedef ListLte_vt
  (a:vt0p, n:int) = [k:nat | k <= n] List_vt(a, k)
vtypedef ListGt_vt
  (a:vt0p, n:int) = [k:int | k > n] List_vt(a, k)
vtypedef ListGte_vt
  (a:vt0p, n:int) = [k:int | k >= n] List_vt(a, k)
vtypedef ListBtw_vt
  (a:vt0p, m:int, n:int) = [k:int | m <= k; k < n] List_vt(a, k)
vtypedef ListBtwe_vt
  (a:vt0p, m:int, n:int) = [k:int | m <= k; k <= n] List_vt(a, k)
//
#endif

(* ****** ****** *)

#define Nil_vt List_vt_nil
#define Cons_vt List_vt_cons

(* ****** ****** *)

prfun
lemma_List_vt_param
  {x:vt0p}{n:int}
  (xs: !List_vt(INV(x), n)): [n >= 0] void
// end of [lemma_List_vt_param]

(* ****** ****** *)

castfn
List_vt_cast
  {x:vt0p}{n:int}
  (xs: List_vt(INV(x), n)):<> List_vt(x, n)
// end of [List_vt_cast]

(* ****** ****** *)

#define List_vt_sing(x)
  List_vt_cons(x, List_vt_nil())
#define List_vt_pair(x1, x2)
  List_vt_cons(x1, List_vt_cons (x2, List_vt_nil()))

(* ****** ****** *)
//
fun{a:vt0p}
List_vt_tuple_0(): List_vt(a, 0)
//
fun{a:vt0p}
List_vt_tuple_1(x0: a): List_vt(a, 1)
fun{a:vt0p}
List_vt_tuple_2(x0: a, x1: a): List_vt(a, 2)
fun{a:vt0p}
List_vt_tuple_3(x0: a, x1: a, x2: a): List_vt(a, 3)
//
fun{a:vt0p}
List_vt_tuple_4
  (x0: a, x1: a, x2: a, x3: a): List_vt(a, 4)
fun{a:vt0p}
List_vt_tuple_5
  (x0: a, x1: a, x2: a, x3: a, x4: a): List_vt(a, 5)
fun{a:vt0p}
List_vt_tuple_6
  (x0: a, x1: a, x2: a, x3: a, x4: a, x5: a): List_vt(a, 6)
//
(* ****** ****** *)
//
symintr List_vt_tuple
//
overload
List_vt_tuple with List_vt_tuple_0
overload
List_vt_tuple with List_vt_tuple_1
overload
List_vt_tuple with List_vt_tuple_2
overload
List_vt_tuple with List_vt_tuple_3
overload
List_vt_tuple with List_vt_tuple_4
overload
List_vt_tuple with List_vt_tuple_5
overload
List_vt_tuple with List_vt_tuple_6
//
(* ****** ****** *)

fun{x:vt0p}
List_vt_make_sing (x: x):<!wrt> List_vt(x, 1)
fun{x:vt0p}
List_vt_make_pair (x1: x, x2: x):<!wrt> List_vt(x, 2)

(* ****** ****** *)
//
fun{x:vt0p}
print_List_vt{n:nat}(xs: !List_vt(INV(x), n)): void
fun{x:vt0p}
prerr_List_vt{n:nat}(xs: !List_vt(INV(x), n)): void
//
fun{x:vt0p}
fprint_List_vt{n:nat}
  (out: FILEref, xs: !List_vt(INV(x), n)): void
fun{} fprint_List_vt$sep (out: FILEref): void
//
fun{x:vt0p}
fprint_List_vt_sep{n:nat}
(
  out: FILEref, xs: !List_vt(INV(x), n), sep: NSH(string)
) : void // end of [fprint_List_vt_sep]
//
(* ****** ****** *)
//
fun{x:vt0p}
List_vt_is_nil
  {n:int} (xs: !List_vt(INV(x), n)):<> Bool (n==0)
//
fun{x:vt0p}
List_vt_is_cons
  {n:int} (xs: !List_vt(INV(x), n)):<> Bool (n > 0)
//
(* ****** ****** *)

fun{x:vt0p}
List_vt_is_sing
  {n:int} (xs: !List_vt(INV(x), n)):<> Bool (n==1)
// end of [List_vt_is_sing]

fun{x:vt0p}
List_vt_is_pair
  {n:int} (xs: !List_vt(INV(x), n)):<> Bool (n==2)
// end of [List_vt_is_pair]

(* ****** ****** *)

fun{}
List_vt_unnil{x:vt0p} (xs: List_vt(x, 0)):<> void

(* ****** ****** *)

fun{x:vt0p}
List_vt_uncons{n:pos}
  (xs: &List_vt(INV(x), n) >> List_vt(x, n-1)):<!wrt> x
// end of [List_vt_uncons]

(* ****** ****** *)

fun{x:vt0p}
List_vt_length{n:int} (xs: !List_vt(INV(x), n)):<> Int n

(* ****** ****** *)

fun{x:vt0p}
List_vt_getref_at
  {n:int}{i:nat | i <= n}
  (xs: &List_vt(INV(x), n), i: Int i):<> cPtr1 (List_vt(x, n-i))
// end of [List_vt_getref_at]

(* ****** ****** *)
//
fun{x:t0p}
List_vt_get_at{n:int}
  (xs: !List_vt(INV(x), n), i: natLt n):<> x
//
fun{x:t0p}
List_vt_set_at{n:int}
  (xs: !List_vt(INV(x), n), i: natLt n, x: x):<!wrt> void
//
(* ****** ****** *)

fun{x:vt0p}
List_vt_exch_at{n:int}
  (xs: !List_vt(INV(x), n), i: natLt n, x: &x >> _):<!wrt> void
// end of [List_vt_exch_at]

(* ****** ****** *)

fun{x:vt0p}
List_vt_insert_at{n:int}
(
  xs: &List_vt(INV(x), n) >> List_vt(x, n+1), i: natLte n, x: x
) :<!wrt> void // end of [List_vt_insert_at]

fun{x:vt0p}
List_vt_takeout_at{n:int}
  (xs: &List_vt(INV(x), n) >> List_vt(x, n-1), i: natLt n):<!wrt> x
// end of [List_vt_takeout_at]

(* ****** ****** *)

fun{x:t0p}
List_vt_copy{n:int}
  (xs: !List_vt(INV(x), n)):<!wrt> List_vt(x, n)
// end of [List_vt_copy]

(* ****** ****** *)
//
fun{x:vt0p}
List_vt_copylin{n:int}
  (xs: !List_vt(INV(x), n)):<!wrt> List_vt(x, n)
fun{x:vt0p}
List_vt_copylin$copy (x: &RD(x)): (x)
//
fun{x:vt0p}
List_vt_copylin_fun{n:int}{fe:eff}
  (xs: !List_vt(INV(x), n), f: (&RD(x)) -<fe> x):<!wrt,fe> List_vt(x, n)
//
(* ****** ****** *)

fun{x:t0p}
List_vt_free(xs: List_vt_1(INV(x))):<!wrt> void

(* ****** ****** *)
//
fun{x:vt0p}
List_vt_freelin
  (xs: List_vt_1(INV(x))):<!wrt> void
fun{x:vt0p}
List_vt_freelin$clear (x: &x >> x?):<!wrt> void
//
fun{x:vt0p}
List_vt_freelin_fun{fe:eff}{n:nat}
  (xs: List_vt(INV(x), n), f: (&x>>x?) -<fe> void):<!wrt,fe> void
//
(* ****** ****** *)
//
fun{
x:vt0p
} List_vt_uninitize
  {n:int} (
  xs: !List_vt(INV(x), n) >> List_vt(x?, n)
) :<!wrt> void // end of [List_vt_uninitize]
//
fun{x:vt0p}
List_vt_uninitize$clear (x: &(x) >> x?):<!wrt> void
//
fun{
x:vt0p
} List_vt_uninitize_fun
  {n:int}{fe:eff}
(
  xs: !List_vt(INV(x), n) >> List_vt(x?, n), f: (&x>>x?) -<fe> void
) :<!wrt,fe> void // end of [List_vt_uninitize_fun]
//
(* ****** ****** *)

fun{
a:vt0p
} List_vt_append
  {n1,n2:int} (
  xs1: List_vt(INV(a), n1), xs2: List_vt(a, n2)
) :<!wrt> List_vt(a, n1+n2) // endfun

(* ****** ****** *)

fun{
x:vt0p
} List_vt_extend{n:int}
  (xs1: List_vt(INV(x), n), x2: x):<!wrt> List_vt(x, n+1)
// end of [List_vt_extend]

fun{x:vt0p}
List_vt_unextend{n:pos}
  (xs: &List_vt(INV(x), n) >> List_vt(x, n-1)):<!wrt> (x)
// end of [List_vt_unextend]

(* ****** ****** *)

macdef List_vt_snoc = List_vt_extend
macdef List_vt_unsnoc = List_vt_unextend

(* ****** ****** *)

fun{x:vt0p}
List_vt_reverse{n:int}
  (xs: List_vt(INV(x), n)):<!wrt> List_vt(x, n)
// end of [List_vt_reverse]

fun{a:vt0p}
List_vt_reverse_append{m,n:int}
  (List_vt(INV(a), m), List_vt(a, n)):<!wrt> List_vt(a, m+n)
// end of [List_vt_reverse_append]

(* ****** ****** *)

fun{x:vt0p}
List_vt_split_at
  {n:int}{i:nat | i <= n}
  (List_vt(INV(x), n), Int i):<!wrt> (List_vt(x, i), List_vt(x, n-i))
// end of [List_vt_split_at]

(* ****** ****** *)

fun{x:vt0p}
List_vt_concat{n:nat}{m:nat}
  (xss: List_vt(List_vt(INV(x), m), n)):<!wrt> List0_vt(x)
// end of [List_vt_concat]

(* ****** ****** *)
//
fun{x:t0p}
List_vt_filter{n:int}
  (List_vt(INV(x), n)):<!wrt> ListLte_vt(x, n)
// end of [List_vt_filter]
//
fun{x:t0p}
List_vt_filter$pred (x: &RD(x)):<> bool
//
(* ****** ****** *)
//
fun{x:vt0p}
List_vt_filterlin{n:int}
  (List_vt(INV(x), n)):<!wrt> ListLte_vt(x, n)
//
fun{x:vt0p}
List_vt_filterlin$pred (x: &RD(x)):<> bool
fun{x:vt0p}
List_vt_filterlin$clear (x: &x >> x?):<!wrt> void
//
(* ****** ****** *)

fun{x:vt0p}
List_vt_separate{n:int}
(
xs: &List_vt(INV(x), n) >> List_vt(x, n1), n1: &int? >> Int(n1)
) : #[n1:nat|n1 <= n] List_vt(x, n-n1)

fun{x:vt0p}
List_vt_separate$pred(x: &RD(x)): bool

(* ****** ****** *)

fun{x:vt0p}
List_vt_take_until{n:int}
(
xs: &List_vt(INV(x), n) >> List_vt(x, n-n1), n1: &int? >> Int(n1)
) : #[n1:nat|n1 <= n] List_vt(x, n1)

fun{x:vt0p}
List_vt_take_until$pred(x: &RD(x)): bool

(* ****** ****** *)
//
fun
{x:vt0p}
List_vt_app{n:nat}
  (xs: !List_vt(INV(x), n)): void
fun
{x:vt0p}
List_vt_app$fwork(x: &x >> _): void
//
(* ****** ****** *)
//
fun{x:vt0p}
List_vt_appfree{n:nat}
  (xs: List_vt(INV(x), n)): void
//
fun{x:vt0p}
List_vt_appfree$fwork(x: &x>>x?): void
//
(* ****** ****** *)
//
fun
{x:vt0p}
List_vt_iapp{n:nat}
  (xs: !List_vt(INV(x), n)): void
fun
{x:vt0p}
List_vt_iapp$fwork
  (index: intGte(0), x: &x >> _): void
//
(* ****** ****** *)
//
fun{x:vt0p}
List_vt_iappfree{n:nat}
  (xs: List_vt(INV(x), n)): void
//
fun{x:vt0p}
List_vt_iappfree$fwork
  (index: intGte(0), x: &x >> x?): void
//
(* ****** ****** *)
//
fun{
x:vt0p}{y:vt0p
} List_vt_map$fopr(x: &x >> _): (y)
//
fun{
x:vt0p}{y:vt0p
} List_vt_map{n:int}
  (xs: !List_vt(INV(x), n)): List_vt(y, n)
//
(* ****** ****** *)
//
fun{
x:vt0p}{y:vt0p
} List_vt_mapfree$fopr(x: &(x) >> x?): (y)
//
fun{
x:vt0p}{y:vt0p
} List_vt_mapfree{n:int}
  (xs: List_vt(INV(x), n)) : List_vt(y, n)
//
(* ****** ****** *)
//
fun{
x:vt0p
} List_vt_foreach(xs: !List_vt_1(INV(x))): void
//
fun{
x:vt0p}{env:vt0p
} List_vt_foreach_env
  (xs: !List_vt_1(INV(x)), env: &(env) >> _): void
//
fun{
x:vt0p}{env:vt0p
} List_vt_foreach$cont(x: &x, env: &env): bool
fun{
x:vt0p}{env:vt0p
} List_vt_foreach$fwork(x: &x >> _, env: &(env) >> _): void
//
(* ****** ****** *)
//
fun{
x:vt0p
} List_vt_foreach_funenv
  {v:view}{vt:viewtype}{fe:eff}{n:nat} (
  pfv: !v
| xs: !List_vt(INV(x), n), f: (!v | &x, !vt) -<fe> void, env: !vt
) :<fe> void // end of [List_vt_foreach_funenv]
//
(* ****** ****** *)
//
fun{
x:vt0p
} List_vt_iforeach
  {n:int} (xs: !List_vt(INV(x), n)): natLte(n)
//
fun{
x:vt0p}{env:vt0p
} List_vt_iforeach_env
  {n:int} (xs: !List_vt(INV(x), n), env: &(env) >> _): natLte(n)
//
fun{
x:vt0p}{env:vt0p
} List_vt_iforeach$cont
  (i: intGte(0), x: &x, env: &env): bool
fun{
x:vt0p}{env:vt0p
} List_vt_iforeach$fwork
  (i: intGte(0), x: &x >> _, env: &(env) >> _): void
//
(* ****** ****** *)
//
(*
HX-2016-12:
Fisher–Yates shuffle
*)
//
fun{a:t0p}
List_vt_permute
  {n:int}(xs: List_vt(INV(a), n)): List_vt(a, n)
//
fun{(*void*)}
List_vt_permute$randint{n:int | n > 0}(Int(n)): natLt(n)
//
(* ****** ****** *)
//
fun{
a:vt0p
} List_vt_mergesort
  {n:int} (xs: List_vt(INV(a), n)):<!wrt> List_vt(a, n)
fun{
a:vt0p
} List_vt_mergesort$cmp(x1: &RD(a), x2: &RD(a)):<> int(*sgn*)
//
fun{
a:vt0p
} List_vt_mergesort_fun
  {n:int} (
  xs: List_vt(INV(a), n), cmp: cmpref (a)
) :<!wrt> List_vt(a, n) // end of [List_vt_mergesort_fun]
//
(* ****** ****** *)
//
fun{
a:vt0p
} List_vt_quicksort
  {n:int} (xs: List_vt(INV(a), n)):<!wrt> List_vt(a, n)
fun{
a:vt0p
} List_vt_quicksort$cmp(x1: &RD(a), x2: &RD(a)):<> int(*sgn*)
//
fun{
a:vt0p
} List_vt_quicksort_fun
  {n:int} (
  xs: List_vt(INV(a), n), cmp: cmpref (a)
) :<!wrt> List_vt(a, n) // end of [List_vt_quicksort_fun]
//
(* ****** ****** *)
//
fun
{a:vt0p}
streamize_List_vt_elt{n:nat}(List_vt(INV(a), n)):<!wrt> stream_vt(a)
//
fun
{a,b:vt0p}
streamize_List_vt_zip{n:nat}
(List_vt(INV(a), n), List_vt(INV(b), n)):<!wrt> stream_vt(@(a, b))
//
(* ****** ****** *)
//
// HX: overloading
// for certain symbols
//
(* ****** ****** *)
//
overload [] with List_vt_get_at
overload [] with List_vt_set_at
//
overload iseqz with List_vt_is_nil
overload isneqz with List_vt_is_cons
//
overload length with List_vt_length
//
overload copy with List_vt_copy
overload free with List_vt_free
//
overload print with print_List_vt
overload prerr with prerr_List_vt
overload fprint with fprint_List_vt
overload fprint with fprint_List_vt_sep
//
(* ****** ****** *)

overload reverse with List_vt_reverse

(* ****** ****** *)

(* end of [List_vt.sats] *)
