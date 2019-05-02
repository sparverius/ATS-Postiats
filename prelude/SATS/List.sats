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
** $PATSHOME/prelude/SATS/CODEGEN/List.atxt
** Time of generation: Fri Jan 11 08:42:03 2019
*)

(* ****** ****** *)

#define NSH (x) x // for commenting: no sharing
#define SHR (x) x // for commenting: it is shared

(* ****** ****** *)

#if(0)
//
// HX:
// these declarations
// are available in [basic_dyn.sats]
//
datatype
List_t0ype_int_type
  (a:t@ype+, int) =
//
// t@ype+: covariant
//
  | List_nil(a, 0) of ((*void*))
  | {n:int | n >= 0}
    List_cons(a, n+1) of (a, List_t0ype_int_type(a, n))
// end of [List_t0ype_int_type]
//
stadef
List = List_t0ype_int_type
//
typedef
List(a:t0p) = [n:int] List(a, n)
typedef
List0(a:t0p) = [n:int | n >= 0] List(a, n)
typedef
List1(a:t0p) = [n:int | n >= 1] List(a, n)
typedef ListLt
  (a:t0p, n:int) = [k:nat | k < n] List(a, k)
typedef ListLte
  (a:t0p, n:int) = [k:nat | k <= n] List(a, k)
typedef ListGt
  (a:t0p, n:int) = [k:int | k > n] List(a, k)
typedef ListGte
  (a:t0p, n:int) = [k:int | k >= n] List(a, k)
typedef ListBtw
  (a:t0p, m:int, n:int) = [k:int | m <= k; k < n] List(a, k)
typedef ListBtwe
  (a:t0p, m:int, n:int) = [k:int | m <= k; k <= n] List(a, k)
//
#endif

(* ****** ****** *)

#define Nil List_nil
#define Cons List_cons

(* ****** ****** *)

exception
ListSubscriptExn of ()
(*
//
fun
ListSubscriptExn():<> exn = "mac#%ListSubscriptExn_make"
fun
isListSubscriptExn(x: !exn):<> bool = "mac#%isListSubscriptExn"
//
macdef
ifListSubscriptExn
  {tres}(exn, body) =
(
let val x = ,(exn) in
(
//
if
isListSubscriptExn(x)
then
  let prval () = __vfree_exn(x) in ,(body) end
else $raise (x)
//
) : tres // end of [if]
end (* end of [let] *)
) // end of [ifListSubscriptExn]
*)

(* ****** ****** *)

prfun
lemma_List_param
  {x:t0p}{n:int}
  (xs: List(INV(x), n)): [n >= 0] void
// end of [lemma_List_param]

(* ****** ****** *)

castfn
List_cast
  {x:t0p}{n:int}
  (xs: List(INV(x), n)):<> List(x, n)
// end of [List_cast]

(* ****** ****** *)
//
castfn
List_vt2t
  {x:t0p}{n:int}
  (xs: List_vt(INV(x), n)):<> List(x, n)
castfn
List_of_List_vt
  {x:t0p}{n:int}
  (xs: List_vt(INV(x), n)):<!wrt> List(x, n)
//
(* ****** ****** *)

#define List_sing(x)
  List_cons(x, List_nil())
#define List_pair(x1, x2)
  List_cons(x1, List_cons(x2, List_nil()))

(* ****** ****** *)
//
fun{a:t0p}
List_tuple_0(): List(a, 0)
//
fun{a:t0p}
List_tuple_1(x0: a): List(a, 1)
fun{a:t0p}
List_tuple_2(x0: a, x1: a): List(a, 2)
fun{a:t0p}
List_tuple_3(x0: a, x1: a, x2: a): List(a, 3)
//
fun{a:t0p}
List_tuple_4
  (x0: a, x1: a, x2: a, x3: a): List(a, 4)
fun{a:t0p}
List_tuple_5
  (x0: a, x1: a, x2: a, x3: a, x4: a): List(a, 5)
fun{a:t0p}
List_tuple_6
  (x0: a, x1: a, x2: a, x3: a, x4: a, x5: a): List(a, 6)
//
(* ****** ****** *)
//
symintr List_tuple
//
overload
List_tuple with List_tuple_0
overload
List_tuple with List_tuple_1
overload
List_tuple with List_tuple_2
overload
List_tuple with List_tuple_3
overload
List_tuple with List_tuple_4
overload
List_tuple with List_tuple_5
overload
List_tuple with List_tuple_6
//
(* ****** ****** *)

fun{x:t0p}
List_make_sing(x: x):<!wrt> List_vt(x, 1)
fun{x:t0p}
List_make_pair(x1: x, x2: x):<!wrt> List_vt(x, 2)

(* ****** ****** *)

fun{x:t0p}
List_make_elt
  {n:nat} (n: Int n, x: x):<!wrt> List_vt(x, n)
// end of [List_make_elt]

(* ****** ****** *)

fun{}
List_make_intrange
  {l,r:int | l <= r}
  (l: Int l, r: Int r):<!wrt> List_vt(intBtw(l, r), r-l)
// end of [List_make_intrange]

(* ****** ****** *)

fun
{a:vt0p}
List_make_array
  {n:int} (
  A: &(@[INV(a)][n]) >> @[a?!][n], n: Size_t(n)
) :<!wrt> List_vt(a, n) // endfun

(* ****** ****** *)
//
symintr List
//
fun
{a:vt0p}
List_make_arrpsz
  {n:int}
  (psz: arrpsz(INV(a), n)):<!wrt> List_vt(a, n)
//
overload List with List_make_arrpsz
//
(* ****** ****** *)
//
fun{x:t0p}
print_List(xs: List_1(INV(x))): void
fun{x:t0p}
prerr_List(xs: List_1(INV(x))): void
//
fun{x:t0p}
fprint_List(out: FILEref, xs: List_1(INV(x))): void
fun{x:t0p}
fprint_List_sep
  (out: FILEref, xs: List_1(INV(x)), sep: string): void
// end of [fprint_List_sep]
//
fun{}
fprint_List$sep(out: FILEref): void
//
(* ****** ****** *)

fun{x:t0p}
fprint_ListList_sep
( out: FILEref
, xss: List_1(List_1(INV(x))), sep1: string, sep2: string
) : void // end of [fprint_ListList_sep]

(* ****** ****** *)
(*
//
// HX: for testing macdef
//
*)
//
(*
//
macdef
fprintlst_mac
  {T:t@ype}
  (fpr, out, xs0, sep) = let
//
val out = ,(out)
val xs0 = ,(xs0); val sep = ,(sep)
//
fun
loop (
xs: List(T), i: int
) : void =
  case+ xs of
  | List_nil
      () => ((*void*))
    // List_nil
  | List_cons
      (x, xs) => let
      val () =
      if i > 0
        then fprint_string(out, sep)
      // end of [if]
      val () = ,(fpr)(out, x)
    in
      loop (xs, i+1)
    end // end of [List_cons]
//
in
  loop(xs0, 0)
end // end of [fprintlst_mac]
*)
//
(* ****** ****** *)
//
fun{}
List_is_nil
  {x:t0p}{n:int}(xs: List(x, n)):<> Bool(n==0)
fun{}
List_is_cons
  {x:t0p}{n:int}(xs: List(x, n)):<> Bool(n > 0)
//
fun{x:t0p}
List_is_sing
  {n:int}(xs: List(INV(x), n)):<> Bool(n == 1)
fun{x:t0p}
List_is_pair
  {n:int}(xs: List(INV(x), n)):<> Bool(n == 2)
//
fun{x:t0p}
List_isnot_sing
  {n:int}(xs: List(INV(x), n)):<> Bool(n != 1)
fun{x:t0p}
List_isnot_pair
  {n:int}(xs: List(INV(x), n)):<> Bool(n != 2)
//
(* ****** ****** *)

fun{x:t0p}
List_head{n:pos}(xs: List(INV(x), n)):<> (x)
fun{x:t0p}
List_head_exn{n:int}(xs: List(INV(x), n)):<!exn> (x)

(* ****** ****** *)

fun{x:t0p}
List_tail{n:pos}
  (xs: SHR(List(INV(x), n))):<> List(x, n-1)
fun{x:t0p}
List_tail_exn{n:int}
  (xs: SHR(List(INV(x), n))):<!exn> List(x, n-1)

(* ****** ****** *)

fun{x:t0p}
List_last{n:pos} (xs: List(INV(x), n)):<> (x)
fun{x:t0p}
List_last_exn{n:int} (xs: List(INV(x), n)):<!exn> (x)

(* ****** ****** *)
//
fun{
x:t0p
} List_nth{n:int}
  (List(INV(x), n), natLt(n)):<> (x)
fun{x:t0p}
List_nth_opt{n:nat}
  (xs: List(INV(x), n), i: intGte(0)):<> Option_vt_1(x)
//
fun{x:t0p}
List_get_at{n:int}
  (List(INV(x), n), natLt(n)):<> (x)
fun{x:t0p}
List_get_at_opt{n:nat}
  (xs: List(INV(x), n), i: intGte(0)):<> Option_vt_1(x)
//
(* ****** ****** *)
//
fun{x:t0p}
List_fset_at{n:nat}
  (List(INV(x), n), natLt(n), x):<> List(x, n)
fun{x:t0p}
List_fexch_at{n:nat}
  (List(INV(x), n), natLt(n), x):<> (List(x, n), x)
//
(* ****** ****** *)

fun{x:t0p}
List_insert_at
  {n:int}
(
xs: SHR(List(INV(x), n)), i: natLte(n), x: x
) :<> List(x, n+1) // end of [List_insert_at]

fun{x:t0p}
List_remove_at
  {n:int} (
  xs: SHR(List(INV(x), n)), i: natLt(n)
) :<> List(x, n-1) // end of [List_remove_at]

fun{x:t0p}
List_takeout_at
  {n:int} (
  xs: SHR(List(INV(x), n)), i: natLt(n), x: &(x)? >> x
) :<!wrt> List(x, n-1) // end of [List_takeout_at]

(* ****** ****** *)

fun{x:t0p}
List_length
  {n:int} (xs: List(INV(x), n)):<> Int(n)
// end of [List_length]

(* ****** ****** *)
//
fun{x:t0p}
List_length_gte
  {n1,n2:int}
  (xs: List(INV(x), n1), n2: Int(n2)): Bool(n1 >= n2)
fun{x:t0p}
List_length_compare
  {n1,n2:int}
  (xs: List(INV(x), n1), n2: Int(n2)): Int(sgn(n1-n2))
//
overload >= with List_length_gte
overload compare with List_length_compare
//
(* ****** ****** *)

fun
{x:t0p}
List_copy
  {n:int}
  (xs: List(INV(x), n)):<!wrt> List_vt(x, n)
// end of [List_copy]

(* ****** ****** *)
//
fun
{a:t0p}
List_append
  {m,n:int}
(
xs: NSH(List(INV(a), m)), ys: SHR(List(a, n))
) :<> List(a, m+n) // end of [List_append]
//
(* ****** ****** *)

fun
{a:t0p}
List_append1_vt
  {i,j:int} (
  xs: List_vt(INV(a), i), ys: SHR(List(a, j))
) :<!wrt> List(a, i+j) // endfun
fun
{a:t0p}
List_append2_vt
  {i,j:int} (
  xs: NSH(List(INV(a), i)), ys: List_vt(a, j)
) :<!wrt> List_vt(a, i+j) // endfun

(* ****** ****** *)
//
fun{
x:t0p
} List_extend{n:int}
  (xs: List(INV(x), n), x: x):<!wrt> List_vt(x, n+1)
// end of [List_extend]
//
macdef List_snoc (xs, x) = List_extend (,(xs), ,(x))
//
(* ****** ****** *)
//
fun
{a:t0p}
mul_int_List
  {m,n:int | m >= 0}
  (m: Int(m), xs: List(a, n)):<!wrt> List_vt(a, m*n)
//
(* ****** ****** *)

fun{x:t0p}
List_reverse
  {n:int} (xs: List(INV(x), n)):<!wrt> List_vt(x, n)
// end of [List_reverse]

(* ****** ****** *)
//
fun{a:t0p}
List_reverse_append
  {m,n:int}
  (xs: NSH(List(INV(a), m)), ys: SHR(List(a, n))):<> List(a, m+n)
// end of [List_reverse_append]
//
fun{a:t0p}
List_reverse_append1_vt
  {m,n:int}
  (xs: List_vt(INV(a), m), ys: SHR(List(a, n))):<!wrt> List(a, m+n)
// end of [List_reverse_append1_vt]
fun{a:t0p}
List_reverse_append2_vt
  {m,n:int}
  (xs: NSH(List(INV(a), m)), ys: List_vt(a, n)):<!wrt> List_vt(a, m+n)
// end of [List_reverse_append2_vt]
//
macdef List_revapp = List_reverse_append
macdef List_revapp1_vt = List_reverse_append1_vt
macdef List_revapp2_vt = List_reverse_append2_vt
//
(* ****** ****** *)

fun{x:t0p}
List_concat(xss: List_1(List_1(INV(x)))):<!wrt> List0_vt(x)

(* ****** ****** *)
//
fun{
x:t0p
} List_take
  {n:int}{i:nat | i <= n}
  (xs: List(INV(x), n), i: Int i):<!wrt> List_vt(x, i)
fun{
x:t0p
} List_take_exn
  {n:int}{i:nat} // it may raise [ListSubscriptException]
  (xs: List(INV(x), n), i: Int i):<!exnwrt> [i <= n] List_vt(x, i)
//
(* ****** ****** *)
//
fun{
x:t0p
} List_drop
  {n:int}{i:nat | i <= n}
  (xs: SHR(List(INV(x), n)), i: Int i):<> List(x, n-i)
fun{
x:t0p
} List_drop_exn
  {n:int}{i:nat} // it may raise [ListSubscriptException]
  (xs: SHR(List(INV(x), n)), i: Int i):<!exn> [i <= n] List(x, n-i)
//
(* ****** ****** *)

fun{
x:t0p
} List_split_at
  {n:int}{i:nat | i <= n}
  (xs: SHR(List(INV(x), n)), i: Int i):<!wrt> (List_vt(x, i), List(x, n-i))
// end of [List_split_at]

(* ****** ****** *)
//
fun{x:t0p}
List_exists$pred(x: x):<> bool
fun{x:t0p}
List_exists(xs: List_1(INV(x))):<> bool
//
(* ****** ****** *)
//
fun{x:t0p}
List_forall$pred(x: x):<> bool
fun{x:t0p}
List_forall(xs: List_1(INV(x))):<> bool
//
(* ****** ****** *)
//
fun{x:t0p}
List_equal$eqfn(x1: x, x2: x):<> bool
fun{x:t0p}
List_equal(xs1: List_1(INV(x)), xs2: List_1(x)):<> bool
//
(* ****** ****** *)
//
fun{x:t0p}
List_compare$cmpfn(x1: x, x2: x):<> int
fun{x:t0p}
List_compare(xs1: List_1(INV(x)), xs2: List_1(x)):<> int
//
(* ****** ****** *)
//
fun{
x:t0p
} List_find{n:int}
(
  xs: List(INV(x), n), x0: &(x)? >> opt(x, i >= 0)
) :<!wrt> #[i:int | i < n] Int(i) // end-of-function
//
fun{x:t0p} List_find$pred (x):<> bool
//
fun{x:t0p} List_find_exn (xs: List_1(INV(x))):<!exn> x
fun{x:t0p} List_find_opt (xs: List_1(INV(x))):<> Option_vt_1(x)
//
(* ****** ****** *)
//
fun{
key,itm:t0p
} List_assoc
(
  List_1 @(INV(key), itm), key, x: &itm? >> opt(itm, b)
) :<> #[b:bool] Bool(b) // end of [List_assoc]
//
fun{key:t0p}
List_assoc$eqfn (k1: key, k2: key):<> bool
//
fun{
key,itm:t0p
} List_assoc_exn
  (kxs: List_1 @(INV(key), itm), k: key):<!exn> itm
fun{
key,itm:t0p
} List_assoc_opt
  (kxs: List_1 @(INV(key), itm), k: key):<> Option_vt_1(itm)
//
(* ****** ****** *)
//
fun{
x:t0p
} List_filter{n:int}
  (xs: List(INV(x), n)): ListLte_vt(x, n)
//
fun{x:t0p} List_filter$pred (x): bool
//
(*
fun{
x:t0p
} List_filter_funenv
  {v:view}{vt:viewtype}{n:int}{fe:eff}
(
  pfv: !v |
  xs: List(INV(x), n)
, f: (!v | x, !vt) -<fun,fe> bool, env: !vt
) :<fe,!wrt> ListLte_vt(x, n) // end-of-function
*)
//
(* ****** ****** *)

fun{
x:t0p
} List_labelize{n:int}
  (xs: List(INV(x), n)):<!wrt> List_vt(@(int, x), n)
// end of [List_labelize]

(* ****** ****** *)
//
fun{x:t0p}
List_app (xs: List_1(INV(x))): void
//
fun{x:t0p} List_app$fwork (x): void
//
(* ****** ****** *)
//
(*
fun{
x:t0p
} List_app_funenv
  {v:view}{vt:viewtype}{n:int}{fe:eff} (
  pfv: !v |
  xs: List(INV(x), n)
, f: (!v | x, !vt) -<fun,fe> void, env: !vt
) :<fe> void // end of [List_app_funenv]
*)
//
(* ****** ****** *)
//
fun{
x:t0p}{y:vt0p
} List_map{n:int}
  (xs: List(INV(x), n)): List_vt(y, n)
// end of [List_map]
//
fun{x:t0p}{y:vt0p} List_map$fopr(x: x): (y)
//
(* ****** ****** *)
//
(*
fun{
x:t0p}{y:vt0p
} List_map_funenv
  {v:view}{vt:viewtype}{n:int}{fe:eff} (
  pfv: !v |
  xs: List(INV(x), n)
, fopr: (!v | x, !vt) -<fun,fe> y, env: !vt
) :<fe,!wrt> List_vt(y, n) // end of [List_map_funenv]
*)
//
(* ****** ****** *)
//
fun
{x:t0p}
{y:vt0p}
List_imap{n:int}
  (xs: List(INV(x), n)): List_vt(y, n)
//
fun
{x:t0p}
{y:vt0p}
List_imap$fopr(i: intGte(0), x: x): (y)
//
(* ****** ****** *)
//
fun
{x:t0p}
{y:vt0p}
List_mapopt{n:int}
  (xs: List(INV(x), n)): ListLte_vt(y, n)
//
fun
{x:t0p}
{y:vt0p}
List_mapopt$fopr(x: x): Option_vt_1(y)
//
(*
fun{
x:t0p}{y:t0p
} List_mapopt_funenv
  {v:view}{vt:viewtype}{n:int}{fe:eff}
(
  pfv: !v |
  xs: List(INV(x), n)
, f: (!v | x, !vt) -<fun,fe> Option_vt(y), env: !vt
) :<fe> ListLte_vt(y, n) // end of [List_mapopt_funenv]
*)
//
(* ****** ****** *)

fun{
x1,x2:t0p}{y:vt0p
} List_map2{n1,n2:int}
(
  xs1: List(INV(x1), n1)
, xs2: List(INV(x2), n2)
) : List_vt(y, min(n1,n2)) // end of [List_map2]
//
fun{
x1,x2:t0p}{y:vt0p
} List_map2$fopr(x1: x1, x2: x2): (y)
//
(*
fun{
x1,x2:t0p}{y:t0p
} List_map2_funenv
  {v:view}{vt:viewtype}{n1,n2:int}{fe:eff}
(
  pfv: !v |
  xs1: List(INV(x1), n1)
, xs2: List(INV(x2), n2)
, f: (!v | x1, x2, !vt) -<fun,fe> y, env: !vt
) :<fe> List_vt(y, min(n1,n2)) // end of [List_map2_funenv]
*)
//
(* ****** ****** *)
//
fun{
a:vt0p
} List_tabulate{n:nat}(n: Int(n)): List_vt(a, n)
//
fun{a:vt0p} List_tabulate$fopr(index: intGte(0)): (a)
//
(* ****** ****** *)
//
fun{
x,y:t0p
} List_zip{m,n:int}
(
  xs: List(INV(x), m)
, ys: List(INV(y), n)
) :<!wrt> List_vt((x, y), min(m,n))
//
fun
{x,y:t0p}
{res:vt0p}
List_zipwith{m,n:int}
(
  xs: List(INV(x), m)
, ys: List(INV(y), n)
) : List_vt(res, min(m,n)) // endfun
//
fun
{x,y:t0p}
{res:vt0p}
List_zipwith$fopr(x: x, y: y): (res)
//
(* ****** ****** *)
//
fun
{x,y:t0p}
List_cross
  {m,n:int}
(
  xs: List(INV(x), m)
, ys: List(INV(y), n)
) :<!wrt> List_vt((x, y), m*n) // endfun
//
fun
{x,y:t0p}
{res:vt0p}
List_crosswith
  {m,n:int}
(
  xs: List(INV(x), m)
, ys: List(INV(y), n)
) : List_vt(res, m*n) // end of [List_crosswith]
//
fun
{x,y:t0p}
{res:vt0p}
List_crosswith$fopr(x: x, y: y): (res)
//
(* ****** ****** *)

fun
{x:t0p}
List_foreach(xs: List_1(INV(x))): void
fun
{x:t0p}
{env:vt0p}
List_foreach_env
  (xs: List_1(INV(x)), env: &(env) >> _): void
//
fun
{x:t0p}
{env:vt0p}
List_foreach$cont (x: x, env: &env): bool
fun
{x:t0p}
{env:vt0p}
List_foreach$fwork (x: x, env: &(env) >> _): void
//
(* ****** ****** *)
//
fun
{x:t0p}
List_foreach_funenv
  {v:view}{env:viewtype}{fe:eff}
(
  pf: !v
| xs: List_1(INV(x))
, fwork: (!v | x, !env) -<fun,fe> void, env: !env
) :<fe> void // end of [List_foreach_funenv]
//
(* ****** ****** *)
//
fun{
x,y:t0p
} List_foreach2
  (xs: List_1(INV(x)), ys: List_1(INV(y))): void
//
fun{
x,y:t0p}{env:vt0p
} List_foreach2_env
  (xs: List_1(INV(x)), ys: List_1(INV(y)), env: &(env) >> _): void
//
fun{
x,y:t0p}{env:vt0p
} List_foreach2$cont(x: x, y: y, env: &env): bool
fun{
x,y:t0p}{env:vt0p
} List_foreach2$fwork(x: x, y: y, env: &(env) >> _): void
//
(* ****** ****** *)

fun{
x:t0p
} List_iforeach{n:int}
  (xs: List(INV(x), n)): natLte(n)

fun{
x:t0p}{env:vt0p
} List_iforeach_env{n:int}
  (xs: List(INV(x), n), env: &(env) >> _): natLte(n)
//
fun{
x:t0p}{env:vt0p
} List_iforeach$cont(i: intGte(0), x: x, env: &env): bool
fun{
x:t0p}{env:vt0p
} List_iforeach$fwork(i: intGte(0), x: x, env: &(env) >> _): void
//
(* ****** ****** *)

fun{
x:t0p // type for elements
} List_iforeach_funenv
  {v:view}{vt:viewtype}{n:int}{fe:eff} (
  pfv: !v |
  xs: List(INV(x), n)
, fwork: (!v | natLt(n), x, !vt) -<fun,fe> void, env: !vt
) :<fe> Int (n) // end of [List_iforeach_funenv]

(* ****** ****** *)

fun{
x,y:t0p
} List_iforeach2{m,n:int}
(
  xs: List(INV(x), m), ys: List(INV(y), n)
) : natLte(min(m,n)) // end-of-function

fun{
x,y:t0p}{env:vt0p
} List_iforeach2_env{m,n:int}
(
  xs: List(INV(x), m), ys: List(INV(y), n), env: &(env) >> _
) : natLte(min(m,n)) // end-of-function
//
fun{
x,y:t0p}{env:vt0p
} List_iforeach2$cont
  (i: intGte(0), x: x, y: y, env: &env): bool
fun{
x,y:t0p}{env:vt0p
} List_iforeach2$fwork
  (i: intGte(0), x: x, y: y, env: &(env) >> _): void
//
(* ****** ****** *)
//
fun{
res:vt0p}{x:t0p
} List_foldleft
  (xs: List_1(INV(x)), ini: res): res
fun{
res:vt0p}{x:t0p
} List_foldleft$fopr(acc: res, x: x): res
//
(* ****** ****** *)
//
fun{
x:t0p}{res:vt0p
} List_foldright
  (xs: List_1(INV(x)), snk: res): res
fun{
x:t0p}{res:vt0p
} List_foldright$fopr(x: x, acc: res): res
//
(* ****** ****** *)
//
// HX-2017-02-19:
// Using [gcompare_val_val] to check
//
fun
{a:t0p}
List_is_ordered(xs: List_1(INV(a))): bool
//
(* ****** ****** *)
//
fun{a:t0p}
List_mergesort{n:int}
  (xs: List(INV(a), n)):<!wrt> List_vt(a, n)
//
fun{a:t0p}
List_mergesort$cmp(x1: a, x2: a):<> int (* sign *)
//
(* ****** ****** *)

fun{
a:t0p
} List_mergesort_fun
  {n:int} (
  xs: List(INV(a), n), cmp: cmpval (a)
) :<!wrt> List_vt(a, n) // end-of-function

fun{
a:t0p
} List_mergesort_cloref
  {n:int} (
  xs: List(INV(a), n), cmp: (a, a) -<cloref> int
) :<!wrt> List_vt(a, n) // end of [List_mergesort_cloref]

(* ****** ****** *)
//
fun{
a:t0p
} List_quicksort{n:int}
  (xs: List(INV(a), n)) :<!wrt> List_vt(a, n)
//
fun{a:t0p}
List_quicksort$cmp(x1: a, x2: a):<> int (* sign *)
//
(* ****** ****** *)

fun{
a:t0p
} List_quicksort_fun
  {n:int} (
  xs: List(INV(a), n), cmp: cmpval (a)
) :<!wrt> List_vt(a, n) // end-of-function

fun{
a:t0p
} List_quicksort_cloref
  {n:int} (
  xs: List(INV(a), n), cmp: (a, a) -<cloref> int
) :<!wrt> List_vt(a, n) // end of [List_quicksort_cloref]

(* ****** ****** *)
//
fun{a:t0p}
streamize_List_elt{n:nat}
  (xs: List(INV(a), n)):<!wrt> stream_vt(a)
//
fun{a:t0p}
streamize_List_choose2{n:nat}
  (xs: List(INV(a), n)):<!wrt> stream_vt(@(a, a))
//
(* ****** ****** *)
//
fun
{a,b:t0p}
streamize_List_zip{n:nat}{m:nat}
  (List(INV(a), n), List(INV(b), m)):<!wrt> stream_vt(@(a, b))
//
fun
{a,b:t0p}
streamize_List_cross{n:nat}{m:nat}
  (List(INV(a), n), List(INV(b), m)):<!wrt> stream_vt(@(a, b))
//
(* ****** ****** *)
//
// HX: overloading
// for certain symbols
//
(* ****** ****** *)
//
overload = with List_equal
//
overload + with List_append
//
(*
overload * with mul_int_List
*)
//
overload [] with List_get_at
//
overload iseqz with List_is_nil
overload isneqz with List_is_cons
//
overload .head with List_head
overload .tail with List_tail
//
overload length with List_length
//
overload copy with List_copy
//
overload print with print_List
overload prerr with prerr_List
overload fprint with fprint_List
overload fprint with fprint_List_sep
//
(* ****** ****** *)

overload reverse with List_reverse
 
(* ****** ****** *)

(* end of [List.sats] *)
