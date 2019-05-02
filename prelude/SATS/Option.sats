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

(*
** Source:
** $PATSHOME/prelude/SATS/CODEGEN/Option.atxt
** Time of generation: Fri Nov 30 08:45:23 2018
*)

(* ****** ****** *)

(* Author: Hongwei Xi *)
(* Authoremail: hwxi AT cs DOT bu DOT edu *)
(* Start time: February, 2012 *)

(* ****** ****** *)

sortdef t0p = t@ype

(* ****** ****** *)

#if(0)
//
// HX:
// these declarations
// are available in [basic_dyn.sats]
//
stadef
Option = Option_t0ype_bool_type
typedef
Option (a:t0p) = [b:bool] Option(a, b)
#endif

(* ****** ****** *)

exception NotSomeExn of ()
(*
fun
NotSomeExn
  ():<> exn = "mac#%NotSomeExn_make"
fun
isNotSomeExn
  (x: !exn):<> bool = "mac#%isNotSomeExn"
macdef
ifNotSomeExn
  {tres}(exn, body) =
(
let val x = ,(exn) in
(
if isNotSomeExn(x)
  then
    let prval () = __vfree_exn (x) in ,(body) end
  else $raise (x)
) : tres // end of [if]
end (* end of [let] *)
) // end of [ifNotSomeExn]
*)

(* ****** ****** *)
//
castfn
Option_cast
  {a:t0p}{b:bool}
(
  opt: Option(INV(a), b)
) :<> Option(a, b) // end-of-fun
//
(* ****** ****** *)
//
castfn
Option_vt2t
  {a:t0p}{b:bool}
(
  opt: Option_vt(INV(a), b)
) :<> Option(a, b) // end-of-fun
castfn
Option_of_Option_vt
  {a:t0p}{b:bool}
(
  opt: Option_vt(INV(a), b)
) :<> Option(a, b) // end-of-fun
//
(* ****** ****** *)
//
fun{a:t0p}
Option_some
  (x0: a):<> Option(a, true)
//
fun{a:t0p}
Option_none
  ((*void*)):<> Option(a, false)
//
(* ****** ****** *)
//
fun{}
Option2bool
  {a:t0p}{b:bool}
  (opt: Option(a, b)):<> Bool(b)
//
(* ****** ****** *)

fun{}
Option_is_some
  {a:t0p}{b:bool}
  (opt: Option(a, b)):<> Bool(b)

fun{}
Option_is_none
  {a:t0p}{b:bool}
  (opt: Option(a, b)):<> Bool(~b)

(* ****** ****** *)
//
fun{a:t0p}
Option_unsome
  (Option(INV(a), true)):<> (a)
//
fun{a:t0p}
Option_unsome_exn
  (opt: Option_1(INV(a))):<!exn> (a)
//
(* ****** ****** *)
//
fun{a:t0p}
Option_equal
(
  opt1: Option_1(a), opt2: Option_1(a)
) :<> bool // end of [Option_equal]
//
fun{a:t0p}
Option_equal$eqfn(x1: a, x2: a):<> bool
//
(* ****** ****** *)
//
fun
{a:t0p}
print_Option(opt: Option_1(INV(a))): void
fun
{a:t0p}
prerr_Option(opt: Option_1(INV(a))): void
fun
{a:t0p}
fprint_Option(FILEref, Option_1(INV(a))): void
//
(* ****** ****** *)
//
// overloading for certain symbols
//
(* ****** ****** *)

overload = with Option_equal

(* ****** ****** *)
//
overload unsome with Option_unsome
//
overload iseqz with Option_is_none
overload isneqz with Option_is_some
//
overload print with print_Option of 0
overload prerr with prerr_Option of 0
overload fprint with fprint_Option of 0
//
(* ****** ****** *)

(* end of [Option.sats] *)
