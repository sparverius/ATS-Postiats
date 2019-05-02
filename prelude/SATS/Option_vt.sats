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
** $PATSHOME/prelude/SATS/CODEGEN/Option_vt.atxt
** Time of generation: Fri Nov 30 08:45:23 2018
*)

(* ****** ****** *)

(* Author: Hongwei Xi *)
(* Authoremail: hwxi AT cs DOT bu DOT edu *)
(* Start time: February, 2012 *)

(* ****** ****** *)

sortdef vt0p = viewt@ype

(* ****** ****** *)

#if(0)
//
// HX: these decls are available in [basic_dyn.sats]
//
stadef Option_vt = Option_vt0ype_bool_vtype
vtypedef Option_vt (a:vt0p) = [b:bool] Option_vt (a, b)
//
#endif

(* ****** ****** *)

fun{a:vt0p}
Option_vt_some (x: a):<!wrt> Option_vt (a, true)
fun{a:vt0p}
Option_vt_none ((*void*)):<!wrt> Option_vt (a, false)

(* ****** ****** *)

fun{
a:vt0p
} Option_vt_make_opt
  {b:bool}
(
  b: Bool(b)
, x: &opt (INV(a), b) >> a?
) :<!wrt> Option_vt(a, b) // end-of-fun

(* ****** ****** *)

fun{}
Option_vt_is_some
  {a:vt0p}{b:bool}
  (opt: !Option_vt(INV(a), b)):<> Bool(b)
// end of [Option_vt_is_some]
fun{}
Option_vt_is_none
  {a:vt0p}{b:bool}
  (opt: !Option_vt(INV(a), b)):<> Bool(~b)
// end of [Option_vt_is_none]

(* ****** ****** *)
//
fun
{a:vt0p}
Option_vt_unsome
(opt: Option_vt(INV(a), true)):<!wrt> (a)
//
fun
{a:vt0p}
Option_vt_unnone
(opt: Option_vt(INV(a), false)):<!wrt> void
//
(* ****** ****** *)
//
fun{a:t0p}
Option_vt_free
  (opt: Option_vt_1(INV(a))):<!wrt> void
fun{a:t0p}
Option2bool_vt
  {b:bool}
  (opt: Option_vt(INV(a), b)):<!wrt> Bool(b)
//
(* ****** ****** *)
//
fun{a:vt0p}
fprint_Option_vt{b:bool}
(out: FILEref, opt: !Option_vt(INV(a), b)): void
//
overload fprint with fprint_Option_vt
//
(* ****** ****** *)
//
// overloading for certain symbols
//
(* ****** ****** *)

overload iseqz with Option_vt_is_none
overload isneqz with Option_vt_is_some

(* ****** ****** *)

(* end of [Option_vt.sats] *)
