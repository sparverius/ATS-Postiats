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
** $PATSHOME/prelude/DATS/CODEGEN/option_vt.atxt
** Time of generation: Wed Oct 10 21:08:51 2018
*)

(* ****** ****** *)

(* Author: Hongwei Xi *)
(* Authoremail: hwxi AT cs DOT bu DOT edu *)
(* Start time: Feburary, 2012 *)

(* ****** ****** *)

implement{a} Option_vt_some (x) = Some1_vt (x)
implement{a} Option_vt_none ( ) = None1_vt ( )

(* ****** ****** *)

implement
{a}(*tmp*)
Option_vt_make_opt
  (b, x) = (
  if b then let
    prval () = opt_unsome{a}(x) in Some1_vt{a}(x)
  end else let
    prval () = opt_unnone{a}(x) in None1_vt{a}( )
  end // end of [if]
) (* end of [Option_vt_make_opt] *)

(* ****** ****** *)

implement
{}(*tmp*)
Option_vt_is_some
  (opt) = case+ opt of
  | Some1_vt _ => true | None1_vt _ => false
// end of [Option_is_some]

implement{}
Option_vt_is_none
  (opt) = case+ opt of
  | Some1_vt _ => false | None1_vt _ => true
// end of [Option_is_none]

(* ****** ****** *)

implement
{a}(*tmp*)
Option_vt_unsome
  (opt) = x where { val+ ~Some1_vt(x) = opt }
// end of [Option_unsome]

implement
{a}(*tmp*)
Option_vt_unnone
  (opt) = () where { val+ ~None1_vt() = opt }
// end of [Option_unnone]

(* ****** ****** *)

implement
{a}(*tmp*)
Option_vt_free(opt) =
(
case+ opt of ~Some1_vt _ => () | ~None1_vt _ => ()
) // end of [Option_vt_free]

implement
{a}(*tmp*)
Option2bool_vt(opt) =
(
case+ opt of ~Some1_vt _ => true | ~None1_vt _ => false
) // end of [Option2bool_vt]

(* ****** ****** *)

implement
{a}(*tmp*)
fprint_Option_vt
  (out, opt) = let
in
//
case+ opt of
| @Some1_vt (x) => {
    val (
    ) = fprint_string (out, "Some1_vt(")
    val () = fprint_ref<a> (out, x)
    val () = fprint_string (out, ")")
    prval () = fold@ (opt)
  } (* end of [Some1_vt] *)
| None1_vt () => {
    val () = fprint_string (out, "None1_vt()")
  } (* end of [None1_vt] *)
//
end // end of [fprint_Option_vt]

(* ****** ****** *)

(* end of [Option_vt.dats] *)
