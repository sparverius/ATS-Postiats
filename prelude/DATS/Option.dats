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
** $PATSHOME/prelude/DATS/CODEGEN/option.atxt
** Time of generation: Wed Oct 10 21:08:51 2018
*)

(* ****** ****** *)

implement{a}
Option_some(x) = Some1(x)
implement{a}
Option_none( ) = None1(*void*)

(* ****** ****** *)

implement
{}(*tmp*)
Option2bool
  (opt) =
(
case+ opt of
| Some1 _ => true | None1 _ => false
) (* end of [Option2bool] *)

(* ****** ****** *)

implement
{}(*tmp*)
Option_is_some
  (opt) =
(
case+ opt of
| Some1 _ => true | None1 _ => false
) (* end of [Option_is_some] *)

implement
{}(*tmp*)
Option_is_none
  (opt) =
(
case+ opt of
| Some1 _ => false | None1 _ => true
) (* end of [Option_is_none] *)

(* ****** ****** *)
//
implement
{a}(*tmp*)
Option_unsome
  (opt) =
(
  x0
) where { val+Some1(x0) = opt }
//
implement
{a}(*tmp*)
Option_unsome_exn
  (opt) =
(
case+ opt of
| Some1 x0 => x0
| None1 () => $raise NotSomeExn()
) (* Option_unsome_exn *)
//
(* ****** ****** *)

implement
{a}(*tmp*)
Option_equal
  (opt1, opt2) =
(
//
case+ opt1 of
| None1 () =>
  (
    case+ opt1 of
    | None1() => true | Some1 _ => false
  ) (* end of [None1] *)
| Some1 x1 =>
  (
    case+ opt2 of
    | None1() => false
    | Some1(x2) => Option_equal$eqfn(x1, x2)
  ) (* end of [Some1] *)
//
) (* end of [Option_equal] *)

(* ****** ****** *)
//
implement
{a}(*tmp*)
print_Option(opt) =
fprint_Option<a>(stdout_ref, opt)
implement
{a}(*tmp*)
prerr_Option(opt) =
fprint_Option<a>(stderr_ref, opt)
//
implement
{a}(*tmp*)
fprint_Option
  (out, opt) =
(
//
case+ opt of
| Some1 x => {
    val () =
      fprint_string(out, "Some1(")
    // end of [val]
    val () = fprint_val<a> (out, x)
    val () = fprint_string (out, ")")
  } (* end of [Some1] *)
| None1 _ => fprint_string(out, "None1()")
//
) (* end of [fprint_Option] *)
//
(* ****** ****** *)

(* end of [Option.dats] *)
