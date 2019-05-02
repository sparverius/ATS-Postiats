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
** $PATSHOME/prelude/DATS/CODEGEN/gprint.atxt
** Time of generation: Wed Oct 10 21:08:53 2018
*)

(* ****** ****** *)

(* Author: Hongwei Xi *)
(* Authoremail: hwxi AT cs DOT bu DOT edu *)
(* Start time: August, 2012 *)

(* ****** ****** *)

implement
{}(*tmp*)
gprint$out() = stdout_ref

(* ****** ****** *)

implement
{}(*tmp*)
gprint_flush() =
fileref_flush(gprint$out<>())

(* ****** ****** *)

implement
{}(*tmp*)
gprint_newline() = let
//
val
out = gprint$out<>() in fprint_newline(out)
//
end // end of [gprint_newline]

(* ****** ****** *)

implement
{a}(*tmp*)
gprint_val(x) = let
//
val
out = gprint$out<>() in fprint_val<a>(out, x)
//
end // end of [gprint_val]

(* ****** ****** *)

implement
{a}(*tmp*)
gprint_ref(x) = let
//
val
out = gprint$out<>() in fprint_ref<a>(out, x)
//
end // end of [gprint_ref]

(* ****** ****** *)
//
implement
{}(*tmp*)
gprint_int(x) =
  fprint_val<int>(gprint$out<>(), x)
implement
{}(*tmp*)
gprint_bool(x) =
  fprint_val<bool> (gprint$out<>(), x)
implement
{}(*tmp*)
gprint_char(x) =
  fprint_val<char>(gprint$out<>(), x)
implement
{}(*tmp*)
gprint_float(x) =
  fprint_val<float>(gprint$out<>(), x)
implement
{}(*tmp*)
gprint_double(x) =
  fprint_val<double>(gprint$out<>(), x)
implement
{}(*tmp*)
gprint_string(x) =
  fprint_val<string>(gprint$out<>(), x)
//
implement
gprint_val<int>(x) = gprint_int(x)
implement
gprint_val<char>(x) = gprint_char(x)
implement
gprint_val<float>(x) = gprint_float(x)
implement
gprint_val<double>(x) = gprint_double(x)
implement
gprint_val<string>(x) = gprint_string(x)
//
(* ****** ****** *)
//
implement
{}(*tmp*)
gprint_List$beg() = gprint_string "("
implement
{}(*tmp*)
gprint_List$end() = gprint_string ")"
implement
{}(*tmp*)
gprint_List$sep() = gprint_string ", "
//
(* ****** ****** *)
//
implement
{a}(*tmp*)
gprint_List
  (xs) = let
//
typedef tenv = int
//
implement
List_foreach$fwork<a><tenv>
  (x, env) = let
  val () =
  if env > 0
    then gprint_List$sep<>()
  // end of [if]
  val () = env := succ (env)
in
  gprint_val<a>(x)
end // end of [List_foreach$fwork]
//
var env: tenv = 0
val () = gprint_List$beg<>()
val () = List_foreach_env<a><tenv>(xs, env)
val () = gprint_List$end<>()
//
in
  // nothing
end // end of [gprint_List]
//
implement
(a)(*tmp*)
gprint_val<List_1(a)>(xs) = gprint_List<a>(xs)
//
(* ****** ****** *)
//
implement
{}(*tmp*)
gprint_ListList$beg1() = gprint_string "("
implement
{}(*tmp*)
gprint_ListList$end1() = gprint_string ")"
implement
{}(*tmp*)
gprint_ListList$sep1() = gprint_string ", "
//
implement
{}(*tmp*)
gprint_ListList$beg2() = gprint_string "("
implement
{}(*tmp*)
gprint_ListList$end2() = gprint_string ")"
implement
{}(*tmp*)
gprint_ListList$sep2() = gprint_string ", "
//
(* ****** ****** *)
//
implement
{a}(*tmp*)
gprint_ListList
  (xss) = let
//
typedef xs = List_1(a)
//
implement
gprint_val<xs>(xs) = let
//
implement
gprint_List$beg<>() =
  gprint_ListList$beg2<>()
implement
gprint_List$end<>() =
  gprint_ListList$end2<>()
implement
gprint_List$sep<>() =
  gprint_ListList$sep2<>()
//
in
  gprint_List<a>(xs)
end // end of [gprint_val]
//
implement
gprint_List$beg<>() =
  gprint_ListList$beg1<>()
implement
gprint_List$end<>() =
  gprint_ListList$end1<>()
implement
gprint_List$sep<>() =
  gprint_ListList$sep1<>()
//
in
  gprint_List<xs>(xss)
end // end of [gprint_ListList]
//
(* ****** ****** *)
//
implement
{}(*tmp*)
gprint_array$beg() = gprint_string "("
implement
{}(*tmp*)
gprint_array$end() = gprint_string ")"
implement
{}(*tmp*)
gprint_array$sep() = gprint_string ", "
//
(* ****** ****** *)

implement
{a}(*tmp*)
gprint_array
  (A, n) = () where
{
//
typedef tenv = size_t
//
implement
(env)(*tmp*)
array_iforeach$fwork<a><env>
  (i, x, env) =
  gprint_ref<a>(x) where
{
  val () =
  if i > 0
    then gprint_array$sep<>()
  // end of [if]
} (* array_iforeach$fwork *)
//
var env: void = ()
//
val () = gprint_array$beg<>()
val
_(*asz*) = array_iforeach<a>(A, n)
val () = gprint_array$end<>()
//
} (* end of [gprint_array] *)

(* ****** ****** *)

implement
{a}(*tmp*)
gprint_arrayptr
  (A, n) = () where
{
//
val p = ptrcast(A)
//
prval pf = arrayptr_takeout(A)
//
val () = gprint_array<a>(!p, n)
//
prval () = arrayptr_addback{a}(pf | A)
//
} (* end of [gprint_arrayptr] *)

(* ****** ****** *)

implement
{a}(*tmp*)
gprint_arrayref
  (A, n) = let
//
val (vbox pf | p) =
  arrayref_get_viewptr(A)
//
in
  $effmask_ref(gprint_array<a>(!p, n))
end // end of [gprint_arrayref]

(* ****** ****** *)

implement
{a}(*tmp*)
gprint_arrszref
  (ASZ) = () where {
//
var n: size_t
val A =
  arrszref_get_refsize<>(ASZ, n)
//
val () = gprint_arrayref<a>(A, n)
//
} (* end of [gprint_arrszref] *)

(* ****** ****** *)

(* end of [gprint.dats] *)
