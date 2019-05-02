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
** $PATSHOME/prelude/SATS/CODEGEN/bool.atxt
** Time of generation: Fri Nov 30 08:45:19 2018
*)

(* ****** ****** *)

(* Author: Hongwei Xi *)
(* Authoremail: hwxi AT cs DOT bu DOT edu *)
(* Start time: September, 2011 *)

(* ****** ****** *)
//
castfn g0ofg1_bool{b:bool} (x: Bool(b)):<> bool
castfn g1ofg0_bool (x: bool):<> [b: bool] Bool(b)
//
overload g0ofg1 with g0ofg1_bool // index-erasing
overload g1ofg0 with g1ofg0_bool // index-inducing
//
(* ****** ****** *)
//
fun
int2bool0 (i: int):<> bool = "mac#%"
fun
int2Bool
  {i:int} (i: int1 i):<> Bool(i != 0) = "mac#%"
//
symintr int2bool
overload int2bool with int2bool0 of 0
overload int2bool with int2Bool of 10
//
fun
bool2int0 (b: bool):<> natLt(2) = "mac#%"
fun
bool2int1
  {b:bool} (b: Bool b):<> int1(bool2int(b)) = "mac#%"
//
symintr bool2int
overload bool2int with bool2int0 of 0
overload bool2int with bool2int1 of 10
//
(* ****** ****** *)

(*
//
// HX: declared in [prelude/basics_dyn.sats]
//
val true : bool (true) and false : bool (false)
*)

(* ****** ****** *)

(*
** HX-2012-06:
** shortcut version of disjuction and conjuction
** note that these two cannot be declared as functions
*)
macdef || (b1, b2) = (if ,(b1) then true else ,(b2)): bool
macdef && (b1, b2) = (if ,(b1) then ,(b2) else false): bool

(* ****** ****** *)

typedef boolLte (b: bool) = [a: bool | a <= b] Bool (a)
typedef boolGte (b: bool) = [a: bool | a >= b] Bool (a)

(* ****** ****** *)
//
fun
neg_bool0
  (b: bool):<> bool = "mac#%"
//
overload ~ with neg_bool0 of 0
overload not with neg_bool0 of 0
//
(* ****** ****** *)
//
fun
add_bool0_bool0
  (b1: bool, b2: bool):<> bool = "mac#%"
fun
mul_bool0_bool0
  (b1: bool, b2: bool):<> bool = "mac#%"
//
overload + with add_bool0_bool0 of 0
overload * with mul_bool0_bool0 of 0
//
(* ****** ****** *)
//
fun
xor_bool0_bool0
  (b1: bool, b2: bool):<> bool = "mac#%"
//
overload xor with xor_bool0_bool0 of 0
//
(* ****** ****** *)

fun
lt_bool0_bool0
  (b1: bool, b2: bool):<> bool = "mac#%"
overload < with lt_bool0_bool0 of 0
fun
lte_bool0_bool0
  (b1: bool, b2: bool):<> bool = "mac#%"
overload <= with lte_bool0_bool0 of 0

fun
gt_bool0_bool0
  (b1: bool, b2: bool):<> bool = "mac#%"
overload > with gt_bool0_bool0 of 0
fun
gte_bool0_bool0
  (b1: bool, b2: bool):<> bool = "mac#%"
overload >= with gte_bool0_bool0 of 0

fun
eq_bool0_bool0
  (b1: bool, b2: bool):<> bool = "mac#%"
overload = with eq_bool0_bool0 of 0
fun
neq_bool0_bool0
  (b1: bool, b2: bool):<> bool = "mac#%"
overload != with neq_bool0_bool0 of 0
overload <> with neq_bool0_bool0 of 0

(* ****** ****** *)

fun compare_bool0_bool0
  (b1: bool, b2: bool):<> Sgn = "mac#%"
overload compare with compare_bool0_bool0

(* ****** ****** *)
//
// HX:
// return is statically allocated
//
fun
bool2string(b: bool):<> string = "mac#%"
//
(* ****** ****** *)
//
fun print_bool (x: bool): void = "mac#%"
fun prerr_bool (x: bool): void = "mac#%"
fun fprint_bool : fprint_type (bool) = "mac#%"
//
overload print with print_bool
overload prerr with prerr_bool
overload fprint with fprint_bool
//
(* ****** ****** *)
//
fun
neg_Bool
  {b:bool}
  (b: Bool b):<> Bool (~b) = "mac#%"
//
overload ~ with neg_Bool of 10
overload not with neg_Bool of 10
//
(* ****** ****** *)

fun
add_bool0_Bool
  {b2:bool}
(
  b1: bool, b2: Bool b2
) :<> [b1:bool] Bool(b1 || b2) = "mac#%"
overload + with add_bool0_Bool of 10

fun
add_Bool_bool0
  {b1:bool}
(
  b1: Bool b1, b2: bool
) :<> [b2:bool] Bool(b1 || b2) = "mac#%"
overload + with add_Bool_bool0 of 10

fun
add_Bool_Bool
  {b1,b2:bool}
  (b1: Bool b1, b2: Bool b2):<> Bool(b1 || b2) = "mac#%"
overload + with add_Bool_Bool of 20

(* ****** ****** *)

fun
mul_bool0_Bool
  {b2:bool}
(
  b1: bool, b2: Bool b2
) :<> [b1:bool] Bool(b1 && b2) = "mac#%"
overload * with mul_bool0_Bool of 10

fun
mul_Bool_bool0
  {b1:bool}
(
  b1: Bool b1, b2: bool
) :<> [b2:bool] Bool(b1 && b2) = "mac#%"
overload * with mul_Bool_bool0 of 10

fun
mul_Bool_Bool
  {b1,b2:bool}
  (b1: Bool b1, b2: Bool b2):<> Bool(b1 && b2) = "mac#%"
overload * with mul_Bool_Bool of 20

(* ****** ****** *)
//
fun
xor_Bool_Bool
  {b1,b2:bool}
  (b1: Bool b1, b2: Bool b2):<> Bool((b1)==(~b2)) = "mac#%"
//
overload xor with xor_Bool_Bool of 20
//
(* ****** ****** *)

//
// (b1 < b2) == (~b1 && b2)
//
fun
lt_Bool_Bool {b1,b2:bool}
  (b1: Bool (b1), b2: Bool (b2)) :<> Bool (b1 < b2) = "mac#%"
overload < with lt_Bool_Bool of 20
//
// (b1 <= b2) == (~b1 || b2)
//
fun
lte_Bool_Bool {b1,b2:bool}
  (b1: Bool (b1), b2: Bool (b2)) :<> Bool (b1 <= b2) = "mac#%"
overload <= with lte_Bool_Bool of 20
//
// (b1 > b2) == (b1 && ~b2)
//
fun
gt_Bool_Bool {b1,b2:bool}
  (b1: Bool (b1), b2: Bool (b2)) :<> Bool (b1 > b2) = "mac#%"
overload > with gt_Bool_Bool of 20
//
// (b1 >= b2) == (b1 || ~b2)
//
fun
gte_Bool_Bool {b1,b2:bool}
  (b1: Bool (b1), b2: Bool (b2)) :<> Bool (b1 >= b2) = "mac#%"
overload >= with gte_Bool_Bool of 20

(* ****** ****** *)

fun
eq_Bool_Bool {b1,b2:bool}
  (b1: Bool (b1), b2: Bool (b2)) :<> Bool (b1 == b2) = "mac#%"
overload = with eq_Bool_Bool of 20
fun
neq_Bool_Bool {b1,b2:bool}
  (b1: Bool (b1), b2: Bool (b2)) :<> Bool (b1 != b2) = "mac#%"
overload != with neq_Bool_Bool of 20
overload <> with neq_Bool_Bool of 20

(* ****** ****** *)

fun
compare_Bool_Bool
  {b1,b2:bool} // HX: this one is a function
(
 b1: Bool b1, b2: Bool b2
) :<> int1 (bool2int(b1) - bool2int(b2)) = "mac#%"
overload compare with compare_Bool_Bool of 20

(* ****** ****** *)

(* end of [bool.sats] *)
