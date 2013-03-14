(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-20?? Hongwei Xi, ATS Trustful Software, Inc.
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
//
// Author: Hongwei Xi (gmhwxi AT gmail DOT com)
// Start Time: October, 2012
//
(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"
staload _(*anon*) = "prelude/DATS/unsafe.dats"

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload
GLOB = "./pats_global.sats"

(* ****** ****** *)
//
staload
S2E = "./pats_staexp2.sats"
staload
D2E = "./pats_dynexp2.sats"
//
typedef d2cst = $D2E.d2cst
typedef d2cstlst = $D2E.d2cstlst
typedef d2cstopt = $D2E.d2cstopt
//
(* ****** ****** *)

staload "./pats_histaexp.sats"
staload "./pats_hidynexp.sats"

(* ****** ****** *)

staload "./pats_ccomp.sats"

(* ****** ****** *)

implement
emit_ats_ccomp_header (out) = let
  val () = emit_text (out, "/*\n")
  val () = emit_text (out, "** include runtime header files\n")
  val () = emit_text (out, "*/\n")
  val () = emit_text (out, "#ifndef _ATS_CCOMP_HEADER_NONE\n")
  val () = emit_text (out, "#include \"pats_ccomp_config.h\"\n")
  val () = emit_text (out, "#include \"pats_ccomp_basics.h\"\n")
  val () = emit_text (out, "#include \"pats_ccomp_typedefs.h\"\n")
  val () = emit_text (out, "#include \"pats_ccomp_instrset.h\"\n")
  val () = emit_text (out, "#include \"pats_ccomp_exception.h\"\n")
  val () = emit_text (out, "#include \"pats_ccomp_memalloc.h\"\n")
  val () = emit_text (out, "#endif /* _ATS_CCOMP_HEADER_NONE */\n")
  val () = emit_newline (out)
in
  emit_newline (out)
end // end of [emit_ats_ccomp_header]

(* ****** ****** *)

implement
emit_ats_ccomp_prelude (out) = let
//
val () = emit_text (out, "/*\n")
val () = emit_text (out, "** include prelude cats files\n")
val () = emit_text (out, "*/\n")
//
val () = emit_text (out, "#ifndef _ATS_CCOMP_PRELUDE_NONE\n")
//
// HX: primary prelude cats files
//
val () = emit_text (out, "//\n")
val () = emit_text (out, "#include \"prelude/CATS/basics.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/integer.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/memory.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/pointer.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/bool.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/char.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/float.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/string.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/strptr.cats\"\n")
//
val () = emit_text (out, "//\n")
val () = emit_text (out, "#include \"prelude/CATS/filebas.cats\"\n")
//
// HX: secondary prelude cats files
//
val () = emit_text (out, "//\n")
val () = emit_text (out, "#include \"prelude/CATS/list.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/option.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/array.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/arrayptr.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/arrayref.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/matrix.cats\"\n")
//
val () = emit_text (out, "//\n")
val () = emit_text (out, "#endif /* _ATS_CCOMP_PRELUDE_NONE */\n")
//
in
  emit_newline (out)
end // end of [emit_ats_ccomp_prelude]

(* ****** ****** *)

extern
fun emit_funlablst_ptype
  (out: FILEref, fls: funlablst): void
implement
emit_funlablst_ptype (out, fls) = let
//
fun loop (
  out: FILEref, fls: funlablst, i: int
) : void = let
in
//
case+ fls of
| list_cons
    (fl, fls) => let
    val-Some (fent) =
      funlab_get_funent (fl)
    // end of [val]
    val () = emit_funent_ptype (out, fent)
  in
    loop (out, fls, i+1)
  end // end of [list_cons]
| list_nil () => ()
//
end // end of [loop]
//
in
  loop (out, fls, 0)
end // end of [emit_funlablst_ptype]

(* ****** ****** *)

extern
fun emit_funlablst_implmnt
  (out: FILEref, fls: funlablst): void
implement
emit_funlablst_implmnt
  (out, fls) = let
//
fun loop (
  out: FILEref, fls: funlablst, i: int
) : void = let
in
//
case+ fls of
| list_cons
    (fl, fls) => let
    val tmpknd = funlab_get_tmpknd (fl)
    val-Some (fent) = funlab_get_funent (fl)
    val () =
      if tmpknd > 0 then fprint_string (out, "#if(0)\n")
    // end of [val]
    val ((*void*)) = emit_funent_implmnt (out, fent)
    val () =
      if tmpknd > 0 then fprint_string (out, "#endif // end of [TEMPLATE]\n")
    // end of [val]
  in
    loop (out, fls, i+1)
  end // end of [list_cons]
| list_nil () => ()
//
end // end of [loop]
//
in
  loop (out, fls, 0)
end // end of [emit_funlablst_implmnt]

(* ****** ****** *)

implement
emit_the_tmpdeclst
  (out) = let
  val p =
    the_toplevel_getref_tmpvarlst ()
  // end of [val]
  val tmplst = $UN.ptrget<tmpvarlst> (p)
in
  emit_tmpdeclst (out, tmplst)
end // end of [emit_the_tmpdeclst]

(* ****** ****** *)

extern fun the_dyncstlst_get2 (): d2cstlst
extern fun the_dyncstlst_set2 (xs: d2cstlst): void

local

val the_d2cstlst = ref<Option(d2cstlst)> (None)

in (* in of [local] *)

implement
the_dyncstlst_get2
  ((*void*)) = let
//
val opt = !the_d2cstlst
//
in
//
case+ opt of
| Some (xs) => xs
| None (  ) => let
    val xs = the_dyncstlst_get ()
    val () = !the_d2cstlst := Some (xs)
  in
    xs
  end // end of [None]
//
end // end of [the_dyncstlst_get2]

implement
the_dyncstlst_set2 (xs) = !the_d2cstlst := Some (xs)

end // end of [local]

(* ****** ****** *)

implement
emit_the_dyncstlst_exdec (out) = let
//
val () = emit_text (out, "/*\n")
val () = emit_text (out, "dyncstlst-declaration(beg)\n")
val () = emit_text (out, "*/\n")
//
val d2cs = the_dyncstlst_get2 ()
val () = emit_d2cstlst_exdec (out, d2cs)
//
val () = emit_text (out, "/*\n")
val () = emit_text (out, "dyncstlst-declaration(end)\n")
val () = emit_text (out, "*/\n")
//
in
  // nothing
end // end of [emit_the_dyncstlst_exdec]

(* ****** ****** *)

extern fun the_extcodelst_get2 (): hideclist
extern fun the_extcodelst_set2 (xs: hideclist): void

local

val the_extlst = ref<Option(hideclist)> (None)

in (* in of [local] *)

implement
the_extcodelst_get2
  ((*void*)) = let
//
val opt = !the_extlst
//
in
//
case+ opt of
| Some (xs) => xs
| None (  ) => let
    val xs = the_extcodelst_get ()
    val () = !the_extlst := Some (xs)
  in
    xs
  end // end of [None]
//
end // end of [the_extcodelst_get2]

implement
the_extcodelst_set2 (xs) = !the_extlst := Some (xs)

end // end of [local]

(* ****** ****** *)

extern fun the_funlablst_get2 (): funlablst

local

val the_flablst = ref<Option(funlablst)> (None)

in (* in of [local] *)

implement
the_funlablst_get2
  ((*void*)) = let
//
val opt = !the_flablst
//
in
//
case+ opt of
| Some (xs) => xs
| None (  ) => let
    val xs = the_funlablst_get ()
    val () = !the_flablst := Some (xs)
  in
    xs
  end // end of [None]
//
end // end of [the_fublablst_get2]

end // end of [local]

(* ****** ****** *)

implement
emit_the_funlablst
  (out) = let
  val fls0 = the_funlablst_get2 ()
  val () = emit_funlablst_ptype (out, fls0)
  val () = emit_funlablst_implmnt (out, fls0)
in
  // nothing
end // end of [emit_the_funlablst]

(* ****** ****** *)

implement
emit_the_primdeclst
  (out) = let
  val p =
    the_toplevel_getref_primdeclst ()
  // end of [val]
  val pmdlst = $UN.ptrget<primdeclst> (p)
in
  emit_primdeclst (out, pmdlst)
end // end of [emit_the_primdeclst]

(* ****** ****** *)

(*
#define MAIN_NONE 0
#define MAIN_VOID 1 // main()
#define MAIN_ARGC_ARGV 2 // main(argc, argv)
#define MAIN_ARGC_ARGV_ENVP 3 // main(argc, argv, envp)
*)

(* ****** ****** *)

extern
fun the_mainats_initize (): void
extern
fun the_mainats_d2copt_get (): d2cstopt

(* ****** ****** *)

local

val the_mainats_d2copt = ref<d2cstopt> (None)

in (* in of [local] *)

implement
the_mainats_initize () = let
//
fun loop (fls: funlablst): void = let
in
//
case+ fls of
| list_cons
    (fl, fls) => let
    val opt = funlab_get_d2copt (fl)
    val () = (
      case+ opt of
      | Some (d2c) =>
          if $D2E.d2cst_is_mainats (d2c) then !the_mainats_d2copt := opt
      | None () => ()
    ) : void // end of [val]
  in
    loop (fls)        
  end // end of [list_cons]
| list_nil () => ()
//
end // end of [loop]
//
in
  loop (the_funlablst_get2 ())
end // end of [the_mainats_initize]

implement the_mainats_d2copt_get () = !the_mainats_d2copt

end // end of [local]

(* ****** ****** *)

extern
fun the_dynloadflag_get (): int

implement
the_dynloadflag_get () = let
//
val the_mainatsflag = $GLOB.the_MAINATSFLAG_get ()
//
in
//
if the_mainatsflag = 0 then let
  val opt = the_mainats_d2copt_get ()
in
//
case+ opt of
| Some _ => 0 | None () => $GLOB.the_DYNLOADFLAG_get ()
//
end else 0 // HX: mainatsflag overrules dynloadflag
//
end // end of [the_dynloadflag_get]

(* ****** ****** *)

extern
fun emit_main_arglst_err
  (out: FILEref, arty: int): void
implement
emit_main_arglst_err
  (out, arty) = let
  val () = if arty >= 1 then emit_text (out, "argc")
  val () = if arty >= 2 then emit_text (out, ", argv")
  val () = if arty >= 3 then emit_text (out, ", envp")
  val () = (
    if arty <= 0
      then emit_text (out, "err") else emit_text (out, ", err")
    // end of [if]
  ) : void // end of [val]
in
  // nothing
end // end of [emit_main_arglst_err]

(* ****** ****** *)

extern
fun emit_dynload
  (out: FILEref, infil: $FIL.filename): void
implement
emit_dynload
  (out, infil) =
{
  val () = emit_filename (out, infil)
  val () = emit_text (out, "__dynload")
}

extern
fun emit_dynloadflag
  (out: FILEref, infil: $FIL.filename): void
implement
emit_dynloadflag
  (out, infil) =
{
  val () = emit_filename (out, infil)
  val () = emit_text (out, "__dynloadflag")
}

(* ****** ****** *)

local

staload _ = "libc/SATS/fcntl.sats"
staload _ = "libc/SATS/stdio.sats"
staload _ = "libc/SATS/stdlib.sats"
staload _ = "libc/SATS/unistd.sats"

staload "./pats_utils.sats"
staload _(*anon*) = "./pats_utils.dats"

fun
the_tmpdeclst_stringize (
) =
  tostring_fprint<int> (
  "postiats_tmpdeclst_", lam (out, _) => emit_the_tmpdeclst (out), 0
) // end of [the_tmpdeclst_stringize]

fun
the_primdeclst_stringize (
) =
  tostring_fprint<int> (
  "postiats_primdeclst_", lam (out, _) => emit_the_primdeclst (out), 0
) // end of [the_funlablst_stringize]

fun
the_funlablst_stringize (
) =
  tostring_fprint<int> (
  "postiats_funlablst_", lam (out, _) => emit_the_funlablst (out), 0
) // end of [the_funlablst_stringize]

fun aux_staload
  (out: FILEref): void = let
//
fun loop (
  out: FILEref, xs: hideclist
) : void = let
in
//
case+ xs of
| list_cons
    (x, xs) => let
    val () =
      emit_staload (out, x) in loop (out, xs)
    // end of [val]
  end // end of [list_cons]
| list_nil () => ()
//
end // end of [loop]
//
val () = emit_text (out, "/*\n")
val () = emit_text (out, "staload-prologues(beg)\n")
val () = emit_text (out, "*/\n")
//
val () = loop (out, the_staloadlst_get ())
//
val () = emit_text (out, "/*\n")
val () = emit_text (out, "staload-prologues(end)\n")
val () = emit_text (out, "*/\n")
//
in
  // nothing
end // end of [aux_staload]

fun
aux_dynload (
  out: FILEref
, infil: $FIL.filename, fbody: string
) : void = let
//
val flag = the_dynloadflag_get ()
//
val () = emit_text (out, "\n/*\n")
val () = emit_text (out, "** for initialization(dynloading)")
val () = emit_text (out, "\n*/\n")
//
val () = emit_text (out, "atsvoid_t0ype\n")
val () = emit_dynload (out, infil)
val () = emit_text (out, "()\n{\n")
val () = if flag = 0 then emit_text (out, "ATSdynload0(\n")
val () = if flag > 0 then emit_text (out, "ATSdynload1(\n")
val () = emit_dynloadflag (out, infil)
val () = emit_text (out, "\n) ;\n")
val () = emit_text (out, "if (\n")
val () = emit_text (out, "ATSCKiseqz(\n")
val () = emit_dynloadflag (out, infil)
val () = emit_text (out, "\n)\n) {\n")
val () = emit_dynloadflag (out, infil)
val () = emit_text (out, " = 1 ;\n")
val () = emit_text (out, fbody)
val () = emit_text (out, "} /* end of [if] */\n")
val () = emit_text (out, "ATSreturn_void() ;\n")
val () = emit_text (out, "} /* end of [*_dynload] */\n")
//
in
  // nothing
end // end of [aux_dynload]

fun
aux_main (
  out: FILEref
, infil: $FIL.filename
, d2cmain: d2cst
) : void = let
//
val () = emit_text (out, "\n/*\n")
val () = emit_text (out, "** the [main] implementation")
val () = emit_text (out, "\n*/\n")
//
val () = emit_text (out, "int\n")
val () = emit_text (out, "main\n")
val () = emit_text (out, "(\n")
val () = emit_text (out, "int argc, char **argv, char **envp")
val () = emit_text (out, "\n) {\n")
val () = emit_text (out, "int err = 0 ;\n")
val () = {
  val () = emit_filename (out, infil)
  val () = emit_text (out, "__dynload() ;\n")
} (* end of [val] *)
//
val arty = let
  val ns = $D2E.d2cst_get_artylst (d2cmain)
in
  case+ ns of
  | list_cons (n, _) => n | list_nil () => 0
end : int // end of [val]
//
val () = emit_text (out, "ATS")
val () = emit_d2cst (out, d2cmain)
val () = emit_lparen (out)
val () = emit_main_arglst_err (out, arty)
val () = emit_rparen (out)
val () = emit_text (out, " ;\n")
//
val () = emit_text (out, "ATSreturn(err) ;\n")
val () = emit_text (out, "} /* end of [main] */")
val () = emit_newline (out)
//
in
  // nothing
end // end of [aux_main]

fun
aux_main_ifopt (
  out: FILEref, infil: $FIL.filename
) : void = let
//
val opt = the_mainats_d2copt_get ()
//
in
//
case+ opt of
| Some (d2c) => aux_main (out, infil, d2c)
| None () => ()
//
end // end of [aux_main_ifopt]

#define DYNBEG 1
#define DYNMID 10
#define DYNEND 99

fun
aux_extcodelst_if (
  out: FILEref, test: (int) -> bool
) : void = let
//
fun loop (
  out: FILEref, test: (int) -> bool, xs: hideclist
) : hideclist = let
in
//
case+ xs of
| list_cons
    (x, xs1) => let
    val-HIDextcode (knd, pos, _) = x.hidecl_node
  in
    if test (pos) then let
      val () = emit_extcode (out, x) in loop (out, test, xs1)
    end else xs // end of [if]
  end // end of [if]
| list_nil () => list_nil ()
//
end // end of [loop]
//
val xs = the_extcodelst_get2 ()
val xs2 = loop (out, test, xs)
val () = the_extcodelst_set2 (xs2)
//
in
  // nothing
end // end of [aux_extcodelst_if]

fun
aux_saspdeclst
  (out: FILEref): void = let
//
fun loop (
  out: FILEref, xs: hideclist
) : void = let
in
//
case+ xs of
| list_cons
    (x, xs) => let
    val () = emit_saspdec (out, x) in loop (out, xs)
  end // end of [list_cons]
| list_nil () => ()
//
end // end of [loop]
//
in
  loop (out, the_saspdeclst_get ())
end // end of [aux_saspdeclst]

in (* in of [local] *)

implement
ccomp_main (
  out, flag, infil, hids
) = let
//
val () = println! ("ccomp_main: enter")
//
val () = emit_time_stamp (out)
val () = emit_ats_ccomp_header (out)
val () = emit_ats_ccomp_prelude (out)
//
val () = let
  val pmds = hideclist_ccomp0 (hids)
  val p_pmds = the_toplevel_getref_primdeclst ()
  val () = $UN.ptrset<primdeclst> (p_pmds, pmds)
  val tmps =
    primdeclst_get_tmpvarset (pmds)
  val tmps =
    tmpvarset_vt_listize_free (tmps)
  val tmps = list_of_list_vt (tmps)
  val p_tmps = the_toplevel_getref_tmpvarlst ()
  val () = $UN.ptrset<tmpvarlst> (p_tmps, tmps)
in
  // nothing
end // end of [val]
//
#if(0)
val () = emit_the_tmpdeclst (out)
val () = emit_the_primdeclst (out)
val () = emit_the_funlablst (out)
#endif // end of [#if(0)]
//
val the_tmpdeclst_rep = the_tmpdeclst_stringize ()
val the_primdeclst_rep = the_primdeclst_stringize ()
val the_funlablst_rep = the_funlablst_stringize ()
//
val () = aux_staload (out)
//
val (
) = aux_extcodelst_if (out, lam (pos) => pos = DYNBEG)
//
val () = emit_the_typedeflst (out)
//
val () = emit_the_dyncstlst_exdec (out)
//
val (
) = aux_extcodelst_if (out, lam (pos) => pos < DYNMID)
//
val () =
  fprint_strptr (out, the_tmpdeclst_rep)
val () = strptr_free (the_tmpdeclst_rep)
//
val (
) = aux_extcodelst_if (out, lam (pos) => pos <= DYNMID)
//
val () =
  fprint_strptr (out, the_funlablst_rep)
val () = strptr_free (the_funlablst_rep)
//
val ( // HX: the call must be made before
) = the_mainats_initize () // aux_dynload is called
//
val () = let
  val fbody =
    $UN.castvwtp1{string}(the_primdeclst_rep)
  // end of [val]
in
  aux_dynload (out, infil, fbody)
end // end of [val]
val () = strptr_free (the_primdeclst_rep)
//
val () = aux_saspdeclst (out)
//
val () = aux_main_ifopt (out, infil)
//
val (
) = aux_extcodelst_if (out, lam (pos) => pos <= DYNEND)
//
val () = println! ("ccomp_main: leave")
//
in
  // nothing
end // end of [ccomp_main]

end // end of [local]

(* ****** ****** *)

(* end of [pats_ccomp_main.dats] *)
