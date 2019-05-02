(* ****** ****** *)
(*
** For writing ATS code
** that translates into JavaScript
*)
(* ****** ****** *)
//
// HX-2014-10:
// prefix for external names
//
#define
ATS_EXTERN_PREFIX "ats2jspre_"
//
(* ****** ****** *)
//
#define
LIBATSCC_targetloc
"$PATSHOME\
/contrib/libatscc/ATS2-0.3.2"
//
#staload "./../basics_js.sats"
//
#include "{$LIBATSCC}/SATS/matrixref.sats"
//
(* ****** ****** *)
//
fun
matrixref_uninitized
  {a:vt0p}
  {m,n:nat}
  ( nrow: Int(m)
  , ncol: Int(n) ) : matrixref(a?, m, n) = "mac#%"
//
(* ****** ****** *)

(* end of [matrixref.sats] *)
