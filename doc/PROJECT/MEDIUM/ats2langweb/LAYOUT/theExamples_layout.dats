(*
** For
** atslangweb_Examples
*)

(* ****** ****** *)

#include "./mylayout.dats"

(* ****** ****** *)

val () =
thePageLeft.content(
"\
<?php\n\
include './thePageLeft/Examples.php';\n\
?>\n\
") (* end of [val] *)

(* ****** ****** *)

val () =
thePageRHeaderTop.content
("\
<?php\n\
include './thePageRHeaderTop/Home.php';\n\
?>\n\
") (* end of [val] *)

val () =
thePageRHeaderSep.content
("\
<?php\n\
include './thePageRHeaderSep/Examples.php';\n\
?>\n\
") (* end of [val] *)

(* ****** ****** *)

val () =
thePageRBodyLHeader.content
("\
<?php\n\
include './thePageRBodyLHeader/Examples.php';\n\
?>\n\
") (* end of [val] *)

val () =
thePageRBodyLContent.content
("\
<?php\n\
include './thePageRBodyLContent/Examples.php';\n\
?>\n\
") (* end of [val] *)

(* ****** ****** *)

val () =
thePageRBodyRight.content
("\
<?php include './thePageRBodyRight/Examples.php'; ?>\n\
") (* end of [val] *)

(* ****** ****** *)

implement
main0 () =
{
//
val out = stdout_ref
//
val () =
  fprint_webox_html_all (out, theBodyProp)
//
} (* end of [main0] *)

(* ****** ****** *)

(* end of [theExamples_layout.dats] *)