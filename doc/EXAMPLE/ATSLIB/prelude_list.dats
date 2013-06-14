(*
** for testing [prelude/list]
*)

(* ****** ****** *)
//
#include
"share/atspre_staload_tmpdef.hats"
//
(* ****** ****** *)

val () =
{
val x0 = 0
val x1 = 1
val xs = nil{int}()
val xs = cons{int}(x0, cons{int}(x1, xs))
val+cons (x, xs) = xs
val () = assertloc (x = x0)
val+cons (x, xs) = xs
val () = assertloc (x = x1)
val+nil () = xs
} (* end of [val] *)

(* ****** ****** *)

implement main0 () = ()

(* ****** ****** *)

(* end of [prelude_list.dats] *)
