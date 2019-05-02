(*
** libatscc-common
*)

(* ****** ****** *)

(*
staload "./../basics.sats"
*)

(* ****** ****** *)
//
macdef
List_sing(x) =
  List_cons(,(x), List_nil)
macdef
List_pair(x1, x2) =
  List_cons(,(x1), List_cons(,(x2), List_nil))
//
(* ****** ****** *)
//
fun{}
List_is_nil
  {a:t0p}{n:int}(List(a, n)): Bool(n==0)
fun{}
List_is_cons
  {a:t0p}{n:int}(List(a, n)): Bool(n > 0)
//
overload iseqz with List_is_nil of 100
overload isneqz with List_is_cons of 100
//
(* ****** ****** *)
//
fun
List_make_elt
  {x:t0p}{n:nat}
  (n: Int n, x: x): List(x, n) = "mac#%"
// end of [list_make_elt]
//
(* ****** ****** *)
//
fun
List_make_intrange_2
  (l: int, r: int): List0(int) = "mac#%"
fun
List_make_intrange_3
  (l: int, r: int, d: int): List0(int) = "mac#%"
//
symintr List_make_intrange
//
overload
List_make_intrange with List_make_intrange_2
overload
List_make_intrange with List_make_intrange_3
//
(* ****** ****** *)
//
fun
{a:t0p}
print_list
  (List_1(INV(a))): void = "mac#%"
fun
{a:t0p}
print_list_sep
  (List_1(INV(a)), sep: string): void = "mac#%"
//
overload print with print_list of 100
//
(* ****** ****** *)
//
fun
List_length
  {a:t0p}{n:int}
  (xs: List(a, n)): Int(n) = "mac#%"
//
overload length with List_length of 100
//
(* ****** ****** *)
//
fun
List_length_gte
  {x:t0p}{n1,n2:int}
  (List(INV(x), n1), Int(n2)): Bool(n1 >= n2) = "mac#%"
fun
List_length_compare
  {x:t0p}{n1,n2:int}
  (List(INV(x), n1), Int(n2)): Int(sgn(n1-n2)) = "mac#%"
//
overload >= with List_length_gte of 100
overload compare with List_length_compare of 100
//
(* ****** ****** *)
//
fun
List_head
{x:t0p}{n:pos}
(List(INV(x), n)):<> (x) = "mac#%"
fun
List_tail
{x:t0p}{n:pos}
(SHR(List(INV(x), n))):<> List(x, n-1) = "mac#%"
//
(* ****** ****** *)
//
fun
List_last
  {a:t0p}{n:pos}
  (xs: List(INV(a), n)): (a) = "mac#%"
//
(* ****** ****** *)
//
fun
List_get_at
  {a:t0p}{n:int}
  (List(INV(a), n), natLt(n)): a = "mac#%"
//
overload [] with List_get_at of 100
//
(* ****** ****** *)
//
fun
List_snoc
  {a:t0p}{n:int}
  (List(INV(a), n), x0: a): List(a, n+1)= "mac#%"
//
fun
List_extend
  {a:t0p}{n:int}
  (List(INV(a), n), x0: a): List(a, n+1)= "mac#%"
//
(* ****** ****** *)
//
fun
List_append
  {a:t0p}{i,j:int}
  (List(INV(a), i), List(a, j)): List(a, i+j)= "mac#%"
//
overload + with List_append of 100 // infix
//
(* ****** ****** *)
//
fun
mul_int_list
  {a:t0p}
  {m,n:int | m >= 0}
  (m: Int(m), xs: List(INV(a), n)): List(a, m*n) = "mac#%"
//
overload * with mul_int_list of 100 // infix
//
(* ****** ****** *)
//
fun
List_reverse
  {a:t0p}{n:int}
  (List(INV(a), n)): List(a, n) = "mac#%"
//
fun
List_reverse_append
  {a:t0p}{i,j:int}
  (List(INV(a), i), List(a, j)): List(a, i+j) = "mac#%"
//
overload reverse with List_reverse of 100
overload revappend with List_reverse_append of 100
//
(* ****** ****** *)
//
fun
List_concat
  {x:t0p}(xss: List_1(List_1(INV(x)))): List0(x) = "mac#%"
//
(* ****** ****** *)
//
fun
List_take
  {a:t0p}
  {n:int}
  {i:nat | i <= n}
  (xs: List(INV(a), n), i: Int(i)): List(a, i) = "mac#%"
fun
List_drop
  {a:t0p}
  {n:int}
  {i:nat | i <= n}
  (xs: List(INV(a), n), i: Int(i)): List(a, n-i) = "mac#%"
//
fun
List_split_at
  {a:t0p}
  {n:int}
  {i:nat | i <= n}
  (List(INV(a), n), Int(i)): $tup(List(a, i), List(a, n-i)) = "mac#%"
//
(* ****** ****** *)
//
fun
List_insert_at
  {a:t0p}
  {n:int}
  {i:nat | i <= n}
  (List(INV(a), n), Int(i), a): List(a, n+1) = "mac#%"
//
fun
List_remove_at
  {a:t0p}
  {n:int}{i:nat | i < n}
  (xs: List(INV(a), n), i: Int(i)): List(a, n-1) = "mac#%"
fun
List_takeout_at
  {a:t0p}
  {n:int}{i:nat | i < n}
  (List(INV(a), n), Int(i)): $tup(a, List(a, n-1)) = "mac#%"
//
(* ****** ****** *)
//
fun
List_exists
  {a:t0p}
(
  xs: List_1(INV(a)), pred: cfun(a, bool)
) : bool = "mac#%" // end-of-function
fun
List_exists_method
  {a:t0p}
(
  xs: List_1(INV(a)))(pred: cfun(a, bool)
) : bool = "mac#%" // end-of-function
//
overload .exists with List_exists_method
//
fun
List_iexists
  {a:t0p}
(
  xs: List_1(INV(a)), pred: cfun(Nat, a, bool)
) : bool = "mac#%" // end of [list_iexists]
fun
List_iexists_method
  {a:t0p}
(
  xs: List_1(INV(a)))(pred: cfun(Nat, a, bool)
) : bool = "mac#%" // end of [list_iexists]
//
overload .iexists with List_iexists_method
//
(* ****** ****** *)
//
fun
List_forall
  {a:t0p}
(
  xs: List_1(INV(a)), pred: cfun(a, bool)
) : bool = "mac#%" // end-of-function
fun
List_forall_method
  {a:t0p}
(
  List_1(INV(a)))(pred: cfun(a, bool)
) : bool = "mac#%" // end-of-function
//
overload .forall with List_forall_method
//
fun
List_iforall
  {a:t0p}
(
  xs: List_1(INV(a)), pred: cfun(Nat, a, bool)
) : bool = "mac#%" // end of [list_iforall]
fun
List_iforall_method
  {a:t0p}
(
  xs: List_1(INV(a)))(pred: cfun(Nat, a, bool)
) : bool = "mac#%" // end of [list_iforall]
//
overload .iforall with List_iforall_method
//
(* ****** ****** *)
//
fun
List_app
  {a:t0p}
(
  xs: List_1(INV(a)), fwork: cfun(a, void)
) : void = "mac#%" // end-of-function
fun
List_foreach
  {a:t0p}
(
  xs: List_1(INV(a))
, fwork: cfun(a, void)
) : void = "mac#%" // end-of-function
//
fun
List_foreach_method
  {a:t0p}
(
  xs: List_1(INV(a)))(fwork: cfun(a, void)
) : void = "mac#%" // end-of-function
//
overload .foreach with List_foreach_method
//
(* ****** ****** *)
//
fun
List_iforeach
  {a:t0p}
(
  xs: List_1(INV(a))
, fwork: cfun(Nat, a, void)
) : void = "mac#%" // end-of-function
fun
List_iforeach_method
  {a:t0p}
(
  xs: List_1(INV(a)))(fwork: cfun(Nat, a, void)
) : void = "mac#%" // end-of-function
//
overload .iforeach with List_iforeach_method
//
(* ****** ****** *)
//
fun
List_rforeach
  {a:t0p}
(
  xs: List_1(INV(a)), fwork: cfun(a, void)
) : void = "mac#%" // end-of-function
fun
List_rforeach_method
  {a:t0p}
(
  xs: List_1(INV(a)))(fwork: cfun(a, void)
) : void = "mac#%" // end-of-function
//
overload .rforeach with List_rforeach_method
//
(* ****** ****** *)
//
fun
List_filter
  {a:t0p}{n:int}
(
  xs: List(INV(a), n), pred: cfun(a, bool)
) : ListLte(a, n) = "mac#%" // end-of-fun
fun
List_filter_method
  {a:t0p}{n:int}
(
  xs: List(INV(a), n))(pred: cfun(a, bool)
) : ListLte(a, n) = "mac#%" // end-of-fun
//
overload .filter with List_filter_method
//
(* ****** ****** *)
//
fun
List_labelize
{x:t0p}{n:int}
(List(INV(x), n)): List($tup(int, x), n) = "mac#%"
// end of [list_labelize]
//
(* ****** ****** *)
//
fun
List_map
  {a:t0p}{b:t0p}{n:int}
(
  xs: List(INV(a), n), fopr: cfun(a, b)
) : List(b, n) = "mac#%" // end-of-function
fun
List_map_method
  {a:t0p}{b:t0p}{n:int}
(
  xs: List(INV(a), n), TYPE(b))(fopr: cfun(a, b)
) : List(b, n) = "mac#%" // end-of-function
//
overload .map with List_map_method // HX: xs.map(TYPE{b})(...)
//
(* ****** ****** *)
//
fun
List_imap
  {a:t0p}{b:t0p}{n:int}
(
  xs: List(INV(a), n), fopr: cfun(Nat, a, b)
) : List(b, n) = "mac#%" // end-of-function
fun
List_imap_method
  {a:t0p}{b:t0p}{n:int}
(
  xs: List(INV(a), n), TYPE(b))(fopr: cfun(Nat, a, b)
) : List(b, n) = "mac#%" // end-of-function
//
overload .imap with List_imap_method // HX: xs.imap(TYPE{b})(...)
//
(* ****** ****** *)
//
fun
List_map2
{a1,a2:t0p}
{b:t0p}{n1,n2:int}
(
  xs1: List(INV(a1), n1)
, xs2: List(INV(a2), n2), fopr: cfun(a1, a2, b)
) : List(b, min(n1,n2)) = "mac#%" // end-of-function
//
(* ****** ****** *)
//
fun
List_foldleft
  {res:vt0p}{a:t0p}
(
  List_1(INV(a)), init: res, fopr: (res, a) -<cloref1> res
) : res = "mac#%" // end of [list_foldleft]
fun
List_foldleft_method
  {res:t@ype}{a:t0p}
(
  xs: List_1(INV(a)), init: res)(fopr: (res, a) -<cloref1> res
) : res = "mac#%" // end of [list_foldleft_method]
//
overload .foldleft with List_foldleft_method
//
(* ****** ****** *)
//
fun
List_ifoldleft
  {res:vt0p}{a:t0p}
(
  List_1(INV(a)), init: res, fopr: (Nat, res, a) -<cloref1> res
) : res = "mac#%" // end of [list_foldleft]
fun
List_ifoldleft_method
  {res:t@ype}{a:t0p}
(
  xs: List_1(INV(a)), init: res)(fopr: (Nat, res, a) -<cloref1> res
) : res = "mac#%" // end of [list_foldleft_method]
//
overload .ifoldleft with List_ifoldleft_method
//
(* ****** ****** *)
//
fun
List_foldright
  {a:t0p}{res:vt0p}
(
  List_1(INV(a)), fopr: (a, res) -<cloref1> res, sink: res
) : res = "mac#%" // end of [list_foldright]
//
fun
List_foldright_method
  {a:t0p}{res:t@ype}
(
  xs: List_1(INV(a)), sink: res)(fopr: (a, res) -<cloref1> res
) : res = "mac#%" // end of [list_foldright]
//
overload .foldright with List_foldright_method
//
(* ****** ****** *)
//
fun
List_ifoldright
  {a:t0p}{res:vt0p}
(
  List_1(INV(a)), fopr: (Nat, a, res) -<cloref1> res, sink: res
) : res = "mac#%" // end of [list_foldright]
//
fun
List_ifoldright_method
  {a:t0p}{res:t@ype}
(
  xs: List_1(INV(a)), sink: res)(fopr: (Nat, a, res) -<cloref1> res
) : res = "mac#%" // end of [list_foldright]
//
overload .ifoldright with List_ifoldright_method
//
(* ****** ****** *)
//
fun
{a:t0p}
List_sort_1
  {n:int}
  (List(INV(a), n)): List(a, n) = "mac#%"
//
fun
List_sort_2
  {a:t0p}{n:int}
(
  List(INV(a), n), cmp: (a, a) -<cloref1> int
) : List(a, n) = "mac#%"
//
symintr List_sort
overload List_sort with List_sort_1 of 100
overload List_sort with List_sort_2 of 100
//
(* ****** ****** *)
//
fun
List_mergesort
{a:t0p}{n:int}
(
  List(INV(a), n), cmp: (a, a) -<cloref1> int
) : List(a, n) = "mac#%"
//
(* ****** ****** *)
//
fun
streamize_list_elt
  {a:t0p}
(
xs: List_1(INV(a))
) :<> stream_vt(a) = "mac#%" // end-of-function
//
(* ****** ****** *)
//
fun
streamize_list_zip
  {a,b:t0p}
(
  List_1(INV(a))
, List_1(INV(b))
) :<> stream_vt($tup(a,b)) = "mac#%" // end-of-fun
//
fun
streamize_list_cross
  {a,b:t0p}
(
  xs: List_1(INV(a))
, ys: List_1(INV(b))
) :<> stream_vt($tup(a,b)) = "mac#%" // end-of-fun
//
(* ****** ****** *)

(* end of [list.sats] *)
