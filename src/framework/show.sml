(* show.sml -- printers used to report counterexamples.
 *
 * These exist for diagnostics only; nothing in the suite asserts anything
 * about their output.
 *)

structure Show =
  struct

    val int    = Int.toString
    val bool   = Bool.toString
    (* EXACT rather than toString: the default formatting keeps only about
     * twelve significant digits, which would print two different reals
     * identically and make a reported counterexample impossible to
     * reproduce. *)
    val real   = Real.fmt StringCvt.EXACT
    val word   = fn w => "0wx" ^ Word.toString w
    val char   = fn c => "#\"" ^ Char.toString c ^ "\""
    val string = fn s => "\"" ^ String.toString s ^ "\""
    val largeInt = LargeInt.toString

    fun order LESS = "LESS"
      | order EQUAL = "EQUAL"
      | order GREATER = "GREATER"

    fun option _ NONE = "NONE"
      | option f (SOME x) = "SOME " ^ f x

    fun list f xs = "[" ^ String.concatWith "," (List.map f xs) ^ "]"

    fun vector f v =
      "#[" ^ String.concatWith "," (List.map f (Vector.foldr (op ::) [] v)) ^ "]"

    fun array f a =
      "#[" ^ String.concatWith "," (List.map f (Array.foldr (op ::) [] a)) ^ "]"

    fun pair (f, g) (a, b) = "(" ^ f a ^ "," ^ g b ^ ")"

    fun triple (f, g, h) (a, b, c) = "(" ^ f a ^ "," ^ g b ^ "," ^ h c ^ ")"

    val intList = list int
    val charList = list char
    val stringList = list string

    val time = Time.toString

  end
