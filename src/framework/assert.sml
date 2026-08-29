(* assert.sml -- assertions.
 *
 * A failing assertion raises TestFail with a human-readable explanation; the
 * runner turns that into a FAIL line.  Any other exception escaping a test is
 * reported separately as an ERROR, so that "the Basis raised something
 * unexpected" is never silently read as "the assertion was false".
 *)

structure Assert =
  struct

    exception TestFail of string

    (* A barrier against compile-time constant folding.
     *
     * A test like `Vector.sub (#[1,2,3], ~1)` has entirely constant
     * arguments, so an optimising compiler is entitled to evaluate it while
     * compiling.  When it does, two things go wrong: the test stops
     * exercising the library at run time, and a compiler whose folder
     * disagrees with its own library about the resulting exception can fail
     * to compile the suite at all -- Poly/ML 5.7.1 reports "Overflow
     * unexpectedly raised while compiling" for exactly this expression.
     *
     * `hide n` is n, but it is a sum involving a value read from mutable
     * storage, so no compiler can discover that it is constant.  A branch on
     * a ref would not do: an optimiser may distribute the surrounding call
     * into both arms and fold the constant arm anyway.  Bounds-checking tests
     * therefore pass their index through `hide`. *)
    val zeroCell = ref 0
    fun hide (n : int) = n + !zeroCell

    (* The same barrier for a value of any type. *)
    fun hideVal x = List.nth ([x], !zeroCell)

    fun fail msg = raise TestFail msg

    fun that msg b = if b then () else fail msg

    fun falsehood msg b = if b then fail msg else ()

    (* eqBy takes the comparison and printer explicitly so that the suite never
     * relies on polymorphic equality for types (real, functions) where it is
     * either unavailable or the wrong notion. *)
    fun eqBy (eq, show) msg (expected, actual) =
      if eq (expected, actual) then ()
      else fail (msg ^ ": expected " ^ show expected ^ " but got " ^ show actual)

    val eqInt    = eqBy (op =, Show.int)
    val eqBool   = eqBy (op =, Show.bool)
    val eqChar   = eqBy (op =, Show.char)
    val eqString = eqBy (op =, Show.string)
    val eqWord   = eqBy (op =, Show.word)
    val eqOrder  = eqBy (op =, Show.order)
    val eqLargeInt = eqBy (op =, Show.largeInt)
    val eqIntList  = eqBy (op =, Show.intList)
    val eqCharList = eqBy (op =, Show.charList)
    val eqStringList = eqBy (op =, Show.stringList)
    val eqIntOption = eqBy (op =, Show.option Show.int)
    val eqStringOption = eqBy (op =, Show.option Show.string)
    val eqCharOption = eqBy (op =, Show.option Show.char)
    val eqTime = eqBy (op =, Show.time)

    fun eqList (eq, show) msg (xs, ys) =
      eqBy (fn (a, b) => ListPair.allEq eq (a, b), Show.list show) msg (xs, ys)

    (* Reals need three different notions of equality and the tests say which
     * one they mean. *)
    fun eqRealExact msg (expected, actual) =
      if Real.== (expected, actual) then ()
      else fail (msg ^ ": expected " ^ Show.real expected
                 ^ " but got " ^ Show.real actual)

    fun eqRealWithin tol msg (expected, actual) =
      if Real.isFinite expected andalso Real.isFinite actual
         andalso Real.abs (expected - actual) <= tol
      then ()
      else if Real.== (expected, actual) then ()
      else fail (msg ^ ": expected " ^ Show.real expected ^ " +/- "
                 ^ Show.real tol ^ " but got " ^ Show.real actual)

    (* Relative tolerance, for values whose magnitude is not known in advance. *)
    fun eqRealRel eps msg (expected, actual) =
      let
        val scale = Real.max (Real.abs expected, 1.0)
      in
        eqRealWithin (eps * scale) msg (expected, actual)
      end

    fun isNaN msg x =
      if Real.isNan x then () else fail (msg ^ ": expected nan, got " ^ Show.real x)

    (* --- exceptions --------------------------------------------------- *)

    (* raises msg p f -- f () must raise an exception satisfying p.  A TestFail
     * thrown from inside f is re-raised rather than caught, so a failed
     * assertion nested in the thunk is not mistaken for the expected
     * exception. *)
    fun raises msg p (f : unit -> 'a) =
      (ignore (f ());
       fail (msg ^ ": expected an exception but none was raised"))
      handle TestFail m => raise TestFail m
           | e => if p e then ()
                  else fail (msg ^ ": expected a different exception, got "
                             ^ exnName e)

    fun noRaise msg (f : unit -> 'a) =
      ignore (f ())
      handle TestFail m => raise TestFail m
           | e => fail (msg ^ ": expected no exception but got " ^ exnName e)

    fun isSubscript Subscript = true | isSubscript _ = false
    fun isSize Size = true | isSize _ = false
    fun isOverflow Overflow = true | isOverflow _ = false
    fun isDomain Domain = true | isDomain _ = false
    fun isDiv Div = true | isDiv _ = false
    fun isChr Chr = true | isChr _ = false
    fun isSpan Span = true | isSpan _ = false
    fun isEmpty List.Empty = true | isEmpty _ = false
    fun isOption Option.Option = true | isOption _ = false
    fun isUnequalLengths ListPair.UnequalLengths = true | isUnequalLengths _ = false
    fun isUnordered IEEEReal.Unordered = true | isUnordered _ = false
    fun isPath OS.Path.Path = true | isPath _ = false
    fun isInvalidArc OS.Path.InvalidArc = true | isInvalidArc _ = false
    fun isIo (IO.Io _) = true | isIo _ = false
    fun isSysErr (OS.SysErr _) = true | isSysErr _ = false
    fun isAny (_ : exn) = true

    fun isEither (p, q) e = p e orelse q e

    (* Several Basis operations are specified to raise one of two exceptions
     * depending on the argument (floor of a NaN, for instance, is Domain by
     * the specification but Overflow in more than one real implementation);
     * where the standard genuinely permits either, the tests say so here
     * rather than pretending one is wrong. *)
    val isDomainOrOverflow = isEither (isDomain, isOverflow)
    val isSizeOrSubscript = isEither (isSize, isSubscript)

  end
