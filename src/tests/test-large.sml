(* Tests for LargeInt, LargeWord, LargeReal and Position.
 *
 * These four are required structures whose whole purpose is to be the widest
 * type of their kind, and to be the common currency the narrower types
 * convert through.  What can be tested is exactly that: the width
 * relationships the Basis fixes, and that every conversion to and from the
 * large type round-trips.  Their absolute sizes are implementation-defined
 * and are read from the implementation, not assumed.
 *
 * Position is the type of file offsets; nothing here opens a file, since
 * OS.FileSys is tested separately.
 *)

functor LargeTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop
    structure LI = LargeInt
    structure LW = LargeWord
    structure LR = LargeReal

    val showLI = LargeInt.toString
    val eqLI = A.eqLargeInt
    fun showLW w = "0wx" ^ LW.toString w
    val eqLW = A.eqBy (op =, showLW)
    val showPos = Position.toString
    val eqPos = A.eqBy (op =, showPos)

    val li = LargeInt.fromInt
    val pos = Position.fromInt

    val smallInts = G.smallInt
    val genLI = G.map li G.smallInt
    val genPos = G.map pos G.smallInt

    (* LargeInt may be arbitrary precision, in which case there are no
     * bounds to test against. *)
    val liFixed = Option.isSome LI.precision
    val posFixed = Option.isSome Position.precision

    val suite = Group ("Large types",
      [ Group ("LargeInt",
        [ Case ("it is at least as wide as the default int", fn () =>
            case (Int.precision, LI.precision) of
                (SOME i, SOME l) =>
                  A.that ("Int.precision " ^ Int.toString i
                          ^ " must not exceed LargeInt.precision "
                          ^ Int.toString l)
                         (l >= i)
              | (SOME _, NONE) => ()    (* arbitrary precision is wider still *)
              | (NONE, NONE) => ()
              | (NONE, SOME _) =>
                  A.fail "int is arbitrary precision but LargeInt is not"),

          Case ("the bounds are consistent", fn () =>
            if not liFixed then
              A.that "an arbitrary precision LargeInt has no bounds"
                (LI.maxInt = NONE andalso LI.minInt = NONE)
            else
              (A.that "maxInt is positive" (LI.> (valOf LI.maxInt, li 0));
               A.that "minInt is negative" (LI.< (valOf LI.minInt, li 0)))),

          Case ("arithmetic", fn () =>
            (eqLI "addition" (li 5, LI.+ (li 2, li 3));
             eqLI "subtraction" (li ~1, LI.- (li 2, li 3));
             eqLI "multiplication" (li 6, LI.* (li 2, li 3));
             eqLI "negation" (li ~2, LI.~ (li 2));
             eqLI "absolute value" (li 2, LI.abs (li ~2));
             eqLI "minimum" (li 2, LI.min (li 2, li 3));
             eqLI "maximum" (li 3, LI.max (li 2, li 3));
             A.eqInt "sign" (~1, LI.sign (li ~5));
             A.eqBool "sameSign" (true, LI.sameSign (li ~1, li ~2)))),

          Case ("division follows the same rules as Int", fn () =>
            (eqLI "div rounds down" (li ~4, LI.div (li ~7, li 2));
             eqLI "mod takes the divisor's sign" (li 1, LI.mod (li ~7, li 2));
             eqLI "quot rounds towards zero" (li ~3, LI.quot (li ~7, li 2));
             eqLI "rem takes the dividend's sign" (li ~1, LI.rem (li ~7, li 2));
             A.raises "division by zero" A.isDiv
               (fn () => LI.div (li 1, li 0)))),

          Case ("comparison", fn () =>
            (A.eqOrder "less" (LESS, LI.compare (li 1, li 2));
             A.eqBool "the operator agrees" (true, LI.< (li 1, li 2));
             A.eqBool "less or equal" (true, LI.<= (li 2, li 2));
             A.eqBool "greater" (true, LI.> (li 3, li 2));
             A.eqBool "greater or equal" (true, LI.>= (li 2, li 2)))),

          Case ("text conversion", fn () =>
            (A.eqString "toString" ("42", LI.toString (li 42));
             A.eqString "negative uses a tilde" ("~42", LI.toString (li ~42));
             A.eqBy (op =, Show.option showLI) "fromString"
               (SOME (li 42), LI.fromString "42");
             A.eqString "fmt in hexadecimal" ("FF", LI.fmt StringCvt.HEX (li 255));
             A.eqBy (op =, Show.option showLI) "scan"
               (SOME (li 255),
                StringCvt.scanString (LI.scan StringCvt.HEX) "FF"))),

          Case ("conversion to and from the default int", fn () =>
            (eqLI "toLarge" (li 42, Int.toLarge 42);
             A.eqInt "fromLarge" (42, Int.fromLarge (li 42));
             eqLI "LargeInt.toLarge is the identity" (li 42, LI.toLarge (li 42));
             eqLI "and so is fromLarge" (li 42, LI.fromLarge (li 42));
             A.eqInt "LargeInt.toInt" (42, LI.toInt (li 42));
             eqLI "LargeInt.fromInt" (li 42, LI.fromInt 42))),

          Case ("converting a value too big for int is refused", fn () =>
            if not (Option.isSome Int.maxInt) then ()
            else
              let
                (* One past the default int's range, built in LargeInt so that
                 * constructing it cannot itself overflow. *)
                val tooBig = LI.+ (Int.toLarge (valOf Int.maxInt), li 1)
              in
                if LI.<= (tooBig, Int.toLarge (valOf Int.maxInt)) then ()
                else
                  A.raises "narrowing overflows" A.isOverflow
                    (fn () => Int.fromLarge tooBig)
              end)
        ]),

        Group ("LargeWord",
        [ Case ("it is at least as wide as the default word", fn () =>
            A.that ("Word.wordSize " ^ Int.toString Word.wordSize
                    ^ " must not exceed LargeWord.wordSize "
                    ^ Int.toString LW.wordSize)
                   (LW.wordSize >= Word.wordSize)),

          Case ("it is at least as wide as Word8", fn () =>
            A.that "LargeWord is at least eight bits" (LW.wordSize >= 8)),

          Case ("arithmetic wraps rather than trapping", fn () =>
            let
              val allOnes = LW.notb (LW.fromInt 0)
            in
              eqLW "adding one wraps to zero"
                (LW.fromInt 0, LW.+ (allOnes, LW.fromInt 1));
              eqLW "subtracting one from zero wraps"
                (allOnes, LW.- (LW.fromInt 0, LW.fromInt 1));
              A.noRaise "no overflow" (fn () => LW.* (allOnes, allOnes))
            end),

          Case ("bitwise operations", fn () =>
            (eqLW "andb" (LW.fromInt 8, LW.andb (LW.fromInt 12, LW.fromInt 10));
             eqLW "orb" (LW.fromInt 14, LW.orb (LW.fromInt 12, LW.fromInt 10));
             eqLW "xorb" (LW.fromInt 6, LW.xorb (LW.fromInt 12, LW.fromInt 10));
             eqLW "notb is an involution"
               (LW.fromInt 5, LW.notb (LW.notb (LW.fromInt 5))))),

          Case ("shifting past the width", fn () =>
            let
              val allOnes = LW.notb (LW.fromInt 0)
              val past = Word.fromInt LW.wordSize
            in
              eqLW "left" (LW.fromInt 0, LW.<< (allOnes, past));
              eqLW "logical right" (LW.fromInt 0, LW.>> (allOnes, past));
              eqLW "arithmetic right keeps the sign bit"
                (allOnes, LW.~>> (allOnes, past))
            end),

          Case ("division", fn () =>
            (eqLW "div" (LW.fromInt 3, LW.div (LW.fromInt 7, LW.fromInt 2));
             eqLW "mod" (LW.fromInt 1, LW.mod (LW.fromInt 7, LW.fromInt 2));
             A.raises "by zero" A.isDiv
               (fn () => LW.div (LW.fromInt 1, LW.fromInt 0)))),

          Case ("comparison is unsigned", fn () =>
            let val allOnes = LW.notb (LW.fromInt 0)
            in
              A.eqBool "all ones is large, not negative"
                (true, LW.> (allOnes, LW.fromInt 1));
              A.eqOrder "compare" (GREATER, LW.compare (allOnes, LW.fromInt 1));
              eqLW "min" (LW.fromInt 1, LW.min (LW.fromInt 1, allOnes));
              eqLW "max" (allOnes, LW.max (LW.fromInt 1, allOnes))
            end),

          Case ("text conversion", fn () =>
            (A.eqString "toString" ("FF", LW.toString (LW.fromInt 255));
             A.eqBy (op =, Show.option showLW) "fromString"
               (SOME (LW.fromInt 255), LW.fromString "FF");
             A.eqString "fmt" ("101", LW.fmt StringCvt.BIN (LW.fromInt 5));
             A.eqBy (op =, Show.option showLW) "scan"
               (SOME (LW.fromInt 5),
                StringCvt.scanString (LW.scan StringCvt.BIN) "101"))),

          Case ("conversion between Word and LargeWord", fn () =>
            (eqLW "toLarge" (LW.fromInt 255, Word.toLarge (Word.fromInt 255));
             A.eqWord "fromLarge" (Word.fromInt 255, Word.fromLarge (LW.fromInt 255));
             eqLW "LargeWord.toLarge is the identity"
               (LW.fromInt 7, LW.toLarge (LW.fromInt 7));
             A.eqInt "toInt" (255, LW.toInt (LW.fromInt 255));
             A.eqInt "toIntX of all ones" (~1, LW.toIntX (LW.notb (LW.fromInt 0))))),

          (* toLarge zero-extends; toLargeX propagates the sign bit. *)
          Case ("toLarge and toLargeX differ on a negative pattern", fn () =>
            let
              val wAllOnes = Word.notb (Word.fromInt 0)
            in
              if LW.wordSize = Word.wordSize then
                eqLW "at equal widths they agree"
                  (Word.toLarge wAllOnes, Word.toLargeX wAllOnes)
              else
                (eqLW "toLargeX fills the top with ones"
                   (LW.notb (LW.fromInt 0), Word.toLargeX wAllOnes);
                 A.that "toLarge does not"
                   (Word.toLarge wAllOnes <> Word.toLargeX wAllOnes))
            end),

          Case ("conversion between Word and LargeInt", fn () =>
            (eqLI "toLargeInt" (li 255, Word.toLargeInt (Word.fromInt 255));
             eqLI "toLargeIntX of all ones"
               (li ~1, Word.toLargeIntX (Word.notb (Word.fromInt 0)));
             A.eqWord "fromLargeInt" (Word.fromInt 255, Word.fromLargeInt (li 255))))
        ]),

        Group ("LargeReal",
        [ Case ("it is at least as precise as the default real", fn () =>
            A.that ("Real.precision " ^ Int.toString Real.precision
                    ^ " must not exceed LargeReal.precision "
                    ^ Int.toString LR.precision)
                   (LR.precision >= Real.precision)),

          Case ("the radix agrees", fn () =>
            A.eqInt "same radix" (Real.radix, LR.radix)),

          Case ("conversion to and from the default real", fn () =>
            (A.that "toLarge then fromLarge is the identity"
               (Real.== (1.5, Real.fromLarge IEEEReal.TO_NEAREST
                                (Real.toLarge 1.5)));
             A.that "zero" (Real.== (0.0, Real.fromLarge IEEEReal.TO_NEAREST
                                            (Real.toLarge 0.0)));
             A.that "a negative value"
               (Real.== (~2.25, Real.fromLarge IEEEReal.TO_NEAREST
                                  (Real.toLarge ~2.25))))),

          Case ("LargeReal supports the same operations", fn () =>
            (A.that "addition" (LR.== (LR.fromInt 3, LR.+ (LR.fromInt 1,
                                                           LR.fromInt 2)));
             A.that "comparison" (LR.< (LR.fromInt 1, LR.fromInt 2));
             A.that "abs" (LR.== (LR.fromInt 2, LR.abs (LR.fromInt ~2)));
             A.eqInt "floor" (1, LR.floor (LR.fromInt 1))))
        ]),

        Group ("Position",
        [ Case ("it is an integer type with the usual operations", fn () =>
            (eqPos "addition" (pos 5, Position.+ (pos 2, pos 3));
             eqPos "subtraction" (pos 1, Position.- (pos 3, pos 2));
             eqPos "negation" (pos ~2, Position.~ (pos 2));
             eqPos "absolute value" (pos 2, Position.abs (pos ~2));
             A.eqOrder "compare" (LESS, Position.compare (pos 1, pos 2));
             A.eqInt "sign" (1, Position.sign (pos 5)))),

          Case ("it is wide enough to be a file offset", fn () =>
            case Position.precision of
                NONE => ()   (* arbitrary precision is certainly enough *)
              | SOME p =>
                  A.that ("Position.precision = " ^ Int.toString p
                          ^ ", which must be at least 31 bits")
                         (p >= 31)),

          Case ("text conversion", fn () =>
            (A.eqString "toString" ("42", Position.toString (pos 42));
             A.eqBy (op =, Show.option showPos) "fromString"
               (SOME (pos 42), Position.fromString "42");
             A.eqString "fmt" ("2A", Position.fmt StringCvt.HEX (pos 42)))),

          Case ("conversion through LargeInt", fn () =>
            (eqLI "toLarge" (li 42, Position.toLarge (pos 42));
             eqPos "fromLarge" (pos 42, Position.fromLarge (li 42));
             A.eqInt "toInt" (42, Position.toInt (pos 42));
             eqPos "fromInt" (pos 42, Position.fromInt 42)))
        ]),

        Group ("laws",
        [ P.forAll ("Int and LargeInt round trip", smallInts, Show.int,
                    fn n => Int.fromLarge (Int.toLarge n) = n),

          P.forAll ("LargeInt arithmetic agrees with Int arithmetic",
                    G.pair (smallInts, smallInts), Show.pair (Show.int, Show.int),
                    fn (a, b) =>
                      LI.+ (li a, li b) = li (a + b)
                      andalso LI.* (li a, li b) = li (a * b)
                      andalso LI.- (li a, li b) = li (a - b)),

          P.forAll ("LargeInt comparison agrees with Int comparison",
                    G.pair (smallInts, smallInts), Show.pair (Show.int, Show.int),
                    fn (a, b) => LI.compare (li a, li b) = Int.compare (a, b)),

          P.forAll ("LargeInt text conversion round trips", genLI, showLI,
                    fn n => LI.fromString (LI.toString n) = SOME n),

          P.forAll ("Word and LargeWord round trip", G.word, Show.word,
                    fn w => Word.fromLarge (Word.toLarge w) = w),

          P.forAll ("toLargeIntX inverts fromLargeInt for small values",
                    smallInts, Show.int,
                    fn n => Word.toLargeIntX (Word.fromLargeInt (li n)) = li n),

          P.forAll ("LargeWord text conversion round trips",
                    G.map (fn n => LW.fromInt n) G.nat, showLW,
                    fn w => LW.fromString (LW.toString w) = SOME w),

          P.forAll ("Real and LargeReal round trip", G.anyReal, Show.real,
                    fn x =>
                      P.implies (Real.isFinite x,
                                 Real.== (x, Real.fromLarge IEEEReal.TO_NEAREST
                                                (Real.toLarge x)))),

          P.forAll ("Position and LargeInt round trip", genPos, showPos,
                    fn p => Position.fromLarge (Position.toLarge p) = p),

          P.forAll ("Position and Int round trip", smallInts, Show.int,
                    fn n => Position.toInt (Position.fromInt n) = n),

          P.forAll ("Position arithmetic agrees with Int arithmetic",
                    G.pair (smallInts, smallInts), Show.pair (Show.int, Show.int),
                    fn (a, b) =>
                      Position.+ (pos a, pos b) = pos (a + b)
                      andalso Position.compare (pos a, pos b) = Int.compare (a, b))
        ])
      ])
  end
