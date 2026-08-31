(* Tests for the Time structure.
 *
 * Time.fromSeconds takes a LargeInt.int, not an int, so every literal here
 * goes through LargeInt.fromInt; writing `Time.fromSeconds 1` compiles on
 * implementations where LargeInt is Int and fails elsewhere, which is exactly
 * the kind of accidental non-portability this suite is meant to catch.
 *)

functor TimeTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val secs = Time.fromSeconds o LargeInt.fromInt
    val ms = Time.fromMilliseconds o LargeInt.fromInt
    val us = Time.fromMicroseconds o LargeInt.fromInt
    val ns = Time.fromNanoseconds o LargeInt.fromInt

    val showT = Show.time
    val eqT = A.eqTime

    (* Kept well away from the extremes: the representable range of time is
     * implementation-defined. *)
    val smallSecs = G.int (~100000, 100000)

    val suite = Group ("Time",
      [ Group ("construction and conversion",
        [ Case ("zeroTime", fn () =>
            (eqT "is zero seconds" (secs 0, Time.zeroTime);
             A.eqLargeInt "converts to zero"
               (LargeInt.fromInt 0, Time.toSeconds Time.zeroTime))),

          Case ("the units are consistent", fn () =>
            (eqT "a second is a thousand milliseconds" (secs 1, ms 1000);
             eqT "a millisecond is a thousand microseconds" (ms 1, us 1000);
             eqT "a microsecond is a thousand nanoseconds" (us 1, ns 1000))),

          Case ("conversion truncates towards zero", fn () =>
            (A.eqLargeInt "1500 ms is one second"
               (LargeInt.fromInt 1, Time.toSeconds (ms 1500));
             A.eqLargeInt "1999 ms is one second"
               (LargeInt.fromInt 1, Time.toSeconds (ms 1999));
             A.eqLargeInt "1500 ms is 1500 ms"
               (LargeInt.fromInt 1500, Time.toMilliseconds (ms 1500)))),

          Case ("negative times", fn () =>
            (A.eqLargeInt "minus one second"
               (LargeInt.fromInt ~1, Time.toSeconds (secs ~1));
             A.that "a negative time is less than zero"
               (Time.< (secs ~1, Time.zeroTime)))),

          Case ("fromReal and toReal", fn () =>
            (A.eqRealWithin 1.0e~6 "one and a half seconds"
               (1.5, Time.toReal (Time.fromReal 1.5));
             A.eqRealWithin 1.0e~6 "a whole number of seconds"
               (2.0, Time.toReal (secs 2))))
        ]),

        Group ("arithmetic",
        [ Case ("addition and subtraction", fn () =>
            (eqT "sum" (secs 3, Time.+ (secs 1, secs 2));
             eqT "difference" (secs 1, Time.- (secs 3, secs 2));
             eqT "a difference may be negative" (secs ~1, Time.- (secs 2, secs 3));
             eqT "adding zero" (secs 5, Time.+ (secs 5, Time.zeroTime)))),

          Case ("comparison", fn () =>
            (A.eqOrder "less" (LESS, Time.compare (secs 1, secs 2));
             A.eqOrder "equal" (EQUAL, Time.compare (secs 2, secs 2));
             A.eqOrder "greater" (GREATER, Time.compare (secs 3, secs 2));
             A.eqBool "less than" (true, Time.< (secs 1, secs 2));
             A.eqBool "less or equal" (true, Time.<= (secs 2, secs 2));
             A.eqBool "greater than" (true, Time.> (secs 3, secs 2));
             A.eqBool "greater or equal" (true, Time.>= (secs 2, secs 2))))
        ]),

        Group ("formatting",
        [ Case ("toString", fn () =>
            (* toString is fmt with three decimal places. *)
            A.eqString "one second" ("1.000", Time.toString (secs 1))),

          Case ("fmt", fn () =>
            (A.eqString "no decimals" ("1", Time.fmt 0 (secs 1));
             A.eqString "one decimal" ("1.5", Time.fmt 1 (ms 1500));
             A.eqString "three decimals" ("1.500", Time.fmt 3 (ms 1500)))),

          (* The three examples the specification gives, which pin down that
           * fmt rounds the fractional part rather than truncating it. *)
          Case ("the examples from the specification", fn () =>
            (A.eqString "fmt 3 of 1.8" ("1.800", Time.fmt 3 (Time.fromReal 1.8));
             A.eqString "fmt 0 of 1.8 rounds up"
               ("2", Time.fmt 0 (Time.fromReal 1.8));
             A.eqString "fmt 0 of zero" ("0", Time.fmt 0 Time.zeroTime))),

          (* "Having n < 0 causes the Size exception to be raised." *)
          Case ("fmt rejects a negative number of digits", fn () =>
            A.raises "negative" A.isSize (fn () => Time.fmt (A.hide ~1) (secs 1))),

          (* "These functions return the number of full seconds ... fractions
           * of the time unit are dropped, i.e., the values are rounded
           * towards 0." *)
          Case ("conversion rounds towards zero, not downwards", fn () =>
            (A.eqLargeInt "~1500 ms is minus one second"
               (LargeInt.fromInt ~1, Time.toSeconds (ms ~1500));
             A.eqLargeInt "~1999 ms is still minus one second"
               (LargeInt.fromInt ~1, Time.toSeconds (ms ~1999));
             A.eqLargeInt "~999 ms is zero seconds"
               (LargeInt.fromInt 0, Time.toSeconds (ms ~999));
             A.eqLargeInt "999 ms is zero seconds"
               (LargeInt.fromInt 0, Time.toSeconds (ms 999)))),

          (* "Thus, if t denotes 2.01 seconds, the functions return 2, 2010,
           * 2010000, and 2010000000 respectively." *)
          Case ("the worked example of the four units", fn () =>
            let
              val t = ms 2010
            in
              A.eqLargeInt "seconds" (LargeInt.fromInt 2, Time.toSeconds t);
              A.eqLargeInt "milliseconds"
                (LargeInt.fromInt 2010, Time.toMilliseconds t);
              A.eqLargeInt "microseconds"
                (LargeInt.fromInt 2010000, Time.toMicroseconds t);
              A.eqLargeInt "nanoseconds"
                (LargeInt.fromInt 2010000000, Time.toNanoseconds t)
            end),

          Case ("fromString", fn () =>
            (A.eqBy (op =, Show.option showT) "whole seconds"
               (SOME (secs 1), Time.fromString "1.000");
             A.eqBy (op =, Show.option showT) "fractional"
               (SOME (ms 1500), Time.fromString "1.5");
             A.eqBy (op =, Show.option showT) "rejects letters"
               (NONE, Time.fromString "abc")))
        ]),

        Group ("resolution",
        [ Case ("the declared resolution is what the implementation delivers",
            fn () =>
              let
                (* One tick must survive; half a tick must not, unless the
                 * implementation is finer than it declares. *)
                val oneTick = ns C.timeResolutionNanos
              in
                A.that "the resolution is a positive number of nanoseconds"
                       (C.timeResolutionNanos > 0);
                A.eqLargeInt "one tick round trips"
                  (LargeInt.fromInt C.timeResolutionNanos,
                   Time.toNanoseconds oneTick)
              end)
        ]),

        Group ("scanning",
        [ Case ("scan reads a time and leaves the rest", fn () =>
            case Time.scan Substring.getc (Substring.full "1.500 tail") of
                NONE => A.fail "scan returned NONE"
              | SOME (t, rest) =>
                  (eqT "value" (ms 1500, t);
                   A.eqString "remainder" (" tail", Substring.string rest))),

          Case ("scan skips leading whitespace", fn () =>
            case Time.scan Substring.getc (Substring.full "   2.000") of
                NONE => A.fail "scan returned NONE"
              | SOME (t, _) => eqT "value" (secs 2, t)),

          Case ("scan rejects what is not a time", fn () =>
            A.that "letters"
              (not (isSome (Time.scan Substring.getc (Substring.full "abc"))))),

          (* "[+~-]?([0-9]+.[0-9]+? | .[0-9]+)" *)
          Case ("scan accepts every shape in the grammar", fn () =>
            let
              val eq = A.eqBy (op =, Show.option showT)
            in
              eq "a plus sign" (SOME (ms 1500), Time.fromString "+1.5");
              eq "a hyphen sign" (SOME (ms ~1500), Time.fromString "-1.5");
              eq "a tilde sign" (SOME (ms ~1500), Time.fromString "~1.5");
              (* The specification's regular expression makes the digits
               * after the point optional but not the point itself, while the
               * bare-integer form every implementation accepts is not in the
               * grammar at all.  Both readings are therefore allowed here;
               * what is checked is that the scanner does not invent a
               * different value. *)
              A.that "a trailing point"
                (case Time.fromString "1." of
                     NONE => true
                   | SOME t => t = secs 1);
              eq "no integral digits" (SOME (ms 500), Time.fromString ".5");
              eq "no point at all" (SOME (secs 42), Time.fromString "42")
            end),

          (* "Note that this function is equivalent to StringCvt.scanString
           * scan." *)
          Case ("fromString is scanString scan", fn () =>
            let
              val eq = A.eqBy (op =, Show.option showT)
            in
              List.app
                (fn s =>
                   eq ("agree on " ^ s)
                     (StringCvt.scanString Time.scan s, Time.fromString s))
                ["1.5", "  2.25", "abc", "", "~3.5", ".5"]
            end),

          Case ("the Time exception exists", fn () =>
            A.eqString "name" ("Time", exnName Time.Time))
        ]),

        Group ("the clock",
        [ Case ("now is monotone across two readings", fn () =>
            let
              val a = Time.now ()
              (* Do enough work that a coarse clock still advances. *)
              val _ = List.foldl op+ 0 (List.tabulate (20000, fn i => i))
              val b = Time.now ()
            in
              A.that "the second reading is not earlier" (Time.>= (b, a))
            end)
        ]),

        Group ("laws",
        [ P.forAll ("seconds round trip", smallSecs, Show.int,
                    fn n => Time.toSeconds (secs n) = LargeInt.fromInt n),

          P.forAll ("milliseconds round trip", smallSecs, Show.int,
                    fn n => Time.toMilliseconds (ms n) = LargeInt.fromInt n),

          P.forAll ("microseconds round trip", smallSecs, Show.int,
                    fn n => Time.toMicroseconds (us n) = LargeInt.fromInt n),

          (* A nanosecond count only survives the round trip when it is a whole
           * number of the implementation's ticks; anything finer is rounded
           * away by a representation the Basis does not constrain. *)
          P.forAll ("nanoseconds round trip at the declared resolution",
                    G.map (fn n => n * C.timeResolutionNanos) (G.int (~100000, 100000)),
                    Show.int,
                    fn n => Time.toNanoseconds (ns n) = LargeInt.fromInt n),

          P.forAll ("addition commutes",
                    G.pair (smallSecs, smallSecs), Show.pair (Show.int, Show.int),
                    fn (a, b) =>
                      Time.+ (secs a, secs b) = Time.+ (secs b, secs a)),

          P.forAll ("addition is associative",
                    G.triple (smallSecs, smallSecs, smallSecs),
                    Show.triple (Show.int, Show.int, Show.int),
                    fn (a, b, c) =>
                      Time.+ (Time.+ (secs a, secs b), secs c)
                      = Time.+ (secs a, Time.+ (secs b, secs c))),

          P.forAll ("zeroTime is a unit", smallSecs, Show.int,
                    fn a => Time.+ (secs a, Time.zeroTime) = secs a),

          P.forAll ("subtraction inverts addition",
                    G.pair (smallSecs, smallSecs), Show.pair (Show.int, Show.int),
                    fn (a, b) =>
                      Time.- (Time.+ (secs a, secs b), secs b) = secs a),

          P.forAll ("compare agrees with the operators",
                    G.pair (smallSecs, smallSecs), Show.pair (Show.int, Show.int),
                    fn (a, b) =>
                      case Time.compare (secs a, secs b) of
                          LESS => Time.< (secs a, secs b)
                        | EQUAL => secs a = secs b
                        | GREATER => Time.> (secs a, secs b)),

          P.forAll ("comparison follows the seconds",
                    G.pair (smallSecs, smallSecs), Show.pair (Show.int, Show.int),
                    fn (a, b) => Time.< (secs a, secs b) = (a < b)),

          P.forAll ("milliseconds are a thousand times seconds",
                    G.int (~1000, 1000), Show.int,
                    fn n => Time.toMilliseconds (secs n)
                            = LargeInt.fromInt (n * 1000)),

          P.forAll ("fromString inverts toString", G.int (0, 100000), Show.int,
                    fn n => Time.fromString (Time.toString (secs n)) = SOME (secs n)),

          (* "toString rounds t to 3 decimal digits.  It is equivalent to
           * fmt 3 t." *)
          P.forAll ("toString is fmt 3", smallSecs, Show.int,
                    fn n => Time.toString (ms n) = Time.fmt 3 (ms n)),

          P.forAll ("fmt rounds to the requested number of digits",
                    G.pair (G.int (~5000, 5000), G.int (0, 6)),
                    Show.pair (Show.int, Show.int),
                    fn (n, k) =>
                      let
                        val t = ms n
                        val s = Time.fmt k t
                        val body = if String.isPrefix "~" s
                                   then String.extract (s, 1, NONE) else s
                        val (whole, frac) =
                          Substring.splitl (fn c => c <> #".")
                                           (Substring.full body)
                      in
                        Substring.size whole >= 1
                        andalso List.all Char.isDigit (Substring.explode whole)
                        andalso (if k = 0 then Substring.size frac = 0
                                 else Substring.size frac = k + 1)
                      end),

          (* "converts the real number r to the time value denoting r
           * seconds", and back. *)
          P.forAll ("fromReal and toReal agree on whole seconds",
                    G.int (~100000, 100000), Show.int,
                    fn n =>
                      Real.== (Real.fromInt n,
                               Time.toReal (Time.fromReal (Real.fromInt n)))),

          P.forAll ("the four units scale as they should",
                    G.int (~1000, 1000), Show.int,
                    fn n =>
                      Time.toMicroseconds (secs n)
                      = LargeInt.fromInt n * LargeInt.fromInt 1000000
                      andalso Time.toNanoseconds (ms n)
                              = LargeInt.fromInt n * LargeInt.fromInt 1000000),

          P.forAll ("subtraction is addition of the negation",
                    G.pair (smallSecs, smallSecs), Show.pair (Show.int, Show.int),
                    fn (a, b) =>
                      Time.- (secs a, secs b) = Time.+ (secs a, secs (~b)))
        ])
      ])
  end
