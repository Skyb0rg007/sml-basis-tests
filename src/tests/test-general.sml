(* Tests for the top-level environment and the General structure. *)

functor GeneralTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    exception Marker
    exception MarkerWith of int

    val suite = Group ("General",
      [ Case ("o composes right to left", fn () =>
          let
            val f = (fn x => x * 2) o (fn x => x + 3)
          in
            A.eqInt "(*2) o (+3) applied to 4" (14, f 4)
          end),

        Case ("before returns its first argument", fn () =>
          let
            val cell = ref 0
            val v = 7 before (cell := 1)
          in
            A.eqInt "value" (7, v);
            A.eqInt "side effect happened" (1, !cell)
          end),

        Case ("ignore discards", fn () =>
          A.eqBool "ignore returns unit" (true, ignore 5 = ())),

        Case ("exnName of a nullary exception", fn () =>
          A.eqString "name" ("Marker", exnName Marker)),

        Case ("exnName of an exception with an argument", fn () =>
          A.eqString "name" ("MarkerWith", exnName (MarkerWith 3))),

        Case ("exnName of a Basis exception", fn () =>
          (A.eqString "Div" ("Div", exnName Div);
           A.eqString "Overflow" ("Overflow", exnName Overflow);
           A.eqString "Subscript" ("Subscript", exnName Subscript))),

        (* The text of exnMessage is implementation-defined, so all that can
         * be required is that there is some. *)
        Case ("exnMessage produces something", fn () =>
          A.that "non-empty" (String.size (exnMessage Marker) > 0)),

        Case ("Fail carries its string", fn () =>
          A.raises "Fail" (fn Fail s => s = "boom" | _ => false)
                   (fn () => raise Fail "boom")),

        (* Bind and Match are raised by the language, not by any library
         * function: a failing val binding and a non-exhaustive match. *)
        Case ("Bind is raised by a failing pattern binding", fn () =>
          A.raises "binding a cons pattern to nil"
            (fn Bind => true | _ => false)
            (fn () => let val x :: _ = A.hideVal ([] : int list) in x end)),

        Case ("Match is raised when no case alternative applies", fn () =>
          A.raises "no matching alternative"
            (fn Match => true | _ => false)
            (fn () =>
               let
                 fun onlyZero 0 = 0
               in
                 onlyZero (A.hide 1)
               end)),

        Case ("the General exceptions all exist and are named", fn () =>
          A.eqStringList "the specified names"
            (["Bind", "Chr", "Div", "Domain", "Fail", "Match", "Overflow",
              "Size", "Span", "Subscript"],
             List.map exnName
               [Bind, Chr, Div, Domain, Fail "x", Match, Overflow,
                Size, Span, Subscript])),

        Case ("order is a three-element type", fn () =>
          (A.eqOrder "LESS" (LESS, Int.compare (1, 2));
           A.eqOrder "EQUAL" (EQUAL, Int.compare (2, 2));
           A.eqOrder "GREATER" (GREATER, Int.compare (3, 2)))),

        Case ("references", fn () =>
          let
            val r = ref 1
          in
            A.eqInt "initial" (1, !r);
            r := 42;
            A.eqInt "after assignment" (42, !r);
            A.that "a ref is equal to itself" (r = r);
            A.that "distinct refs with equal contents differ" (ref 1 <> ref 1)
          end),

        (* "The name returned may be that of any exception constructor
         * aliasing with ex." *)
        Case ("exnName of an aliased exception names one of the aliases",
          fn () =>
            let
              exception Alias = Marker
            in
              A.that "either name"
                (exnName Alias = "Marker" orelse exnName Alias = "Alias")
            end),

        (* "The precise format of the message may vary between
         * implementations and locales, but will at least contain the string
         * exnName ex." *)
        Case ("exnMessage contains exnName", fn () =>
          let
            fun check e =
              A.that (exnName e ^ " appears in its message")
                (String.isSubstring (exnName e) (exnMessage e))
          in
            List.app check
              [Marker, MarkerWith 3, Div, Overflow, Subscript, Size,
               Fail "boom", Domain, Chr, Span, Bind, Match]
          end),

        (* Each General exception is raised by the operation the description
         * names it for: Chr by chr, Size by an over-large or negative
         * aggregate, Span by an incompatible pair of substrings, Div by
         * division by zero, Subscript by an index out of range and Overflow
         * by an unrepresentable arithmetic result. *)
        Case ("the General exceptions are raised where they are specified",
          fn () =>
            (A.raises "chr out of range" A.isChr
               (fn () => Char.chr (A.hide (Char.maxOrd + 1)));
             A.raises "a negative array size" A.isSize
               (fn () => Array.array (A.hide ~1, 0));
             A.raises "span of unrelated substrings" A.isSpan
               (fn () =>
                  Substring.span (Substring.full "a", Substring.full "b"));
             A.raises "an index out of range" A.isSubscript
               (fn () => List.nth ([1, 2, 3], A.hide 5));
             A.raises "division by zero" A.isDiv
               (fn () => 1 div (A.hide 0)))),

        P.forAll ("o is application of one function to the result of the other",
                  G.smallInt, Show.int, fn n =>
          let
            val f = fn x => x + 1
            val g = fn x => x * 2
          in
            (f o g) n = f (g n)
          end),

        P.forAll ("before returns its first argument and evaluates its second",
                  G.smallInt, Show.int, fn n =>
          let
            val cell = ref 0
            val v = n before (cell := n + 1)
          in
            v = n andalso !cell = n + 1
          end),

        P.forAll ("assignment then dereference returns what was assigned",
                  G.pair (G.smallInt, G.smallInt),
                  Show.pair (Show.int, Show.int),
                  fn (a, b) =>
                    let val r = ref a
                    in !r = a andalso (r := b; !r = b) end),

        P.forAll ("o is associative", G.smallInt, Show.int, fn n =>
          let
            val f = fn x => x + 1
            val g = fn x => x * 2
            val h = fn x => x - 3
          in
            ((f o g) o h) n = (f o (g o h)) n
          end),

        P.forAll ("ignore o f is total wherever f is",
                  G.smallInt, Show.int,
                  fn n => (ignore (n + 0); true))
      ])
  end
