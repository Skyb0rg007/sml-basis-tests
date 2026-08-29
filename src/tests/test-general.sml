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
