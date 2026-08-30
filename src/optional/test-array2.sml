(* Tests for Array2, the two-dimensional mutable arrays.
 *
 * Array2 is optional, so this file is only reached through a build
 * description that names it; see build/optional/.
 *
 * Two things distinguish this signature from Array and account for most of
 * what is tested here.  Every traversal takes a `traversal` argument saying
 * whether it visits row by row or column by column, and the result is
 * observable: `fold` over a non-commutative operator, or `appi` recording the
 * indices it is handed, tells the two apart.  And the bulk operations work on
 * a *region* -- a base array with an origin and optional extents, where NONE
 * means "to the edge" -- so the defaulting of those extents, and the
 * behaviour of a region that runs off the array, are part of the contract.
 *)

functor Array2TestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop
    structure A2 = Array2

    val eqIL = A.eqIntList
    val eqIIL = A.eqBy (op =, Show.list Show.intList)

    (* rows a -- the contents as a list of rows, which is how the tests state
     * their expectations.  Everything else is compared through this. *)
    fun rows a =
      List.tabulate (A2.nRows a, fn r =>
        List.tabulate (A2.nCols a, fn c => A2.sub (a, r, c)))

    fun showA a = Show.list Show.intList (rows a)
    (* Comparing two arrays means comparing their contents: polymorphic
     * equality on Array2.array is identity, so it would call any two distinct
     * arrays different however they were filled. *)
    fun eqA msg (e, a) = eqIIL msg (rows e, rows a)

    (* The 3 by 4 array whose entry at (r, c) is 10r + c, so a transposed or
     * mis-strided read names a different number rather than a plausible one. *)
    fun grid (nr, nc) = A2.tabulate A2.RowMajor (nr, nc, fn (r, c) => 10 * r + c)
    fun sample () = grid (3, 4)

    fun region (a, r, c, nr, nc) =
      { base = a, row = r, col = c, nrows = nr, ncols = nc }

    fun wholeOf a = region (a, 0, 0, NONE, NONE)

    (* A recorder for the traversals: appi and friends are specified to visit
     * the entries in a particular order, and the only way to check an order is
     * to write down what was seen. *)
    fun collect f =
      let
        val seen = ref ([] : (int * int * int) list)
      in
        f (fn x => seen := x :: !seen);
        List.rev (!seen)
      end
    fun triples ts = List.map (fn (r, c, x) => [r, c, x]) ts

    (* The two traversals hand over the same entries in different orders, so
     * comparing them means comparing multisets; sorting is the cheapest way
     * to say that here. *)
    fun sortInts xs =
      let
        fun insert (x, []) = [x]
          | insert (x, y :: ys) =
              if x <= y then x :: y :: ys else y :: insert (x, ys)
      in
        List.foldl insert [] xs
      end
    val eqTriples = A.eqBy (op =, Show.list Show.intList)

    (* --- generators --------------------------------------------------- *)

    val genDims = G.pair (G.int (1, 6), G.int (1, 6))

    val genArray = G.map grid genDims

    (* An array together with a legal index into it. *)
    val genIndexed =
      G.bind genDims (fn (nr, nc) =>
        G.map (fn (r, c) => (nr, nc, r, c))
              (G.pair (G.int (0, nr - 1), G.int (0, nc - 1))))
    val showIndexed =
      fn (nr, nc, r, c) => Show.list Show.int [nr, nc, r, c]

    (* An array and a region entirely inside it. *)
    val genRegion =
      G.bind genDims (fn (nr, nc) =>
        G.bind (G.pair (G.int (0, nr - 1), G.int (0, nc - 1))) (fn (r, c) =>
          G.map (fn (dr, dc) => (nr, nc, r, c, dr, dc))
                (G.pair (G.int (0, nr - r), G.int (0, nc - c)))))
    val showRegion =
      fn (nr, nc, r, c, dr, dc) => Show.list Show.int [nr, nc, r, c, dr, dc]

    val suite = Group ("Array2",
      [ Case ("array fills every entry with the same value", fn () =>
          let
            val a = A2.array (2, 3, 7)
          in
            A.eqInt "nRows" (2, A2.nRows a);
            A.eqInt "nCols" (3, A2.nCols a);
            A.eqBy (op =, Show.pair (Show.int, Show.int)) "dimensions"
              ((2, 3), A2.dimensions a);
            eqIIL "contents" ([[7, 7, 7], [7, 7, 7]], rows a)
          end),

        Case ("an array may have no entries", fn () =>
          (A.eqInt "no rows" (0, A2.nRows (A2.array (0, 3, 0)));
           A.eqInt "no columns" (0, A2.nCols (A2.array (3, 0, 0)));
           eqIIL "and holds nothing" ([], rows (A2.array (0, 3, 0))))),

        (* array (r, c, init) is specified to build an r by c array, so a zero
         * in one dimension does not erase the other.  Implementations differ
         * here, which is why it is its own case rather than a clause of the
         * one above. *)
        Case ("a zero dimension does not forget the other one", fn () =>
          (A.eqBy (op =, Show.pair (Show.int, Show.int))
             "no rows, three columns"
             ((0, 3), A2.dimensions (A2.array (0, 3, 0)));
           A.eqBy (op =, Show.pair (Show.int, Show.int))
             "three rows, no columns"
             ((3, 0), A2.dimensions (A2.array (3, 0, 0))))),

        Case ("a negative dimension raises Size", fn () =>
          (A.raises "negative rows" A.isSize
             (fn () => A2.array (A.hide ~1, 3, 0));
           A.raises "negative columns" A.isSize
             (fn () => A2.array (3, A.hide ~1, 0)))),

        Case ("fromList reads a list of rows", fn () =>
          let
            val a = A2.fromList [[1, 2, 3], [4, 5, 6]]
          in
            A.eqInt "rows" (2, A2.nRows a);
            A.eqInt "columns" (3, A2.nCols a);
            eqIIL "contents" ([[1, 2, 3], [4, 5, 6]], rows a);
            A.eqInt "the first index is the row" (4, A2.sub (a, 1, 0))
          end),

        Case ("fromList of unequal rows raises Size", fn () =>
          A.raises "a short row" A.isSize
            (fn () => A2.fromList [[1, 2, 3], A.hideVal [4, 5]])),

        Case ("fromList of an empty list", fn () =>
          let
            val a = A2.fromList []
          in
            A.eqInt "no rows" (0, A2.nRows a);
            A.eqInt "no columns" (0, A2.nCols a)
          end),

        Case ("tabulate is called for every entry", fn () =>
          (eqIIL "row major"
             ([[0, 1, 2], [10, 11, 12]],
              rows (A2.tabulate A2.RowMajor (2, 3, fn (r, c) => 10 * r + c)));
           eqIIL "column major gives the same array"
             ([[0, 1, 2], [10, 11, 12]],
              rows (A2.tabulate A2.ColMajor (2, 3, fn (r, c) => 10 * r + c))))),

        Case ("tabulate visits in the order it is told", fn () =>
          let
            fun order t =
              let val seen = ref ([] : (int * int) list)
              in
                ignore (A2.tabulate t (2, 3, fn rc => (seen := rc :: !seen; 0)));
                List.map (fn (r, c) => [r, c]) (List.rev (!seen))
              end
          in
            eqIIL "row major"
              ([[0,0],[0,1],[0,2],[1,0],[1,1],[1,2]], order A2.RowMajor);
            eqIIL "column major"
              ([[0,0],[1,0],[0,1],[1,1],[0,2],[1,2]], order A2.ColMajor)
          end),

        Case ("sub and update address the same entry", fn () =>
          let
            val a = sample ()
          in
            A.eqInt "sub" (12, A2.sub (a, 1, 2));
            A2.update (a, 1, 2, 99);
            A.eqInt "after update" (99, A2.sub (a, 1, 2));
            A.eqInt "a neighbour in the same row" (13, A2.sub (a, 1, 3));
            A.eqInt "a neighbour in the same column" (22, A2.sub (a, 2, 2))
          end),

        Case ("sub out of range raises Subscript", fn () =>
          let
            val a = sample ()
          in
            A.raises "a negative row" A.isSubscript
              (fn () => A2.sub (a, A.hide ~1, 0));
            A.raises "a negative column" A.isSubscript
              (fn () => A2.sub (a, 0, A.hide ~1));
            A.raises "a row past the end" A.isSubscript
              (fn () => A2.sub (a, A.hide 3, 0));
            A.raises "a column past the end" A.isSubscript
              (fn () => A2.sub (a, 0, A.hide 4));
            (* The two dimensions are not interchangeable: an index legal for
             * the columns need not be legal for the rows. *)
            A.raises "the column bound applied to the row" A.isSubscript
              (fn () => A2.sub (a, A.hide 3, 3))
          end),

        Case ("update out of range raises Subscript", fn () =>
          let
            val a = sample ()
          in
            A.raises "a negative row" A.isSubscript
              (fn () => A2.update (a, A.hide ~1, 0, 0));
            A.raises "a row past the end" A.isSubscript
              (fn () => A2.update (a, A.hide 3, 0, 0));
            A.raises "a column past the end" A.isSubscript
              (fn () => A2.update (a, 0, A.hide 4, 0));
            eqA "and the array is unchanged" (sample (), a)
          end),

        Case ("row and column extract vectors", fn () =>
          let
            val a = sample ()
          in
            eqIL "a row" ([10, 11, 12, 13],
                          Vector.foldr (op ::) [] (A2.row (a, 1)));
            eqIL "a column" ([2, 12, 22],
                             Vector.foldr (op ::) [] (A2.column (a, 2)));
            A.eqInt "a row is as long as there are columns"
              (4, Vector.length (A2.row (a, 0)));
            A.eqInt "a column is as long as there are rows"
              (3, Vector.length (A2.column (a, 0)));
            A.raises "row out of range" A.isSubscript
              (fn () => A2.row (a, A.hide 3));
            A.raises "column out of range" A.isSubscript
              (fn () => A2.column (a, A.hide 4))
          end),

        Case ("app visits every entry in the given order", fn () =>
          let
            fun order t =
              let val seen = ref ([] : int list)
              in A2.app t (fn x => seen := x :: !seen) (grid (2, 3));
                 List.rev (!seen)
              end
          in
            eqIL "row major" ([0, 1, 2, 10, 11, 12], order A2.RowMajor);
            eqIL "column major" ([0, 10, 1, 11, 2, 12], order A2.ColMajor)
          end),

        Case ("appi reports the index of each entry", fn () =>
          let
            val a = grid (2, 2)
            fun order t = triples (collect (fn f => A2.appi t f (wholeOf a)))
          in
            eqTriples "row major"
              ([[0,0,0],[0,1,1],[1,0,10],[1,1,11]], order A2.RowMajor);
            eqTriples "column major"
              ([[0,0,0],[1,0,10],[0,1,1],[1,1,11]], order A2.ColMajor)
          end),

        Case ("appi over a region visits only that region", fn () =>
          let
            val a = sample ()
            val seen =
              triples (collect (fn f =>
                A2.appi A2.RowMajor f (region (a, 1, 1, SOME 2, SOME 2))))
          in
            eqTriples "the indices are the array's, not the region's"
              ([[1,1,11],[1,2,12],[2,1,21],[2,2,22]], seen)
          end),

        Case ("a region's extents default to the edge of the array", fn () =>
          let
            val a = sample ()
            fun count reg =
              List.length (collect (fn f => A2.appi A2.RowMajor f reg))
          in
            A.eqInt "the whole array" (12, count (wholeOf a));
            (* Rows 1 and 2, columns 2 and 3. *)
            A.eqInt "from an interior origin"
              (4, count (region (a, 1, 2, NONE, NONE)));
            A.eqInt "with only the row count given"
              (4, count (region (a, 1, 2, SOME 2, NONE)));
            A.eqInt "with only the column count given"
              (2, count (region (a, 1, 2, NONE, SOME 1)))
          end),

        (* SOME 0 and NONE are different answers: one asks for no rows at
         * all, the other for every row to the edge.  Reading the first as the
         * second makes an empty region silently traverse the array. *)
        Case ("an extent of zero is empty, not defaulted", fn () =>
          let
            val a = sample ()
            fun count reg =
              A2.foldi A2.RowMajor (fn (_, _, _, n) => n + 1) 0 reg
          in
            A.eqInt "no rows" (0, count (region (a, 0, 0, SOME 0, SOME 4)));
            A.eqInt "no columns" (0, count (region (a, 0, 0, SOME 3, SOME 0)));
            A.eqInt "neither" (0, count (region (a, 1, 1, SOME 0, SOME 0)));
            A.eqInt "no rows, columns left to default"
              (0, count (region (a, 0, 0, SOME 0, NONE)))
          end),

        Case ("a region that runs off the array raises Subscript", fn () =>
          let
            val a = sample ()
            fun visit reg = A2.appi A2.RowMajor (fn _ => ()) reg
          in
            A.raises "too many rows" A.isSubscript
              (fn () => visit (region (a, 1, 0, SOME (A.hide 3), NONE)));
            A.raises "too many columns" A.isSubscript
              (fn () => visit (region (a, 0, 2, NONE, SOME (A.hide 3))));
            A.raises "a negative origin" A.isSubscript
              (fn () => visit (region (a, A.hide ~1, 0, NONE, NONE)));
            A.raises "an origin past the end" A.isSubscript
              (fn () => visit (region (a, A.hide 4, 0, NONE, NONE)));
            A.noRaise "an origin at the far edge with an empty extent"
              (fn () => visit (region (a, 3, 4, SOME 0, SOME 0)))
          end),

        Case ("fold accumulates in the given order", fn () =>
          let
            val a = grid (2, 3)
            fun seq t = List.rev (A2.fold t (op ::) [] a)
          in
            eqIL "row major" ([0, 1, 2, 10, 11, 12], seq A2.RowMajor);
            eqIL "column major" ([0, 10, 1, 11, 2, 12], seq A2.ColMajor);
            A.eqInt "the sum does not depend on the order"
              (A2.fold A2.RowMajor (op +) 0 a, A2.fold A2.ColMajor (op +) 0 a)
          end),

        Case ("foldi folds over a region with indices", fn () =>
          let
            val a = sample ()
            val total =
              A2.foldi A2.RowMajor (fn (r, c, x, acc) => acc + r + c + x) 0
                       (region (a, 1, 1, SOME 2, SOME 2))
          in
            (* (11+1+1) + (12+1+2) + (21+2+1) + (22+2+2) *)
            A.eqInt "sum over the region" (78, total)
          end),

        Case ("modify replaces every entry", fn () =>
          let
            val a = grid (2, 3)
          in
            A2.modify A2.RowMajor (fn x => x + 1) a;
            eqIIL "each entry moved on" ([[1, 2, 3], [11, 12, 13]], rows a)
          end),

        Case ("modifyi replaces only the region", fn () =>
          let
            val a = sample ()
          in
            A2.modifyi A2.RowMajor (fn (r, c, x) => x + 1000)
                       (region (a, 1, 1, SOME 1, SOME 2));
            eqIIL "the rest is untouched"
              ([[0, 1, 2, 3], [10, 1011, 1012, 13], [20, 21, 22, 23]],
               rows a)
          end),

        Case ("copy moves a region within one array", fn () =>
          let
            val a = sample ()
          in
            A2.copy { src = region (a, 0, 0, SOME 1, SOME 4),
                      dst = a, dst_row = 2, dst_col = 0 };
            eqIIL "the first row overwrote the last"
              ([[0, 1, 2, 3], [10, 11, 12, 13], [0, 1, 2, 3]], rows a)
          end),

        Case ("copy between arrays", fn () =>
          let
            val src = sample ()
            val dst = A2.array (3, 4, 0)
          in
            A2.copy { src = region (src, 1, 1, SOME 2, SOME 2),
                      dst = dst, dst_row = 0, dst_col = 2 };
            eqIIL "placed at the destination corner"
              ([[0, 0, 11, 12], [0, 0, 21, 22], [0, 0, 0, 0]], rows dst)
          end),

        (* Overlap within one array is the case a naive implementation gets
         * wrong: copying a block one row down must not read entries it has
         * already written. *)
        Case ("copy handles overlapping regions", fn () =>
          let
            val a = sample ()
          in
            A2.copy { src = region (a, 0, 0, SOME 2, SOME 4),
                      dst = a, dst_row = 1, dst_col = 0 };
            eqIIL "the block moved down one row"
              ([[0, 1, 2, 3], [0, 1, 2, 3], [10, 11, 12, 13]], rows a)
          end),

        Case ("copy off the destination raises Subscript", fn () =>
          let
            val a = sample ()
            val dst = A2.array (2, 2, 0)
          in
            A.raises "the region does not fit" A.isSubscript
              (fn () => A2.copy { src = wholeOf a, dst = dst,
                                  dst_row = A.hide 0, dst_col = 0 });
            A.raises "a negative destination" A.isSubscript
              (fn () => A2.copy { src = region (a, 0, 0, SOME 1, SOME 1),
                                  dst = dst, dst_row = A.hide ~1, dst_col = 0 })
          end),

        P.forAll ("tabulate agrees with sub at every index",
                  genIndexed, showIndexed,
                  fn (nr, nc, r, c) => A2.sub (grid (nr, nc), r, c) = 10 * r + c),

        P.forAll ("dimensions agrees with nRows and nCols", genArray, showA,
                  fn a => A2.dimensions a = (A2.nRows a, A2.nCols a)),

        P.forAll ("update is visible through sub", genIndexed, showIndexed,
                  fn (nr, nc, r, c) =>
                    let val a = grid (nr, nc)
                    in A2.update (a, r, c, ~1); A2.sub (a, r, c) = ~1 end),

        P.forAll ("update changes exactly one entry", genIndexed, showIndexed,
                  fn (nr, nc, r, c) =>
                    let
                      val a = grid (nr, nc)
                      val () = A2.update (a, r, c, ~1)
                    in
                      List.all
                        (fn (r', c') =>
                           (r' = r andalso c' = c)
                           orelse A2.sub (a, r', c') = 10 * r' + c')
                        (List.concat
                           (List.tabulate (nr, fn r' =>
                              List.tabulate (nc, fn c' => (r', c')))))
                    end),

        P.forAll ("row and column agree with sub", genIndexed, showIndexed,
                  fn (nr, nc, r, c) =>
                    let val a = grid (nr, nc)
                    in Vector.sub (A2.row (a, r), c) = A2.sub (a, r, c)
                       andalso Vector.sub (A2.column (a, c), r) = A2.sub (a, r, c)
                    end),

        P.forAll ("both traversals see the same entries", genArray, showA,
                  fn a =>
                    sortInts (A2.fold A2.RowMajor (op ::) [] a)
                    = sortInts (A2.fold A2.ColMajor (op ::) [] a)),

        P.forAll ("fold visits every entry once", genArray, showA,
                  fn a =>
                    A2.fold A2.RowMajor (fn (_, n) => n + 1) 0 a
                    = A2.nRows a * A2.nCols a),

        P.forAll ("appi over the whole array reports every index",
                  genArray, showA,
                  fn a =>
                    let
                      val seen = collect (fn f => A2.appi A2.RowMajor f (wholeOf a))
                    in
                      List.all (fn (r, c, x) => x = A2.sub (a, r, c)) seen
                      andalso List.length seen = A2.nRows a * A2.nCols a
                    end),

        P.forAll ("a region's extents may be given or left to default",
                  genRegion, showRegion,
                  fn (nr, nc, r, c, dr, dc) =>
                    let
                      val a = grid (nr, nc)
                      fun count reg =
                        A2.foldi A2.RowMajor (fn (_, _, _, n) => n + 1) 0 reg
                    in
                      count (region (a, r, c, SOME dr, SOME dc)) = dr * dc
                      andalso count (region (a, r, c, NONE, NONE))
                              = (nr - r) * (nc - c)
                    end),

        P.forAll ("copy of the whole array reproduces it", genArray, showA,
                  fn a =>
                    let
                      val b = A2.array (A2.nRows a, A2.nCols a, 0)
                    in
                      A2.copy { src = wholeOf a, dst = b,
                                dst_row = 0, dst_col = 0 };
                      rows a = rows b
                    end),

        P.forAll ("modify agrees with tabulate over the same function",
                  genArray, showA,
                  fn a =>
                    let
                      val b = A2.tabulate A2.RowMajor
                                (A2.nRows a, A2.nCols a,
                                 fn (r, c) => A2.sub (a, r, c) + 1)
                    in
                      A2.modify A2.RowMajor (fn x => x + 1) a;
                      rows a = rows b
                    end)
      ])
  end
