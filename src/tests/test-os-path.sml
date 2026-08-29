(* Tests for OS.Path.
 *
 * OS.Path is entirely syntactic -- it never touches the file system -- so it
 * can be tested anywhere.  What it cannot be is host-independent: the
 * separator, the notion of a volume and the spelling of the root all differ.
 * The concrete string expectations therefore live in two groups selected by
 * C.pathStyle, and everything that can be stated without naming a separator
 * is stated as a law that runs on both.
 *)

functor OSPathTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop
    structure Path = OS.Path

    val isUnix = (C.pathStyle = PathStyle.UNIX)
    val isWindows = (C.pathStyle = PathStyle.WINDOWS)

    val showDF = fn { dir, file } => "{dir=" ^ Show.string dir
                                     ^ ", file=" ^ Show.string file ^ "}"
    val eqDF = A.eqBy (op =, showDF)

    val showBE = fn { base, ext } =>
      "{base=" ^ Show.string base ^ ", ext=" ^ Show.option Show.string ext ^ "}"
    val eqBE = A.eqBy (op =, showBE)

    (* Arcs made only of letters and digits, so that they are legal on every
     * host and never collide with a separator or an extension marker. *)
    val arc = G.map String.implode (G.list1 G.alphaNumChar)
    val arcs = G.bind (G.int (1, 4)) (fn n => G.listN n arc)
    val relPath = G.map (fn a => Path.toString { isAbs = false, vol = "", arcs = a }) arcs
    val showS = Show.string

    val suite = Group ("OS.Path",
      [ Group ("the special arcs",
        [ Case ("currentArc and parentArc", fn () =>
            (A.eqString "current" (".", Path.currentArc);
             A.eqString "parent" ("..", Path.parentArc)))
        ]),

        Group ("Unix syntax",
          onlyIf (isUnix, "configured for a different path style")
          [ Case ("concat joins with a slash", fn () =>
              (A.eqString "two arcs" ("a/b", Path.concat ("a", "b"));
               A.eqString "onto a directory" ("a/b/c", Path.concat ("a/b", "c"));
               A.eqString "onto the root" ("/b", Path.concat ("/", "b")))),

            Case ("splitDirFile", fn () =>
              (eqDF "nested" ({ dir = "a", file = "b" }, Path.splitDirFile "a/b");
               eqDF "bare name" ({ dir = "", file = "b" }, Path.splitDirFile "b");
               eqDF "at the root" ({ dir = "/", file = "b" }, Path.splitDirFile "/b");
               eqDF "trailing slash means an empty file part"
                 ({ dir = "a", file = "" }, Path.splitDirFile "a/"))),

            Case ("dir and file", fn () =>
              (A.eqString "dir" ("a", Path.dir "a/b");
               A.eqString "file" ("b", Path.file "a/b"))),

            Case ("joinDirFile", fn () =>
              (A.eqString "nested"
                 ("a/b", Path.joinDirFile { dir = "a", file = "b" });
               A.eqString "empty directory"
                 ("b", Path.joinDirFile { dir = "", file = "b" }))),

            Case ("isAbsolute and isRelative", fn () =>
              (A.eqBool "leading slash is absolute" (true, Path.isAbsolute "/a");
               A.eqBool "the root is absolute" (true, Path.isAbsolute "/");
               A.eqBool "a bare name is relative" (true, Path.isRelative "a");
               A.eqBool "a dot path is relative" (true, Path.isRelative "./a"))),

            Case ("getVolume is empty on Unix", fn () =>
              (A.eqString "absolute" ("", Path.getVolume "/a");
               A.eqString "relative" ("", Path.getVolume "a"))),

            Case ("fromString", fn () =>
              (A.that "absolute"
                 (Path.fromString "/a/b"
                  = { isAbs = true, vol = "", arcs = ["a", "b"] });
               A.that "relative"
                 (Path.fromString "a/b"
                  = { isAbs = false, vol = "", arcs = ["a", "b"] }))),

            Case ("toString", fn () =>
              (A.eqString "absolute"
                 ("/a/b", Path.toString { isAbs = true, vol = "",
                                          arcs = ["a", "b"] });
               A.eqString "relative"
                 ("a/b", Path.toString { isAbs = false, vol = "",
                                         arcs = ["a", "b"] }))),

            Case ("mkCanonical removes redundant arcs", fn () =>
              (A.eqString "a current arc" ("a/b", Path.mkCanonical "a/./b");
               A.eqString "a parent arc" ("a/c", Path.mkCanonical "a/b/../c");
               A.eqString "a trailing slash" ("a/b", Path.mkCanonical "a/b/");
               A.eqString "the empty path becomes the current directory"
                 (".", Path.mkCanonical "");
               A.eqString "the parent of the root is the root"
                 ("/", Path.mkCanonical "/.."))),

            Case ("mkAbsolute and mkRelative", fn () =>
              (A.eqString "made absolute"
                 ("/a/b", Path.mkAbsolute { path = "b", relativeTo = "/a" });
               A.eqString "an absolute path is left alone"
                 ("/c", Path.mkAbsolute { path = "/c", relativeTo = "/a" });
               A.eqString "made relative"
                 ("b", Path.mkRelative { path = "/a/b", relativeTo = "/a" }))),

            Case ("splitBaseExt", fn () =>
              (eqBE "one extension"
                 ({ base = "a", ext = SOME "b" }, Path.splitBaseExt "a.b");
               eqBE "no extension"
                 ({ base = "a", ext = NONE }, Path.splitBaseExt "a");
               eqBE "only the last dot counts"
                 ({ base = "a.b", ext = SOME "c" }, Path.splitBaseExt "a.b.c");
               eqBE "a leading dot is not an extension"
                 ({ base = ".b", ext = NONE }, Path.splitBaseExt ".b");
               (* A trailing dot leaves nothing after it, and an empty
                * extension is reported as no extension at all. *)
               eqBE "a trailing dot is not an extension"
                 ({ base = "a.", ext = NONE }, Path.splitBaseExt "a."))),

            Case ("joinBaseExt", fn () =>
              (A.eqString "with an extension"
                 ("a.b", Path.joinBaseExt { base = "a", ext = SOME "b" });
               A.eqString "without one"
                 ("a", Path.joinBaseExt { base = "a", ext = NONE })))
          ]),

        Group ("Windows syntax",
          onlyIf (isWindows, "configured for a different path style")
          [ Case ("concat joins with a backslash", fn () =>
              A.eqString "two arcs" ("a\\b", Path.concat ("a", "b"))),

            Case ("a volume is recognised", fn () =>
              (A.eqString "drive letter" ("C:", Path.getVolume "C:\\a");
               A.eqBool "a rooted path with a volume is absolute"
                 (true, Path.isAbsolute "C:\\a"))),

            Case ("validVolume", fn () =>
              (A.eqBool "a drive letter is a valid absolute volume"
                 (true, Path.validVolume { isAbs = true, vol = "C:" });
               A.eqBool "the empty volume is valid for a relative path"
                 (true, Path.validVolume { isAbs = false, vol = "" })))
          ]),

        Group ("errors",
        [ Case ("concat rejects an absolute second argument", fn () =>
            A.raises "absolute" A.isPath
              (fn () => Path.concat ("a", Path.toString { isAbs = true, vol = "",
                                                          arcs = ["b"] }))),

          Case ("mkAbsolute requires an absolute base", fn () =>
            A.raises "relative base" A.isPath
              (fn () => Path.mkAbsolute { path = "b", relativeTo = "a" })),

          Case ("mkRelative requires an absolute base", fn () =>
            A.raises "relative base" A.isPath
              (fn () => Path.mkRelative { path = "b", relativeTo = "a" })),

          Case ("toString rejects an arc containing a separator", fn () =>
            A.raises "embedded separator" A.isInvalidArc
              (fn () =>
                 Path.toString { isAbs = false, vol = "",
                                 arcs = [Path.concat ("x", "y")] }))
        ]),

        Group ("laws",
        [ P.forAll ("toString inverts fromString on paths it produced",
                    relPath, showS,
                    fn p => Path.toString (Path.fromString p) = p),

          P.forAll ("fromString recovers the arcs it was given", arcs,
                    Show.list showS,
                    fn a =>
                      let
                        val p = Path.toString { isAbs = false, vol = "", arcs = a }
                        val { arcs = a', ... } = Path.fromString p
                      in
                        a' = a
                      end),

          P.forAll ("absoluteness survives a round trip", arcs, Show.list showS,
                    fn a =>
                      let
                        fun round isAbs =
                          let
                            val p = Path.toString { isAbs = isAbs, vol = "", arcs = a }
                            val { isAbs = b, ... } = Path.fromString p
                          in
                            b = isAbs
                          end
                      in
                        round true andalso round false
                      end),

          P.forAll ("absolute and relative are complementary", relPath, showS,
                    fn p => Path.isAbsolute p = not (Path.isRelative p)),

          P.forAll ("joinDirFile inverts splitDirFile", relPath, showS,
                    fn p => Path.joinDirFile (Path.splitDirFile p) = p),

          P.forAll ("dir and file are the two halves of splitDirFile",
                    relPath, showS,
                    fn p =>
                      let val { dir, file } = Path.splitDirFile p
                      in Path.dir p = dir andalso Path.file p = file end),

          P.forAll ("joinBaseExt inverts splitBaseExt", relPath, showS,
                    fn p => Path.joinBaseExt (Path.splitBaseExt p) = p),

          P.forAll ("base and ext are the two halves of splitBaseExt",
                    relPath, showS,
                    fn p =>
                      let val { base, ext } = Path.splitBaseExt p
                      in Path.base p = base andalso Path.ext p = ext end),

          P.forAll ("splitBaseExt then joinBaseExt with a fresh extension",
                    G.pair (relPath, arc), Show.pair (showS, showS),
                    fn (p, e) =>
                      let
                        val { base, ... } = Path.splitBaseExt p
                        val joined = Path.joinBaseExt { base = base, ext = SOME e }
                      in
                        Path.ext joined = SOME e
                      end),

          P.forAll ("mkCanonical is idempotent", relPath, showS,
                    fn p => Path.mkCanonical (Path.mkCanonical p)
                            = Path.mkCanonical p),

          P.forAll ("a path built from clean arcs is already canonical",
                    relPath, showS,
                    fn p => Path.mkCanonical p = p),

          P.forAll ("concat appends an arc",
                    G.pair (relPath, arc), Show.pair (showS, showS),
                    fn (p, a) =>
                      let
                        val { arcs = pa, ... } = Path.fromString p
                        val { arcs = ca, ... } = Path.fromString (Path.concat (p, a))
                      in
                        ca = pa @ [a]
                      end),

          P.forAll ("concatenating then taking the file gives the arc back",
                    G.pair (relPath, arc), Show.pair (showS, showS),
                    fn (p, a) => Path.file (Path.concat (p, a)) = a),

          P.forAll ("mkAbsolute then mkRelative round trips",
                    G.pair (relPath, arcs), Show.pair (showS, Show.list showS),
                    fn (p, base) =>
                      let
                        val root = Path.toString { isAbs = true, vol = "", arcs = base }
                        val abs = Path.mkAbsolute { path = p, relativeTo = root }
                      in
                        Path.isAbsolute abs
                        andalso Path.mkRelative { path = abs, relativeTo = root } = p
                      end),

          P.forAll ("making a path absolute makes it absolute",
                    G.pair (relPath, arcs), Show.pair (showS, Show.list showS),
                    fn (p, base) =>
                      Path.isAbsolute
                        (Path.mkAbsolute
                           { path = p,
                             relativeTo =
                               Path.toString { isAbs = true, vol = "", arcs = base } }))
        ])
      ])
  end
