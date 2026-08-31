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
                 ("a", Path.joinBaseExt { base = "a", ext = NONE }))),

            (* "Note that although splitBaseExt will never return the
             * extension SOME(""), joinBaseExt treats this as equivalent to
             * NONE." *)
            Case ("joinBaseExt treats an empty extension as none", fn () =>
              A.eqString "an empty extension"
                (Path.joinBaseExt { base = "a", ext = NONE },
                 Path.joinBaseExt { base = "a", ext = SOME "" })),

            (* The example table for fromString. *)
            Case ("the fromString examples from the specification", fn () =>
              let
                val show = fn { isAbs, vol, arcs } =>
                  "{isAbs=" ^ Show.bool isAbs ^ ", vol=" ^ Show.string vol
                  ^ ", arcs=" ^ Show.stringList arcs ^ "}"
                val eq = A.eqBy (op =, show)
                fun check (p, expected) =
                  eq (Show.string p) (expected, Path.fromString p)
              in
                List.app check
                  [("", { isAbs = false, vol = "", arcs = [] }),
                   ("/", { isAbs = true, vol = "", arcs = [""] }),
                   ("//", { isAbs = true, vol = "", arcs = ["", ""] }),
                   ("a", { isAbs = false, vol = "", arcs = ["a"] }),
                   ("/a", { isAbs = true, vol = "", arcs = ["a"] }),
                   ("//a", { isAbs = true, vol = "", arcs = ["", "a"] }),
                   ("a/", { isAbs = false, vol = "", arcs = ["a", ""] }),
                   ("a//", { isAbs = false, vol = "", arcs = ["a", "", ""] }),
                   ("a/b", { isAbs = false, vol = "", arcs = ["a", "b"] })]
              end),

            (* The example table for getParent. *)
            Case ("the getParent examples from the specification", fn () =>
              List.app
                (fn (p, expected) =>
                   A.eqString ("getParent " ^ Show.string p)
                     (expected, Path.getParent p))
                [("/", "/"), ("a", "."), ("a/", "a/.."), ("a///", "a///.."),
                 ("a/b", "a"), ("a/b/", "a/b/.."), ("..", "../.."),
                 (".", ".."), ("", "..")]),

            (* The example table for splitDirFile. *)
            Case ("the splitDirFile examples from the specification", fn () =>
              List.app
                (fn (p, expected) =>
                   eqDF ("splitDirFile " ^ Show.string p)
                     (expected, Path.splitDirFile p))
                [("", { dir = "", file = "" }),
                 (".", { dir = "", file = "." }),
                 ("b", { dir = "", file = "b" }),
                 ("b/", { dir = "b", file = "" }),
                 ("a/b", { dir = "a", file = "b" }),
                 ("/a", { dir = "/", file = "a" })]),

            (* The example table for splitBaseExt. *)
            Case ("the splitBaseExt examples from the specification", fn () =>
              List.app
                (fn (p, expected) =>
                   eqBE ("splitBaseExt " ^ Show.string p)
                     (expected, Path.splitBaseExt p))
                [("", { base = "", ext = NONE }),
                 (".login", { base = ".login", ext = NONE }),
                 ("/.login", { base = "/.login", ext = NONE }),
                 ("a", { base = "a", ext = NONE }),
                 ("a.", { base = "a.", ext = NONE }),
                 ("a.b", { base = "a", ext = SOME "b" }),
                 ("a.b.c", { base = "a.b", ext = SOME "c" }),
                 (".news/comp", { base = ".news/comp", ext = NONE })]),

            (* The example table for mkRelative. *)
            Case ("the mkRelative examples from the specification", fn () =>
              List.app
                (fn (path, relativeTo, expected) =>
                   A.eqString ("mkRelative " ^ Show.string path ^ " to "
                               ^ Show.string relativeTo)
                     (expected,
                      Path.mkRelative { path = path, relativeTo = relativeTo }))
                [("a/b", "/c/d", "a/b"),
                 ("/", "/a/b/c", "../../.."),
                 ("/a/b/", "/a/c", "../b/"),
                 ("/a/b", "/a/c", "../b"),
                 ("/a/b/", "/a/c/", "../b/"),
                 ("/a/b", "/a/c/", "../b"),
                 ("/", "/", "."),
                 ("/", "/.", "."),
                 ("/", "/..", "."),
                 ("/a/b/../c", "/a/d", "../b/../c"),
                 ("/a/b", "/c/d", "../../a/b"),
                 ("/c/a/b", "/c/d", "../a/b"),
                 ("/c/d/a/b", "/c/d", "a/b")]),

            (* "concat does not preserve canonical paths.  For example,
             * concat("a/b", "../c") returns "a/b/../c"." *)
            Case ("concat is syntactic, not canonical", fn () =>
              (A.eqString "a parent arc is kept"
                 ("a/b/../c", Path.concat ("a/b", "../c"));
               (* concatArcs "is like List.@, except that a trailing empty arc
                * in the first argument is dropped". *)
               A.eqString "a trailing separator is not doubled"
                 ("a/b", Path.concat ("a/", "b"));
               A.eqString "onto the current directory"
                 ("./b", Path.concat (".", "b")))),

            (* "It returns "" when applied to
             * {isAbs=false, vol="", arcs=[]}." *)
            Case ("toString of the empty path", fn () =>
              A.eqString "the empty path"
                ("", Path.toString { isAbs = false, vol = "", arcs = [] })),

            (* "The exception Path is raised ... if isAbs is false and arcs
             * has an initial empty arc." *)
            Case ("toString rejects a relative path with a leading empty arc",
              fn () =>
                A.raises "leading empty arc" A.isPath
                  (fn () => Path.toString { isAbs = false, vol = "",
                                            arcs = ["", "a"] })),

            (* "Under Unix, the only valid volume name is ""." *)
            Case ("validVolume on Unix", fn () =>
              (A.eqBool "the empty volume, absolute"
                 (true, Path.validVolume { isAbs = true, vol = "" });
               A.eqBool "the empty volume, relative"
                 (true, Path.validVolume { isAbs = false, vol = "" });
               A.eqBool "anything else"
                 (false, Path.validVolume { isAbs = false, vol = "C:" }))),

            Case ("joinDirFile rejects a file that is not an arc", fn () =>
              A.raises "an embedded separator" A.isInvalidArc
                (fn () => Path.joinDirFile { dir = "a", file = "b/c" })),

            Case ("isRoot only accepts the canonical root", fn () =>
              (A.eqBool "the root" (true, Path.isRoot "/");
               A.eqBool "a doubled separator is not canonical"
                 (false, Path.isRoot "//");
               A.eqBool "nor is a current arc" (false, Path.isRoot "/.");
               A.eqBool "the empty path" (false, Path.isRoot "")))
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

        Group ("canonical form and roots",
        [ Case ("isCanonical", fn () =>
            if not isUnix then ()
            else
              (A.eqBool "a plain path is canonical" (true, Path.isCanonical "a/b");
               A.eqBool "a current arc is not"
                 (false, Path.isCanonical "a/./b");
               A.eqBool "a trailing separator is not"
                 (false, Path.isCanonical "a/b/");
               A.eqBool "the root is canonical" (true, Path.isCanonical "/"))),

          Case ("getParent", fn () =>
            if not isUnix then ()
            else
              (A.eqString "of a nested path" ("/a", Path.getParent "/a/b");
               A.eqString "of a path just below the root"
                 ("/", Path.getParent "/a");
               A.eqString "the root is its own parent" ("/", Path.getParent "/");
               A.eqString "of a relative path" ("a", Path.getParent "a/b");
               A.eqString "of a bare name" (".", Path.getParent "a");
               A.eqString "of the current arc" ("..", Path.getParent "."))),

          Case ("isRoot", fn () =>
            if not isUnix then ()
            else
              (A.eqBool "the root" (true, Path.isRoot "/");
               A.eqBool "a path below it" (false, Path.isRoot "/a");
               A.eqBool "a relative path" (false, Path.isRoot "a"))),

          Case ("mkCanonical produces canonical paths", fn () =>
            List.app
              (fn p =>
                 A.eqBool ("mkCanonical " ^ Show.string p ^ " is canonical")
                   (true, Path.isCanonical (Path.mkCanonical p)))
              ["a/./b", "a/b/", "a/b/../c", "", "."]),

          (* The Unix-syntax conversions are identities on a Unix host and a
           * genuine translation elsewhere, so only the round trip is stated
           * in a host-independent way. *)
          Case ("fromUnixPath and toUnixPath", fn () =>
            if isUnix then
              (A.eqString "fromUnixPath is the identity here"
                 ("a/b", Path.fromUnixPath "a/b");
               A.eqString "and so is toUnixPath"
                 ("a/b", Path.toUnixPath "a/b"))
            else
              A.eqString "a Unix path converts and converts back"
                ("a/b", Path.toUnixPath (Path.fromUnixPath "a/b")))
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

          P.forAll ("getParent of a path with a parent drops the last arc",
                    G.pair (relPath, arc), Show.pair (showS, showS),
                    fn (p, a) =>
                      Path.mkCanonical (Path.getParent (Path.concat (p, a)))
                      = Path.mkCanonical p),

          P.forAll ("mkCanonical always yields a canonical path", relPath, showS,
                    fn p => Path.isCanonical (Path.mkCanonical p)),

          P.forAll ("a Unix path survives the round trip", relPath, showS,
                    fn p => Path.toUnixPath (Path.fromUnixPath p) = p),

          P.forAll ("only the root is a root", relPath, showS,
                    fn p => P.implies (Path.isRoot p, Path.isAbsolute p)),

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

          (* "It is equivalent to (path = mkCanonical path)." *)
          P.forAll ("isCanonical is equality with mkCanonical",
                    G.oneOf [relPath,
                             G.map (fn a => Path.toString
                                              { isAbs = true, vol = "",
                                                arcs = a }) arcs],
                    showS,
                    fn p => Path.isCanonical p = (p = Path.mkCanonical p)),

          (* "It holds that getParent path = path if and only if path is a
           * root." *)
          P.forAll ("only a root is its own parent",
                    G.oneOf [relPath,
                             G.map (fn a => Path.toString
                                              { isAbs = true, vol = "",
                                                arcs = a }) arcs],
                    showS,
                    fn p => (Path.getParent p = p) = Path.isRoot p),

          (* "In addition, isRelative(toString {isAbs=false, vol, arcs})
           * evaluates to true when defined." *)
          P.forAll ("a path built as relative is relative", arcs,
                    Show.list showS,
                    fn a =>
                      Path.isRelative
                        (Path.toString { isAbs = false, vol = "", arcs = a })),

          (* "They are equivalent to #dir o splitDirFile and
           * #file o splitDirFile", and the same for base and ext. *)
          P.forAll ("dir, file, base and ext are the projections",
                    relPath, showS,
                    fn p =>
                      Path.dir p = #dir (Path.splitDirFile p)
                      andalso Path.file p = #file (Path.splitDirFile p)
                      andalso Path.base p = #base (Path.splitBaseExt p)
                      andalso Path.ext p = #ext (Path.splitBaseExt p)),

          (* "if path and relativeTo are canonical, the result will be
           * canonical", for both mkAbsolute and mkRelative. *)
          P.forAll ("mkAbsolute of canonical paths is canonical",
                    G.pair (arcs, arcs), Show.pair (Show.list showS,
                                                    Show.list showS),
                    fn (a, b) =>
                      let
                        val rel = Path.toString { isAbs = false, vol = "",
                                                  arcs = a }
                        val base = Path.toString { isAbs = true, vol = "",
                                                   arcs = b }
                      in
                        P.implies (Path.isCanonical rel
                                   andalso Path.isCanonical base,
                                   Path.isCanonical
                                     (Path.mkAbsolute { path = rel,
                                                        relativeTo = base }))
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
