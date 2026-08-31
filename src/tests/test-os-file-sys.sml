(* Tests for OS.FileSys, OS.IO and the OS-level error values.
 *
 * These are the parts of OS that actually touch the host, so almost
 * everything here is gated on the configuration.  The tests create what they
 * need under the configured scratch directory and remove it again, and the
 * one test that changes the process's working directory restores it whatever
 * happens.
 *)

functor OSFileSysTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop
    structure FS = OS.FileSys

    val scratch = C.scratchDir
    fun scratchFile name = OS.Path.concat (scratch, name)
    fun ensureScratch () =
      if FS.access (scratch, []) then () else FS.mkDir scratch
    fun removeQuietly path = FS.remove path handle _ => ()
    fun rmDirQuietly path = FS.rmDir path handle _ => ()

    fun writeFile (path, contents) =
      let val outs = TextIO.openOut path
      in TextIO.output (outs, contents); TextIO.closeOut outs end

    fun readFile path =
      let val ins = TextIO.openIn path
      in TextIO.inputAll ins before TextIO.closeIn ins end

    (* Everything the file tests touch lives in one throwaway directory, made
     * fresh so that a leftover from an earlier run cannot affect the result. *)
    fun withTempDir name f =
      let
        val () = ensureScratch ()
        val dir = scratchFile name
        val () = if FS.access (dir, []) then () else FS.mkDir dir
        fun cleanup () =
          let
            val stream = FS.openDir dir
            fun drain acc =
              case FS.readDir stream of
                  NONE => acc
                | SOME e => drain (e :: acc)
            val entries = drain []
          in
            FS.closeDir stream;
            List.app (fn e => removeQuietly (OS.Path.concat (dir, e))) entries;
            rmDirQuietly dir
          end
      in
        (f dir; cleanup ()) handle e => (cleanup (); raise e)
      end

    val fsWhy = "no file system available"

    (* An iodesc for a real file, which is the only portable way to get one:
     * the primitive reader underneath a stream carries it. *)
    fun withFileDesc (path, f) =
      let
        val ins = TextIO.openIn path
        val (TextPrimIO.RD { ioDesc, ... }, _) =
          TextIO.StreamIO.getReader (TextIO.getInstream ins)
      in
        (f ioDesc; TextIO.closeIn ins handle _ => ())
        handle e => (TextIO.closeIn ins handle _ => (); raise e)
      end

    val suite = Group ("OS.FileSys",
      [ Group ("directories",
          onlyIf (C.hasFileSystem, fsWhy)
          [ Case ("getDir returns an absolute path", fn () =>
              let val d = FS.getDir ()
              in
                A.that "non-empty" (String.size d > 0);
                A.that "absolute" (OS.Path.isAbsolute d)
              end),

            Case ("mkDir, isDir and rmDir", fn () =>
              let
                val () = ensureScratch ()
                val dir = scratchFile "a-new-directory"
                val () = rmDirQuietly dir
              in
                FS.mkDir dir;
                A.eqBool "it exists" (true, FS.access (dir, []));
                A.eqBool "and is a directory" (true, FS.isDir dir);
                FS.rmDir dir;
                A.eqBool "and is gone afterwards" (false, FS.access (dir, []))
              end),

            Case ("isDir is false for a regular file", fn () =>
              withTempDir "isdir" (fn dir =>
                let val f = OS.Path.concat (dir, "plain.txt")
                in
                  writeFile (f, "x");
                  A.eqBool "a file is not a directory" (false, FS.isDir f)
                end)),

            Case ("mkDir fails when the directory is already there", fn () =>
              withTempDir "mkdir-twice" (fn dir =>
                A.raises "second mkDir" (fn OS.SysErr _ => true | _ => false)
                  (fn () => FS.mkDir dir))),

            Case ("reading a directory lists what is in it", fn () =>
              withTempDir "listing" (fn dir =>
                let
                  val () = writeFile (OS.Path.concat (dir, "one"), "1")
                  val () = writeFile (OS.Path.concat (dir, "two"), "2")
                  val stream = FS.openDir dir
                  fun drain acc =
                    case FS.readDir stream of
                        NONE => List.rev acc
                      | SOME e => drain (e :: acc)
                  val entries = drain []
                  val () = FS.closeDir stream
                in
                  A.eqInt "two entries" (2, List.length entries);
                  A.that "one is there" (List.exists (fn e => e = "one") entries);
                  A.that "two is there" (List.exists (fn e => e = "two") entries);
                  (* The Basis says the current and parent arcs are not
                   * reported. *)
                  A.that "the current arc is not listed"
                    (not (List.exists (fn e => e = OS.Path.currentArc) entries));
                  A.that "the parent arc is not listed"
                    (not (List.exists (fn e => e = OS.Path.parentArc) entries))
                end)),

            Case ("rewindDir starts the listing again", fn () =>
              withTempDir "rewind" (fn dir =>
                let
                  val () = writeFile (OS.Path.concat (dir, "only"), "x")
                  val stream = FS.openDir dir
                  val first = FS.readDir stream
                  val () = FS.rewindDir stream
                  val again = FS.readDir stream
                  val () = FS.closeDir stream
                in
                  A.eqStringOption "the same first entry" (first, again)
                end)),

            Case ("an empty directory has no entries", fn () =>
              withTempDir "empty-dir" (fn dir =>
                let
                  val stream = FS.openDir dir
                  val first = FS.readDir stream
                  val () = FS.closeDir stream
                in
                  A.eqStringOption "nothing to read" (NONE, first)
                end)),

            Case ("opening a directory that is not there", fn () =>
              A.raises "no such directory" (fn OS.SysErr _ => true | _ => false)
                (fn () => FS.openDir (scratchFile "no-such-directory"))),

            (* "Any subsequent read or rewind on the stream will raise
             * exception SysErr.  Closing a closed directory stream, however,
             * has no effect." *)
            Case ("a closed directory stream is unusable but may be closed again",
              fn () =>
                withTempDir "closedir" (fn dir =>
                  let
                    val stream = FS.openDir dir
                    val () = FS.closeDir stream
                  in
                    A.raises "reading after closing"
                      (fn OS.SysErr _ => true | _ => false)
                      (fn () => FS.readDir stream);
                    A.raises "rewinding after closing"
                      (fn OS.SysErr _ => true | _ => false)
                      (fn () => FS.rewindDir stream);
                    A.noRaise "closing twice" (fn () => FS.closeDir stream)
                  end)),

            (* "It raises SysErr if, for example, s does not exist ... or if
             * the directory is not empty." *)
            Case ("rmDir refuses what it cannot remove", fn () =>
              withTempDir "rmdir" (fn dir =>
                let
                  val inner = OS.Path.concat (dir, "inner")
                  val () = FS.mkDir inner
                  val () = writeFile (OS.Path.concat (inner, "f"), "x")
                in
                  A.raises "a directory that is not empty"
                    (fn OS.SysErr _ => true | _ => false)
                    (fn () => FS.rmDir inner);
                  A.raises "a directory that is not there"
                    (fn OS.SysErr _ => true | _ => false)
                    (fn () => FS.rmDir (OS.Path.concat (dir, "absent")));
                  removeQuietly (OS.Path.concat (inner, "f"));
                  rmDirQuietly inner
                end)),

            Case ("isDir rejects a path that is not there", fn () =>
              A.raises "no such file" (fn OS.SysErr _ => true | _ => false)
                (fn () => FS.isDir (scratchFile "no-such-thing-at-all"))),

            (* chDir changes process-wide state, so the original directory is
             * restored even if the assertions fail. *)
            Case ("chDir moves and getDir follows", fn () =>
              withTempDir "chdir" (fn dir =>
                let
                  val original = FS.getDir ()
                in
                  (FS.chDir dir;
                   A.that "the new directory ends with the one we asked for"
                     (String.isSuffix "chdir" (FS.getDir ()));
                   FS.chDir original)
                  handle e => (FS.chDir original; raise e);
                  A.eqString "and we are back" (original, FS.getDir ())
                end))
          ]),

        Group ("files",
          onlyIf (C.hasFileSystem, fsWhy)
          [ Case ("fileSize agrees with what was written", fn () =>
              withTempDir "size" (fn dir =>
                let val f = OS.Path.concat (dir, "sized")
                in
                  writeFile (f, "12345");
                  A.eqBy (op =, Position.toString) "five bytes"
                    (Position.fromInt 5, FS.fileSize f)
                end)),

            Case ("access reports the modes a new file has", fn () =>
              withTempDir "access" (fn dir =>
                let val f = OS.Path.concat (dir, "readable")
                in
                  writeFile (f, "x");
                  A.eqBool "it exists" (true, FS.access (f, []));
                  A.eqBool "and is readable" (true, FS.access (f, [FS.A_READ]));
                  A.eqBool "and writable" (true, FS.access (f, [FS.A_WRITE]));
                  A.eqBool "asking for two modes at once"
                    (true, FS.access (f, [FS.A_READ, FS.A_WRITE]));
                  (* Whether a plain file is executable is a property of the
                   * host, so only that the query answers is asserted. *)
                  A.noRaise "asking about execute permission"
                    (fn () => FS.access (f, [FS.A_EXEC]));
                  A.eqBool "a directory is readable" (true, FS.access (dir, [FS.A_READ]));
                  A.eqBool "an absent file is not accessible"
                    (false, FS.access (OS.Path.concat (dir, "absent"), []))
                end)),

            Case ("remove deletes", fn () =>
              withTempDir "remove" (fn dir =>
                let val f = OS.Path.concat (dir, "doomed")
                in
                  writeFile (f, "x");
                  FS.remove f;
                  A.eqBool "gone" (false, FS.access (f, []));
                  A.raises "removing it again" (fn OS.SysErr _ => true | _ => false)
                    (fn () => FS.remove f)
                end)),

            Case ("rename moves a file and its contents", fn () =>
              withTempDir "rename" (fn dir =>
                let
                  val a = OS.Path.concat (dir, "before")
                  val b = OS.Path.concat (dir, "after")
                in
                  writeFile (a, "payload");
                  FS.rename { old = a, new = b };
                  A.eqBool "the old name is gone" (false, FS.access (a, []));
                  A.eqBool "the new name is there" (true, FS.access (b, []));
                  A.eqString "contents survived" ("payload", readFile b)
                end)),

            Case ("modTime and setTime", fn () =>
              withTempDir "times" (fn dir =>
                let
                  val f = OS.Path.concat (dir, "timed")
                  val () = writeFile (f, "x")
                  val stamp = Time.fromSeconds (LargeInt.fromInt 1000000000)
                in
                  A.that "a fresh file has a modification time"
                    (Time.>= (FS.modTime f, Time.zeroTime));
                  FS.setTime (f, SOME stamp);
                  A.eqTime "the time we set" (stamp, FS.modTime f);
                  (* NONE means "now", which must be later than the stamp
                   * above. *)
                  FS.setTime (f, NONE);
                  A.that "setting to now moves it forward"
                    (Time.> (FS.modTime f, stamp))
                end)),

            Case ("fullPath makes a relative name absolute", fn () =>
              withTempDir "fullpath" (fn dir =>
                let
                  val f = OS.Path.concat (dir, "target")
                  val () = writeFile (f, "x")
                  val full = FS.fullPath f
                in
                  A.that "absolute" (OS.Path.isAbsolute full);
                  A.that "canonical" (OS.Path.isCanonical full);
                  A.eqString "and names the same file"
                    ("target", OS.Path.file full)
                end)),

            (* realPath is only required to yield a canonical path denoting
             * the same object; whether it is absolute follows its argument. *)
            Case ("realPath yields a canonical path to the same file", fn () =>
              withTempDir "realpath" (fn dir =>
                let
                  val f = OS.Path.concat (dir, "target")
                  val () = writeFile (f, "x")
                  val real = FS.realPath f
                in
                  A.that "canonical" (OS.Path.isCanonical real);
                  A.eqBool "and it exists" (true, FS.access (real, []));
                  A.eqOrder "and it is the same file"
                    (EQUAL, FS.compare (FS.fileId f, FS.fileId real));
                  A.eqBool "an absolute argument gives an absolute result"
                    (true, OS.Path.isAbsolute (FS.realPath (FS.fullPath f)))
                end)),

            Case ("fullPath of something absent raises", fn () =>
              A.raises "no such file" (fn OS.SysErr _ => true | _ => false)
                (fn () => FS.fullPath (scratchFile "not-here-at-all"))),

            Case ("tmpName produces a usable, fresh name", fn () =>
              let val n = FS.tmpName ()
              in
                A.that "non-empty" (String.size n > 0);
                A.that "two calls differ" (n <> FS.tmpName ())
              end),

            (* "This creates a new empty file with a unique name and returns
             * the full pathname of the file." *)
            Case ("tmpName creates the file it names", fn () =>
              let
                val n = FS.tmpName ()
              in
                A.eqBool "the file exists" (true, FS.access (n, []));
                A.eqBool "and is empty"
                  (true, FS.fileSize n = Position.fromInt 0);
                A.eqString "the name is absolute"
                  (n, OS.Path.mkAbsolute { path = n,
                                           relativeTo = FS.getDir () });
                removeQuietly n
              end),

            (* "remove ... It raises SysErr if path does not exist ... or file
             * is a directory." *)
            Case ("remove refuses a directory and a missing file", fn () =>
              withTempDir "remove-dir" (fn dir =>
                (A.raises "a directory" (fn OS.SysErr _ => true | _ => false)
                   (fn () => FS.remove dir);
                 A.raises "a file that is not there"
                   (fn OS.SysErr _ => true | _ => false)
                   (fn () => FS.remove (OS.Path.concat (dir, "absent")))))),

            (* "If new and old refer to the same file, rename does nothing.
             * If a file called new exists, it is removed." *)
            Case ("rename over an existing file, and onto itself", fn () =>
              withTempDir "rename-over" (fn dir =>
                let
                  val a = OS.Path.concat (dir, "a")
                  val bb = OS.Path.concat (dir, "b")
                  val () = writeFile (a, "first")
                  val () = writeFile (bb, "second")
                in
                  FS.rename { old = a, new = bb };
                  A.eqBool "the old name is gone" (false, FS.access (a, []));
                  A.eqString "and the new name has the old contents"
                    ("first", readFile bb);
                  FS.rename { old = bb, new = bb };
                  A.eqString "renaming onto itself changes nothing"
                    ("first", readFile bb)
                end)),

            (* "If opt is SOME(t), then the time t is used; otherwise the
             * current time (i.e., Time.now()) is used." *)
            Case ("setTime with no time uses the current time", fn () =>
              withTempDir "settime-now" (fn dir =>
                let
                  val f = OS.Path.concat (dir, "f")
                  val () = writeFile (f, "x")
                  val old = Time.fromSeconds (LargeInt.fromInt 1000000)
                  val () = FS.setTime (f, SOME old)
                  val () = A.eqTime "the explicit time was taken"
                             (old, FS.modTime f)
                  val before' = Time.now ()
                  val () = FS.setTime (f, NONE)
                in
                  A.that "the modification time moved forward to about now"
                    (Time.>= (FS.modTime f,
                              Time.- (before',
                                      Time.fromSeconds (LargeInt.fromInt 5))))
                end)),

            (* "An empty path is treated as "."." *)
            Case ("fullPath of the empty path is the current directory",
              fn () =>
                A.eqString "the empty path"
                  (FS.fullPath OS.Path.currentArc, FS.fullPath "")),

            (* "If path is an absolute path, then realPath acts like fullPath.
             * If path is relative ... it returns a path that is relative to
             * the current working directory." *)
            Case ("realPath keeps a relative path relative", fn () =>
              withTempDir "realpath" (fn dir =>
                let
                  val f = OS.Path.concat (dir, "f")
                  val () = writeFile (f, "x")
                  val abs = FS.fullPath f
                in
                  A.eqString "an absolute path goes through fullPath"
                    (FS.fullPath abs, FS.realPath abs);
                  A.eqBool "a relative path stays relative"
                    (true, OS.Path.isRelative (FS.realPath f))
                end)),

            Case ("access with no modes tests existence", fn () =>
              withTempDir "access-exists" (fn dir =>
                let
                  val f = OS.Path.concat (dir, "f")
                  val () = writeFile (f, "x")
                in
                  A.eqBool "a file that is there" (true, FS.access (f, []));
                  A.eqBool "one that is not"
                    (false, FS.access (OS.Path.concat (dir, "absent"), []));
                  A.eqBool "a missing file has no read access either"
                    (false, FS.access (OS.Path.concat (dir, "absent"),
                                       [FS.A_READ]))
                end)),

            Case ("fileId identifies a file", fn () =>
              withTempDir "fileid" (fn dir =>
                let
                  val a = OS.Path.concat (dir, "a")
                  val bb = OS.Path.concat (dir, "b")
                  val () = writeFile (a, "x")
                  val () = writeFile (bb, "y")
                  val ida = FS.fileId a
                  val idb = FS.fileId bb
                in
                  A.eqOrder "a file is the same file as itself"
                    (EQUAL, FS.compare (ida, ida));
                  A.that "two different files have different ids"
                    (FS.compare (ida, idb) <> EQUAL);
                  A.that "the same file read twice gives the same id"
                    (FS.compare (ida, FS.fileId a) = EQUAL);
                  A.eqWord "hash agrees with itself" (FS.hash ida, FS.hash ida);
                  A.that "equal ids hash equally"
                    (FS.hash ida = FS.hash (FS.fileId a))
                end)),

            Case ("isLink is false for an ordinary file",
              fn () =>
                if not C.hasSymbolicLinks then ()
                else
                  withTempDir "islink" (fn dir =>
                    let val f = OS.Path.concat (dir, "plain")
                    in
                      writeFile (f, "x");
                      A.eqBool "a regular file is not a link" (false, FS.isLink f);
                      A.raises "readLink on a non-link"
                        (fn OS.SysErr _ => true | _ => false)
                        (fn () => FS.readLink f)
                    end))
          ]),

        Group ("system errors",
        [ Case ("SysErr carries a message and maybe a code", fn () =>
            if not C.hasFileSystem then ()
            else
              let
                fun inspect (msg, code) =
                  (A.that "the message says something" (String.size msg > 0);
                   case code of
                       NONE => ()   (* the code is optional *)
                     | SOME e =>
                         (A.that "errorMsg says something"
                            (String.size (OS.errorMsg e) > 0);
                          A.that "errorName says something"
                            (String.size (OS.errorName e) > 0);
                          (* syserror inverts errorName. *)
                          A.that "syserror finds the name again"
                            (OS.syserror (OS.errorName e) = SOME e)))
              in
                (FS.remove (scratchFile "certainly-absent");
                 A.fail "expected SysErr")
                handle OS.SysErr pair => inspect pair
              end),

          Case ("syserror rejects a name that is not an error", fn () =>
            A.that "no such error"
              (OS.syserror "certainly-not-a-real-system-error-name" = NONE))
        ]),

        Group ("OS.IO",
        [ Case ("the descriptor kinds are distinct", fn () =>
            let
              val kinds = [OS.IO.Kind.file, OS.IO.Kind.dir, OS.IO.Kind.symlink,
                           OS.IO.Kind.tty, OS.IO.Kind.pipe, OS.IO.Kind.socket,
                           OS.IO.Kind.device]
              fun distinct [] = true
                | distinct (x :: xs) =
                    not (List.exists (fn y => y = x) xs) andalso distinct xs
            in
              A.eqInt "seven kinds" (7, List.length kinds);
              A.that "all distinct" (distinct kinds)
            end),

          Case ("the Poll exception exists", fn () =>
            A.eqString "name" ("Poll", exnName OS.IO.Poll)),

          Case ("polling nothing returns nothing", fn () =>
            A.eqInt "no descriptors, no results"
              (0, List.length (OS.IO.poll ([], SOME Time.zeroTime)))),

          Case ("a file descriptor can be hashed and compared",
            fn () =>
              if not C.hasFileSystem then ()
              else
                withTempDir "iodesc" (fn dir =>
                  let val f = OS.Path.concat (dir, "described")
                  in
                    writeFile (f, "x");
                    withFileDesc (f, fn ioDesc =>
                      case ioDesc of
                          NONE => ()   (* a stream need not expose one *)
                        | SOME d =>
                            (A.eqOrder "a descriptor equals itself"
                               (EQUAL, OS.IO.compare (d, d));
                             A.eqWord "and hashes consistently"
                               (OS.IO.hash d, OS.IO.hash d);
                             A.that "its kind is that of a file"
                               (OS.IO.kind d = OS.IO.Kind.file)))
                  end)),

          Case ("a readable file polls as ready to read",
            fn () =>
              if not (C.hasFileSystem andalso C.hasPollingIO) then ()
              else
                withTempDir "poll" (fn dir =>
                  let val f = OS.Path.concat (dir, "pollable")
                  in
                    writeFile (f, "x");
                    withFileDesc (f, fn ioDesc =>
                      case Option.mapPartial OS.IO.pollDesc ioDesc of
                          NONE => ()   (* not pollable on this host *)
                        | SOME pd =>
                            let
                              val infos = OS.IO.poll ([OS.IO.pollIn pd],
                                                      SOME Time.zeroTime)
                            in
                              A.eqInt "one result" (1, List.length infos);
                              case infos of
                                  [] => ()
                                | info :: _ =>
                                    (A.eqBool "ready to read"
                                       (true, OS.IO.isIn info);
                                     (* infoToPollDesc and pollToIODesc take
                                      * the answer back to the descriptor it
                                      * was asked about. *)
                                     A.eqOrder "and it names the same descriptor"
                                       (EQUAL,
                                        OS.IO.compare
                                          (OS.IO.pollToIODesc
                                             (OS.IO.infoToPollDesc info),
                                           OS.IO.pollToIODesc pd)))
                            end)
                  end)),

          (* A descriptor for a file open for writing, so that pollOut can be
           * asked a question it can meaningfully answer. *)
          Case ("a writable file polls as ready to write",
            fn () =>
              if not (C.hasFileSystem andalso C.hasPollingIO) then ()
              else
                withTempDir "pollout" (fn dir =>
                  let
                    val f = OS.Path.concat (dir, "writable")
                    val outs = TextIO.openOut f
                    val (TextPrimIO.WR { ioDesc, ... }, _) =
                      TextIO.StreamIO.getWriter (TextIO.getOutstream outs)
                  in
                    (case Option.mapPartial OS.IO.pollDesc ioDesc of
                         NONE => ()
                       | SOME pd =>
                           case OS.IO.poll ([OS.IO.pollOut pd],
                                            SOME Time.zeroTime) of
                               [] => ()
                             | info :: _ =>
                                 (A.eqBool "ready to write"
                                    (true, OS.IO.isOut info);
                                  A.noRaise "isPri answers"
                                    (fn () => OS.IO.isPri info)));
                    TextIO.closeOut outs
                  end)),

          (* Adding a condition a descriptor does not support is specified to
           * raise Poll, and a regular file supports no notion of priority
           * data, so refusing is as correct as accepting. *)
          Case ("pollPri either applies or reports that it cannot",
            fn () =>
              if not (C.hasFileSystem andalso C.hasPollingIO) then ()
              else
                withTempDir "pollpri" (fn dir =>
                  let val f = OS.Path.concat (dir, "prioritised")
                  in
                    writeFile (f, "x");
                    withFileDesc (f, fn ioDesc =>
                      case Option.mapPartial OS.IO.pollDesc ioDesc of
                          NONE => ()
                        | SOME pd =>
                            (ignore (OS.IO.poll ([OS.IO.pollPri pd],
                                                 SOME Time.zeroTime)))
                            handle OS.IO.Poll => ()
                                 | e => A.fail ("unexpected exception "
                                                ^ exnName e))
                  end)),

          Case ("several descriptors can be polled in one call",
            fn () =>
              if not (C.hasFileSystem andalso C.hasPollingIO) then ()
              else
                withTempDir "pollmany" (fn dir =>
                  let val f = OS.Path.concat (dir, "many")
                  in
                    writeFile (f, "x");
                    withFileDesc (f, fn ioDesc =>
                      case Option.mapPartial OS.IO.pollDesc ioDesc of
                          NONE => ()
                        | SOME pd =>
                            let
                              (* Two separate descriptors for the same file,
                               * each carrying one condition. *)
                              val infos = OS.IO.poll
                                            ([OS.IO.pollIn pd, OS.IO.pollIn pd],
                                             SOME Time.zeroTime)
                            in
                              A.that "at most one result per descriptor asked"
                                (List.length infos <= 2);
                              (* "The returned list respects the order of the
                               * argument list", and every result names one of
                               * the descriptors that was asked about. *)
                              A.that "every result names the descriptor asked"
                                (List.all
                                   (fn info =>
                                      OS.IO.compare
                                        (OS.IO.pollToIODesc
                                           (OS.IO.infoToPollDesc info),
                                         OS.IO.pollToIODesc pd) = EQUAL)
                                   infos)
                            end)
                  end)),

          (* "SOME(t) means timeout after time t" -- a poll with a timeout on
           * a descriptor that is ready must not wait for it. *)
          Case ("a timeout is an upper bound, not a wait",
            fn () =>
              if not (C.hasFileSystem andalso C.hasPollingIO) then ()
              else
                withTempDir "polltimeout" (fn dir =>
                  let val f = OS.Path.concat (dir, "timed")
                  in
                    writeFile (f, "x");
                    withFileDesc (f, fn ioDesc =>
                      case Option.mapPartial OS.IO.pollDesc ioDesc of
                          NONE => ()
                        | SOME pd =>
                            let
                              val timer = Timer.startRealTimer ()
                              val infos =
                                OS.IO.poll ([OS.IO.pollIn pd],
                                            SOME (Time.fromSeconds
                                                    (LargeInt.fromInt 10)))
                              val elapsed = Timer.checkRealTimer timer
                            in
                              A.that "a ready descriptor is reported at once"
                                (Time.< (elapsed,
                                         Time.fromSeconds (LargeInt.fromInt 5)));
                              A.eqInt "and it is reported" (1, List.length infos)
                            end)
                  end)),

          (* "This will raise OS.SysErr if, for example, iod refers to a
           * closed file." *)
          Case ("kind of a closed descriptor is an error",
            fn () =>
              if not C.hasFileSystem then ()
              else
                withTempDir "closedkind" (fn dir =>
                  let
                    val f = OS.Path.concat (dir, "closed")
                    val () = writeFile (f, "x")
                    val ins = TextIO.openIn f
                    val (rd, _) =
                      TextIO.StreamIO.getReader (TextIO.getInstream ins)
                    val TextPrimIO.RD { ioDesc, close, ... } = rd
                  in
                    close ();
                    case ioDesc of
                        NONE => ()
                      | SOME d =>
                          A.raises "a closed descriptor"
                            (fn OS.SysErr _ => true | _ => false)
                            (fn () => OS.IO.kind d)
                  end)),

          Group ("both directions on one descriptor",
            onlyIf (C.hasFileSystem andalso C.hasPollingIO
                    andalso C.canPollBothDirections,
                    "configured off; see canPollBothDirections")
            [ Case ("one descriptor may carry both directions",
              fn () =>
                withTempDir "pollboth" (fn dir =>
                  let val f = OS.Path.concat (dir, "both")
                  in
                    writeFile (f, "x");
                    withFileDesc (f, fn ioDesc =>
                      case Option.mapPartial OS.IO.pollDesc ioDesc of
                          NONE => ()
                        | SOME pd =>
                            case OS.IO.poll ([OS.IO.pollOut (OS.IO.pollIn pd)],
                                             SOME Time.zeroTime) of
                                [] => ()
                              | info :: _ =>
                                  A.that "some direction is ready"
                                    (OS.IO.isIn info orelse OS.IO.isOut info))
                  end)) ])
        ]),

        Group ("OS.Process",
        [ Case ("system runs a child process",
            fn () =>
              if not C.canSpawnProcesses then ()
              else
                (A.eqBool "a command that succeeds"
                   (true, OS.Process.isSuccess (OS.Process.system "exit 0"));
                 A.eqBool "a command that fails"
                   (false, OS.Process.isSuccess (OS.Process.system "exit 3")))),

          Case ("sleep returns after a short wait", fn () =>
            let
              val t = Timer.startRealTimer ()
              val () = OS.Process.sleep (Time.fromMilliseconds (LargeInt.fromInt 5))
            in
              A.that "some time passed"
                (Time.>= (Timer.checkRealTimer t, Time.zeroTime))
            end),

          (* "If t is zero or negative, then the calling process does not
           * sleep, but returns immediately.  No exception is raised." *)
          Case ("sleeping for no time at all is allowed", fn () =>
            A.noRaise "zero sleep" (fn () => OS.Process.sleep Time.zeroTime)),

          Case ("a positive sleep advances the real clock", fn () =>
            let
              val t = Timer.startRealTimer ()
              val () = OS.Process.sleep
                         (Time.fromMilliseconds (LargeInt.fromInt 50))
              val elapsed = Timer.checkRealTimer t
            in
              A.that ("at least a millisecond passed, got "
                      ^ Time.toString elapsed)
                (Time.>= (elapsed,
                          Time.fromMilliseconds (LargeInt.fromInt 1)))
            end),

          (* "success ... The unique status value that signifies successful
           * termination", and isSuccess reports it. *)
          Case ("the status of a child process is a status value", fn () =>
            if not C.canSpawnProcesses then ()
            else
              let
                val ok = OS.Process.system "exit 0"
                val bad = OS.Process.system "exit 3"
              in
                A.eqBool "success is successful"
                  (true, OS.Process.isSuccess ok);
                A.eqBool "failure is not" (false, OS.Process.isSuccess bad);
                A.eqBool "the failure constant is not a success"
                  (false, OS.Process.isSuccess OS.Process.failure)
              end)
        ]
        (* The negative half of the sleep sentence, behind a flag because
         * SML/NJ 2026.1 blocks forever on it rather than returning; see
         * negativeSleepReturns. *)
        @ onlyIf (C.negativeSleepReturns,
                  "implementation not declared to return from a negative sleep")
        [ Case ("sleeping for a negative time returns at once", fn () =>
            A.noRaise "a negative sleep"
              (fn () => OS.Process.sleep
                          (Time.- (Time.zeroTime,
                                   Time.fromSeconds (LargeInt.fromInt 5)))))
        ])
      ])
  end
