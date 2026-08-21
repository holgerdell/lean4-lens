/-
`review_cone.lean` — emit exact, elaborator-derived declaration data as JSON.

It serves two readers, and `REVIEW_CONE_DEPS` chooses between them: the review
document `render_review_cone.py` renders, and the dependency graph `dep_tree.py`
answers from. What each reader needs, and why neither answer suits the other,
is set out in the environment variables below.

Project-independent by construction:

  * roots are supplied by name in `REVIEW_CONE_ROOTS` — render_review_cone.py
    sets it from the project's `review-cone.toml` (every decl named anywhere in
    that config is a root) — no in-source attribute, no hardcoded allowlist, no
    paper cross-reference file;
  * the project's libraries are discovered from its `lakefile` and imported
    dynamically at run time (no static `import` of project code), so this one
    file works unmodified in any Lean project;
  * it imports Lean core only, so a project without Mathlib works too;
  * it elaborates on Lean v4.19 and up. Where core's string API moved under it
    (`String.ofList`, `trimAscii`, `drop`, `dropEnd`), the helpers below stand
    in with one spelling that works across the whole range;
  * configuration is read from the environment:
      REVIEW_CONE_LIBS      comma-separated `lean_lib` names to scan (REQUIRED;
                            render_review_cone.py sets it from the lakefile)
      REVIEW_CONE_ROOTS     comma-separated fully-qualified root decl names
                            (REQUIRED in cone mode; render_review_cone.py sets it
                            from review-cone.toml). Every name must resolve to a
                            project declaration or the run fails. Ignored in
                            dependency mode, which has no roots.
      REVIEW_CONE_DEPS      1 emits every project declaration, with a theorem's
                            refs covering its proof — a dependency graph's
                            question. The default emits the roots' closure with
                            statement-only refs — what a reader of the document
                            must trust, a proof being trusted via the kernel.
                            Neither answer is the other's; do not "fix" one into
                            the other (optional; default: the document's).
      REVIEW_CONE_PREFIXES  comma-separated namespace prefixes counting as
                            "project" (optional; default: the library names)
      REVIEW_CONE_OUT       output JSON path (optional; default: review_cone.json)

Run it from the project root once the project is built:

    lake env lean --run <this file>

`render_review_cone.py` orchestrates that (build → run → render) for you.
-/
import Lean

open Lean Elab Meta

namespace ReviewCone

/-- A module is "project" iff it lives under one of the configured namespace
prefixes (from `REVIEW_CONE_PREFIXES`, or the library names). -/
def isProjectModule (prefixes : Array Name) (m : Name) : Bool :=
  prefixes.any (·.isPrefixOf m)

/-- The name a declaration is *written* under, recovering `CountColorings.foo`
from a `private` decl's mangled `_private.….0.CountColorings.foo`; a no-op on
public names. Normalise before testing `isInternal`: a mangled name reports
`true` for it, so testing first discards every private decl. -/
def userName (n : Name) : Name := (privateToUserName? n).getD n

/-- The module a declaration is defined in. (The older `Environment.getModuleFor?`
was removed; this reconstructs it from `getModuleIdxFor?` + `moduleNames`.) -/
def moduleFor? (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx]?
  | none => none

/-- mathlib4_docs URL for a declaration, from its defining module. -/
def docUrl (env : Environment) (n : Name) : Option String :=
  match moduleFor? env n with
  | none => none
  | some m =>
    let path := m.toString.replace "." "/"
    some s!"https://leanprover-community.github.io/mathlib4_docs/{path}.html#{n}"

/-- Constants referenced in an expression, filtered to real (non-internal) decls.
Internal auxiliaries (e.g. `foo._proof_1`, lifted from a proof obligation in a
def body) are transparently expanded to the constants *they* use, so genuine
references hidden behind them are still collected. -/
partial def usedConsts (env : Environment) (e : Expr) : Array Name := Id.run do
  let mut out : Array Name := #[]
  let mut seen : NameSet := {}
  let mut work := e.getUsedConstants.toList
  while !work.isEmpty do
    let n := work.head!
    work := work.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if n == ``sorryAx then continue  -- placeholder left by `eraseProofs`
    -- `Lean.*` constants are elaboration internals (e.g. an omega certificate
    -- in a def value), never genuine statement dependencies of a project.
    if (`Lean).isPrefixOf n then continue
    let some ci := env.find? n | continue
    -- normalise first: a private name reports isInternal, and is not one
    let u := userName n
    if u.isInternal then
      -- expand the lifted auxiliary into the constants it actually references
      work := work ++ ci.type.getUsedConstants.toList
      match ci with
      | .defnInfo d => work := work ++ d.value.getUsedConstants.toList
      | .thmInfo d => work := work ++ d.value.getUsedConstants.toList
      | .opaqueInfo d => work := work ++ d.value.getUsedConstants.toList
      | _ => pure ()
    else
      out := out.push u
  return out

/-- `e` with every proof subterm replaced by a `sorryAx` placeholder, so a
statement's embedded proof terms (an instance's field, a tactic-built index
bound, …) contribute no constants of their own. -/
def eraseProofs (e : Expr) : MetaM Expr :=
  Meta.transform e (skipConstInApp := true)
    (pre := fun s => do
      if ← Meta.isProof s then
        return .done (← mkSorry (← Meta.inferType s) true)
      return .continue)

/-- All constants this decl exposes: its type, the field types of a
structure/inductive, and — when `withValue` — its value, including a theorem's
proof. Proof subterms embedded in *types* are erased first, so tactic internals
are never reported as dependencies. -/
def stmtConsts (env : Environment) (ci : ConstantInfo) (withValue : Bool) :
    MetaM (Array Name) := do
  let mut r := usedConsts env (← eraseProofs ci.type)
  if withValue then
    match ci with
    | .defnInfo d => r := r ++ usedConsts env d.value
    | .opaqueInfo d => r := r ++ usedConsts env d.value
    | .thmInfo d => r := r ++ usedConsts env d.value
    | _ => pure ()
  match ci with
  | .inductInfo iv =>
    for c in iv.ctors do
      if let some (.ctorInfo cv) := env.find? c then
        r := r ++ usedConsts env (← eraseProofs cv.type)
  | _ => pure ()
  return r

/-- If `n` is a structure-field projection, return its parent structure. -/
def fieldParent? (env : Environment) (n : Name) : Option Name :=
  let p := n.getPrefix
  if isStructure env p && (getStructureFields env p).any (fun f => p ++ f == n)
  then some p else none

/-- If `n` is a companion that should never get its own review-cone entry —
either a Lean-generated one with no source text of its own (the primitive
recursor, an auxiliary eliminator `casesOn`/`recOn`/`brecOn`/`below`, a
`noConfusion` lemma, an equation-compiler match auxiliary `.match_N`, or a
per-constructor `.sizeOf_spec` lemma from the auto-derived `SizeOf` instance),
or a *constructor* (hand-named or the structure default `mk`) — return the
type/decl it belongs to. Every constructor of an inductive redirects to its
parent type: even a hand-named constructor with its own doc comment (e.g.
`| merge …`) is a facet of the one inductive, not a standalone declaration,
and reads better inlined at the inductive's own entry (whose source range
already covers all constructors). A `.sizeOf_spec` lemma redirects to its
constructor, which in turn redirects to that same inductive. -/
def synthesizedParent? (env : Environment) (n : Name) (ci : ConstantInfo) : Option Name :=
  match ci with
  | .recInfo _ => some n.getPrefix
  | .ctorInfo cv => some cv.induct
  | _ =>
    if isAuxRecursor env n || isNoConfusion env n || isMatcherCore env n then
      some n.getPrefix
    else if mkSizeOfSpecLemmaName n.getPrefix == n then
      match env.find? n.getPrefix with
      | some (.ctorInfo _) => some n.getPrefix
      | _ => none
    else none

/-- Where `n` redirects to for review-cone purposes: its parent structure (a
field projection) or its parent type (a synthesized recursor/eliminator/
constructor companion) — `none` if `n` is a genuine standalone declaration. -/
def redirectParent? (env : Environment) (n : Name) (ci : ConstantInfo) : Option Name :=
  (fieldParent? env n).orElse (fun _ => synthesizedParent? env n ci)

/-- Transitive statement dependencies seeded from `roots`. Recurse through the
statement constants of every project decl (definitions also expand their value);
stop (collect, no recurse) at non-project (e.g. mathlib) decls. Roots' own values
are never inspected. Structure-field projections and synthesized recursor/
eliminator/constructor companions redirect to their parent (recorded in
`fields`) rather than being emitted as their own entry. Only the document's
mode has roots; the graph's uses `allProject`. -/
partial def closure (env : Environment) (prefixes : Array Name) (roots : Array Name) :
    MetaM (Array Name × Array Name × Array (Name × Name)) := do
  let mut visited : NameSet := {}
  let mut proj : Array Name := #[]
  let mut mlib : Array Name := #[]
  let mut seenMlib : NameSet := {}
  let mut fields : Array (Name × Name) := #[]
  let mut work : List Name := []
  for r in roots do
    if let some ci := env.find? r then
      work := work ++ (usedConsts env (← eraseProofs ci.type)).toList
  while !work.isEmpty do
    let n := work.head!
    work := work.tail!
    if visited.contains n then continue
    visited := visited.insert n
    let some ci := env.find? n | continue
    let m := (moduleFor? env n).getD Name.anonymous
    if isProjectModule prefixes m then
      match redirectParent? env n ci with
      | some p =>
        fields := fields.push (n, p)
        work := work ++ [p]
      | none =>
        proj := proj.push n
        -- statement-only for theorems, matching what this mode emits
        let withVal := match ci with | .thmInfo _ => false | _ => true
        work := work ++ (← stmtConsts env ci withVal).toList
    else
      -- doc-gen4 has no page for a synthesized companion (recursor, `casesOn`,
      -- matcher, `noConfusion`, …), so report the parent type the reader can
      -- actually look up. Constructors keep their own entry: docs cover them.
      let n := match ci with
        | .ctorInfo _ => n
        | _ => (synthesizedParent? env n ci).getD n
      if !seenMlib.contains n then
        seenMlib := seenMlib.insert n
        mlib := mlib.push n
  return (proj, mlib, fields)

/-- Every project declaration and its `fields` redirects, selected by module
prefix alone. Internal names are skipped and `private` ones kept (see
`userName`), and names come back as stored, not as written. -/
def allProject (env : Environment) (prefixes : Array Name) :
    Array Name × Array (Name × Name) :=
  env.constants.fold (init := (#[], #[])) fun (proj, fields) n ci =>
    if (userName n).isInternal then (proj, fields)
    else if !isProjectModule prefixes ((moduleFor? env n).getD Name.anonymous) then (proj, fields)
    else match redirectParent? env n ci with
      | some p => (proj, fields.push (n, p))
      | none => (proj.push n, fields)

def kindStr (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.defnInfo _) => "def"
  | some (.thmInfo _) => "theorem"
  | some (.inductInfo _) =>
    -- a class is also a structure, so test it first
    if isClass env n then "class"
    else if isStructure env n then "structure"
    else "inductive"
  | some (.ctorInfo _) => "constructor"
  | some (.axiomInfo _) => "axiom"
  | _ => "other"

/-- `List Char` as a `String`. Spelled with `String.push` because the direct
spellings are each unavailable at one end of the supported range: `String.ofList`
does not exist before Lean v4.27, and `String.mk` is deprecated from v4.27 on. -/
def ofChars (cs : List Char) : String := cs.foldl (·.push ·) ""

/-- `s` without leading or trailing ASCII whitespace. Same reason as `ofChars`:
`String.trimAscii` arrived in v4.27 and `String.trim` is deprecated from v4.27
on, so neither spelling works across the range. -/
def trimAscii (s : String) : String :=
  ofChars ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- `s` with its first `n` characters dropped. `String.drop` answers a `String`
before Lean v4.27 and a `String.Slice` from v4.27 on, so its result type is not
portable; this one is always a `String`. -/
def dropChars (s : String) (n : Nat) : String := ofChars (s.toList.drop n)

/-- `s` with its last `n` characters dropped. `String.dropEnd` arrived in Lean
v4.27, so the older half of the range has no spelling for it at all. -/
def dropEndChars (s : String) (n : Nat) : String := ofChars (s.toList.take (s.length - n))

/-- JSON-escape a string: the mandatory `"` and `\` plus the whitespace control
chars, and any remaining control char (< U+0020) as a `\uXXXX` escape, so a decl
or module name containing an escaped identifier can never emit malformed JSON. -/
def jsonEsc (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | c =>
        if c.toNat < 0x20 then
          let hex := ofChars (Nat.toDigits 16 c.toNat)
          "\\u" ++ ofChars (List.replicate (4 - hex.length) '0') ++ hex
        else c.toString) ""

/-- The axioms a `verified` classification may depend on; any other axiom marks
its decl `tainted`. Emitted in the JSON so renderers explain verdicts with the
same list that produced them. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Classify a declaration by its axiom dependencies: `verified` (only the
standard axioms), `tainted` (sorry-free but depends on extra axioms), or `sorry`
(depends on `sorryAx`). Also returns the non-standard axioms. -/
def axiomInfo (decl : Name) : CoreM (String × List Name) := do
  let axs ← collectAxioms decl
  let isSorry := axs.any (· == `sorryAx)
  let extras := axs.toList.filter (fun a => a != `sorryAx && !standardAxioms.contains a)
  let status := if isSorry then "sorry" else if extras.isEmpty then "verified" else "tainted"
  return (status, extras)

/-- The `.lean` source path a project module `Name` was read from — the
inverse of `pathToModule`. -/
def moduleToPath (root : System.FilePath) (m : Name) : System.FilePath :=
  root / (m.toString.replace "." "/" ++ ".lean")

/-- Whether the elaborator chose the decl's name itself (an anonymous
`instance`, a macro-generated companion): true iff the name's final component
is never spelled inside the decl's own source lines `startLine..endLine`. -/
def isAutoNamed (src : String) (n : Name) (startLine endLine : Nat) : Bool :=
  if startLine == 0 then false  -- no recorded range: nothing to compare against
  else
    let last := match n with | .str _ s => s | x => x.toString
    let block := String.intercalate "\n"
      (((src.splitOn "\n").drop (startLine - 1)).take (endLine + 1 - startLine))
    (block.splitOn last).length == 1

/-- Build the JSON for the imported `env`, from `roots` the driver has already
checked resolve to project declarations. `depMode` picks the reader, as
`REVIEW_CONE_DEPS` above describes; `roots` go unused under it. -/
def emitJson (prefixes : Array Name) (projectRoot : String) (roots : Array Name)
    (depMode : Bool) : MetaM String := do
  let env ← getEnv
  let rootSet : NameSet := roots.foldl (·.insert ·) {}

  let (proj, mlib, fields) ←
    if depMode then
      let (p, f) := allProject env prefixes
      pure (p, #[], f)
    else
      let (projC, mlib, f) ← closure env prefixes roots
      pure ((roots ++ projC).toList.eraseDups.toArray, mlib, f)
  -- sorted and emitted under the written name; the `Name`s stay as stored
  let projSorted := proj.qsort (fun a b => (userName a).toString < (userName b).toString)
  let mlibSorted := mlib.qsort (fun a b => a.toString < b.toString)

  let mut out := "{\n"
  out := out ++ s!"  \"projectRoot\": \"{jsonEsc projectRoot}\",\n"
  out := out ++ s!"  \"roots\": {roots.size},\n"
  -- the list `axiomInfo` classified with, so renderers never restate their own
  let stdStr := String.intercalate ", "
    (standardAxioms.map (fun a => s!"\"{jsonEsc a.toString}\""))
  out := out ++ s!"  \"standardAxioms\": [{stdStr}],\n"
  -- field projection -> parent structure (fields link to the structure entry)
  let fieldStr := String.intercalate ",\n"
    (fields.toList.eraseDups.map (fun (f, p) =>
      s!"    \"{jsonEsc (userName f).toString}\": \"{jsonEsc (userName p).toString}\""))
  out := out ++ "  \"fieldOf\": {\n" ++ fieldStr ++ "\n  },\n"
  out := out ++ "  \"project\": [\n"
  let mut first := true
  let mut srcCache : NameMap String := {}
  for n in projSorted do
    let m := (moduleFor? env n).getD Name.anonymous
    let ranges ← findDeclarationRanges? n
    let (sl, el) := match ranges with
      | some r => (r.range.pos.line, r.range.endPos.line)
      | none => (0, 0)
    let some ci := env.find? n | continue
    -- read the decl's source once per module to decide `autoName` exactly
    let mut src? := srcCache.find? m
    if src?.isNone && sl > 0 then
      let p := moduleToPath ⟨projectRoot⟩ m
      if ← p.pathExists then
        let s ← IO.FS.readFile p
        srcCache := srcCache.insert m s
        src? := some s
    let autoName := match src? with
      | some src => isAutoNamed src (userName n) sl el
      | none => false
    -- a theorem exposes only its type, unless the reader wants its proof
    let withVal := depMode || kindStr env n != "theorem"
    let refs := (← stmtConsts env ci withVal).toList.eraseDups
    let refsStr := String.intercalate ", " (refs.map (fun r => s!"\"{jsonEsc r.toString}\""))
    let (status, axsList) ← axiomInfo n
    let axsStr := String.intercalate ", " (axsList.map (fun a => s!"\"{jsonEsc a.toString}\""))
    let rootStr := if rootSet.contains n then ", \"isRoot\": true" else ", \"isRoot\": false"
    let sep := if first then "" else ",\n"
    first := false
    out := out ++ sep ++ s!"    \{\"name\": \"{jsonEsc (userName n).toString}\", \"module\": \"{jsonEsc m.toString}\", \"kind\": \"{kindStr env n}\", \"startLine\": {sl}, \"endLine\": {el}, \"autoName\": {autoName}, \"status\": \"{status}\", \"axioms\": [{axsStr}]{rootStr}, \"refs\": [{refsStr}]}"
  out := out ++ "\n  ],\n  \"mathlib\": [\n"
  first := true
  for n in mlibSorted do
    let url := (docUrl env n).getD ""
    let sep := if first then "" else ",\n"
    first := false
    out := out ++ sep ++ s!"    \{\"name\": \"{jsonEsc n.toString}\", \"url\": \"{jsonEsc url}\"}"
  out := out ++ "\n  ]\n}"
  return out

/-- Comma-split an env-var value into trimmed, non-empty pieces. -/
def splitComma (s : String) : List String :=
  (s.splitOn ",").filterMap (fun x =>
    let t := trimAscii x
    if t == "" then none else some t)

/-- Walk up from `dir` to the nearest directory containing a lakefile. -/
partial def findProjectRoot (dir : System.FilePath) : IO (Option System.FilePath) := do
  if (← (dir / "lakefile.lean").pathExists) || (← (dir / "lakefile.toml").pathExists) then
    return some dir
  match dir.parent with
  | some p => if p == dir then return none else findProjectRoot p
  | none => return none

/-- Recursively list `.lean` files under `dir`. -/
partial def walkLeanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for entry in (← dir.readDir) do
    let p := entry.path
    if ← p.isDir then
      out := out ++ (← walkLeanFiles p)
    else if p.toString.endsWith ".lean" then
      out := out.push p
  return out

/-- A source path relative to the project root, like `Coloring/K3/Weights`
(no extension, `/`-separated), as a module `Name`. -/
def pathToModule (relNoExt : String) : Name :=
  (relNoExt.splitOn "/").foldl (fun n s => Name.mkStr n s) Name.anonymous

/-- Whether `m`'s compiled `.olean` actually exists on the current Lean search
path. `findOLean`/`findWithExt` only check that the module's *root* package
directory is present, not the specific nested file, so they are not enough
here; `SearchPath.findModuleWithExt` additionally checks `pathExists`. -/
def hasOlean (m : Name) : IO Bool := do
  let sp ← searchPathRef.get
  return (← sp.findModuleWithExt "olean" m).isSome

/-- Every `.lean` module under the library `lib`, as module `Name`s: the root
aggregator `<lib>.lean` (if present) plus everything under `<lib>/`. A source
file on disk need not be part of `lib`'s actual build (excluded from the
lakefile's globs, an orphaned scratch file, …); `importModules` fails hard on
the whole bulk import for a single such name, so these are filtered out here
rather than assumed built. -/
def libModules (root : System.FilePath) (lib : String) : IO (Array Name) := do
  let mut mods : Array Name := #[]
  let rootFile := root / (lib ++ ".lean")
  if ← rootFile.pathExists then mods := mods.push (Name.mkSimple lib)
  let libDir := root / lib
  if ← libDir.pathExists then
    let prefixLen := root.toString.length + 1  -- strip "<root>/"
    for p in (← walkLeanFiles libDir) do
      let rel := dropEndChars (dropChars p.toString prefixLen) ".lean".length
      mods := mods.push (pathToModule rel)
  let mut built : Array Name := #[]
  for m in mods do
    if ← hasOlean m then
      built := built.push m
    else
      IO.eprintln s!"review_cone: skipping {m} — no compiled .olean (not part of the {lib} build)"
  return built

/-- Run a `MetaM` action against a freshly imported environment `env` in `IO`. -/
def runMeta {α : Type} (env : Environment) (act : MetaM α) : IO α := do
  let ctx : Core.Context := { fileName := "<review_cone>", fileMap := FileMap.ofString "" }
  let (a, _) ← (act.run').toIO ctx { env := env }
  return a

/-- Best-effort direct imports of a project module, parsed from its source
text (`import X` / `public import X`, optionally with a leading `all`) rather
than its `.olean` header — cheap, and all `libModules` needs it for is
pruning a broken transitive-import chain (see `pruneMissingOleans` and
`pruneAndImport`), not
correctness of the actual build. Non-project modules (Mathlib, `Init`, …)
have no source file under `root` and are reported with no imports; that is
fine here since only project modules can appear in `mods`. -/
def directImports (root : System.FilePath) (m : Name) : IO (Array Name) := do
  let path := moduleToPath root m
  if !(← path.pathExists) then return #[]
  let mut out : Array Name := #[]
  for line in (← IO.FS.readFile path).splitOn "\n" do
    let l := trimAscii line
    if l.startsWith "import " || l.startsWith "public import " then
      let l := if l.startsWith "public " then dropChars l "public ".length else l
      let l := dropChars l "import ".length
      let l := if l.startsWith "all " then dropChars l "all ".length else l
      out := out.push (trimAscii l).toName
  return out

/-- Drop from `mods` every module whose transitive imports (per
`directImports`) reach a project module with no compiled `.olean` — the module
`libModules` kept (its own `.olean` exists) that imports one it dropped (a
broken/orphaned source file, stale on disk but not part of the current build).
`importModules` fails hard on the *whole* batch over any such module, so they
are computed and excluded up front rather than diagnosed from the failure. -/
partial def pruneMissingOleans (root : System.FilePath) (mods : Array Name) :
    IO (Array Name) := do
  -- walk the project import graph; `blame` maps a module to the missing-olean
  -- culprit it reaches (itself, when its own .olean is the missing one)
  let mut imports : NameMap (Array Name) := {}
  let mut blame : NameMap Name := {}
  let mut work := mods.toList
  while !work.isEmpty do
    let m := work.head!
    work := work.tail!
    if imports.contains m then continue
    -- non-project imports (no source under `root`) end the walk: their build
    -- is not ours to judge, and a truly broken one should fail loudly later
    if !(← (moduleToPath root m).pathExists) then continue
    let deps ← directImports root m
    imports := imports.insert m deps
    if !(← hasOlean m) then blame := blame.insert m m
    work := work ++ deps.toList
  let mut changed := true
  while changed do
    changed := false
    for (m, deps) in imports.toList do
      if !(blame.contains m) then
        if let some c := deps.findSome? (blame.find? ·) then
          blame := blame.insert m c
          changed := true
  for m in mods do
    if let some c := blame.find? m then
      if c != m then  -- `libModules` already reported the culprits themselves
        IO.eprintln s!"review_cone: skipping {m} — transitively imports {c}, which has no compiled .olean"
  return mods.filter (!blame.contains ·)

/-- Import `mods` in one batch. Missing-`.olean` chains are already excluded
(`pruneMissingOleans`), so the one failure recovered from here is two leaf
modules that each privately `@[expose]`-unfold the same third module clashing
on the auto-generated duplicate private copy (the module system never expects
two modules' `.private` content to coexist in one flat environment; a normal
one-file-at-a-time build never hits this). Recover by pruning the offender and
everything that (transitively, per `directImports`) reaches it, then retrying
— capped by `fuel` so an unrelated import failure still surfaces as an error
instead of looping. -/
unsafe def pruneAndImport (root : System.FilePath) (mods : Array Name) (fuel : Nat) :
    IO (Environment × Array Name) := do
  try
    -- a failed `importModules (loadExts := true)` clears the "initializers
    -- enabled" flag it needs, so a retry must re-arm it first.
    enableInitializersExecution
    let env ← importModules (mods.map (fun m => { module := m })) {}
      (trustLevel := 0) (loadExts := true)
    return (env, mods)
  catch e =>
    if fuel == 0 then throw e
    -- TOOLCHAIN-COUPLED: no API reports which module clashed, so the offender
    -- is parsed out of core's "import <M> failed, environment already
    -- contains <decl>" message; a rewording downgrades this to a hard error.
    match (toString e).splitOn " failed, environment already contains" with
    | [modStr, _] =>
      let bad := (trimAscii (dropChars modStr "import ".length)).toName
      let mut banned : NameSet := ({} : NameSet).insert bad
      let mut changed := true
      while changed do
        changed := false
        for m in mods do
          if !banned.contains m then
            if (← directImports root m).any banned.contains then
              banned := banned.insert m
              changed := true
      let kept := mods.filter (!banned.contains ·)
      if kept.size == mods.size then throw e  -- nothing prunable; a real failure
      for m in mods do
        if banned.contains m then
          IO.eprintln s!"review_cone: skipping {m} — clashes with an already-imported module on a duplicate private declaration"
      pruneAndImport root kept (fuel - 1)
    | _ => throw e

unsafe def run : IO Unit := do
  let cwd ← IO.currentDir
  let some root ← findProjectRoot cwd
    | throw <| IO.userError "review_cone: no lakefile.lean/.toml found from the current directory"
  -- libraries to scan (comma-separated lean_lib names; the driver sets this)
  let some libsStr ← IO.getEnv "REVIEW_CONE_LIBS"
    | throw <| IO.userError "review_cone: set REVIEW_CONE_LIBS (comma-separated lean_lib names); render_review_cone.py sets it automatically"
  let libs := splitComma libsStr
  if libs.isEmpty then
    throw <| IO.userError "review_cone: REVIEW_CONE_LIBS is empty"
  -- dependency mode: every project decl, proofs included, no roots (see header)
  let depMode := ((← IO.getEnv "REVIEW_CONE_DEPS").getD "") == "1"
  -- root decl names (comma-separated fully-qualified names; the driver sets this
  -- from review-cone.toml — every decl named in the config is a root)
  let rootNames ← if depMode then pure #[] else do
    let some rootsStr ← IO.getEnv "REVIEW_CONE_ROOTS"
      | throw <| IO.userError "review_cone: set REVIEW_CONE_ROOTS (comma-separated root decl names); render_review_cone.py sets it from review-cone.toml"
    let names := (splitComma rootsStr).map (String.toName ·) |>.toArray
    if names.isEmpty then
      throw <| IO.userError "review_cone: REVIEW_CONE_ROOTS is empty — the config named no declarations"
    pure names
  -- project namespace prefixes (env override, else the library names)
  let prefixNames := (match (← IO.getEnv "REVIEW_CONE_PREFIXES") with
    | some s => splitComma s
    | none => libs).map (String.toName ·) |>.toArray
  -- every module of every library, imported dynamically
  let mut mods : Array Name := #[]
  for lib in libs do
    mods := mods ++ (← libModules root lib)
  mods ← pruneMissingOleans root mods
  if mods.isEmpty then
    throw <| IO.userError s!"review_cone: no modules found under libraries {libs}"
  -- `loadExts := true` folds imported environment-extension data (structure
  -- info, declaration ranges, …); it uses the interpreter, so initializers must
  -- be enabled first. Default `level := .private` loads all module data.
  enableInitializersExecution
  let (env, prunedMods) ← pruneAndImport root mods 20
  -- every config root must resolve to a project declaration; a typo fails here
  let bad := rootNames.filter fun n =>
    match env.find? n with
    | some _ => !isProjectModule prefixNames ((moduleFor? env n).getD Name.anonymous)
    | none => true
  if !bad.isEmpty then
    throw <| IO.userError s!"review_cone: these review-cone.toml roots are not project declarations: {bad.toList}"
  let json ← runMeta env (emitJson prefixNames root.toString rootNames depMode)
  let out := (← IO.getEnv "REVIEW_CONE_OUT").getD "review_cone.json"
  IO.FS.writeFile out json
  let what := if depMode then "every project decl, proofs included" else s!"{rootNames.size} roots"
  IO.println s!"wrote {out}  ({what}, {prunedMods.size} modules scanned)"
  (← IO.getStdout).flush
  -- Exit rather than return: once the JSON is on disk, tearing down an
  -- environment holding every imported module is pure cost. Safe only from the
  -- main thread — hence the `lean --run` entry point below, not an `#eval`.
  IO.Process.exit 0

end ReviewCone

/-- Run as a script (`lean --run`), never `#eval`. An `#eval` is elaborated in an
async snapshot on a worker thread; exiting the process from there tears the
frontend down under itself — losing every message (this file's own output
included) and, on macOS, segfaulting instead of exiting. -/
unsafe def main : IO Unit := ReviewCone.run
