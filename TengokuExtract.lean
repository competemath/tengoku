/-
The index extractor: walks the Lean environment of the tree and writes one
JSON object per declaration (decls.jsonl) plus its dependency edges
(deps.jsonl). Reads the compiled tree from the cache; compiles nothing.

  lake build tengoku-extract
  lake env .lake/build/bin/tengoku-extract [--module Tengoku.All]... [--out index] [--limit N]
-/
import Lean
open Lean Meta

structure Args where
  modules : Array Name := #[]
  out : System.FilePath := "index"
  limit : Nat := 0

partial def parseArgs : List String → Args → Args
  | "--module" :: m :: rest, a => parseArgs rest { a with modules := a.modules.push m.toName }
  | "--out" :: o :: rest, a => parseArgs rest { a with out := o }
  | "--limit" :: n :: rest, a => parseArgs rest { a with limit := n.toNat! }
  | _ :: rest, a => parseArgs rest a
  | [], a => a

/-- Auxiliary and compiler-generated names nobody searches for. -/
def skipName (n : Name) : Bool :=
  n.isAnonymous || n.hasMacroScopes || n.isInternal ||
  n.components.any (fun c => match c with
    | .str _ s => s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
        s.startsWith "instDecidableEq" && false
    | _ => false) ||
  (match n with
    | .str _ s => s ∈ ["rec", "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow", "noConfusion",
        "noConfusionType", "sizeOf_spec", "inj", "injEq", "ofNat", "mk.injEq", "mk.sizeOf_spec"]
    | _ => false)

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor" | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"

def headConst (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ => some n
  | _ => none

def fmt (f : Format) : String := f.pretty (width := 1000000)

def binderKind : BinderInfo → String
  | .default => "explicit" | .implicit => "implicit" | .strictImplicit => "strict" | .instImplicit => "inst"

/-- Everything the index wants to know about one declaration. -/
def describe (env : Environment) (simp : SimpTheorems) (n : Name) (ci : ConstantInfo) : MetaM (Json × Array Name) := do
  let type ← instantiateMVars ci.type
  let (binders, concl, hypHeads) ← forallTelescope type fun xs body => do
    let mut bs : Array Json := #[]
    let mut heads : Array Name := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      bs := bs.push (Json.mkObj [("name", toString d.userName), ("kind", binderKind d.binderInfo), ("type", fmt (← ppExpr d.type))])
      if let some h := headConst d.type then heads := heads.push h
    return (bs, body, heads)
  let stmt := fmt (← ppExpr type)
  let consts := type.getUsedConstants.filter (!skipName ·)
  let valueConsts := (ci.value?.map (·.getUsedConstants)).getD #[] |>.filter (!skipName ·)
  let deps := (consts ++ valueConsts).foldl (fun (acc : Array Name) c => if acc.contains c || c == n then acc else acc.push c) #[]
  let modIdx := env.getModuleIdxFor? n
  let module := modIdx.bind (fun i => env.header.moduleNames[i.toNat]?) |>.map toString |>.getD ""
  let doc ← findDocString? env n
  let range ← findDeclarationRanges? n
  let deprecated := (Lean.Linter.deprecatedAttr.getParam? env n).map (fun d => (d.newName?.map toString).getD "")
  let j := Json.mkObj [
    ("name", toString n), ("kind", kindOf ci), ("module", module),
    ("line", (range.map (·.range.pos.line)).map (Json.num ·) |>.getD Json.null),
    ("statement", stmt), ("binders", Json.arr binders),
    ("conclusion_head", (headConst concl).map (Json.str ∘ toString) |>.getD Json.null),
    ("hypothesis_heads", Json.arr (hypHeads.map (Json.str ∘ toString))),
    ("constants_type", Json.arr (consts.map (Json.str ∘ toString))),
    ("universe_params", Json.arr (ci.levelParams.toArray.map (Json.str ∘ toString))),
    ("docstring", doc.map Json.str |>.getD Json.null),
    ("is_simp", Json.bool (simp.isLemma (.decl n))),
    ("is_instance", Json.bool (isInstanceCore env n)),
    ("deprecated_for", deprecated.map Json.str |>.getD Json.null),
    ("proof_depth", (ci.value?.map (fun v => Json.num v.approxDepth.toNat)).getD Json.null),
    ("value_consts", Json.num valueConsts.size)]
  return (j, deps)

def run (a : Args) : MetaM Unit := do
  let env ← getEnv
  IO.FS.createDirAll a.out
  let hd ← IO.FS.Handle.mk (a.out / "decls.jsonl") .write
  let he ← IO.FS.Handle.mk (a.out / "deps.jsonl") .write
  let simp ← getSimpTheorems
  let mut count := 0
  let mut skipped := 0
  for (n, ci) in env.constants.toList do
    if a.limit > 0 && count ≥ a.limit then break
    if skipName n || (match ci with | .recInfo _ => true | .quotInfo _ => true | _ => false) then
      skipped := skipped + 1
      continue
    -- The tree's own modules only: nothing from Init/Lean/Std internals.
    let fromTree := (env.getModuleIdxFor? n).bind (fun i => env.header.moduleNames[i.toNat]?) |>.map (fun m => (`Tengoku).isPrefixOf m) |>.getD false
    if !fromTree then
      skipped := skipped + 1
      continue
    try
      let (j, deps) ← describe env simp n ci
      hd.putStrLn j.compress
      he.putStrLn (Json.mkObj [("from", toString n), ("to", Json.arr (deps.map (Json.str ∘ toString)))]).compress
      count := count + 1
      if count % 20000 == 0 then IO.eprintln s!"… {count} declarations"
    catch e =>
      IO.eprintln s!"skip {n}: {← e.toMessageData.toString}"
  hd.flush; he.flush
  IO.println s!"wrote {count} declarations ({skipped} skipped) to {a.out}"

unsafe def main (argv : List String) : IO UInt32 := do
  enableInitializersExecution
  let a := parseArgs argv {}
  let a := if a.modules.isEmpty then { a with modules := #[`Tengoku.All] } else a
  initSearchPath (← findSysroot)
  let env ← importModules (a.modules.map fun m => { module := m }) {} (trustLevel := 0) (loadExts := true)
  let ctx : Core.Context := { fileName := "<tengoku-extract>", fileMap := default, maxHeartbeats := 0 }
  let _ ← (run a).run'.toIO ctx { env }
  return 0
