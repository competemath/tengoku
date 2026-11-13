/-
Vendored from `google-deepmind/debate` (Apache-2.0) via the Lean v4.31.0 port
`LukaHobor/debate` @ `dafe25d`, and migrated in place to Lean v4.33.0. Changed at
the header only; ledger and rationale: `vendor/debate/PROVENANCE.md`.
-/

module

public import Tengoku.Seed.Topology.MetricSpace.Basic
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.Debate.Prob.Defs
public import Tengoku.Seed.Data.Vector.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/mbrcic/ai-safety-formalization-atlas@a65e32f80475, `AISafetyAtlas/Upstream/Debate/Comp/Oracle.lean`: removed 7 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

@[expose] public section
namespace Tengoku.AisafetyAtlas end Tengoku.AisafetyAtlas open Tengoku.AisafetyAtlas 
-- Linters off per `vendor/debate/PROVENANCE.md`; no correctness linter is
-- touched and incomplete proofs stay errors.

/-!
Stochastic oracle as a model of general, randomized computations

We formalize debate w.r.t. randomized computations allowed to query a stochastic oracle.
For simplicity, we embed all details of the computation as the oracle, including deterministic
features.  Concretely, we start with zero bits, and repeatedly prepend bits from the oracle
for some number of steps.  The final bit is the result.
-/

open Classical
open Tengoku.AisafetyAtlas.Prob
open Option (some none)
open scoped Real
noncomputable section

/-- A stochastic oracle-/
def _root_.Tengoku.AisafetyAtlas.Oracle := (n : ℕ) → List.Vector Bool n → Prob Bool

/-- n random bits from an oracle, each given by feeding the oracle the previous result.
    This models an arbitrary computation, as o can behave differently based on input length.-/
def Tengoku.AisafetyAtlas.Oracle.fold (o : Oracle) : (n : ℕ) → Prob (List.Vector Bool n)
| 0 => pure List.Vector.nil
| n+1 => do
  let y ← o.fold n
  let x ← o _ y
  return y.cons x

/-- The (n+1)th bit of o.fold-/
def Tengoku.AisafetyAtlas.Oracle.final (o : Oracle) (t : ℕ) : Prob Bool := do
  let x ← o.fold (t+1)
  return x.head

/-- The distance between two oracles is the sup of their probability differences-/
instance : Dist Oracle where
  dist o0 o1 := ⨆ n, ⨆ y : List.Vector Bool n, |(o0 _ y).prob true - (o1 _ y).prob true|

/-- An oracle computation is k-Lipschitz if the final probability differs by ≤ k * oracle dist.
    We define this asymmetrically, as we want the neighborhood of a particular oracle.-/
structure Tengoku.AisafetyAtlas.Oracle.lipschitz (o : Oracle) (t : ℕ) (k : ℝ) : Prop where
  k0 : 0 ≤ k
  le : ∀ o' : Oracle, |(o.final t).prob true - (o'.final t).prob true| ≤ k * dist o o'
-- Tengoku: root names of this library moved to Tengoku.AisafetyAtlas so they do not collide with other libraries (generated)
