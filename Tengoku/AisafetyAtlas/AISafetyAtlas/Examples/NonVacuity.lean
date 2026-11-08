module

import Tengoku.AisafetyAtlas.AISafetyAtlas.Explainability
import Tengoku.AisafetyAtlas.AISafetyAtlas.Verification.AgentBehavior
import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge.Embedded
import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge.Embedded.Composition
import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge.Embedded.Finite
import Tengoku.Seed.Data.Fintype.Card
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Non-vacuity witnesses for published gate predicates

These anonymous compile-time examples provide concrete inhabitants for the
hypotheses used by the published Rice and attribution bridges, and for the
abstract Breuer measurement core. The regret gate is witnessed in
`Examples.WorkbenchConsumers` by `binaryCorruption.halfMaximalRegretBound`.
No public declarations are added.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AISafetyAtlas.Examples.NonVacuity

private def zeroOnly : AISafetyAtlas.Verification.BehavioralProperty :=
  {behavior | behavior 0 = Part.some 0}

/-! A total, extensional property with one accepted and one rejected code. -/

private def twoFeatures : AISafetyAtlas.Explainability.FeatureIndex where
  P := 2
  L := 1
  hP := by decide
  groupOf := fun _ => 0

private def oppositeAttribution : Fin 2 → Bool → ℝ :=
  fun feature model =>
    if feature.val = 0 then
      if model then 1 else 0
    else
      if model then 0 else 1

/-! Two features in one group exchange order across two concrete models. -/

/-! A concrete Breuer-core model satisfying both hypotheses at once.

The global state is `Bool`, the apparatus has one reading, restriction is
constant, and every nonempty reading set infers every global state.  The
inference map meshes because the only apparatus reading is `()`, while proper
inclusion is witnessed by `false` and `true`.  Thus the two no-go propositions
below are not vacuous consequences of an inconsistent pair of hypotheses.
-/
private def unitRestriction : Bool → Unit := fun _ => ()

private def unitInference : AISafetyAtlas.Knowledge.Embedded.InferenceMap Bool Unit where
  infer _ := Set.univ
  infer_eq_union_singletons := by
    intro U
    ext s
    constructor
    · intro _
      obtain ⟨a, ha⟩ := U.2
      exact ⟨a, ha, Set.mem_univ _⟩
    · intro _
      exact Set.mem_univ _

private theorem unitMeshing :
    AISafetyAtlas.Knowledge.Embedded.Meshing unitRestriction unitInference := by
  intro a
  ext x
  constructor
  · rintro ⟨s, -, -⟩
    simp
  · intro hx
    cases a
    cases x
    exact ⟨false, Set.mem_univ _, rfl⟩

/-! ### Why there is no empty-apparatus witness here

Neither proposition assumes `Nonempty A`, which matches the printed statements.
Its absence is **faithfulness, not strength**, and no example can show otherwise:
a restriction `Ω → A` with `A` empty forces `Ω` empty, so there are no states
`s₁ s₂` to feed the proposition in the first place. Dropping the hypothesis
closes a gap in the *statement*, not in what the statement can be applied to.
Recorded here so nobody looks for the missing witness. -/

/-! ## Both Breuer hypotheses are load-bearing

The witnesses above inhabit the *hypotheses* of the two propositions. These
inhabit their *conclusions*, which is the half that stops them being vacuous: if
no meshing map ever measured every state, `no_meshing_inference_measures_all_states`
would hold for free and `ProperInclusion` would carry no weight; likewise if
`Distinguishes` were uninhabited.

One model settles both. The apparatus reads the whole state (`restrict = id` on
`Bool`), so proper inclusion *fails* — and exactly then the map does measure
every state and does distinguish the two. -/

private def boolRestriction : AISafetyAtlas.Knowledge.Embedded.Restriction Bool Bool :=
  id

private def boolInference : AISafetyAtlas.Knowledge.Embedded.InferenceMap Bool Bool where
  infer := fun U => U.1
  infer_eq_union_singletons := by
    intro U
    ext s
    constructor
    · intro hs
      exact ⟨s, hs, rfl⟩
    · rintro ⟨a, ha, hsa⟩
      have : s = a := hsa
      exact this ▸ ha

/-! ## Physical bridges (Composition / Finite)

These inhabit the *derived* proper-inclusion hypotheses, not the abstract
Breuer core alone: nontrivial remainder ⇒ collision, and a strict finite
cardinality gap ⇒ collision. The core module is unchanged. -/

open AISafetyAtlas.Knowledge.Embedded
open AISafetyAtlas.Knowledge.Embedded.Composition
open AISafetyAtlas.Knowledge.Embedded.Finite

/-! ### The bridged no-go results are not vacuous

The witnesses above inhabit the *hypotheses* the bridges derive
(`ProperInclusion`). These inhabit the bridges' full antecedent — a meshing map
**and** a cardinality gap at once — which is the half that shows the composite
theorems say something. Without them a reader cannot rule out that no meshing map
survives the gap and the conclusions hold for free.

`unitRestriction : Bool → Unit` with `unitInference` is exactly such a model:
`card Unit = 1 < 2 = card Bool`, and `unitMeshing` proves it meshes. -/

end AISafetyAtlas.Examples.NonVacuity
