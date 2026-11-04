import Tengoku.DeletionCodesLean.DeletionCode.RuleReconstruction
import Tengoku.DeletionCodesLean.DeletionCode.GeneratingCount

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms ruleSet_data_exists` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms chooseRuleData_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms generatingRuleSet_finite` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms generatingRuleSet_card_le_data` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms generatingRuleSet_card_bound` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Counting signed generating rule sets with a fixed bubble-to-rule indexing.
The class is defined by actual signed spectra and structural bubble geometry.
Signed generation is converted to word generation, and recovered finite data
determines the rule set. No finiteness or injective coding premise is assumed.
Additional catalogue restrictions only reduce this class.
-/
namespace DeletionCode.SignedRuleCount

open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RecordSerialization GeneratingCount DescriptionCount

abbrev RuleSet (k : ℕ) := Finset (Gram (windowLength k) → ℤ)

/-- Rule sets admitting indexed, disjoint bubbles and signed generating provenance.-/
def GeneratingRuleSet (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : RuleSet k) : Prop :=
  ∃ E : EditedFamily (Fin ν) k,
    (∀ b, E.rank b = (group b).val) ∧
    BubbleGeometry E.family (windowLength k) ∧
    (∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) ∧
    SignedGenerating E.family x n (windowLength k) ∧
    Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) = c ∧
    rulesOfFamily E group = Q

/-- Every admitted signed rule set has a generating finite-data preimage.
@isnad1 id=ex.1h8v.s5.4ecf1b42d6dd from=translated src=- shape=abcd5ec3 vocab=5aa430ee
-/
theorem ruleSet_data_exists (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : RuleSet k) (hQ : GeneratingRuleSet x n k ν R c group Q) :
    ∃ data : RecoveredData ν, GeneratingData x n k ν c data ∧ rulesOfData k group data = Q := by
  obtain ⟨E, _, H, hdis, hgen, hc, hQ⟩ := hQ
  have hg := signed_generating_implies_generating E.family x n (windowLength k) H hdis hgen
  exact ⟨dataOfFamily E, ⟨E, hg, hc, rfl⟩, (rules_roundtrip E group).trans hQ⟩

/-- Choose finite recovered data, whose existence was proved from signed provenance.-/
noncomputable def chooseRuleData (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q}) :
    {data : RecoveredData ν // GeneratingData x n k ν c data} :=
  ⟨Classical.choose (ruleSet_data_exists x n k ν R c group Q.val Q.property),
    (Classical.choose_spec (ruleSet_data_exists x n k ν R c group Q.val Q.property)).1⟩

/--
@isnad1 id=eq.0h8v.s6.9746fadf94e9 from=translated src=- shape=ce81869c vocab=a1e4dc82
-/
theorem rulesOf_chosenData (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q}) :
    rulesOfData k group (chooseRuleData x n k ν R c group Q).val = Q.val :=
  (Classical.choose_spec (ruleSet_data_exists x n k ν R c group Q.val Q.property)).2

/-- Deterministic rule reconstruction makes the chosen preimage assignment injective.
@isnad1 id=injectiv.0h7v.s5.b163468aa2a5 from=translated src=- shape=935d523b vocab=f24e245d
-/
theorem chooseRuleData_injective (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R) :
    Function.Injective (chooseRuleData x n k ν R c group) := by
  intro Q₁ Q₂ heq
  apply Subtype.ext
  calc
    Q₁.val = rulesOfData k group (chooseRuleData x n k ν R c group Q₁).val :=
      (rulesOf_chosenData x n k ν R c group Q₁).symm
    _ = rulesOfData k group (chooseRuleData x n k ν R c group Q₂).val :=
      congrArg (fun data : {data : RecoveredData ν // GeneratingData x n k ν c data} =>
        rulesOfData k group data.val) heq
    _ = Q₂.val := rulesOf_chosenData x n k ν R c group Q₂

/--
@isnad1 id=finite.2h7v.s5.17205ba22f26 from=translated src=- shape=a8bad0fe vocab=425d48aa
-/
theorem generatingRuleSet_finite (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Finite {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} := by
  let : Finite {data : RecoveredData ν // GeneratingData x n k ν c data} :=
    generatingData_finite x n k ν c hν hx
  exact Finite.of_injective (chooseRuleData x n k ν R c group)
    (chooseRuleData_injective x n k ν R c group)

/--
@isnad1 id=le.2h7v.s6.f103d2fa9858 from=translated src=- shape=8708371f vocab=7c61c56c
-/
theorem generatingRuleSet_card_le_data (x : Letters) (n k ν R c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} ≤
      Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} := by
  let : Finite {data : RecoveredData ν // GeneratingData x n k ν c data} :=
    generatingData_finite x n k ν c hν hx
  exact Nat.card_le_card_of_injective (chooseRuleData x n k ν R c group)
    (chooseRuleData_injective x n k ν R c group)

/-- The entire class of such signed generating rule sets satisfies the finite-record bound.
@isnad1 id=le.2h7v.s6.048f3b7c7206 from=translated src=- shape=f4ad5a8b vocab=cadd9bc2
-/
theorem generatingRuleSet_card_bound (x : Letters) (n k ν R c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by
  exact (generatingRuleSet_card_le_data x n k ν R c group hν hx).trans
    (generatingData_card_bound x n k ν c hν hx)

end DeletionCode.SignedRuleCount
