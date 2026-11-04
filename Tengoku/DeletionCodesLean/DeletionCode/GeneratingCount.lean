import Tengoku.DeletionCodesLean.DeletionCode.RecordSerialization
import Tengoku.Seed.SetTheory.Cardinal.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms generatingData_record_exists` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms encodeGeneratingData_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms generatingData_finite` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms generatingData_card_le_description` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms editedFamily_component_count_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms generatingData_card_bound` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Counting all finite recovered data represented by generating edited families.
Ranks and unused infinite word tails are omitted from the counted objects.
Finiteness and the cardinal bound follow from the proved finite-record decoder
coverage; neither an injective encoding nor finiteness is assumed as a premise.
-/
namespace DeletionCode.GeneratingCount

open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount

/-- Finite headers and finite negative words admitting a generating-family witness.-/
def GeneratingData (x : Letters) (n k ν c : ℕ) (data : RecoveredData ν) : Prop :=
  ∃ E : EditedFamily (Fin ν) k,
    E.family.Generating x n (windowLength k) ∧
    Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) = c ∧
    dataOfFamily E = data

/--
@isnad1 id=ex.2h6v.s6.d4f9c45ba6bc from=translated src=- shape=a1ad49ef vocab=35c24c5c
-/
theorem generatingData_record_exists (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k)
    (data : {data : RecoveredData ν // GeneratingData x n k ν c data}) :
    ∃ d : Description n (windowLength k) ν c,
      decodeDescription x n k ν c hν d = some data.val := by
  obtain ⟨E, hg, hc, hdata⟩ := data.property
  obtain ⟨d, hd⟩ := serialized_generating_coverage E x n c hν hx hg hc
  exact ⟨d, by simpa only [hdata] using hd⟩

/-- Choose a successful finite record, justified by the concrete coverage theorem.-/
noncomputable def encodeGeneratingData (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k)
    (data : {data : RecoveredData ν // GeneratingData x n k ν c data}) :
    Description n (windowLength k) ν c :=
  Classical.choose (generatingData_record_exists x n k ν c hν hx data)

/--
@isnad1 id=eq.2h6v.s6.5c1c179f4d3a from=translated src=- shape=da0462b4 vocab=9579a2e4
-/
theorem decode_encodeGeneratingData (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k)
    (data : {data : RecoveredData ν // GeneratingData x n k ν c data}) :
    decodeDescription x n k ν c hν (encodeGeneratingData x n k ν c hν hx data) = some data.val :=
  Classical.choose_spec (generatingData_record_exists x n k ν c hν hx data)

/--
@isnad1 id=injectiv.2h5v.s5.f829ca168375 from=translated src=- shape=8e210c0c vocab=7208f5f2
-/
theorem encodeGeneratingData_injective (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Function.Injective (encodeGeneratingData x n k ν c hν hx) := by
  intro a b hab
  have ha := decode_encodeGeneratingData x n k ν c hν hx a
  have hb := decode_encodeGeneratingData x n k ν c hν hx b
  rw [hab] at ha
  exact Subtype.ext (Option.some.inj (ha.symm.trans hb))

/-- The entire class of generating finite data is finite, without a Fintype premise.
@isnad1 id=finite.2h5v.s5.38d3c1c2188d from=translated src=- shape=b541debe vocab=88315362
-/
theorem generatingData_finite (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Finite {data : RecoveredData ν // GeneratingData x n k ν c data} :=
  Finite.of_injective (encodeGeneratingData x n k ν c hν hx)
    (encodeGeneratingData_injective x n k ν c hν hx)

/--
@isnad1 id=le.2h5v.s8.fa434ec142ee from=translated src=- shape=016249c4 vocab=82616055
-/
theorem generatingData_card_le_description (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} ≤
      Fintype.card (Description n (windowLength k) ν c) := by
  simpa only [Nat.card_eq_fintype_card] using
    Nat.card_le_card_of_injective (encodeGeneratingData x n k ν c hν hx)
      (encodeGeneratingData_injective x n k ν c hν hx)

/-- There cannot be more supported graph components than indexed bubbles.
@isnad1 id=le.0h3v.s4.6215d8b8a5af from=translated src=- shape=13e27f0a vocab=1abfbc31
-/
theorem editedFamily_component_count_le {ν k : ℕ} (E : EditedFamily (Fin ν) k) :
    Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) ≤ ν := by
  classical
  rw [← Fintype.card_congr (componentGraphEquiv E)]
  let : Fintype (GeneratingModel.Components E) := componentsFintype E
  let f : Fin ν → GeneratingModel.Components E :=
    Quotient.mk (GeneratingModel.componentSetoid E.family (windowLength k))
  have hsurj : Function.Surjective f := by
    intro C
    induction C using Quotient.inductionOn with
    | _ b => exact ⟨b, rfl⟩
  have hcard := Fintype.card_le_of_surjective f hsurj
  simpa only [Fintype.card_fin] using hcard

/--
@isnad1 id=le.1h6v.s4.52f53ae95ada from=translated src=- shape=3bfc9610 vocab=fe588201
-/
theorem generatingData_components_le (x : Letters) (n k ν c : ℕ)
    (data : RecoveredData ν) (hdata : GeneratingData x n k ν c data) : c ≤ ν := by
  obtain ⟨E, _, hc, _⟩ := hdata
  rw [← hc]
  exact editedFamily_component_count_le E

/--
@isnad1 id=le.3h5v.s6.e7413857d230 from=translated src=- shape=78115acd vocab=b2872e7f
-/
theorem generatingData_card_bound_of_le (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) (hc : c ≤ ν) :
    Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by
  exact (generatingData_card_le_description x n k ν c hν hx).trans
    (description_bound n (windowLength k) ν c (by unfold windowLength; omega) hν hc)

/-- The complete class of generating finite path data obeys the description bound.
@isnad1 id=le.2h5v.s6.eb1cba968294 from=translated src=- shape=0ea6e903 vocab=b2872e7f
-/
theorem generatingData_card_bound (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by
  by_cases hc : c ≤ ν
  · exact generatingData_card_bound_of_le x n k ν c hν hx hc
  · let : IsEmpty {data : RecoveredData ν // GeneratingData x n k ν c data} :=
      ⟨fun data => hc (generatingData_components_le x n k ν c data.val data.property)⟩
    simp

end DeletionCode.GeneratingCount
