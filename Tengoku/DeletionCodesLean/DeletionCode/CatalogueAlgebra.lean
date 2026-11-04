import Tengoku.DeletionCodesLean.DeletionCode.RelationSavings
import Tengoku.Seed.LinearAlgebra.Finsupp.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms catalogue_signed_unit` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms catalogue_nonzero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms new_relation_support` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Actual catalogue rules are nonzero signed-unit vectors when t is positive.
A new in-span rule distinct from every old rule and its negative therefore
has a finite relation with at least two nonzero coefficients.
-/
namespace DeletionCode.CatalogueAlgebra

open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks CatalogueBridge
open scoped BigOperators

def rational {L : ℕ} (u : Gram L → ℤ) : Gram L → ℚ := fun g => (u g : ℚ)

/--
@isnad1 id=injectiv.0h1v.s3.64df97e7acc5 from=translated src=- shape=a63464cb vocab=696b7aff
-/
theorem rational_injective {L : ℕ} : Function.Injective (@rational L) := by
  intro u v h
  funext g
  have hg : (u g : ℚ) = (v g : ℚ) := congrFun h g
  exact_mod_cast hg

/--
@isnad1 id=eq.0h1v.s5.89d4ad37f959 from=translated src=- shape=713ddbf1 vocab=9fb80127
-/
@[simp] theorem rational_zero {L : ℕ} : rational (0 : Gram L → ℤ) = 0 := by
  funext g
  simp [rational]

/--
@isnad1 id=eq.0h2v.s5.2d2a9a3d4b75 from=translated src=- shape=169fcc1f vocab=5e38502a
-/
@[simp] theorem rational_neg {L : ℕ} (u : Gram L → ℤ) : rational (-u) = -rational u := by
  funext g
  simp [rational]

/--
@isnad1 id=signedun.1h3v.s4.dbc47110ce4f from=translated src=- shape=37d3b64c vocab=edd3bb6f
-/
theorem catalogue_signed_unit {t k : ℕ} (u : Gram (windowLength k) → ℤ)
    (hu : CatalogueRule t k u) : WitnessAlgebra.SignedUnitVector (rational u) := by
  classical
  obtain ⟨words, hvalid, _, hvalue⟩ := hu
  have hd : VertexDisjointOn (indexedFamily words (fun _ => (0 : Fin 1))).family
      (windowLength k) Finset.univ := by
    simpa only [Finset.filter_true] using hvalid.within_rule_disjoint (0 : Fin 1)
  have h := WitnessAlgebra.ruleSpectrum_signed_unit _ _ hvalid.geometry Finset.univ hd
  change WitnessAlgebra.SignedUnitVector (fun g => (u g : ℚ))
  simpa only [hvalue] using h

/--
@isnad1 id=ne.2h3v.s5.26f1f699ab97 from=translated src=- shape=b7166118 vocab=17a96eab
-/
theorem catalogue_nonzero {t k : ℕ} (ht : 1 ≤ t)
    (u : Gram (windowLength k) → ℤ) (hu : CatalogueRule t k u) : u ≠ 0 := by
  classical
  obtain ⟨words, hvalid, _, hvalue⟩ := hu
  let E := indexedFamily words (fun _ => (0 : Fin 1))
  let b : Fin (2 * t) := ⟨0, by omega⟩
  have hd : VertexDisjointOn E.family (windowLength k) Finset.univ := by
    simpa only [Finset.filter_true] using hvalid.within_rule_disjoint (0 : Fin 1)
  let g := gram (E.family.path b false) (windowLength k) 0
  have hgram : g ∈ windowSet (E.family.path b false) (windowLength k)
      (E.family.extra b false) := ⟨⟨0, by omega⟩, rfl⟩
  have hneg := rule_negative_of_window E.family (windowLength k) hvalid.geometry
    Finset.univ hd b (Finset.mem_univ b) g hgram
  rw [hvalue] at hneg
  intro hz
  rw [hz] at hneg
  norm_num at hneg

/-- Removing zero coefficients gives a genuine finite relation; novelty up to
sign forces at least two participating rules.
@isnad1 id=ex.5h4v.s8.d55ab44e8374 from=translated src=- shape=58119fca vocab=248b873e
-/
theorem new_relation_support {t k : ℕ} (ht : 1 ≤ t) (G : RuleSet k)
    (hcat : ∀ u ∈ G, CatalogueRule t k u)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hnew : ∀ u ∈ G, w ≠ u ∧ w ≠ -u)
    (hspan : rational w ∈ Submodule.span ℚ (rational '' (↑G : Set _))) :
    ∃ I : RuleSet k, I ⊆ G ∧ 2 ≤ I.card ∧
      ∃ a : (Gram (windowLength k) → ℤ) → ℚ,
        (∀ u ∈ I, a u ≠ 0) ∧
        ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ) := by
  classical
  obtain ⟨a, hsum⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' ℚ).mp hspan
  let I := G.filter (fun u => a u ≠ 0)
  have hIG : I ⊆ G := Finset.filter_subset _ _
  have ha : ∀ u ∈ I, a u ≠ 0 := fun u hu => (Finset.mem_filter.mp hu).2
  have hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ) := by
    intro g
    have h := congrFun hsum g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rational] at h
    rw [← h]
    symm
    apply Finset.sum_subset hIG
    intro u huG huI
    have hz : a u = 0 := by
      by_contra hne
      exact huI (Finset.mem_filter.mpr ⟨huG, hne⟩)
    simp [hz]
  have hcard : 2 ≤ I.card := by
    by_contra hnot
    have hsmall : I.card ≤ 1 := by omega
    by_cases hzero : I.card = 0
    · have hIempty := Finset.card_eq_zero.mp hzero
      have hwzero : w = 0 := by
        funext g
        have h := hrel g
        simp only [hIempty, Finset.sum_empty] at h
        exact_mod_cast h
      exact catalogue_nonzero ht w hw hwzero
    · have hone : I.card = 1 := by omega
      obtain ⟨u, hI⟩ := Finset.card_eq_one.mp hone
      have huI : u ∈ I := by rw [hI]; exact Finset.mem_singleton_self u
      have huG := hIG huI
      have hlinear : rational w = a u • rational u := by
        funext g
        simpa only [hI, Finset.sum_singleton, rational, Pi.smul_apply, smul_eq_mul]
          using hrel g
      have hu0 : rational u ≠ 0 := by
        intro hu0
        apply catalogue_nonzero ht u (hcat u huG)
        exact rational_injective (hu0.trans rational_zero.symm)
      rcases WitnessAlgebra.scalar_multiple_eq_or_neg (rational u) (rational w) (a u)
        (catalogue_signed_unit u (hcat u huG)) (catalogue_signed_unit w hw)
        hu0 (ha u huI) hlinear with heq | heq
      · exact (hnew u huG).1 (rational_injective heq)
      · exact (hnew u huG).2 (rational_injective (heq.trans (rational_neg u).symm))
  exact ⟨I, hIG, hcard, a, ha, hrel⟩

end DeletionCode.CatalogueAlgebra
