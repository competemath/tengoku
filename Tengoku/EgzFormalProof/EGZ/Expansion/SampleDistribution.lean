import Tengoku.EgzFormalProof.EGZ.Expansion.FiniteProbability
import Tengoku.EgzFormalProof.EGZ.Expansion.ThickSupport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Mixtures of valid finite samples

Each component has total mass at most one.  Removing a small exceptional
set from every sample space retains positive mass and preserves thickness
provided one component witnesses escape from each central slab.
-/

open scoped BigOperators Classical

namespace EGZ.Expansion

section FiniteSamples

variable {I β : Type*} [Fintype I] [Fintype β]
  (A : I → Type*) [∀ i, Fintype (A i)]
  (value : ∀ i, A i → β) (valid : ∀ i, A i → Prop)

/-- Equal mixture of the valid samples, retaining their vector values.-/
noncomputable def sampleWeight (v : β) : ℝ :=
  ∑ i, finiteProb (fun x : A i ↦ valid i x ∧ value i x = v)

/--
@isnad1 id=le.0h6v.s5.66ccce126380 from=translated src=- shape=a4b9214b vocab=89544f1b
-/
theorem sampleWeight_nonneg (v : β) : 0 ≤ sampleWeight A value valid v :=
  Finset.sum_nonneg (fun i _ ↦ finiteProb_nonneg _)

/--
@isnad1 id=eq.0h5v.s6.57d2367364ff from=translated src=- shape=3ccc5c9a vocab=56f0414b
-/
theorem finiteProb_sum_fibres {α : Type*} [Fintype α]
    (f : α → β) (Q : α → Prop) (P : β → Prop) :
    (∑ v, if P v then finiteProb (fun x ↦ Q x ∧ f x = v) else 0) =
      finiteProb (fun x ↦ Q x ∧ P (f x)) := by
  classical
  have hterm (v : β) : (if P v then finiteProb (fun x ↦ Q x ∧ f x = v) else 0) =
      finiteProb (fun x ↦ Q x ∧ f x = v ∧ P v) := by
    by_cases hv : P v <;> simp [hv]
  simp_rw [hterm]
  unfold finiteProb
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro x _
  by_cases hx : Q x
  · simp only [hx, true_and]
    by_cases hp : P (f x)
    · have heq (v : β) : (f x = v ∧ P v) ↔ f x = v := by
        constructor
        · exact And.left
        · intro h; exact ⟨h, h ▸ hp⟩
      simp only [heq, ite_eq_left hp]
      simp
    · have heq (v : β) : ¬(f x = v ∧ P v) := by
        rintro ⟨rfl, hv⟩
        exact hp hv
      simp only [heq, ↓reduceIte, Finset.sum_const_zero, ite_eq_right hp]
  · simp [hx]

/-- Mass on a set of vectors is the sum of the corresponding valid-sample
probabilities over all components.
@isnad1 id=eq.0h6v.s6.66a0bf99d2fe from=translated src=- shape=18528a13 vocab=cd6d0546
-/
theorem sampleWeight_massOn (P : β → Prop) :
    (∑ v, if P v then sampleWeight A value valid v else 0) =
      ∑ i, finiteProb (fun x : A i ↦ valid i x ∧ P (value i x)) := by
  classical
  simp only [sampleWeight]
  have heq (v : β) : (if P v then ∑ i, finiteProb (fun x : A i ↦ valid i x ∧ value i x = v) else 0) =
      ∑ i, if P v then finiteProb (fun x : A i ↦ valid i x ∧ value i x = v) else 0 := by
    by_cases hv : P v <;> simp [hv]
  simp_rw [heq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact finiteProb_sum_fibres (value i) (valid i) P

/--
@isnad1 id=eq.0h5v.s6.449ccdcca365 from=translated src=- shape=452b75a7 vocab=1767fd31
-/
theorem sampleWeight_mass : (∑ v, sampleWeight A value valid v) =
    ∑ i, finiteProb (valid i) := by
  simpa using sampleWeight_massOn A value valid (fun _ ↦ True)

variable [∀ i, Nonempty (A i)]

/--
@isnad1 id=le.0h5v.s6.8cf2e9c89de0 from=translated src=- shape=1b8c9275 vocab=0a0d85af
-/
theorem sampleWeight_mass_le : (∑ v, sampleWeight A value valid v) ≤ Fintype.card I := by
  rw [sampleWeight_mass]
  calc
    (∑ i, finiteProb (valid i)) ≤ ∑ _i : I, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ finiteProb_le_one _
    _ = _ := by simp

/--
@isnad1 id=le.1h6v.s6.2dfdc7ec1dea from=translated src=- shape=b1d9cc63 vocab=968eff1a
-/
theorem sampleWeight_mass_ge {e : ℝ}
    (hbad : ∀ i, finiteProb (fun x : A i ↦ ¬valid i x) ≤ e) :
    (Fintype.card I : ℝ) * (1 - e) ≤ ∑ v, sampleWeight A value valid v := by
  rw [sampleWeight_mass]
  calc
    _ = ∑ _i : I, (1 - e) := by simp; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have hh := hbad i
      rw [finiteProb_not] at hh
      linarith

/--
@isnad1 id=ex.1h6v.s6.d062ee1396cd from=translated src=- shape=83f0f44f vocab=d4b6e97b
-/
theorem sampleWeight_pos_exists {v : β} (hv : 0 < sampleWeight A value valid v) :
    ∃ (i : I) (x : A i), valid i x ∧ value i x = v := by
  classical
  by_contra! hn
  have hzero : sampleWeight A value valid v = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have heq : (fun x : A i ↦ valid i x ∧ value i x = v) = (fun _ ↦ False) := by
      funext x
      exact propext ⟨fun h ↦ hn i x h.1 h.2, False.elim⟩
    rw [heq, finiteProb_false]
  linarith

end FiniteSamples

/-- Removing an exceptional set loses at most its probability from any
event, without any independence assumption.
@isnad1 id=le.0h3v.s5.b1309b0ca042 from=translated src=- shape=cb1d3d26 vocab=18443622
-/
theorem finiteProb_and_ge_sub {A : Type*} [Fintype A]
    (P Q : A → Prop) : finiteProb Q - finiteProb (fun x ↦ ¬P x) ≤
      finiteProb (fun x ↦ P x ∧ Q x) := by
  classical
  unfold finiteProb
  rw [← Finset.expect_sub_distrib]
  apply Finset.expect_le_expect
  intro x _
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq]

section Thickness

variable {p d W : ℕ} [NeZero p]
  {I : Type*} [Fintype I] [Nonempty I]
  (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
  (value : ∀ i, A i → FpCoord p d) (valid : ∀ i, A i → Prop)
  {η : ℝ} (hη : 0 < η) (hηone : η ≤ 1)
  (hbad : ∀ i, finiteProb (fun x : A i ↦ ¬valid i x) ≤ η / 2)

include hη hηone hbad

/--
@isnad1 id=lt.3h7v.s7.99ed19ba4aa3 from=translated src=- shape=dd607736 vocab=331cbef1
-/
theorem sampleWeight_mass_pos : 0 < ∑ v, sampleWeight A value valid v := by
  have hh := sampleWeight_mass_ge A value valid hbad
  have hI : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have : 0 < (Fintype.card I : ℝ) * (1 - η / 2) := mul_pos hI (by linarith)
  linarith

/--
@isnad1 id=iscentra.4h8v.s10.1b396cd0ee07 from=translated src=- shape=ca8da928 vocab=3b8be553
-/
theorem sampleWeight_centrallyThick
    (hout : ∀ ξ : FpCoord p d →ₗ[ZMod p] ZMod p, ξ ≠ 0 →
      ∃ i, η ≤ finiteProb (fun x : A i ↦
        ¬ HasBoundedRepresentative p W (ξ (value i x)))) :
    IsCentrallyThick (sampleWeight A value valid) W (η / (2 * Fintype.card I)) := by
  classical
  intro ξ hξ
  obtain ⟨i, hi⟩ := hout ξ hξ
  have hsample : η / 2 ≤ finiteProb (fun x : A i ↦ valid i x ∧
      ¬ HasBoundedRepresentative p W (ξ (value i x))) := by
    have hh := finiteProb_and_ge_sub (valid i)
      (fun x ↦ ¬ HasBoundedRepresentative p W (ξ (value i x)))
    have hb := hbad i
    linarith
  have hsum : η / 2 ≤ ∑ j, finiteProb (fun x : A j ↦ valid j x ∧
      ¬ HasBoundedRepresentative p W (ξ (value j x))) :=
    hsample.trans (Finset.single_le_sum
      (f := fun j ↦ finiteProb (fun x : A j ↦ valid j x ∧
        ¬ HasBoundedRepresentative p W (ξ (value j x))))
      (fun j _ ↦ finiteProb_nonneg _) (Finset.mem_univ i))
  have hmass := sampleWeight_mass_le A value valid
  have hI : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  calc
    η / (2 * Fintype.card I) * (∑ v, sampleWeight A value valid v) ≤
        η / (2 * Fintype.card I) * Fintype.card I :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = η / 2 := by field_simp
    _ ≤ ∑ j, finiteProb (fun x : A j ↦ valid j x ∧
        ¬ HasBoundedRepresentative p W (ξ (value j x))) := hsum
    _ = _ := by
      rw [← sampleWeight_massOn A value valid (fun v ↦ ¬ HasBoundedRepresentative p W (ξ v))]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> rfl

end Thickness

end EGZ.Expansion
