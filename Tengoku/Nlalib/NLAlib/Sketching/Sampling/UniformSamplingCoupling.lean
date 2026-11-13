/-
Copyright (c) 2026 Diar Heidary.

The support-extension/permutation architecture is adapted from
Rerandomized-Subsampled-Trigonometric-Transforms, SRHT/SamplingCoupling.lean,
commit 929653a019eb4910fc6efb9cb34cc3c3c2f949d4. This version couples iid
sequences to exact-size subsets and uses Mathlib PMF directly.

MIT License

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
import Tengoku.Seed.Probability.Distributions.Uniform
import Tengoku.Nlalib.NLAlib.ForMathlib.Data.ExactRowSubset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A literal finite iid/subset sampling coupling

An iid uniform sequence is symmetrized together with a deterministic size-`k`
extension of its support by one independent uniform label permutation. Its
sequence marginal remains iid uniform; its subset marginal is uniform over
all size-`k` subsets. Source: Hoeffding 1963, Theorem 4. Supports atlas `srht-ose`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Classical
namespace NLAlib

/-- Real weights of a mapped finite PMF are ordinary fiber sums.
Source: Mathlib PMF map.
@isnad1 id=eq.0h5v.s6.714f4a84e361 from=translated src=- shape=ca0915da vocab=8011b10b
-/
theorem toReal_map_pmf_apply {α β : Type*} [Fintype α] (p : PMF α) (f : α → β) (b : β) :
    ((p.map f) b).toReal = ∑ a, if f a = b then (p a).toReal else 0 := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : f a = b
    · rw [ite_eq_left ha.symm, ite_eq_left ha]
    · rw [ite_eq_right (Ne.symm ha), ite_eq_right ha, ENNReal.toReal_zero]
  · intro a _
    split_ifs
    · exact p.apply_ne_top a
    · simp

/-- Real weights of every finite PMF sum to one.
Source: Mathlib PMF normalization.
@isnad1 id=eq.0h2v.s5.860e80102d13 from=translated src=- shape=821dc207 vocab=947d49fd
-/
theorem sum_toReal_pmf {α : Type*} [Fintype α] (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  have hh : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  have hr := congrArg ENNReal.toReal hh
  rwa [ENNReal.toReal_sum (fun a _ => p.apply_ne_top a), ENNReal.toReal_one] at hr

/-- Equivariant mapping preserves invariance of the finite probability masses.
Source: the support-extension coupling architecture.
@isnad1 id=eq.2h7v.s7.5ed1f1b4fad7 from=translated src=- shape=1d3c7e00 vocab=756e0199
-/
theorem toReal_map_pmf_invariant {α β : Type*} [Fintype α]
    (p : PMF α) (f : α → β) (e : α ≃ α) (g : β ≃ β)
    (hp : ∀ a, (p (e a)).toReal = (p a).toReal)
    (hf : ∀ a, f (e a) = g (f a)) (b : β) :
    ((p.map f) (g b)).toReal = ((p.map f) b).toReal := by
  rw [toReal_map_pmf_apply, toReal_map_pmf_apply,
    ← e.sum_comp (fun a => if f a = g b then (p a).toReal else 0)]
  simp_rw [hf, hp, g.injective.eq_iff]

/-- A sequence's distinct support has cardinality at most its length.
Source: Hoeffding 1963, Theorem 4.
@isnad1 id=le.0h3v.s4.693becef2697 from=translated src=- shape=8dba070a vocab=855a811a
-/
theorem card_image_univ_sequence_le {α : Type*} [DecidableEq α] {k : ℕ} (I : Fin k → α) :
    (Finset.univ.image I).card ≤ k := by
  exact Finset.card_image_le.trans (by simp)

/-- Extend the distinct support of an iid sequence to a literal size-`k`
subset. The later uniform permutation removes dependence on this choice.
Source: Hoeffding 1963, Theorem 4.-/
def sequenceSupportExtension {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (I : Fin k → α) : ExactRowSubset α k :=
  ⟨Classical.choose (Finset.exists_superset_card_eq (card_image_univ_sequence_le I) hk),
    (Classical.choose_spec (Finset.exists_superset_card_eq
      (card_image_univ_sequence_le I) hk)).2⟩

/-- The extension contains every label that actually appears in the sequence.
Source: Hoeffding 1963, Theorem 4.
@isnad1 id=le.1h3v.s6.74050b041f88 from=translated src=- shape=04c63473 vocab=21728cef
-/
theorem image_univ_subset_sequenceSupportExtension
    {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (I : Fin k → α) :
    Finset.univ.image I ⊆ (sequenceSupportExtension hk I).val :=
  (Classical.choose_spec (Finset.exists_superset_card_eq
    (card_image_univ_sequence_le I) hk)).1

/-- Label permutations act on exact-size row subsets.
Source: Hoeffding 1963, Theorem 4.-/
def permuteExactRowSubset {α : Type*} [Fintype α] {k : ℕ}
    (σ : Equiv.Perm α) (T : ExactRowSubset α k) : ExactRowSubset α k :=
  ⟨T.val.map σ.toEmbedding, by simpa using T.property⟩

/-- The label action on exact subsets is a bijection.
Source: Hoeffding 1963, Theorem 4.-/
def permuteExactRowSubsetEquiv {α : Type*} [Fintype α] {k : ℕ}
    (σ : Equiv.Perm α) : ExactRowSubset α k ≃ ExactRowSubset α k where
  toFun := permuteExactRowSubset σ
  invFun := permuteExactRowSubset σ.symm
  left_inv T := by apply Subtype.ext; simp [permuteExactRowSubset, Finset.map_map]
  right_inv T := by apply Subtype.ext; simp [permuteExactRowSubset, Finset.map_map]

/-- Label permutations act transitively on literal subsets of a fixed size.
Source: Hoeffding 1963, Theorem 4.
@isnad1 id=ex.0h4v.s5.25117584781a from=translated src=- shape=092c4e06 vocab=02e754ee
-/
theorem exists_perm_exactRowSubset {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (T U : ExactRowSubset α k) : ∃ σ : Equiv.Perm α, permuteExactRowSubset σ T = U := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq T.val U.val
    (T.property.trans U.property.symm)
  exact ⟨σ, Subtype.ext hσ⟩

/-- One independent uniform permutation jointly symmetrizes the original
uniform iid sequence and its support extension.
Source: Hoeffding 1963, Theorem 4.-/
def iidSubsetOutcome {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (z : (Fin k → α) × Equiv.Perm α) :
    (Fin k → α) × ExactRowSubset α k :=
  (z.2 ∘ z.1, permuteExactRowSubset z.2 (sequenceSupportExtension hk z.1))

/-- The joint iid/exact-subset coupling PMF.
Source: Hoeffding 1963, Theorem 4.-/
def iidSubsetJointPMF {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) : PMF ((Fin k → α) × ExactRowSubset α k) :=
  (PMF.uniformOfFintype ((Fin k → α) × Equiv.Perm α)).map (iidSubsetOutcome hk)

/-- The permutation coupling always places the sequence support inside
the selected subset. Source: Hoeffding 1963, Theorem 4.
@isnad1 id=le.1h3v.s6.0f8dcb255d9f from=translated src=- shape=9915efb9 vocab=4b10d3b2
-/
theorem iidSubsetOutcome_support_subset {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (z : (Fin k → α) × Equiv.Perm α) :
    Finset.univ.image (iidSubsetOutcome hk z).1 ⊆ (iidSubsetOutcome hk z).2.val := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  apply Finset.mem_map.mpr
  refine ⟨z.1 i, ?_, rfl⟩
  exact image_univ_subset_sequenceSupportExtension hk z.1
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- Pairs outside the literal support-extension relation have zero joint mass.
Source: Hoeffding 1963, Theorem 4.
@isnad1 id=eq.2h4v.s7.d10555169eff from=translated src=- shape=0f8bcb1d vocab=741dc5db
-/
theorem iidSubsetJointPMF_toReal_eq_zero_of_not_subset
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (I : Fin k → α) (T : ExactRowSubset α k)
    (h : ¬Finset.univ.image I ⊆ T.val) : (iidSubsetJointPMF hk (I, T)).toReal = 0 := by
  rw [iidSubsetJointPMF, toReal_map_pmf_apply]
  apply Finset.sum_eq_zero
  intro z _
  split_ifs with hz
  · exfalso
    apply h
    have hh := iidSubsetOutcome_support_subset hk z
    simpa only [hz] using hh
  · rfl

end NLAlib
