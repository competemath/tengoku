/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Tengoku.GrunbaumLean.Grunbaum.Basic
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Switching, relabelling and principal submatrices

If `A i j = εᵢ εⱼ B (f i) (f j)` for an injective map `f` and signs `εᵢ = ±1`, then every
orthonormal pair for `A` gives an orthonormal pair for `B` with the same value of
`uᵀAu + vᵀAv`: extend by zero along `f` and multiply by the signs (`Grunbaum.transfer`).
This covers switching (`f = id`), relabelling (`f` bijective) and principal submatrices, as used
throughout the errata: "if `B` is a principal submatrix of `S`, then `Π(2, B) ≤ Π(2, S)`: extend
the weights by zero", and "replacing `(S, D)` by `(QᵗSQ, QᵗDQ)` for a signed permutation matrix
`Q` does not change the spectrum".

## Main results

* `Grunbaum.sumTopTwo_weightedMatrix_le_of_transfer` : `π₂(√D S √D) ≤ π₂(√D' T √D')`, where
  `D'` extends `D` by zero along `f`;
* `Grunbaum.sumTopTwo_weightedMatrix_eq_of_equiv` : the equality for bijective `f`;
* `Grunbaum.sumTopTwo_weightedMatrix_nonneg` : `π₂(√D S √D) ≥ 0`.

This file is adapted from `ProjectionConstants/Grunbaum/Transfer.lean` of the library
*Projection constants in Lean*.
-/

open Finset Matrix

namespace Grunbaum

variable {ι κ : Type*}

/-- Extension by zero along `f`, twisted by the signs `ε`: the vector on `κ` with entries
`εᵢ xᵢ` at `f i` and zero outside the range of `f`.-/
noncomputable def signedExtend (f : ι → κ) (ε x : ι → ℝ) : κ → ℝ :=
  Function.extend f (fun i => ε i * x i) 0

/--
@isnad1 id=eq.1h6v.s5.d11c77b45ace from=translated src=- shape=e21d5745 vocab=5b43bac2
-/
lemma signedExtend_apply {f : ι → κ} (hf : Function.Injective f) (ε x : ι → ℝ) (i : ι) :
    signedExtend f ε x (f i) = ε i * x i :=
  hf.extend_apply _ _ i

/--
@isnad1 id=eq.1h6v.s5.fbf833df749d from=translated src=- shape=851141ce vocab=6f16749d
-/
lemma signedExtend_apply_of_notMem {f : ι → κ} (ε x : ι → ℝ) {k : κ} (hk : ¬∃ i, f i = k) :
    signedExtend f ε x k = 0 := by
  simp [signedExtend, Function.extend_apply' _ _ _ hk]

variable [Fintype ι] [Fintype κ]

/-- Sums over `κ` of functions vanishing outside the range of an injective map `f : ι → κ`.
@isnad1 id=eq.2h4v.s6.822ae7eda640 from=translated src=- shape=53ed224a vocab=9827b1fc
-/
lemma sum_eq_sum_comp_of_injective {f : ι → κ} (hf : Function.Injective f) (H : κ → ℝ)
    (h0 : ∀ k, (¬∃ i, f i = k) → H k = 0) : ∑ k, H k = ∑ i, H (f i) :=
  (Fintype.sum_of_injective f hf _ H (fun k hk => h0 k (by simpa using hk)) fun _ => rfl).symm

/--
@isnad1 id=eq.2h6v.s6.5ef86722e9e3 from=translated src=- shape=e9790ec0 vocab=bdb787cf
-/
lemma dotProduct_signedExtend {f : ι → κ} (hf : Function.Injective f) {ε : ι → ℝ}
    (hε : ∀ i, ε i * ε i = 1) (x y : ι → ℝ) :
    signedExtend f ε x ⬝ᵥ signedExtend f ε y = x ⬝ᵥ y := by
  rw [dotProduct, sum_eq_sum_comp_of_injective hf]
  · simp only [signedExtend_apply hf, dotProduct]
    exact sum_congr rfl fun i _ => by linear_combination (x i * y i) * hε i
  · intro k hk
    simp [signedExtend_apply_of_notMem _ _ hk]

/--
@isnad1 id=eq.2h7v.s7.39b95aff0faa from=translated src=- shape=e189f775 vocab=a3613669
-/
lemma dotProduct_mulVec_signedExtend {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ} {f : ι → κ}
    (hf : Function.Injective f) {ε : ι → ℝ} (hAB : ∀ i j, A i j = ε i * ε j * B (f i) (f j))
    (x : ι → ℝ) :
    signedExtend f ε x ⬝ᵥ (B *ᵥ signedExtend f ε x) = x ⬝ᵥ (A *ᵥ x) := by
  rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum, sum_eq_sum_comp_of_injective hf]
  · refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_sum_comp_of_injective hf]
    · refine sum_congr rfl fun j _ => ?_
      rw [signedExtend_apply hf, signedExtend_apply hf, hAB]
      ring
    · intro k hk
      simp [signedExtend_apply_of_notMem _ _ hk]
  · intro k hk
    simp [signedExtend_apply_of_notMem _ _ hk]

/-- **Transfer** of orthonormal pairs along signed injections.
@isnad1 id=and.4h8v.s7.5d59b719e66f from=translated src=- shape=bb777e30 vocab=b9fdd5d8
-/
theorem transfer {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ} {f : ι → κ} (hf : Function.Injective f)
    {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1) (hAB : ∀ i j, A i j = ε i * ε j * B (f i) (f j))
    {x y : ι → ℝ} (h : IsOrthonormalPair x y) :
    IsOrthonormalPair (signedExtend f ε x) (signedExtend f ε y) ∧
      fanValue B (signedExtend f ε x) (signedExtend f ε y) = fanValue A x y := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [dotProduct_signedExtend hf hε]; exact h.norm_left
  · rw [dotProduct_signedExtend hf hε]; exact h.norm_right
  · rw [dotProduct_signedExtend hf hε]; exact h.orth
  · simp only [fanValue, dotProduct_mulVec_signedExtend hf hAB]

/-- Hence `π₂ A ≤ π₂ B`, provided that there is an orthonormal pair in `ℝ^ι`.
@isnad1 id=le.4h6v.s6.4125349d729e from=translated src=- shape=f56a6e84 vocab=8795e09f
-/
theorem sumTopTwo_le_of_transfer {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ} {f : ι → κ}
    (hf : Function.Injective f) {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1)
    (hAB : ∀ i j, A i j = ε i * ε j * B (f i) (f j)) (hne : (fanValues A).Nonempty) :
    π₂ A ≤ π₂ B := by
  refine sumTopTwo_le hne fun x y h => ?_
  obtain ⟨h', hval⟩ := transfer hf hε hAB h
  rw [← hval]
  exact fanValue_le_sumTopTwo B h'

/-! ### Weighted sign matrices -/

/--
@isnad1 id=isorthon.1h3v.s5.db7273a5762f from=translated src=- shape=d86b8d44 vocab=2c7a9fc1
-/
lemma isOrthonormalPair_single [DecidableEq ι] {a b : ι} (hab : a ≠ b) :
    IsOrthonormalPair (Pi.single a 1 : ι → ℝ) (Pi.single b 1) :=
  ⟨by simp, by simp, by simp [hab.symm]⟩

omit [Fintype κ] in
/-- If there is an orthonormal pair in `ℝ^ι`, then `ι` has two distinct elements.
@isnad1 id=ex.1h3v.s4.31c13cfa4eef from=translated src=- shape=96614eb7 vocab=199ab5f3
-/
lemma exists_ne_of_isOrthonormalPair {x y : ι → ℝ} (h : IsOrthonormalPair x y) :
    ∃ a b : ι, a ≠ b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i⟩ : Nonempty ι := by
    by_contra hi
    rw [not_nonempty_iff] at hi
    have := h.norm_left
    simp [dotProduct] at this
  have hsum : ∀ g : ι → ℝ, ∑ k, g k = g i := fun g =>
    Fintype.sum_eq_single i (fun k hk => absurd (hcon k i) hk)
  have e1 := h.norm_left
  have e2 := h.norm_right
  have e3 := h.orth
  simp only [dotProduct, hsum] at e1 e2 e3
  nlinarith [e1, e2, e3]

omit [Fintype κ] in
/-- For a weighted sign matrix, `π₂ ≥ 0`.
@isnad1 id=le.2h3v.s5.fe623f07dab8 from=translated src=- shape=f676f5f4 vocab=635f2fb2
-/
lemma sumTopTwo_weightedMatrix_nonneg {S : Matrix ι ι ℝ} {w : ι → ℝ} (hS : IsSignMatrix S)
    (hw : IsWeight w) : 0 ≤ π₂ (weightedMatrix S w) := by
  classical
  by_cases h : (fanValues (weightedMatrix S w)).Nonempty
  · obtain ⟨_, x, y, hxy, rfl⟩ := h
    obtain ⟨a, b, hab⟩ := exists_ne_of_isOrthonormalPair hxy
    have := fanValue_le_sumTopTwo (weightedMatrix S w) (isOrthonormalPair_single hab)
    have haa : weightedMatrix S w a a = w a := by
      simp [weightedMatrix, hS.diag, Real.mul_self_sqrt (hw.nonneg a)]
    have hbb : weightedMatrix S w b b = w b := by
      simp [weightedMatrix, hS.diag, Real.mul_self_sqrt (hw.nonneg b)]
    simp only [fanValue, mulVec_single_one, single_dotProduct, one_mul] at this
    simp only [col_apply, haa, hbb] at this
    linarith [hw.nonneg a, hw.nonneg b]
  · rw [sumTopTwo_of_not_nonempty h]

/--
@isnad1 id=isweight.2h4v.s5.1446509bf49a from=translated src=- shape=5cfcb7b0 vocab=4f76ab19
-/
lemma isWeight_extend {f : ι → κ} (hf : Function.Injective f) {w : ι → ℝ} (hw : IsWeight w) :
    IsWeight (Function.extend f w 0) := by
  refine ⟨fun k => ?_, ?_⟩
  · by_cases hk : ∃ i, f i = k
    · obtain ⟨i, rfl⟩ := hk
      rw [hf.extend_apply]
      exact hw.nonneg i
    · rw [Function.extend_apply' _ _ _ hk]
      simp
  · rw [sum_eq_sum_comp_of_injective hf]
    · simp only [hf.extend_apply]
      exact hw.sum_eq
    · intro k hk
      rw [Function.extend_apply' _ _ _ hk]
      simp

/-- **Transfer for weighted sign matrices.** If `S i j = εᵢ εⱼ T (f i) (f j)` with `f` injective,
then `π₂(√D S √D) ≤ π₂(√D' T √D')`, where `D'` extends `D` by zero along `f`.
@isnad1 id=le.5h7v.s7.ab21e0e182dc from=translated src=- shape=6da8720d vocab=61a0f38d
-/
theorem sumTopTwo_weightedMatrix_le_of_transfer {S : Matrix ι ι ℝ} {T : Matrix κ κ ℝ}
    {w : ι → ℝ} (hT : IsSignMatrix T) (hw : IsWeight w) {f : ι → κ} (hf : Function.Injective f)
    {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1) (hST : ∀ i j, S i j = ε i * ε j * T (f i) (f j)) :
    π₂ (weightedMatrix S w) ≤ π₂ (weightedMatrix T (Function.extend f w 0)) := by
  by_cases hne : (fanValues (weightedMatrix S w)).Nonempty
  · refine sumTopTwo_le_of_transfer hf hε (fun i j => ?_) hne
    simp only [weightedMatrix, of_apply, hf.extend_apply, hST]
    ring
  · rw [sumTopTwo_of_not_nonempty hne]
    exact sumTopTwo_weightedMatrix_nonneg hT (isWeight_extend hf hw)

/-- **Relabelling and switching** do not change `π₂`: if `S i j = εᵢ εⱼ T (e i) (e j)` for a
bijection `e`, then `π₂(√D S √D) = π₂(√D' T √D')` with `D' = D ∘ e⁻¹`.
@isnad1 id=eq.5h7v.s7.ad33e915e012 from=translated src=- shape=64241953 vocab=29590d90
-/
theorem sumTopTwo_weightedMatrix_eq_of_equiv {S : Matrix ι ι ℝ} {T : Matrix κ κ ℝ} {w : ι → ℝ}
    (hS : IsSignMatrix S) (hT : IsSignMatrix T) (hw : IsWeight w) (e : ι ≃ κ) {ε : ι → ℝ}
    (hε : ∀ i, ε i * ε i = 1) (hST : ∀ i j, S i j = ε i * ε j * T (e i) (e j)) :
    π₂ (weightedMatrix S w) = π₂ (weightedMatrix T (w ∘ e.symm)) := by
  have hext : Function.extend e w 0 = w ∘ e.symm := by
    funext k
    obtain ⟨i, rfl⟩ := e.surjective k
    simp [e.injective.extend_apply]
  have hw' : IsWeight (w ∘ e.symm) := hext ▸ isWeight_extend e.injective hw
  apply le_antisymm
  · rw [← hext]
    exact sumTopTwo_weightedMatrix_le_of_transfer hT hw e.injective hε hST
  · have hTS : ∀ k l, T k l = ε (e.symm k) * ε (e.symm l) * S (e.symm k) (e.symm l) := by
      intro k l
      rw [hST, e.apply_symm_apply, e.apply_symm_apply]
      linear_combination (-(T k l) * ε (e.symm l) * ε (e.symm l)) * hε (e.symm k)
        - T k l * hε (e.symm l)
    have hext' : Function.extend e.symm (w ∘ e.symm) 0 = w := by
      funext i
      obtain ⟨k, rfl⟩ := e.symm.surjective i
      simp [e.symm.injective.extend_apply]
    have := sumTopTwo_weightedMatrix_le_of_transfer hS hw' e.symm.injective
      (fun k => hε (e.symm k)) hTS
    rwa [hext'] at this

end Grunbaum
