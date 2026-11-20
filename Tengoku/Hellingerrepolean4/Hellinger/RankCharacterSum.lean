import Tengoku.Hellingerrepolean4.Hellinger.QuadraticDual
import Tengoku.Seed.LinearAlgebra.Matrix.Rank
import Tengoku.Seed.FieldTheory.Finiteness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms double_character_sum` (it only prints; the queue checks the axioms of every declaration). -/

/-! Exact finite-field character sums with the true matrix rank over F₂. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace Hellinger.RankCharacterSum
open F2Model QuadraticRadical QuadraticDual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance kernelFintype (B : Matrix ι ι F2) : Fintype B.mulVecLin.ker :=
  Fintype.ofFinite _

/--
@isnad1 id=eq.0h1v.s6.553393d9857b from=translated src=- shape=34b8be76 vocab=a462139c
-/
theorem coordinate_character_sum (v : F2) :
    (∑ x : F2, sign (x * v)) = if v = 0 then (2 : ℝ) else 0 := by
  obtain ⟨b, rfl⟩ := bitEquiv.surjective v
  rw [← bitEquiv.sum_comp]
  cases b <;> norm_num [boolSign]

/--
@isnad1 id=eq.0h2v.s7.634bee9fff71 from=translated src=- shape=b14e3ea6 vocab=345fa4ac
-/
theorem sum_character (v : ι → F2) :
    (∑ x : ι → F2, sign (x ⬝ᵥ v)) = if v = 0 then (2 : ℝ) ^ Fintype.card ι else 0 := by
  have hs (x : ι → F2) : sign (x ⬝ᵥ v) = ∏ i, sign (x i * v i) :=
    sign_sum Finset.univ _
  simp_rw [hs]
  rw [← Fintype.prod_sum (fun i x => sign (x * v i))]
  simp_rw [coordinate_character_sum]
  by_cases hv : v = 0
  · simp [hv]
  · rw [ite_eq_right hv]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

omit [DecidableEq ι] in
/--
@isnad1 id=eq.0h2v.s9.6be8cc44901a from=translated src=- shape=0f9bdd49 vocab=0a8f9c20
-/
theorem kernel_card (B : Matrix ι ι F2) :
    Fintype.card B.mulVecLin.ker = 2 ^ (Fintype.card ι - B.rank) := by
  rw [Module.card_eq_pow_finrank (K := F2) (V := B.mulVecLin.ker)]
  have hr := B.mulVecLin.finrank_range_add_finrank_ker
  have hdim : Module.finrank F2 (ι → F2) = Fintype.card ι := Module.finrank_pi F2
  rw [hdim] at hr
  have hk : Module.finrank F2 B.mulVecLin.ker = Fintype.card ι - B.rank := by
    unfold Matrix.rank
    omega
  rw [hk]
  simp [F2]

/-- Orthogonality on a principal coordinate space, with rank interpreted by mathlib's
finite-dimensional linear-algebra definition, not as a supplied combinatorial invariant.
@isnad1 id=eq.0h2v.s7.3b56d5a496dd from=translated src=- shape=be4086e3 vocab=c53a11d2
-/
theorem double_character_sum (B : Matrix ι ι F2) :
    (∑ s : ι → F2, ∑ d : ι → F2, sign (d ⬝ᵥ B *ᵥ s)) =
      (2 : ℝ) ^ (2 * Fintype.card ι - B.rank) := by
  simp_rw [sum_character]
  have hsum : (∑ s : ι → F2, if B *ᵥ s = 0 then (2 : ℝ) ^ Fintype.card ι else 0) =
      (Fintype.card B.mulVecLin.ker : ℝ) * (2 : ℝ) ^ Fintype.card ι := by
    simp only [Fintype.card_subtype, LinearMap.mem_ker]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    congr 2
  rw [hsum, kernel_card]
  push_cast
  rw [← pow_add]
  congr 1
  have hle := B.rank_le_card_width
  omega

end Hellinger.RankCharacterSum
