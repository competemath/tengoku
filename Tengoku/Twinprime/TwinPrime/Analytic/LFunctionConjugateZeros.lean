import Tengoku.Twinprime.TwinPrime.Analytic.CharacterDirichletContinuation
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionZeroSigns
import Tengoku.Seed.Analysis.Calculus.Deriv.Star
import Tengoku.Seed.NumberTheory.MulChar.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conjugate L-functions and two actual zero contributions

Conjugation of the ordered sums identifies the inverse-character L-function
globally for nonprincipal characters. For a character whose square is one,
nonreal zeros occur in conjugate pairs. Distinct actual zeros each retain
their positive multiplicity in the finite local divisor sum.
-/

noncomputable section

open Finset Function Filter Metric MeromorphicOn
open scoped Topology ComplexConjugate

namespace TwinPrime.Analytic

theorem characterDirichletPartialSum_inv_conj {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (N : ℕ) :
    characterDirichletPartialSum χ⁻¹ (conj s) N =
      conj (characterDirichletPartialSum χ s N) := by
  unfold characterDirichletPartialSum
  rw [map_sum]
  apply sum_congr rfl
  intro n _
  have hp : (n : ℂ) ^ (-conj s) = conj ((n : ℂ) ^ (-s)) := by
    simpa only [map_neg, map_natCast] using
      Complex.cpow_conj (n : ℂ) (-s) (by simp [Real.pi_ne_zero.symm])
  rw [map_mul, hp]
  congr 1
  exact (MulChar.star_apply' χ (n : ZMod q)).symm

theorem LFunction_inv_conj_of_one_lt_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ⁻¹ (conj s) =
      conj (DirichletCharacter.LFunction χ s) := by
  have h₁ := tendsto_characterDirichletPartialSum_LFunction χ⁻¹ (conj s) (by simpa using hs)
  have h₂ := Complex.continuous_conj.continuousAt.tendsto.comp
    (tendsto_characterDirichletPartialSum_LFunction χ s hs)
  apply tendsto_nhds_unique h₁
  simpa only [Function.comp_def, ← characterDirichletPartialSum_inv_conj] using h₂

/-- Conjugation identifies the entire continuations for nonprincipal characters.-/
theorem LFunction_inv_conj {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction χ⁻¹ (conj s) =
      conj (DirichletCharacter.LFunction χ s) := by
  let f : ℂ → ℂ := DirichletCharacter.LFunction χ
  let g : ℂ → ℂ := conj ∘ DirichletCharacter.LFunction χ⁻¹ ∘ conj
  have hf : AnalyticOnNhd ℂ f Set.univ :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hg : AnalyticOnNhd ℂ g Set.univ := by
    have hg' : Differentiable ℂ g := by
      intro z
      apply differentiableAt_conj_conj_iff.mpr
      exact DirichletCharacter.differentiable_LFunction (by simpa using hχ) _
    exact fun z _ => hg'.analyticAt z
  have he : f =ᶠ[𝓝 (2 : ℂ)] g := by
    have htwo : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [htwo] with z hz
    dsimp [f, g]
    rw [LFunction_inv_conj_of_one_lt_re χ z hz, Complex.conj_conj]
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) he (Set.mem_univ s)
  have hc := congrArg conj heq
  simpa only [f, g, Function.comp_apply, Complex.conj_conj] using hc.symm

theorem character_inv_eq_self_of_sq_eq_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) : χ⁻¹ = χ := by
  apply inv_eq_of_mul_eq_one_left
  simpa only [pow_two] using hχ

theorem LFunction_conj_of_sq_eq_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχ₂ : χ ^ 2 = 1) (s : ℂ) :
    DirichletCharacter.LFunction χ (conj s) =
      conj (DirichletCharacter.LFunction χ s) := by
  simpa only [character_inv_eq_self_of_sq_eq_one χ hχ₂] using LFunction_inv_conj χ hχ s

theorem deriv_LFunction_conj_of_sq_eq_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχ₂ : χ ^ 2 = 1) (s : ℂ) :
    deriv (DirichletCharacter.LFunction χ) (conj s) =
      conj (deriv (DirichletCharacter.LFunction χ) s) := by
  have heq : conj ∘ DirichletCharacter.LFunction χ ∘ conj =
      DirichletCharacter.LFunction χ := by
    ext z
    simp only [Function.comp_apply, LFunction_conj_of_sq_eq_one χ hχ hχ₂,
      Complex.conj_conj]
  have hd := congrFun (deriv_conj_conj (f := DirichletCharacter.LFunction χ)) (conj s)
  simpa only [heq, Function.comp_apply, Complex.conj_conj] using hd

theorem LFunction_conj_zero_of_sq_eq_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχ₂ : χ ^ 2 = 1)
    (ρ : ℂ) (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    DirichletCharacter.LFunction χ (conj ρ) = 0 := by
  rw [LFunction_conj_of_sq_eq_one χ hχ hχ₂, hzero, map_zero]

/-- Two distinct divisor terms are dominated together by the actual zero sum.-/
theorem two_LFunction_divisor_terms_re_le_zeroSum {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (c s ρ₁ ρ₂ : ℂ) (hs : 1 < s.re) (hne : ρ₁ ≠ ρ₂) :
    ((divisor (DirichletCharacter.LFunction χ) (closedBall c (5 / 4)) ρ₁ : ℂ) /
        (s - ρ₁)).re +
      ((divisor (DirichletCharacter.LFunction χ) (closedBall c (5 / 4)) ρ₂ : ℂ) /
        (s - ρ₂)).re ≤ (localLFunctionZeroSum χ c s).re := by
  classical
  let F : ℂ → ℝ := fun ρ =>
    ((divisor (DirichletCharacter.LFunction χ) (closedBall c (5 / 4)) ρ : ℂ) /
      (s - ρ)).re
  have hfin : F.HasFiniteSupport := by
    apply (localLFunctionZeroTerm_hasFiniteSupport χ c s).subset
    intro ρ hρ heq
    exact hρ (congrArg Complex.re heq)
  let S : Finset ℂ := insert ρ₁ (insert ρ₂ hfin.toFinset)
  have hsub : F.support ⊆ S := by
    intro ρ hρ
    exact mem_insert_of_mem (mem_insert_of_mem (hfin.mem_toFinset.mpr hρ))
  rw [localLFunctionZeroSum_re, finsum_eq_sum_of_support_subset F hsub]
  change F ρ₁ + F ρ₂ ≤ ∑ ρ ∈ S, F ρ
  calc
    _ = ∑ ρ ∈ ({ρ₁, ρ₂} : Finset ℂ), F ρ := by simp [hne]
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro ρ hρ
        simp only [mem_insert, mem_singleton] at hρ
        rcases hρ with rfl | rfl <;> simp [S]
      · intro ρ _ _
        exact LFunction_divisor_term_re_nonneg hq χ hχ _ s ρ hs

/-- A selected actual zero contributes at least one reciprocal, at any
evaluation point strictly to the right of one.-/
theorem zero_reciprocal_re_le_LFunction_divisor_term {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (K : Set ℂ) (s ρ : ℂ) (hs : 1 < s.re) (hK : ρ ∈ K)
    (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    (1 / (s - ρ)).re ≤ ((divisor (DirichletCharacter.LFunction χ) K ρ : ℂ) /
      (s - ρ)).re := by
  have hmult : (1 : ℝ) ≤ divisor (DirichletCharacter.LFunction χ) K ρ := by
    exact_mod_cast one_le_LFunction_divisor_of_zero hq χ hχ K ρ hK hzero
  have hre := primitiveLFunction_zero_re_lt_one hq χ hχ ρ hzero
  simp only [Complex.div_re, Complex.one_re, Complex.one_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, zero_div, add_zero, one_mul, Complex.sub_re]
  exact div_le_div_of_nonneg_right
    (by nlinarith : s.re - ρ.re ≤ (divisor (DirichletCharacter.LFunction χ) K ρ : ℝ) *
      (s.re - ρ.re)) (Complex.normSq_nonneg _)

/-- A finite lower bound supplied by two distinct actual zeros, each with
its proved positive multiplicity. No character reality is needed here.-/
theorem two_zero_reciprocals_re_le_localLFunctionZeroSum {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (c s ρ₁ ρ₂ : ℂ) (hs : 1 < s.re) (hne : ρ₁ ≠ ρ₂)
    (hρ₁ : ρ₁ ∈ closedBall c (5 / 4)) (hρ₂ : ρ₂ ∈ closedBall c (5 / 4))
    (hz₁ : DirichletCharacter.LFunction χ ρ₁ = 0)
    (hz₂ : DirichletCharacter.LFunction χ ρ₂ = 0) :
    (1 / (s - ρ₁)).re + (1 / (s - ρ₂)).re ≤ (localLFunctionZeroSum χ c s).re :=
  (add_le_add
    (zero_reciprocal_re_le_LFunction_divisor_term hq χ hχ _ s ρ₁ hs hρ₁ hz₁)
    (zero_reciprocal_re_le_LFunction_divisor_term hq χ hχ _ s ρ₂ hs hρ₂ hz₂)).trans
      (two_LFunction_divisor_terms_re_le_zeroSum hq χ hχ c s ρ₁ ρ₂ hs hne)

theorem re_one_div_real_sub_complex (σ β t : ℝ) :
    (1 / ((σ : ℂ) - ((β : ℂ) + Complex.I * t))).re =
      (σ - β) / ((σ - β) ^ 2 + t ^ 2) := by
  simp only [Complex.div_re, Complex.one_re, Complex.one_im, zero_mul, zero_div,
    add_zero, one_mul, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_add, zero_sub,
    sub_zero, mul_zero]
  ring

/-- A nonreal conjugate pair contributes twice the real reciprocal kernel.
Membership of the actual zero in the local disk is retained explicitly.-/
theorem conjugate_pair_le_localLFunctionZeroSum_re {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hχ₂ : χ ^ 2 = 1) (β t σ : ℝ) (ht : t ≠ 0) (hσ : 1 < σ)
    (hmem : (β : ℂ) + Complex.I * t ∈ closedBall (2 : ℂ) (5 / 4))
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * t) = 0) :
    2 * (σ - β) / ((σ - β) ^ 2 + t ^ 2) ≤
      (localLFunctionZeroSum χ (2 : ℂ) (σ : ℂ)).re := by
  let ρ : ℂ := (β : ℂ) + Complex.I * t
  have hconj : conj ρ = (β : ℂ) + Complex.I * (-t) := by
    dsimp [ρ]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hne : ρ ≠ conj ρ := by
    intro heq
    have him := congrArg Complex.im heq
    simp [ρ] at him
    exact ht (by linarith)
  have hmconj : conj ρ ∈ closedBall (2 : ℂ) (5 / 4) := by
    rw [mem_closedBall_iff_norm]
    have hnorm : ‖conj ρ - (2 : ℂ)‖ = ‖ρ - (2 : ℂ)‖ := by
      simpa only [map_sub, map_ofNat] using Complex.norm_conj (ρ - (2 : ℂ))
    rw [hnorm]
    exact mem_closedBall_iff_norm.mp hmem
  have hzconj := LFunction_conj_zero_of_sq_eq_one χ (primitive_character_ne_one hq χ hχ)
    hχ₂ ρ hzero
  have hpair := two_zero_reciprocals_re_le_localLFunctionZeroSum hq χ hχ (2 : ℂ)
    (σ : ℂ) ρ (conj ρ) (by simpa using hσ) hne hmem hmconj hzero hzconj
  rw [hconj] at hpair
  dsimp [ρ] at hpair
  have hneg : (1 / ((σ : ℂ) - ((β : ℂ) + Complex.I * -(t : ℂ)))).re =
      (σ - β) / ((σ - β) ^ 2 + t ^ 2) := by
    simpa only [Complex.ofReal_neg, neg_sq] using re_one_div_real_sub_complex σ β (-t)
  rw [re_one_div_real_sub_complex, hneg] at hpair
  convert hpair using 1
  ring

end TwinPrime.Analytic
