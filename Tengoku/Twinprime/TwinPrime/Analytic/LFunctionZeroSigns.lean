import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionZeroCount
import Tengoku.Seed.NumberTheory.LSeries.Nonvanishing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# Signs of the actual local L-function zero sum

Qualitative nonvanishing places every zero of a primitive nonprincipal
L-function strictly to the left of one.  Its actual divisor therefore
gives nonnegative real reciprocal terms when the evaluation point is to
the right of one.  A selected zero contributes with multiplicity at least one.
-/

noncomputable section

open Finset Function Metric MeromorphicOn

namespace TwinPrime.Analytic

/-- The actual divisor sum used by the local logarithmic-derivative expansion.-/
def localLFunctionZeroSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (c s : ℂ) : ℂ :=
  ∑ᶠ ρ, (divisor (DirichletCharacter.LFunction χ) (closedBall c (5 / 4)) ρ : ℂ) / (s - ρ)

/--
@isnad1 id=lt.3h3v.s6.196916b68d65 from=translated src=- shape=bfeaa2c1 vocab=0c8bd06c
-/
theorem primitiveLFunction_zero_re_lt_one {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (ρ : ℂ) (hρ : DirichletCharacter.LFunction χ ρ = 0) : ρ.re < 1 := by
  by_contra h
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
    (Or.inl (primitive_character_ne_one hq χ hχ)) (not_lt.mp h) hρ

/-- Every point in the support of the actual divisor is strictly left of one.
@isnad1 id=lt.3h4v.s7.8e8f04fafa8d from=translated src=- shape=49fe3d52 vocab=8508be58
-/
theorem LFunction_divisor_re_lt_one {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (K : Set ℂ) (ρ : ℂ) (hρ : divisor (DirichletCharacter.LFunction χ) K ρ ≠ 0) :
    ρ.re < 1 := by
  have ha := DirichletCharacter.differentiable_LFunction (primitive_character_ne_one hq χ hχ)
  have hK : ρ ∈ K := (divisor (DirichletCharacter.LFunction χ) K).supportWithinDomain hρ
  by_contra hre
  have hn := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
    (Or.inl (primitive_character_ne_one hq χ hχ)) (not_lt.mp hre)
  have ho := (ha.analyticAt ρ).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn
  rw [divisor_apply (fun z _ => (ha.analyticAt z).meromorphicAt) hK, ho] at hρ
  simp at hρ

/--
@isnad1 id=ne.2h3v.s6.ab68b7f7cb1d from=translated src=- shape=4aac0934 vocab=41d0c710
-/
theorem meromorphicOrderAt_primitiveLFunction_ne_top {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (ρ : ℂ) :
    meromorphicOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
  have ha := DirichletCharacter.differentiable_LFunction (primitive_character_ne_one hq χ hχ)
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ := fun z _ => ha.analyticAt z
  apply hF.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ (2 : ℂ)) (Set.mem_univ ρ)
  have hn := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
    (s := (2 : ℂ)) (Or.inl (primitive_character_ne_one hq χ hχ)) (by norm_num)
  rw [(ha.analyticAt (2 : ℂ)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn]
  simp

/-- An actual zero in the divisor domain has positive integer multiplicity.
@isnad1 id=le.4h4v.s7.376a4e11ba2a from=translated src=- shape=66c21f7b vocab=76c1d840
-/
theorem one_le_LFunction_divisor_of_zero {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (K : Set ℂ) (ρ : ℂ) (hK : ρ ∈ K) (hρ : DirichletCharacter.LFunction χ ρ = 0) :
    1 ≤ divisor (DirichletCharacter.LFunction χ) K ρ := by
  have ha := DirichletCharacter.differentiable_LFunction (primitive_character_ne_one hq χ hχ)
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) K := fun z _ => ha.analyticAt z
  have hn : MeromorphicNFOn (DirichletCharacter.LFunction χ) K :=
    fun z _ => (ha.analyticAt z).meromorphicNFAt
  have heq := hn.zero_set_eq_divisor_support
    (fun z => meromorphicOrderAt_primitiveLFunction_ne_top hq χ hχ z)
  have hsupport : ρ ∈ (divisor (DirichletCharacter.LFunction χ) K).support := by
    exact heq.subset ⟨hK, hρ⟩
  have hnonneg : 0 ≤ divisor (DirichletCharacter.LFunction χ) K ρ := hF.divisor_nonneg ρ
  change divisor (DirichletCharacter.LFunction χ) K ρ ≠ 0 at hsupport
  omega

/-- Each actual-divisor reciprocal term has nonnegative real part.
@isnad1 id=le.3h5v.s7.b6228915d350 from=translated src=- shape=d65ff310 vocab=404c6ab1
-/
theorem LFunction_divisor_term_re_nonneg {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (K : Set ℂ) (s ρ : ℂ) (hs : 1 < s.re) :
    0 ≤ ((divisor (DirichletCharacter.LFunction χ) K ρ : ℂ) / (s - ρ)).re := by
  by_cases hρ : divisor (DirichletCharacter.LFunction χ) K ρ = 0
  · simp [hρ]
  have hre := LFunction_divisor_re_lt_one hq χ hχ K ρ hρ
  have ha : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) K :=
    fun z _ => (DirichletCharacter.differentiable_LFunction
      (primitive_character_ne_one hq χ hχ)).analyticAt z
  have hD : (0 : ℝ) ≤ divisor (DirichletCharacter.LFunction χ) K ρ := by
    exact_mod_cast ha.divisor_nonneg ρ
  simp only [Complex.div_re, Complex.intCast_re, Complex.intCast_im, Complex.sub_re,
    zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg hD (by linarith)) (Complex.normSq_nonneg _)

/--
@isnad1 id=hasfinit.0h4v.s7.6aa51b95e43d from=translated src=- shape=a2e7be44 vocab=5b4cdabd
-/
theorem localLFunctionZeroTerm_hasFiniteSupport {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (c s : ℂ) :
    (fun ρ => (divisor (DirichletCharacter.LFunction χ) (closedBall c (5 / 4)) ρ : ℂ) /
      (s - ρ)).HasFiniteSupport := by
  apply ((divisor (DirichletCharacter.LFunction χ) (closedBall c (5 / 4))).finiteSupport
    (isCompact_closedBall c (5 / 4))).subset
  intro ρ hρ
  change divisor (DirichletCharacter.LFunction χ) (closedBall c (5 / 4)) ρ ≠ 0
  intro hD
  exact hρ (by simp [hD])

/--
@isnad1 id=eq.0h4v.s7.656575c8e712 from=translated src=- shape=9158ef87 vocab=2f9b16ca
-/
theorem localLFunctionZeroSum_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (c s : ℂ) :
    (localLFunctionZeroSum χ c s).re =
      ∑ᶠ ρ, ((divisor (DirichletCharacter.LFunction χ) (closedBall c (5 / 4)) ρ : ℂ) /
        (s - ρ)).re :=
  Complex.reAddGroupHom.map_finsum (localLFunctionZeroTerm_hasFiniteSupport χ c s)

/--
@isnad1 id=le.3h4v.s6.7a9b7d878adf from=translated src=- shape=b335ff60 vocab=236a8096
-/
theorem localLFunctionZeroSum_re_nonneg {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (c s : ℂ) (hs : 1 < s.re) : 0 ≤ (localLFunctionZeroSum χ c s).re := by
  rw [localLFunctionZeroSum_re]
  exact finsum_nonneg (fun ρ => LFunction_divisor_term_re_nonneg hq χ hχ _ s ρ hs)

/-- A single term is bounded by the whole actual zero sum.
@isnad1 id=le.3h5v.s8.88a753c86280 from=translated src=- shape=d351be78 vocab=c886d0e5
-/
theorem LFunction_divisor_term_re_le_zeroSum {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (c s ρ : ℂ) (hs : 1 < s.re) :
    ((divisor (DirichletCharacter.LFunction χ) (closedBall c (5 / 4)) ρ : ℂ) /
      (s - ρ)).re ≤ (localLFunctionZeroSum χ c s).re := by
  rw [localLFunctionZeroSum_re]
  apply single_le_finsum ρ
  · apply ((divisor (DirichletCharacter.LFunction χ) (closedBall c (5 / 4))).finiteSupport
      (isCompact_closedBall c (5 / 4))).subset
    intro u hu
    change divisor (DirichletCharacter.LFunction χ) (closedBall c (5 / 4)) u ≠ 0
    intro hD
    exact hu (by simp [hD])
  · exact fun u => LFunction_divisor_term_re_nonneg hq χ hχ _ s u hs

/-- A zero at the evaluation height contributes at least its simple-zero
reciprocal.  The real cutoff `3/4` ensures membership in the radius-`5/4`
divisor disk centered at `2+iγ`; no upper restriction on `σ` is needed here.
@isnad1 id=le.5h5v.s7.79c084a8d8d0 from=translated src=- shape=7f1d859f vocab=cfa204bb
-/
theorem one_div_sub_le_localLFunctionZeroSum_re_of_zero {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (β γ σ : ℝ) (hβ : 3 / 4 ≤ β) (hσ : 1 < σ)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * γ) = 0) :
    1 / (σ - β) ≤
      (localLFunctionZeroSum χ ((2 : ℂ) + Complex.I * γ)
        ((σ : ℂ) + Complex.I * γ)).re := by
  let ρ : ℂ := (β : ℂ) + Complex.I * γ
  let c : ℂ := (2 : ℂ) + Complex.I * γ
  let s : ℂ := (σ : ℂ) + Complex.I * γ
  have hβ1 : β < 1 := by
    simpa [ρ] using primitiveLFunction_zero_re_lt_one hq χ hχ ρ hzero
  have hdiff : ρ - c = ((β - 2 : ℝ) : ℂ) := by dsimp [ρ, c]; push_cast; ring
  have hmem : ρ ∈ closedBall c (5 / 4) := by
    rw [mem_closedBall_iff_norm, hdiff, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hmult := one_le_LFunction_divisor_of_zero hq χ hχ (closedBall c (5 / 4)) ρ hmem hzero
  have hmultR : (1 : ℝ) ≤ divisor (DirichletCharacter.LFunction χ) (closedBall c (5 / 4)) ρ := by
    exact_mod_cast hmult
  have heval : s - ρ = ((σ - β : ℝ) : ℂ) := by dsimp [s, ρ]; push_cast; ring
  have hs : 1 < s.re := by simpa [s] using hσ
  calc
    _ ≤ (divisor (DirichletCharacter.LFunction χ) (closedBall c (5 / 4)) ρ : ℝ) / (σ - β) :=
      div_le_div_of_nonneg_right hmultR (by linarith)
    _ = ((divisor (DirichletCharacter.LFunction χ) (closedBall c (5 / 4)) ρ : ℂ) /
        (s - ρ)).re := by rw [heval, Complex.div_ofReal_re, Complex.intCast_re]
    _ ≤ _ := LFunction_divisor_term_re_le_zeroSum hq χ hχ c s ρ hs

end TwinPrime.Analytic
