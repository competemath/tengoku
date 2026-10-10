import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.HilbertSchmidt

namespace OAI

noncomputable section

universe u_54 u_55 u_56 u_57 u_58 u_59 u_60

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace
open Set Metric Filter Complex
open scoped Topology
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace CompleteCrouzeix

section

section

section

section
variable {E : Type u_54} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
namespace FourierResolution
variable (D : FourierResolution E)
variable (J : E ≃ₗᵢ⋆[ℂ] E)
    (hJJ : Function.Involutive J)
    (hJ0 : ∀ u, J (D.proj 0 u) = D.proj 0 (J u))
    (hJ1 : ∀ u, J (D.proj 1 u) = D.proj 2 (J u))

include hJJ hJ1 in
lemma star_negative (u : E) : J (D.proj 2 u) = D.proj 1 (J u) := by
  have h := congrArg J (hJ1 (J u))
  simpa only [hJJ u, hJJ (D.proj 1 (J u))] using h.symm

lemma nonnegative_decompose (v : E) (hv : D.proj 2 v = 0) :
    D.proj 0 v + D.proj 1 v = v := by
  simpa only [hv, add_zero] using D.decompose v

include hJ1 in

lemma hermitian_fourier_norm (v : E) (hv : D.proj 2 v = 0)
    (hv0 : J (D.proj 0 v) = D.proj 0 v) :
    ‖v + J v‖ ^ 2 = 2 * (‖v‖ ^ 2 + ‖D.proj 0 v‖ ^ 2) := by
  have hvd := D.nonnegative_decompose v hv
  have hjd : J v = D.proj 0 v + D.proj 2 (J v) := by
    calc
      J v = J (D.proj 0 v + D.proj 1 v) := congrArg J hvd.symm
      _ = _ := by rw [map_add, hv0, hJ1]
  have hn1 : ‖D.proj 2 (J v)‖ = ‖D.proj 1 v‖ := by
    rw [← hJ1, J.norm_map]
  have hsum : v + J v = (2 : ℂ) • D.proj 0 v + D.proj 1 v + D.proj 2 (J v) := by
    calc
      _ = (D.proj 0 v + D.proj 1 v) + (D.proj 0 v + D.proj 2 (J v)) :=
        congrArg₂ (· + ·) hvd.symm hjd
      _ = _ := by simp only [two_smul]; abel
  have ho1 : inner ℂ ((2 : ℂ) • D.proj 0 v) (D.proj 1 v) = 0 := by
    rw [inner_smul_left, D.orthogonal 0 1 (by decide)]
    simp
  have ho2 : inner ℂ ((2 : ℂ) • D.proj 0 v + D.proj 1 v)
      (D.proj 2 (J v)) = 0 := by
    rw [inner_add_left, inner_smul_left,
      D.orthogonal 0 2 (by decide), D.orthogonal 1 2 (by decide)]
    simp
  rw [hsum, norm_sq_add_orthogonal _ _ ho2, norm_sq_add_orthogonal _ _ ho1,
    norm_smul, hn1]
  have hn := D.norm_decompose v
  rw [hv, norm_zero, zero_pow (by decide), add_zero] at hn
  norm_num
  nlinarith

lemma adjoint_module_apply (M L : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M)
    (hmod : (D.cauchy M).comp (L.comp (D.cauchy M)) = L.comp (D.cauchy M))
    (r : E) :
    D.cauchyAdjoint M (L.adjoint (D.cauchyAdjoint M r)) =
      D.cauchyAdjoint M (L.adjoint r) := by
  have h := congrArg ContinuousLinearMap.adjoint hmod
  simp only [ContinuousLinearMap.adjoint_comp, D.adjoint_cauchy M hswap] at h
  exact congrArg (fun T : E →L[ℂ] E => T r) h

include hJ0 hJ1 in
lemma hermitian_diagonal_bound (M L : E →L[ℂ] E)
    (hM : ‖M‖ ≤ 1) (hL : ‖L‖ ≤ 1)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M)
    (hmod : (D.cauchy M).comp (L.comp (D.cauchy M)) = L.comp (D.cauchy M))
    (p r : E) (hp : p = L.adjoint r) (hpJ : J p = p) :
    ‖D.cauchyAdjoint M p + J (D.cauchyAdjoint M p)‖ ^ 2 ≤
      4 * ‖D.cauchyAdjoint M r‖ ^ 2 := by
  have hdiag := D.hermitian_fourier_norm J hJ1 (D.cauchyAdjoint M p)
    (D.negative_adjoint M hswap p)
    (by rw [D.mean_adjoint M hswap, hJ0, hpJ])
  have heq : D.cauchyAdjoint M p =
      D.cauchyAdjoint M (L.adjoint (D.cauchyAdjoint M r)) := by
    rw [D.adjoint_module_apply M L hswap hmod, hp]
  have hw := D.weighted_adjoint_bound M hM hswap (L.adjoint (D.cauchyAdjoint M r))
  have hnorm : ‖L.adjoint (D.cauchyAdjoint M r)‖ ≤ ‖D.cauchyAdjoint M r‖ := by
    calc _ ≤ ‖L.adjoint‖ * ‖D.cauchyAdjoint M r‖ := L.adjoint.le_opNorm _
      _ ≤ 1 * ‖D.cauchyAdjoint M r‖ := by gcongr; simpa using hL
      _ = _ := one_mul _
  rw [hdiag, heq, D.mean_adjoint M hswap]
  nlinarith [norm_nonneg (L.adjoint (D.cauchyAdjoint M r)),
    norm_nonneg (D.cauchyAdjoint M r)]

include hJ0 hJ1 in
lemma opposite_adjoint_orthogonal (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M)
    (r : E) (hr : D.proj 0 r = 0) :
    inner ℂ (D.cauchyAdjoint M r) (J (D.cauchyAdjoint M (J r))) = 0 := by
  have hpos : D.proj 1 (D.cauchyAdjoint M r) = D.cauchyAdjoint M r := by
    have h := D.nonnegative_decompose (D.cauchyAdjoint M r)
      (D.negative_adjoint M hswap r)
    simpa only [D.mean_adjoint M hswap, hr, zero_add] using h
  have hjr : D.proj 0 (J r) = 0 := by rw [← hJ0, hr]; simp
  have hjpos : D.proj 1 (D.cauchyAdjoint M (J r)) = D.cauchyAdjoint M (J r) := by
    have h := D.nonnegative_decompose (D.cauchyAdjoint M (J r))
      (D.negative_adjoint M hswap (J r))
    simpa only [D.mean_adjoint M hswap, hjr, zero_add] using h
  have hneg : D.proj 2 (J (D.cauchyAdjoint M (J r))) =
      J (D.cauchyAdjoint M (J r)) := by rw [← hJ1, hjpos]
  conv_lhs => lhs; rw [← hpos]
  conv_lhs => rhs; rw [← hneg]
  exact D.orthogonal 1 2 (by decide) _ _

include hJ0 hJ1 in

theorem density_comparison_core (M L R : E →L[ℂ] E)
    (hM : ‖M‖ ≤ 1) (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M)
    (hmodL : (D.cauchy M).comp (L.comp (D.cauchy M)) = L.comp (D.cauchy M))
    (hmodR : (D.cauchy M).comp (R.comp (D.cauchy M)) = R.comp (D.cauchy M))
    (p q r : E) (hp : p = L.adjoint r) (hq : q = R.adjoint r)
    (hpJ : J p = p) (hqJ : J q = q) (hr : D.proj 0 r = 0)
    (hp0 : D.proj 0 p ≠ 0) (κ : ℝ) (hκ : 0 < κ)
    (hblock : 2 * ‖(κ : ℂ) • D.cauchyAdjoint M r +
        ((κ⁻¹ : ℝ) : ℂ) • J (D.cauchyAdjoint M (J r))‖ ^ 2 ≤
      ‖D.cauchyAdjoint M p + J (D.cauchyAdjoint M p)‖ ^ 2 +
      ‖D.cauchyAdjoint M q + J (D.cauchyAdjoint M q)‖ ^ 2) : κ ≤ 2 := by
  have hg : D.cauchyAdjoint M r ≠ 0 := by
    intro hz
    apply hp0
    have hc : D.cauchyAdjoint M p = 0 := by
      rw [hp, ← D.adjoint_module_apply M L hswap hmodL, hz]
      simp
    rw [← D.mean_adjoint M hswap p, hc]
    simp
  have hgp : 0 < ‖D.cauchyAdjoint M r‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
  have hdiag1 := D.hermitian_diagonal_bound J hJ0 hJ1 M L hM hL hswap hmodL p r hp hpJ
  have hdiag2 := D.hermitian_diagonal_bound J hJ0 hJ1 M R hM hR hswap hmodR q r hq hqJ
  have hortho := D.opposite_adjoint_orthogonal J hJ0 hJ1 M hswap r hr
  have hscaled : inner ℂ ((κ : ℂ) • D.cauchyAdjoint M r)
      (((κ⁻¹ : ℝ) : ℂ) • J (D.cauchyAdjoint M (J r))) = 0 := by
    rw [inner_smul_left, inner_smul_right, hortho]
    simp
  rw [norm_sq_add_orthogonal _ _ hscaled] at hblock
  have hnorm : ‖(κ : ℂ) • D.cauchyAdjoint M r‖ ^ 2 =
      κ ^ 2 * ‖D.cauchyAdjoint M r‖ ^ 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ, mul_pow]
  rw [hnorm] at hblock
  have hmul : κ ^ 2 * ‖D.cauchyAdjoint M r‖ ^ 2 ≤
      4 * ‖D.cauchyAdjoint M r‖ ^ 2 := by
    nlinarith [sq_nonneg (‖((κ⁻¹ : ℝ) : ℂ) • J (D.cauchyAdjoint M (J r))‖)]
  have hs : κ ^ 2 ≤ 4 := le_of_mul_le_mul_right hmul hgp
  nlinarith

end FourierResolution
end

open MeasureTheory
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
lemma scalarFourier_star_zero (u : CircleL2) :
    star (scalarFourier.proj 0 u) = scalarFourier.proj 0 (star u) := by
  apply circle_fourier_ext
  intro n
  rw [circle_fourier_star, scalarFourier_coefficient, scalarFourier_coefficient,
    circle_fourier_star]
  by_cases hn : n = 0
  · subst n; simp [frequencyPart]
  · have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
    by_cases hp : 0 < n <;> by_cases hm : n < 0 <;>
      simp [frequencyPart, hn, hneg, hp, hm]

lemma scalarFourier_star_positive (u : CircleL2) :
    star (scalarFourier.proj 1 u) = scalarFourier.proj 2 (star u) := by
  apply circle_fourier_ext
  intro n
  rw [circle_fourier_star, scalarFourier_coefficient, scalarFourier_coefficient,
    circle_fourier_star]
  by_cases hn : n = 0
  · subst n; simp [frequencyPart]
  · have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
    by_cases hp : 0 < n
    · have hm : ¬ n < 0 := by omega
      simp [frequencyPart, hn, hneg, hp, hm]
    · have hm : n < 0 := by omega
      simp [frequencyPart, hn, hneg, hp, hm]

variable {m : Type u_55} [Fintype m] [DecidableEq m]
abbrev MatrixCircleL2 := Lp (HSMatrix m) 2 (@AddCircle.haarAddCircle 1 inferInstance)

def matrixFourier : FourierResolution (MatrixCircleL2 (m := m)) :=
  vectorResolution scalarFourier

end

open MeasureTheory
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)
variable {m : Type u_56} [Fintype m] [instDecidableEqM : DecidableEq m]

end AnalyticBidiskKernel
end

open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {ι : Type u_57} [Fintype ι] [DecidableEq ι]
local notation "V" => VectorL2 (μ := @AddCircle.haarAddCircle 1 inferInstance) (ι := ι)

lemma l2_sum_embedding_coordinate (u : V) :
    ∑ i, l2Embedding i (l2Coordinate i u) = u := by
  apply l2Coordinate_injective
  intro j
  simp only [map_sum,coordinate_embedding]
  simp

end

open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

section ActualFields
variable {ι : Type u_59} [Fintype ι] [DecidableEq ι]
local notation "V" => VectorL2 (μ := @AddCircle.haarAddCircle 1 inferInstance) (ι := ι)

end ActualFields

end CompleteCrouzeix

end

end OAI
