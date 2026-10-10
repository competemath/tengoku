import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.MarkovOperator

namespace OAI

noncomputable section

universe u_40 u_41 u_42 u_43

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace

open scoped ComplexConjugate InnerProductSpace
namespace CompleteCrouzeix

section

section

variable {E : Type u_40} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [instCompleteSpaceE : CompleteSpace E]

structure FourierResolution (E : Type u_41) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] where
  proj : Fin 3 → E →L[ℂ] E
  selfAdjoint : ∀ i, (proj i).adjoint = proj i
  product : ∀ i j, (proj i).comp (proj j) = if i = j then proj i else 0
  total : proj 0 + proj 1 + proj 2 = ContinuousLinearMap.id ℂ E

lemma norm_sq_add_orthogonal
    {E : Type u_40} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (x y : E)
    (h : inner ℂ x y = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y h

namespace FourierResolution
variable (D : FourierResolution E)

lemma decompose (u : E) : D.proj 0 u + D.proj 1 u + D.proj 2 u = u := by
  exact congrArg (fun T : E →L[ℂ] E => T u) D.total

@[simp] lemma proj_proj (i j : Fin 3) (u : E) :
    D.proj i (D.proj j u) = if i = j then D.proj i u else 0 := by
  have h := congrArg (fun T : E →L[ℂ] E => T u) (D.product i j)
  split_ifs with hij <;> simpa [hij] using h

lemma orthogonal (i j : Fin 3) (hij : i ≠ j) (u v : E) :
    inner ℂ (D.proj i u) (D.proj j v) = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, D.selfAdjoint, D.proj_proj]
  simp [hij]

lemma norm_decompose (u : E) :
    ‖u‖ ^ 2 = ‖D.proj 0 u‖ ^ 2 + ‖D.proj 1 u‖ ^ 2 + ‖D.proj 2 u‖ ^ 2 := by
  conv_lhs => rw [← D.decompose u]
  rw [norm_sq_add_orthogonal]
  · rw [norm_sq_add_orthogonal]
    exact D.orthogonal 0 1 (by decide) u u
  · rw [inner_add_left, D.orthogonal 0 2 (by decide), D.orthogonal 1 2 (by decide)]
    simp

def cauchy (M : E →L[ℂ] E) : E →L[ℂ] E :=
  D.proj 0 + D.proj 1 + M.comp (D.proj 1)

def cauchyAdjoint (M : E →L[ℂ] E) : E →L[ℂ] E :=
  D.proj 0 + D.proj 1 + M.adjoint.comp (D.proj 2)

lemma adjoint_cauchy (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) :
    (D.cauchy M).adjoint = D.cauchyAdjoint M := by
  have h := congrArg ContinuousLinearMap.adjoint hswap
  simp only [ContinuousLinearMap.adjoint_comp, D.selfAdjoint] at h
  simp only [cauchy, cauchyAdjoint, map_add, ContinuousLinearMap.adjoint_comp,
    D.selfAdjoint, h]

lemma adjoint_markov_swap (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) :
    (D.proj 1).comp M.adjoint = M.adjoint.comp (D.proj 2) := by
  have h := congrArg ContinuousLinearMap.adjoint hswap
  simpa only [ContinuousLinearMap.adjoint_comp, D.selfAdjoint] using h

lemma adjoint_apply (M : E →L[ℂ] E) (u : E) :
    D.cauchyAdjoint M u = D.proj 0 u + D.proj 1 u + M.adjoint (D.proj 2 u) := rfl

lemma adjoint_positive (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) (u : E) :
    M.adjoint (D.proj 2 u) = D.proj 1 (M.adjoint u) := by
  exact (congrArg (fun T : E →L[ℂ] E => T u) (D.adjoint_markov_swap M hswap)).symm

lemma mean_adjoint (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) (u : E) :
    D.proj 0 (D.cauchyAdjoint M u) = D.proj 0 u := by
  rw [D.adjoint_apply, D.adjoint_positive M hswap]
  simp only [map_add, D.proj_proj]
  simp

lemma negative_adjoint (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) (u : E) :
    D.proj 2 (D.cauchyAdjoint M u) = 0 := by
  rw [D.adjoint_apply, D.adjoint_positive M hswap]
  simp only [map_add, D.proj_proj]
  simp [Fin.ext_iff]

theorem weighted_adjoint_bound (M : E →L[ℂ] E) (hM : ‖M‖ ≤ 1)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) (u : E) :
    ‖D.cauchyAdjoint M u‖ ^ 2 + ‖D.proj 0 u‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 := by
  have hd : ‖M.adjoint (D.proj 2 u)‖ ≤ ‖D.proj 2 u‖ := by
    calc _ ≤ ‖M.adjoint‖ * ‖D.proj 2 u‖ := M.adjoint.le_opNorm _
      _ ≤ 1 * ‖D.proj 2 u‖ := by
        gcongr
        simpa using hM
      _ = _ := one_mul _
  have hadd : ‖D.proj 1 u + M.adjoint (D.proj 2 u)‖ ^ 2 ≤
      2 * (‖D.proj 1 u‖ ^ 2 + ‖D.proj 2 u‖ ^ 2) := by
    have htri := norm_add_le (D.proj 1 u) (M.adjoint (D.proj 2 u))
    have h1 := norm_nonneg (D.proj 1 u)
    have h2 := norm_nonneg (M.adjoint (D.proj 2 u))
    have h3 := norm_nonneg (D.proj 2 u)
    have h4 := norm_nonneg (D.proj 1 u + M.adjoint (D.proj 2 u))
    nlinarith [sq_nonneg (‖D.proj 1 u‖ - ‖D.proj 2 u‖)]
  have horth : inner ℂ (D.proj 0 u)
      (D.proj 1 u + M.adjoint (D.proj 2 u)) = 0 := by
    rw [D.adjoint_positive M hswap, inner_add_right,
      D.orthogonal 0 1 (by decide), D.orthogonal 0 1 (by decide)]
    simp
  rw [D.adjoint_apply, add_assoc,
    norm_sq_add_orthogonal _ _ horth,
    D.norm_decompose u]
  linarith

end FourierResolution
end

open scoped lp
variable {ι : Type u_42} {E : Type u_43} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [instCompleteSpaceE : CompleteSpace E]

def modeMask (c : ι → Fin 3) (j : Fin 3) (u : ℓ²(ι, ℂ)) : ℓ²(ι, ℂ) :=
  ⟨fun n => if c n = j then u n else 0, (lp.memℓp u).mono' (by
    intro n; split_ifs <;> simp)⟩

@[simp] lemma modeMask_apply (c : ι → Fin 3) (j : Fin 3) (u : ℓ²(ι, ℂ)) (n : ι) :
    modeMask c j u n = if c n = j then u n else 0 := rfl

lemma modeMask_norm (c : ι → Fin 3) (j : Fin 3) (u : ℓ²(ι, ℂ)) :
    ‖modeMask c j u‖ ≤ ‖u‖ := by
  apply lp.norm_mono (by norm_num)
  intro n
  simp only [modeMask_apply]
  split_ifs <;> simp

def modeMaskL (c : ι → Fin 3) (j : Fin 3) : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  LinearMap.mkContinuous
  { toFun := modeMask c j
    map_add' u v := by ext n; simp only [modeMask_apply, lp.coeFn_add, Pi.add_apply]; split_ifs <;> simp
    map_smul' a u := by ext n; simp only [modeMask_apply, lp.coeFn_smul, Pi.smul_apply]; split_ifs <;> simp }
    1 (by intro u; simpa using modeMask_norm c j u)

@[simp] lemma modeMaskL_apply (c : ι → Fin 3) (j : Fin 3) (u : ℓ²(ι, ℂ)) (n : ι) :
    modeMaskL c j u n = if c n = j then u n else 0 := rfl

def basisProjection (b : HilbertBasis ι ℂ E) (c : ι → Fin 3) (j : Fin 3) : E →L[ℂ] E :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((modeMaskL c j).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] lemma basisProjection_repr
    {ι : Type u_42} {E : Type u_43} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (b : HilbertBasis ι ℂ E) (c : ι → Fin 3)
    (j : Fin 3) (u : E) (n : ι) :
    b.repr (basisProjection b c j u) n = if c n = j then b.repr u n else 0 := by
  simp [basisProjection]

lemma basisProjection_inner (b : HilbertBasis ι ℂ E) (c : ι → Fin 3)
    (j : Fin 3) (u v : E) :
    inner ℂ (basisProjection b c j u) v = inner ℂ u (basisProjection b c j v) := by
  rw [← b.repr.inner_map_map, ← b.repr.inner_map_map]
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [basisProjection_repr]
  split_ifs <;> simp

def basisResolution (b : HilbertBasis ι ℂ E) (c : ι → Fin 3) : FourierResolution E where
  proj := basisProjection b c
  selfAdjoint i := by
    symm
    exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (basisProjection_inner b c i)
  product i j := by
    ext u
    apply b.repr.injective
    ext n
    by_cases hij : i = j
    · subst j
      simp only [ContinuousLinearMap.comp_apply, basisProjection_repr]
      by_cases hc : c n = i <;> simp [hc]
    · simp only [ite_eq_right hij, zero_apply, map_zero, lp.coeFn_zero, Pi.zero_apply,
        ContinuousLinearMap.comp_apply, basisProjection_repr]
      by_cases hc : c n = i
      · simp [hc, hij]
      · simp [hc]

  total := by
    ext u
    apply b.repr.injective
    ext n
    simp only [add_apply, map_add, lp.coeFn_add, Pi.add_apply,
      basisProjection_repr, ContinuousLinearMap.id_apply]
    have h : c n = 0 ∨ c n = 1 ∨ c n = 2 := by omega
    rcases h with h | h | h <;> simp [h]

def frequencyPart (n : ℤ) : Fin 3 := if n = 0 then 0 else if 0 < n then 1 else 2

open MeasureTheory
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
abbrev CircleL2 := Lp ℂ 2 (@AddCircle.haarAddCircle 1 inferInstance)

def scalarFourier : FourierResolution CircleL2 :=
  basisResolution fourierBasis frequencyPart

lemma scalarFourier_coefficient (j : Fin 3) (u : CircleL2) (n : ℤ) :
    fourierCoeff (scalarFourier.proj j u) n =
      if frequencyPart n = j then fourierCoeff u n else 0 := by
  simpa only [← fourierBasis_repr, scalarFourier, basisResolution] using
    basisProjection_repr (E := CircleL2) fourierBasis frequencyPart j u n

end

open MeasureTheory ComplexConjugate
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma circle_fourier_ext {u v : CircleL2}
    (h : ∀ n : ℤ, fourierCoeff u n = fourierCoeff v n) : u = v := by
  apply fourierBasis.repr.injective
  apply lp.ext
  funext n
  simpa only [fourierBasis_repr] using h n

lemma circle_fourier_star (u : CircleL2) (n : ℤ) :
    fourierCoeff (star u : CircleL2) n = star (fourierCoeff u (-n)) := by
  rw [fourierCoeff, fourierCoeff]
  change _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u] with t ht
  simp only [ht, Pi.star_apply, smul_eq_mul, map_mul, neg_neg,
    fourier_neg, RCLike.star_def]

lemma integral_fourier_nonzero (n : ℤ) (hn : n ≠ 0) :
    (∫ t : UnitAddCircle, fourier n t ∂AddCircle.haarAddCircle) = 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) n) 0
  simpa [fourierCoeff, Pi.single_eq_of_ne hn.symm] using h

lemma scalarFourier_fourier (j : Fin 3) (n : ℤ) :
    scalarFourier.proj j (fourierLp 2 n) =
      if frequencyPart n = j then fourierLp 2 n else 0 := by
  apply circle_fourier_ext
  intro k
  rw [scalarFourier_coefficient]
  have hf : fourierCoeff (fourierLp 2 n : CircleL2) k = (Pi.single n (1 : ℂ) : ℤ → ℂ) k := by
    rw [fourierCoeff_congr_ae (coeFn_fourierLp 2 n), fourierCoeff_fourier]
  by_cases h : frequencyPart n = j
  · simp only [h, ite_true, hf]
    by_cases hkn : k = n
    · subst k; simp [h]
    · simp [Pi.single_eq_of_ne hkn]
  · have hz : fourierCoeff (0 : CircleL2) k = 0 := by
      rw [fourierCoeff_congr_ae (Lp.coeFn_zero _ _ _)]
      simp [fourierCoeff]
    simp only [h, ite_false, hz, hf]
    by_cases hkn : k = n
    · subst k; simp [h]
    · simp [Pi.single_eq_of_ne hkn]

namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)

lemma kernel_complex (w t : UnitAddCircle) :
    (K.kernel w t : ℂ) = 1 + K.circleB w t + conj (K.circleB w t) := by
  apply Complex.ext <;> simp [kernel, Complex.add_re, Complex.add_im]; ring

lemma star_fourierLp (n : ℤ) :
    star (fourierLp 2 n : CircleL2) = fourierLp 2 (-n) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (fourierLp 2 n : CircleL2),
    coeFn_fourierLp 2 n, coeFn_fourierLp 2 (-n)] with t hs hn hneg
  simp only [hs,Pi.star_apply,hn,hneg,fourier_neg,RCLike.star_def]

end AnalyticBidiskKernel
end CompleteCrouzeix

end

end OAI
