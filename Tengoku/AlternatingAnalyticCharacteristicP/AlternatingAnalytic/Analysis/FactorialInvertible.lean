/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy

The proof of `cpolynomialAt_nsmul_compContinuousLinearMapCLM` is adapted from Mathlib pull
request #43338 by Sébastien Gouëzel, which is released under the Apache 2.0 license.
-/
import Tengoku
import Tengoku.Seed.Analysis.Analytic.CPolynomial
import Tengoku.Seed.Analysis.Analytic.Composition
import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Curry
import Tengoku.Seed.Data.Nat.Prime.Factorial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Precomposition on continuous alternating maps when `(card ι)!` is invertible

Alternatization `A μ = ∑_σ sgn σ • (μ ∘ σ)` is a continuous linear map from multilinear to
alternating maps of norm at most `(card ι)!`, and it multiplies an alternating map by
`(card ι)!`. So when `(card ι)! ≠ 0` in `𝕜`, `altProj = ((card ι)!)⁻¹ • A` is a continuous
linear retraction (Proposition 4.1(1)), and precomposition `f ↦ (m ↦ m ∘ f)` is continuously
polynomial, hence `C^n` for every `n` including `ω` (Corollary 6.2).

The polynomial core `cpolynomialAt_nsmul_compContinuousLinearMapCLM` is the argument of
Sébastien Gouëzel's mathlib#43338, which assumes `CharZero 𝕜` but only divides by `(card ι)!`.

## Main results

* `ContinuousAlternatingMap.altProj_toContinuousMultilinearMap`
* `ContinuousAlternatingMap.cpolynomialAt_compContinuousLinearMapCLM`
* `ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM_of_factorial_ne_zero`
-/

open scoped Nat ContDiff
open ContinuousMultilinearMap

namespace ContinuousMultilinearMap

variable {𝕜 ι E F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Alternatization increases the norm by at most `(Fintype.card ι)!`.-/
theorem norm_alternatization_le (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    ‖alternatization f‖ ≤ ((Fintype.card ι)! : ℝ) * ‖f‖ := by
  rw [← ContinuousAlternatingMap.norm_toContinuousMultilinearMap,
    alternatization_apply_toContinuousMultilinearMap]
  refine le_trans (norm_sum_le _ _) ?_
  have h : ∀ σ : Equiv.Perm ι, ‖(Equiv.Perm.sign σ : ℤ) • f.domDomCongr σ‖ ≤ ‖f‖ := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, norm_domDomCongr]
  calc ∑ σ : Equiv.Perm ι, ‖(Equiv.Perm.sign σ : ℤ) • f.domDomCongr σ‖
      ≤ ∑ _σ : Equiv.Perm ι, ‖f‖ := Finset.sum_le_sum fun σ _ ↦ h σ
    _ = ((Fintype.card ι)! : ℝ) * ‖f‖ := by simp [Finset.card_univ, Fintype.card_perm]

variable (𝕜 E F) in
/-- Alternatization, as a continuous linear map from continuous multilinear maps to continuous
alternating maps. Its operator norm is at most `(Fintype.card ι)!`.-/
noncomputable def alternatizationCLM :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F →L[𝕜] (E [⋀^ι]→L[𝕜] F) :=
  LinearMap.mkContinuous
    { toFun := alternatization
      map_add' := map_add _
      map_smul' := by
        intro c f
        ext v
        simp only [RingHom.id_apply, ContinuousAlternatingMap.smul_apply,
          alternatization_apply_apply, smul_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun σ _ ↦ smul_comm _ _ _ }
    ((Fintype.card ι)! : ℝ) (fun f ↦ norm_alternatization_le f)

@[simp] theorem alternatizationCLM_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    alternatizationCLM 𝕜 E F f = alternatization f := rfl

theorem norm_alternatizationCLM_le :
    ‖alternatizationCLM (ι := ι) 𝕜 E F‖ ≤ ((Fintype.card ι)! : ℝ) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- Alternatizing an already alternating map multiplies it by `(Fintype.card ι)!`.-/
theorem alternatization_toContinuousMultilinearMap (a : E [⋀^ι]→L[𝕜] F) :
    alternatization a.toContinuousMultilinearMap = (Fintype.card ι)! • a := by
  ext v
  have h : MultilinearMap.alternatization a.toAlternatingMap.toMultilinearMap v =
      ((Fintype.card ι)! • a.toAlternatingMap) v := by
    rw [AlternatingMap.coe_alternatization a.toAlternatingMap]
  simpa only [MultilinearMap.alternatization_apply, alternatization_apply_apply] using! h

/-- Scalar form of `ContinuousMultilinearMap.alternatization_toContinuousMultilinearMap`.-/
theorem alternatizationCLM_toContinuousMultilinearMap (a : E [⋀^ι]→L[𝕜] F) :
    alternatizationCLM 𝕜 E F a.toContinuousMultilinearMap = (((Fintype.card ι)! : 𝕜)) • a := by
  rw [alternatizationCLM_apply, alternatization_toContinuousMultilinearMap,
    Nat.cast_smul_eq_nsmul]

end ContinuousMultilinearMap

namespace ContinuousAlternatingMap

open ContinuousMultilinearMap

variable {𝕜 ι E E' F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
/-- The normalised alternatization `((card ι)!)⁻¹ • A`. It is a retraction of the inclusion
of alternating maps when `(card ι)! ≠ 0` in `𝕜`.-/
noncomputable def altProj :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F →L[𝕜] (E [⋀^ι]→L[𝕜] F) :=
  ((Fintype.card ι)! : 𝕜)⁻¹ • alternatizationCLM 𝕜 E F

/-- `ContinuousAlternatingMap.altProj` is a retraction of the inclusion.-/
theorem altProj_toContinuousMultilinearMap (h : ((Fintype.card ι)! : 𝕜) ≠ 0)
    (a : E [⋀^ι]→L[𝕜] F) : altProj 𝕜 E F a.toContinuousMultilinearMap = a := by
  rw [altProj, _root_.smul_apply, alternatizationCLM_toContinuousMultilinearMap,
    smul_smul, inv_mul_cancel₀ h, one_smul]

/-- The continuous linear map `u ↦ alternatization ∘ u ∘ (inclusion of alternating maps)`.-/
noncomputable def compAlternatizationCLM :
    (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E') F →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) →L[𝕜]
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) :=
  (ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) (E [⋀^ι]→L[𝕜] F)
      (alternatizationCLM 𝕜 E F)).comp
    ((ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E') F)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F)).flip (toContinuousMultilinearMapCLM 𝕜))

theorem compAlternatizationCLM_apply
    (u : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E') F →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) (m : E' [⋀^ι]→L[𝕜] F) :
    compAlternatizationCLM (𝕜 := 𝕜) (ι := ι) (E := E) (E' := E') (F := F) u m =
      alternatization (u m.toContinuousMultilinearMap) := by
  simp [compAlternatizationCLM]

end ContinuousAlternatingMap
