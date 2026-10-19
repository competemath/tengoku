/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Analysis.Calculus.ImplicitContDiff
import Tengoku.Seed.Analysis.Complex.Polynomial.Basic
import Tengoku.Seed.Algebra.MvPolynomial.Eval
import Tengoku.Seed.Analysis.Calculus.Deriv.Polynomial
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.FieldTheory.Separable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Simple roots of polynomials with holomorphic coefficients depend holomorphically on parameters

Let `E` be a complex Banach space and `p : E → ℂ[X]` a family of polynomials of bounded degree
whose coefficients are analytic at `z₀`. If `t₀` is a simple root of `p z₀`, the complex
implicit function theorem yields an analytic function `ψ` near `z₀` with `ψ z₀ = t₀` such that,
near `(z₀, t₀)`, the zero set of `(z, t) ↦ (p z)(t)` is exactly the graph of `ψ`.

If all roots of `p z₀` are simple (`p z₀` separable) and the `p z` are monic of degree `n`, then
near `z₀` the polynomial `p z` factors as `∏ⱼ (X - ψⱼ z)` with `n` analytic functions `ψⱼ` taking
pairwise distinct values.

Both statements are specialised to `μ ∈ (MvPolynomial ι ℂ)[X]`, `p z = μ_z` the specialisation
of the coefficients at `z : ι → ℂ`.

## Main results

- `Polynomial.exists_analyticOnNhd_root_of_eval_derivative_ne_zero`
- `Polynomial.exists_analyticOnNhd_eq_prod_X_sub_C_of_separable`
- `Polynomial.exists_analyticOnNhd_root_map_eval_of_eval_derivative_ne_zero`
- `Polynomial.exists_analyticOnNhd_map_eval_eq_prod_X_sub_C_of_separable`
-/

open Filter Metric Set
open scoped Topology ContDiff

namespace Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private theorem analyticAt_mvPolynomial_eval {ι : Type*} [Fintype ι]
    (q : MvPolynomial ι ℂ) (x : ι → ℂ) :
    AnalyticAt ℂ (fun z : ι → ℂ ↦ MvPolynomial.eval z q) x := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval_C]
      exact analyticAt_const
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
  | mul_X p i hp =>
      have hi : AnalyticAt ℂ (fun z : ι → ℂ ↦ z i) x :=
        (ContinuousLinearMap.proj (R := ℂ) i).analyticAt x
      simp only [map_mul, MvPolynomial.eval_X]
      exact hp.mul hi

omit [CompleteSpace E] in
/-- Evaluation `(z, t) ↦ (p z)(t)` of a family of polynomials of bounded degree with coefficients
analytic at `z₀` is jointly analytic at `(z₀, t₀)`. -/
theorem analyticAt_eval_of_analyticAt_coeff {p : E → ℂ[X]} {n : ℕ}
    (hn : ∀ z, (p z).natDegree ≤ n) {z₀ : E}
    (ha : ∀ i, AnalyticAt ℂ (fun z ↦ (p z).coeff i) z₀) (t₀ : ℂ) :
    AnalyticAt ℂ (fun v : E × ℂ ↦ (p v.1).eval v.2) (z₀, t₀) := by
  have h : (fun v : E × ℂ ↦ (p v.1).eval v.2) =
      fun v ↦ ∑ i ∈ Finset.range (n + 1), (p v.1).coeff i * v.2 ^ i := by
    funext v
    exact eval_eq_sum_range' (Nat.lt_succ_of_le (hn v.1)) v.2
  rw [h]
  refine Finset.analyticAt_fun_sum _ fun i _ ↦ ?_
  have hfst : AnalyticAt ℂ (Prod.fst : E × ℂ → E) (z₀, t₀) := analyticAt_fst
  exact ((ha i).comp hfst).mul (analyticAt_snd.pow i)

/-- **Holomorphic dependence of a simple root.** Let `p z` be polynomials of degree `≤ n` whose
coefficients are analytic at `z₀`, and let `t₀` be a simple root of `p z₀`. Then there are an
open neighbourhood `U` of `z₀`, a radius `ε > 0` and a function `ψ`, analytic on `U`, with
`ψ z₀ = t₀`, such that for `z ∈ U` the value `ψ z` is the unique root of `p z` in the ball
`B(t₀, ε)`. -/
theorem exists_analyticOnNhd_root_of_eval_derivative_ne_zero {p : E → ℂ[X]} {n : ℕ}
    (hn : ∀ z, (p z).natDegree ≤ n) {z₀ : E}
    (ha : ∀ i, AnalyticAt ℂ (fun z ↦ (p z).coeff i) z₀) {t₀ : ℂ}
    (hroot : (p z₀).IsRoot t₀) (hsimple : (p z₀).derivative.eval t₀ ≠ 0) :
    ∃ U : Set E, IsOpen U ∧ z₀ ∈ U ∧ ∃ ε > 0, ∃ ψ : E → ℂ, AnalyticOnNhd ℂ ψ U ∧ ψ z₀ = t₀ ∧
      ∀ z ∈ U, ψ z ∈ ball t₀ ε ∧ ∀ t ∈ ball t₀ ε, ((p z).IsRoot t ↔ ψ z = t) := by
  set f : E × ℂ → ℂ := fun v ↦ (p v.1).eval v.2 with hfdef
  set u : E × ℂ := (z₀, t₀)
  have hf : AnalyticAt ℂ f u := analyticAt_eval_of_analyticAt_coeff hn ha t₀
  have cdf : ContDiffAt ℂ ω f u := hf.contDiffAt
  -- the partial derivative in `t` is multiplication by `c = (p z₀)'(t₀)`
  set c := (p z₀).derivative.eval t₀
  have hpart : fderiv ℂ f u ∘L .inr ℂ E ℂ = (1 : ℂ →L[ℂ] ℂ).smulRight c := by
    have h1 : HasFDerivAt (f ∘ fun t ↦ (z₀, t)) (fderiv ℂ f u ∘L .inr ℂ E ℂ) t₀ :=
      hf.differentiableAt.hasFDerivAt.comp t₀ (hasFDerivAt_prodMk_right z₀ t₀)
    have h2 : HasFDerivAt (f ∘ fun t ↦ (z₀, t)) ((1 : ℂ →L[ℂ] ℂ).smulRight c) t₀ :=
      ((p z₀).hasDerivAt t₀).hasFDerivAt
    exact h1.unique h2
  have if₂ : (fderiv ℂ f u ∘L .inr ℂ E ℂ).IsInvertible := by
    rw [hpart]
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := (1 : ℂ →L[ℂ] ℂ).smulRight c⁻¹) ?_ ?_ <;>
    · ext
      simp [hsimple]
  set ψ := cdf.implicitFunction (by simp) if₂
  have hψ0 : ψ z₀ = t₀ := cdf.implicitFunction_apply_self (by simp) if₂
  have hψa : AnalyticAt ℂ ψ z₀ := (cdf.contDiffAt_implicitFunction (by simp) if₂).analyticAt
  have hfu : f u = 0 := hroot
  have heq := cdf.eventually_apply_eq_iff_implicitFunction (by simp) if₂
  rw [hfu] at heq
  obtain ⟨s, hs, w, hw, hsw⟩ := mem_nhds_prod_iff.1 heq
  obtain ⟨ε, hε, hεw⟩ := Metric.mem_nhds_iff.1 hw
  have hball : ψ ⁻¹' ball t₀ ε ∈ 𝓝 z₀ :=
    hψa.continuousAt.preimage_mem_nhds (hψ0 ▸ ball_mem_nhds t₀ hε)
  set W := s ∩ ψ ⁻¹' ball t₀ ε ∩ {z | AnalyticAt ℂ ψ z}
  have hW : W ∈ 𝓝 z₀ := inter_mem (inter_mem hs hball) hψa.eventually_analyticAt
  refine ⟨interior W, isOpen_interior, mem_interior_iff_mem_nhds.2 hW, ε, hε, ψ,
    fun z hz ↦ (interior_subset hz).2, hψ0, fun z hz ↦ ?_⟩
  have hz := interior_subset hz
  refine ⟨hz.1.2, fun t ht ↦ ?_⟩
  exact hsw (mk_mem_prod hz.1.1 (hεw ht))

/-- **Local factorisation at a separable fibre.** If the `p z` are monic of degree `n` with
coefficients analytic at `z₀`, and `p z₀` is separable, then near `z₀` there are `n` analytic
functions `ψⱼ`, with pairwise distinct values, such that `p z = ∏ⱼ (X - ψⱼ z)`. -/
theorem exists_analyticOnNhd_eq_prod_X_sub_C_of_separable {p : E → ℂ[X]} {n : ℕ}
    (hm : ∀ z, (p z).Monic) (hn : ∀ z, (p z).natDegree = n) {z₀ : E}
    (ha : ∀ i, AnalyticAt ℂ (fun z ↦ (p z).coeff i) z₀) (hsep : (p z₀).Separable) :
    ∃ U : Set E, IsOpen U ∧ z₀ ∈ U ∧ ∃ ψ : Fin n → E → ℂ, (∀ j, AnalyticOnNhd ℂ (ψ j) U) ∧
      ∀ z ∈ U, Function.Injective (fun j ↦ ψ j z) ∧ p z = ∏ j, (X - C (ψ j z)) := by
  classical
  -- the roots of `p z₀`: `n` distinct simple roots
  have hnd : (p z₀).roots.Nodup := nodup_roots hsep
  have hcard : (p z₀).roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, IsAlgClosed.card_roots_eq_natDegree, hn]
  let e : Fin n ≃ (p z₀).roots.toFinset := ((p z₀).roots.toFinset.equivFin.trans
    (finCongr hcard)).symm
  let t : Fin n → ℂ := fun j ↦ e j
  have ht : ∀ j, (p z₀).IsRoot (t j) := fun j ↦
    (mem_roots (hm z₀).ne_zero).1 (Multiset.mem_toFinset.1 (e j).2)
  have htinj : Function.Injective t := fun j k h ↦ e.injective (Subtype.ext h)
  have hsimple : ∀ j, (p z₀).derivative.eval (t j) ≠ 0 := fun j ↦ by
    simpa using hsep.aeval_derivative_ne_zero (x := t j) (by simpa using ht j)
  choose U hU hzU ε hε ψ hψa hψ0 hψ using fun j ↦
    exists_analyticOnNhd_root_of_eval_derivative_ne_zero (fun z ↦ (hn z).le) ha (ht j)
      (hsimple j)
  have hcont : ∀ j, ContinuousAt (ψ j) z₀ := fun j ↦
    ((hψa j) z₀ (hzU j)).continuousAt
  have hne : ∀ j k, j ≠ k → ∀ᶠ z in 𝓝 z₀, ψ j z - ψ k z ≠ 0 := fun j k hjk ↦
    ((hcont j).sub (hcont k)).eventually_ne (by
      rw [Pi.sub_apply, hψ0, hψ0, sub_ne_zero]; exact htinj.ne hjk)
  set W := {z | (∀ j, z ∈ U j) ∧ ∀ j k, j ≠ k → ψ j z - ψ k z ≠ 0}
  have hW : W ∈ 𝓝 z₀ := inter_mem (eventually_all.2 fun j ↦ (hU j).mem_nhds (hzU j))
    (eventually_all.2 fun j ↦ eventually_all.2 fun k ↦ by
      by_cases hjk : j = k
      · exact Eventually.of_forall fun _ h ↦ absurd hjk h
      · filter_upwards [hne j k hjk] with z hz _ using hz)
  refine ⟨interior W, isOpen_interior, mem_interior_iff_mem_nhds.2 hW, ψ,
    fun j z hz ↦ hψa j z ((interior_subset hz).1 j), fun z hz ↦ ?_⟩
  have hz := interior_subset hz
  have hinj : Function.Injective (fun j ↦ ψ j z) := fun j k h ↦ by
    by_contra hjk
    exact hz.2 j k hjk (sub_eq_zero.2 h)
  refine ⟨hinj, ?_⟩
  set r : Multiset ℂ := Finset.univ.val.map (fun j ↦ ψ j z)
  have hrnd : r.Nodup := Finset.univ.nodup.map hinj
  have hrle : r ≤ (p z).roots := (Multiset.le_iff_subset hrnd).2 fun x hx ↦ by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hx
    have h := hψ j z (hz.1 j)
    exact (mem_roots (hm z).ne_zero).2 ((h.2 _ h.1).2 rfl)
  have hcardz : Multiset.card (p z).roots = (p z).natDegree :=
    IsAlgClosed.card_roots_eq_natDegree
  have hr : r = (p z).roots := Multiset.eq_of_le_of_card_le hrle (by
    rw [hcardz, hn z, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin])
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hm z) hcardz, ← hr,
    Finset.prod_eq_multiset_prod, Multiset.map_map]
  rfl

section MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- `exists_analyticOnNhd_root_of_eval_derivative_ne_zero` for `μ ∈ (MvPolynomial ι ℂ)[X]`: a
simple root `t₀` of `μ_{z₀}` extends to an analytic root `ψ` of `μ_z` near `z₀`, the unique
root of `μ_z` in `B(t₀, ε)`. -/
theorem exists_analyticOnNhd_root_map_eval_of_eval_derivative_ne_zero
    (μ : (MvPolynomial ι ℂ)[X]) {z₀ : ι → ℂ} {t₀ : ℂ}
    (hroot : (μ.map (MvPolynomial.eval z₀)).IsRoot t₀)
    (hsimple : (μ.map (MvPolynomial.eval z₀)).derivative.eval t₀ ≠ 0) :
    ∃ U : Set (ι → ℂ), IsOpen U ∧ z₀ ∈ U ∧ ∃ ε > 0, ∃ ψ : (ι → ℂ) → ℂ,
      AnalyticOnNhd ℂ ψ U ∧ ψ z₀ = t₀ ∧ ∀ z ∈ U, ψ z ∈ ball t₀ ε ∧
        ∀ t ∈ ball t₀ ε, ((μ.map (MvPolynomial.eval z)).IsRoot t ↔ ψ z = t) :=
  exists_analyticOnNhd_root_of_eval_derivative_ne_zero (n := μ.natDegree)
    (fun _ ↦ natDegree_map_le) (fun i ↦ by
      simpa only [coeff_map] using analyticAt_mvPolynomial_eval (μ.coeff i) z₀) hroot hsimple

/-- `exists_analyticOnNhd_eq_prod_X_sub_C_of_separable` for monic `μ ∈ (MvPolynomial ι ℂ)[X]`:
if `μ_{z₀}` is separable, then near `z₀` we have `μ_z = ∏ⱼ (X - ψⱼ z)` with analytic `ψⱼ`
taking pairwise distinct values. -/
theorem exists_analyticOnNhd_map_eval_eq_prod_X_sub_C_of_separable
    {μ : (MvPolynomial ι ℂ)[X]} (hμ : μ.Monic) {z₀ : ι → ℂ}
    (hsep : (μ.map (MvPolynomial.eval z₀)).Separable) :
    ∃ U : Set (ι → ℂ), IsOpen U ∧ z₀ ∈ U ∧ ∃ ψ : Fin μ.natDegree → (ι → ℂ) → ℂ,
      (∀ j, AnalyticOnNhd ℂ (ψ j) U) ∧ ∀ z ∈ U, Function.Injective (fun j ↦ ψ j z) ∧
        μ.map (MvPolynomial.eval z) = ∏ j, (X - C (ψ j z)) :=
  exists_analyticOnNhd_eq_prod_X_sub_C_of_separable (p := fun z ↦ μ.map (MvPolynomial.eval z))
    (fun _ ↦ hμ.map _) (fun _ ↦ hμ.natDegree_map _) (fun i ↦ by
      simpa only [coeff_map] using analyticAt_mvPolynomial_eval (μ.coeff i) z₀) hsep

end MvPolynomial

end Polynomial
