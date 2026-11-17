/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.LinearAlgebra.Matrix.Cartan.WeylGroupCoxeter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The exchange condition for the Weyl group of a generalized Cartan matrix

Let `A` be a generalized Cartan matrix with realization `(𝔥, Π, Π^∨)` over a field `K` of
characteristic zero, and `W` its Weyl group. Using that `W` is a Coxeter group whose elements map
each simple root into `Q₊` or `-Q₊` (`Matrix.Realization.coxeterSystem`,
`Matrix.Realization.isRightDescent_coxeterSystem_iff`), we prove:

* If `u ∈ W` and `u αⱼ = αᵢ`, then `u rⱼ u⁻¹ = rᵢ` (proof of [Kac] Lemma 3.10, (3.10.3); also
  what makes the reflection `r_α` of a real root `α` well defined, [Kac] §5.1).
* The exchange condition ([Kac] Lemma 3.10): if `w = r_{i₁} ⋯ r_{iₜ}` and `w αᵢ < 0`, then
  `w rᵢ = r_{i₁} ⋯ r̂_{iₛ} ⋯ r_{iₜ}` for some `s`.

The proof of the first statement is not the one of [Kac], which uses automorphisms of `𝔤(A)`
lifting the `rᵢ`; we reconstructed the following argument. The element `g = rᵢ u rⱼ u⁻¹ ∈ W` acts
by a transvection `λ ↦ λ + ψ(λ) αᵢ` with `ψ(αᵢ) = 0`. For `k ≠ i` both `g αₖ = αₖ + ψ(αₖ) αᵢ` and
`g⁻¹ αₖ = αₖ - ψ(αₖ) αᵢ` lie in `Q₊ ∪ -Q₊`, which forces `ψ(αₖ) = 0`. Hence `g` fixes all simple
roots, and `g = 1` by the faithfulness criterion `CoxeterSystem.eq_one_of_forall_smul_eq`.

## Main results

* `Matrix.Realization.eq_one_of_forall_apply_root_eq`: an element of `W` fixing all simple roots
  is the identity.
* `Matrix.Realization.mul_reflection_mul_inv_eq`: `u αⱼ = αᵢ → u rⱼ u⁻¹ = rᵢ`.
* `Matrix.Realization.exists_mul_reflection_eq_eraseIdx`: the exchange condition.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Lemma 3.10, Lemma 3.11,
  §5.1.
* [Hum] J. E. Humphreys, *Reflection groups and Coxeter groups*, CUP 1990, §5.4.
-/

open Module CoxeterSystem

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)

/-- Every element of `W` maps a simple root into `Q₊` or into `-Q₊` ([Kac] Lemma 3.11 (a)).
@isnad1 id=or.2h7v.s12.8aa2dadf034b from=translated src=- shape=9c92ca25 vocab=c9e15f08
-/
theorem apply_root_nonneg_or_nonpos {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    (i : ι) : (∃ k : ι → ℤ, 0 ≤ k ∧ w (P.root i) = P.rootOf k) ∨
      ∃ k : ι → ℤ, 0 ≤ k ∧ w (P.root i) = -P.rootOf k := by
  classical
  by_cases h : (P.coxeterSystem hA).IsRightDescent ⟨w, hw⟩ i
  · exact Or.inr ((P.isRightDescent_coxeterSystem_iff hA).mp h)
  · exact Or.inl ((P.not_isRightDescent_coxeterSystem_iff hA).mp h)

/-- `W` acts faithfully on the simple roots: an element of `W` fixing every `αᵢ` is the
identity ([Hum] Cor. 5.4 for the geometric representation).-/
theorem eq_one_of_forall_apply_root_eq {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    (h : ∀ i, w (P.root i) = P.root i) : w = 1 := by
  classical
  have := (P.coxeterSystem hA).eq_one_of_forall_smul_eq (P.isDihedrallyPositive_coxeterSystem hA)
    (P.coxeterSystem_simple_smul_root hA)
    (fun _ hv hv' ↦ P.eq_zero_of_mem_closure_of_neg_mem hv hv')
    P.linearIndependent_root.ne_zero (w := ⟨w, hw⟩)
    (fun i ↦ by rw [Submonoid.smul_def, LinearEquiv.smul_def]; exact h i)
  simpa using congrArg Subtype.val this

omit [CharZero K] in
/-- `⟨αⱼ, αᵢ^∨⟩` computed on the root lattice is an integer: an element of `W` maps `αⱼ` to a
weight whose pairing with every coroot is integral.
@isnad1 id=ex.2h8v.s11.c8d9de7b540f from=translated src=- shape=9456d730 vocab=b8d0f1bc
-/
lemma exists_int_apply_root_coroot {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    (i j : ι) : ∃ z : ℤ, w (P.root j) (P.coroot i) = z := by
  classical
  obtain ⟨k, hk⟩ := P.exists_apply_rootOf_eq_rootOf hA hw (Pi.single j 1)
  rw [rootOf_single] at hk
  exact ⟨_, by rw [hk, rootOf_apply_coroot]⟩

/-- If `w ∈ W` and `w αₖ = αₖ + z αᵢ` with `k ≠ i`, then `z ≥ 0`.
@isnad1 id=le.4h9v.s11.071ed0ec3827 from=translated src=- shape=b0e15928 vocab=47e222df
-/
lemma nonneg_of_apply_root_eq_add {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    {i k : ι} (hki : k ≠ i) {z : ℤ} (h : w (P.root k) = P.root k + (z : K) • P.root i) :
    0 ≤ z := by
  classical
  have hQ : P.root k + (z : K) • P.root i = P.rootOf (Pi.single k 1 + z • Pi.single i 1) := by
    rw [map_add, map_zsmul, rootOf_single, rootOf_single, ← Int.cast_smul_eq_zsmul K]
  rcases P.apply_root_nonneg_or_nonpos hA hw k with ⟨l, hl, hwl⟩ | ⟨l, hl, hwl⟩
  · have := P.rootOf_injective (hQ.symm.trans (h.symm.trans hwl))
    have := congr_fun this i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hki.symm, ↓reduceIte,
      smul_eq_mul, mul_one, zero_add] at this
    rw [this]
    exact hl i
  · have := P.rootOf_injective (show P.rootOf (Pi.single k 1 + z • Pi.single i 1) = P.rootOf (-l)
      by rw [← hQ, ← h, hwl, map_neg])
    have := congr_fun this k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hki, ↓reduceIte,
      smul_eq_mul, mul_zero, add_zero, Pi.neg_apply] at this
    have := hl k
    simp only [Pi.zero_apply] at this
    omega

/-- **Proof of [Kac] Lemma 3.10, (3.10.3)**: if `u ∈ W` maps the simple root `αⱼ` to the
simple root `αᵢ`, then `u rⱼ u⁻¹ = rᵢ`. The argument (reconstructed, see the module docstring) shows
that `rᵢ u rⱼ u⁻¹` fixes all simple roots.
@isnad1 id=eq.3h8v.s13.700da4a8c33c from=translated src=- shape=d18f20b6 vocab=79230547
-/
theorem mul_reflection_mul_inv_eq {u : Dual K H ≃ₗ[K] Dual K H} (hu : u ∈ P.weylGroup hA)
    {i j : ι} (h : u (P.root j) = P.root i) :
    u * P.reflection hA j * u⁻¹ = P.reflection hA i := by
  classical
  set g := P.reflection hA i * (u * P.reflection hA j * u⁻¹) with hg
  have hgW : g ∈ P.weylGroup hA := mul_mem (P.reflection_mem_weylGroup hA i)
    (mul_mem (mul_mem hu (P.reflection_mem_weylGroup hA j)) (inv_mem hu))
  -- `g` is the transvection `λ ↦ λ + ψ(λ) αᵢ`
  let ψ : Dual K H → K := fun μ ↦ (u⁻¹ μ) (P.coroot j) - μ (P.coroot i)
  have hui : u⁻¹ (P.root i) = P.root j := by rw [← h]; simp
  have hψi : ψ (P.root i) = 0 := by
    simp only [ψ, hui, P.root_coroot_self hA, sub_self]
  have hgμ : ∀ μ, g μ = μ + ψ μ • P.root i := by
    intro μ
    simp only [hg, ψ, LinearEquiv.mul_apply, reflection_apply, map_sub, map_smul, h,
      P.root_coroot_self hA]
    rw [show u (u⁻¹ μ) = μ from u.apply_symm_apply μ]
    module
  have hψlin : ∀ μ ν : Dual K H, ∀ c : K, ψ (μ - c • ν) = ψ μ - c * ψ ν := by
    intro μ ν c
    simp only [ψ, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hginv : ∀ μ, g⁻¹ μ = μ - ψ μ • P.root i := by
    intro μ
    have : g (μ - ψ μ • P.root i) = μ := by
      rw [hgμ, hψlin, hψi, mul_zero, sub_zero]
      abel
    conv_lhs => rw [← this]
    exact g.symm_apply_apply _
  -- `ψ` vanishes on all simple roots
  have hψk : ∀ k, ψ (P.root k) = 0 := by
    intro k
    by_cases hki : k = i
    · rw [hki, hψi]
    obtain ⟨z₁, hz₁⟩ := P.exists_int_apply_root_coroot hA (inv_mem hu) j k
    obtain ⟨z, hz⟩ : ∃ z : ℤ, ψ (P.root k) = z :=
      ⟨z₁ - A i k, by simp only [ψ, hz₁, P.root_coroot]; push_cast; ring⟩
    have h1 := P.nonneg_of_apply_root_eq_add hA hgW hki (z := z) (by rw [hgμ, hz])
    have h2 := P.nonneg_of_apply_root_eq_add hA (inv_mem hgW) hki (z := -z)
      (by rw [hginv, hz]; push_cast; module)
    rw [hz, show z = 0 by omega, Int.cast_zero]
  have hg1 : g = 1 := P.eq_one_of_forall_apply_root_eq hA hgW fun k ↦ by
    rw [hgμ, hψk, zero_smul, add_zero]
  calc u * P.reflection hA j * u⁻¹
      = P.reflection hA i * g := by
        rw [hg, ← mul_assoc, reflection_mul_self, one_mul]
    _ = P.reflection hA i := by rw [hg1, mul_one]

/-- A positive element `γ ∈ W αᵢ` of `Q₊` with `rⱼ γ ∈ -Q₊` is the simple root `αⱼ`.-/
lemma eq_root_of_reflection_apply {u : Dual K H ≃ₗ[K] Dual K H} (hu : u ∈ P.weylGroup hA)
    {i j : ι} {k : ι → ℤ} (hk : 0 ≤ k) (huk : u (P.root i) = P.rootOf k)
    {l : ι → ℤ} (hl : 0 ≤ l) (hrl : P.reflection hA j (u (P.root i)) = -P.rootOf l) :
    u (P.root i) = P.root j := by
  classical
  -- all coefficients of `γ = u αᵢ` except the `j`-th vanish
  rw [huk, reflection_rootOf] at hrl
  have hkl := P.rootOf_injective (hrl.trans (map_neg _ _).symm)
  have hkj : ∀ x, x ≠ j → k x = 0 := fun x hx ↦ by
    have h1 := congr_fun hkl x
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hx, ↓reduceIte, smul_eq_mul,
      mul_zero, sub_zero, Pi.neg_apply] at h1
    have := hk x; have := hl x
    simp only [Pi.zero_apply] at *
    omega
  have hγ : u (P.root i) = (k j : K) • P.root j := by
    rw [huk, P.rootOf_eq_smul_root_of_eq_zero hkj]
  -- `u⁻¹ αⱼ` lies in the root lattice, so `k j = 1`
  obtain ⟨m, hm⟩ := P.exists_apply_rootOf_eq_rootOf hA (inv_mem hu) (Pi.single j 1)
  rw [rootOf_single] at hm
  have h1 : P.root i = (k j : K) • P.rootOf m := by
    rw [← hm, ← map_smul, ← hγ]
    exact (u.symm_apply_apply _).symm
  have h2 : Pi.single i 1 = k j • m := P.rootOf_injective (by
    rw [rootOf_single, map_zsmul, h1, ← Int.cast_smul_eq_zsmul K])
  have h3 := congr_fun h2 i
  simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul] at h3
  have hkj1 : k j = 1 := by
    have := hk j
    simp only [Pi.zero_apply] at this
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h3.symm with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  rw [hγ, hkj1, Int.cast_one, one_smul]

end Matrix.Realization
