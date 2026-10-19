/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Analytic.RiemannExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded holomorphic functions on a Kummer covering along a normal crossings divisor

Let `E` be a finite-dimensional complex normed space, `M > 0` and `κ : E × ℂʳ → E × ℂʳ` the map
`(b, u) ↦ (b, u₁ᴹ, …, uᵣᴹ)`. Let `V ⊆ E × ℂʳ` be open and `Z = {u₁ ⋯ uᵣ = 0}`. A holomorphic
function on `κ⁻¹(V) \ Z` which is bounded near every point of `κ⁻¹(V)` extends holomorphically to
`κ⁻¹(V)` (`KummerPi.exists_differentiableOn_powMap_eqOn`), and the extension is invariant under
every multiplication of the coordinates by `M`-th roots of unity under which the function is
invariant (`KummerPi.eqOn_comp_rotMap`). So the bounded holomorphic functions on the quotient of the
Kummer covering by a group of roots of unity are the invariant holomorphic functions on `κ⁻¹(V)`.

## Main definitions

- `KummerPi.powMap M`: the map `(b, u) ↦ (b, uᴹ)` on `E × ℂʳ`.
- `KummerPi.rotMap M a`: multiplication of the `i`-th coordinate by `exp(2πi aᵢ / M)`.

## Main results

- `KummerPi.interior_inter_preimage_prod_eq_empty`: the divisor `u₁ ⋯ uᵣ = 0` has empty interior.
- `KummerPi.exists_differentiableOn_powMap_eqOn`: Riemann extension on the Kummer covering.
- `KummerPi.eqOn_comp_rotMap`: the extension of an invariant function is invariant.
-/

open Set Filter Topology Metric

namespace KummerPi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℕ}

/-- The map `(b, u) ↦ (b, u₁ᴹ, …, uᵣᴹ)` on `E × ℂʳ`. -/
def powMap (M : ℕ) (x : E × (Fin r → ℂ)) : E × (Fin r → ℂ) := (x.1, fun i ↦ x.2 i ^ M)

/-- The product `u₁ ⋯ uᵣ` of the coordinates of the second factor. -/
def prodCoord (x : E × (Fin r → ℂ)) : ℂ := ∏ i, x.2 i

/-- Multiplication of the `i`-th coordinate by the root of unity `exp(2πi aᵢ / M)`. -/
noncomputable def rotMap (M : ℕ) (a : Fin r → ℤ) (x : E × (Fin r → ℂ)) : E × (Fin r → ℂ) :=
  (x.1, fun i ↦ Complex.exp (2 * Real.pi * Complex.I * a i / M) * x.2 i)

@[fun_prop]
lemma differentiable_powMap (M : ℕ) : Differentiable ℂ (powMap (E := E) (r := r) M) := by
  unfold powMap
  fun_prop

@[fun_prop]
lemma differentiable_prodCoord : Differentiable ℂ (prodCoord (E := E) (r := r)) := by
  unfold prodCoord
  fun_prop

omit [NormedSpace ℂ E] in
@[fun_prop]
lemma continuous_rotMap (M : ℕ) (a : Fin r → ℤ) : Continuous (rotMap (E := E) M a) := by
  unfold rotMap
  fun_prop

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma powMap_rotMap {M : ℕ} (hM : M ≠ 0) (a : Fin r → ℤ) (x : E × (Fin r → ℂ)) :
    powMap M (rotMap M a x) = powMap M x := by
  refine Prod.ext rfl (funext fun i ↦ ?_)
  simp only [powMap, rotMap, mul_pow, ← Complex.exp_nat_mul]
  rw [show (M : ℂ) * (2 * Real.pi * Complex.I * a i / M) = a i * (2 * Real.pi * Complex.I) by
    field_simp, Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- The divisor `u₁ ⋯ uᵣ = 0` has empty interior in any subset of `E × ℂʳ`. -/
lemma interior_inter_preimage_prod_eq_empty (U : Set (E × (Fin r → ℂ))) :
    interior (U ∩ prodCoord ⁻¹' {0}) = ∅ := by
  have hi (i : Fin r) : interior (univ ∩ (fun x : E × (Fin r → ℂ) ↦ x.2 i) ⁻¹' {0}) = ∅ :=
    AnalyticOnNhd.interior_inter_preimage_zero_eq_empty
      (fun x _ ↦ ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r ↦ ℂ) i).comp
        (ContinuousLinearMap.snd ℂ E (Fin r → ℂ))).analyticAt x) isPreconnected_univ
      (z := (0, fun _ ↦ 1)) trivial one_ne_zero
  have h := interior_inter_preimage_zero_prod_eq_empty (U := univ) Finset.univ
    (g := fun i (x : E × (Fin r → ℂ)) ↦ x.2 i) (fun i _ ↦ by fun_prop) (fun i _ ↦ hi i)
  exact subset_empty_iff.1 (h ▸ interior_mono (inter_subset_inter_left _ (subset_univ U)))

variable [FiniteDimensional ℂ E]

/-- **Riemann extension on a Kummer covering along a normal crossings divisor.** A holomorphic
function on `κ⁻¹(V) \ {u₁ ⋯ uᵣ = 0}` which is bounded near every point of `κ⁻¹(V)` extends
holomorphically to `κ⁻¹(V)`. -/
theorem exists_differentiableOn_powMap_eqOn (M : ℕ) {V : Set (E × (Fin r → ℂ))} (hV : IsOpen V)
    {f : E × (Fin r → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (powMap M ⁻¹' V \ prodCoord ⁻¹' {0}))
    (hbdd : ∀ x ∈ powMap M ⁻¹' V,
      IsBoundedUnder (· ≤ ·) (𝓝[powMap M ⁻¹' V \ prodCoord ⁻¹' {0}] x) (‖f ·‖)) :
    ∃ F : E × (Fin r → ℂ) → ℂ, DifferentiableOn ℂ F (powMap M ⁻¹' V) ∧
      EqOn F f (powMap M ⁻¹' V \ prodCoord ⁻¹' {0}) :=
  exists_differentiableOn_eqOn_of_isBoundedUnder
    (hV.preimage (differentiable_powMap M).continuous) differentiable_prodCoord.differentiableOn
    (interior_inter_preimage_prod_eq_empty _) hf hbdd

omit [FiniteDimensional ℂ E] in
/-- **Invariance of the extension**: if `F` is continuous on `κ⁻¹(V)` and invariant under a
multiplication of the coordinates by roots of unity off `u₁ ⋯ uᵣ = 0`, then it is invariant on
`κ⁻¹(V)`. -/
theorem eqOn_comp_rotMap {M : ℕ} (hM : M ≠ 0) (a : Fin r → ℤ) {V : Set (E × (Fin r → ℂ))}
    (hV : IsOpen V) {F : E × (Fin r → ℂ) → ℂ} (hF : ContinuousOn F (powMap M ⁻¹' V))
    (h : EqOn (F ∘ rotMap M a) F (powMap M ⁻¹' V \ prodCoord ⁻¹' {0})) :
    EqOn (F ∘ rotMap M a) F (powMap M ⁻¹' V) :=
  EqOn.of_eqOn_diff_zero (hV.preimage (differentiable_powMap M).continuous)
    (interior_inter_preimage_prod_eq_empty _)
    (hF.comp (continuous_rotMap M a).continuousOn fun x hx ↦ by
      rw [mem_preimage, powMap_rotMap hM]
      exact hx) hF h

end KummerPi
