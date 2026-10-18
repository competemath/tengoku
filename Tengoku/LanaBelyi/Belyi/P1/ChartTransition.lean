/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.P1.AffineChart0
import Tengoku.LanaBelyi.Belyi.P1.AffineChartBaseChange
import Tengoku.LanaBelyi.Belyi.P1.Transcendental
import Tengoku.Seed.Algebra.MvPolynomial.Division

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The chart-transition lemma for the valued points of `ℙ¹`

For `u v : R` with `u * v = 1`, the `R`-valued point of `ℙ¹` with affine coordinate `u`
in the chart `D₊(X₁)` (`Belyi.P1.point k u`) equals the `R`-valued point with affine
coordinate `v` in the chart `D₊(X₀)` (`Belyi.P1.point₀ k v`): both name the point
`[u : 1] = [1 : v]` of `ℙ¹`.

This is the reusable crux behind gluing the two chart maps of the polynomial self-map
of `ℙ¹` (taxis issue #106, statement **B4**): on the overlap `D₊(X₁·G)` of the source
cover `{D₊(X₁), D₊(G)}` the two target-chart coordinates `g(x) = G/X₁ᵈ` and `X₁ᵈ/G` are
mutually inverse, so the two chart maps agree there.

## Method

Both `point k u` and `point₀ k v` factor through the overlap chart `awayι (X₀·X₁)`:

* `point k u = Spec.map ρ ≫ awayι (X₀·X₁)` where `ρ` is the evaluation of the double-chart
  ring `(k[X₀,X₁]_{X₀X₁})₀` at `u` (`X₀·X₁ ↦ u`, a unit since `u·v = 1`);
* `point₀ k v = Spec.map ρ ≫ awayι (X₀·X₁)` for the *same* `ρ`.

The two factorizations follow from `HomogeneousLocalization.awayMap_mk` and
`AlgebraicGeometry.Proj.SpecMap_awayMap_awayι`, reducing to the ring-hom identities
`ρ ∘ (Away X₁ → Away X₀X₁) = awayEval k u` and `ρ ∘ (Away X₀ → Away X₀X₁) = awayEval₀ k v`.
The second uses the homogeneous-scaling identity `aeval (c • g) a = c ^ n · aeval g a`
(`aeval_smul_of_isHomogeneous`), since on degree-`n` fractions the two evaluations at
`![u,1]` and `![1,v] = v • ![u,1]` differ exactly by `v ^ n`.

## Main results

* `Belyi.P1.aeval_smul_of_isHomogeneous`: homogeneous polynomials scale under `aeval`.
* `Belyi.P1.point_eq_point₀`: the chart-transition lemma.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [CommRing k]
variable {R : Type u} [CommRing R] [Algebra k R]

/-- **Homogeneous scaling under evaluation.** A homogeneous polynomial of degree `n`
evaluated at a rescaled point `c • g` picks up a factor `c ^ n`. -/
theorem aeval_smul_of_isHomogeneous {n : ℕ} {a : MvPolynomial (Fin 2) k}
    (ha : a.IsHomogeneous n) (c : R) (g : Fin 2 → R) :
    aeval (c • g) a = c ^ n * aeval g a := by
  conv_lhs => rw [a.as_sum]
  conv_rhs => rw [a.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]; exact ha (mem_support_iff.mp hd)
  rw [aeval_monomial, aeval_monomial, show (c • g) = (fun i => c * g i) from rfl]
  have hprod : (d.prod fun i e => (c * g i) ^ e)
      = c ^ (d.degree) * d.prod fun i e => g i ^ e := by
    rw [Finsupp.prod, Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _
  rw [hprod, hdeg]
  ring

/-- The `k`-algebra evaluation of the chart ring `(k[X₀,X₁]_{X₀})₀` on a homogeneous
fraction `a / (X₀)^n` returns `aeval ![1, s] a`: the denominator `X₀` evaluates to `1`. -/
lemma awayEval₀_mk (s : R) (n : ℕ) (a : MvPolynomial (Fin 2) k)
    (ha : a ∈ P1Grading k (n • 1)) :
    awayEval₀ k s (Away.mk (P1Grading k) (X_mem_P1Grading k 0) n a ha) = aeval ![1, s] a := by
  simp only [awayEval₀, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.awayLift_mk (v := 1) (hv := by simp)]
  simp

section Crux

variable (k)

/-- The `aeval ![u, 1]` evaluation as a ring hom, abbreviated for readability. -/
private noncomputable abbrev evalU (u : R) : MvPolynomial (Fin 2) k →+* R :=
  (aeval ![u, 1] : MvPolynomial (Fin 2) k →ₐ[k] R)

/-- Evaluation of the overlap-chart ring `(k[X₀,X₁]_{X₀X₁})₀` at `u`, sending `X₀·X₁ ↦ u`.
When `u` is a unit this factors through the localization at `X₀·X₁`. -/
noncomputable def awayEvalD (u : R) (hu : IsUnit (evalU k u (X 0 * X 1))) :
    Away (P1Grading k) (X 0 * X 1 : MvPolynomial (Fin 2) k) →+* R :=
  (Localization.awayLift (evalU k u) (X 0 * X 1) hu).comp
    (algebraMap (Away (P1Grading k) (X 0 * X 1))
      (Localization.Away (X 0 * X 1 : MvPolynomial (Fin 2) k)))

lemma awayEvalD_mk (u v : R) (huv : u * v = 1) (hu : IsUnit (evalU k u (X 0 * X 1)))
    (n d : ℕ) (a : MvPolynomial (Fin 2) k)
    (hmem : (X 0 * X 1 : MvPolynomial (Fin 2) k) ∈ P1Grading k d)
    (ha : a ∈ P1Grading k (n • d)) :
    awayEvalD k u hu (Away.mk (P1Grading k) hmem n a ha) = aeval ![u, 1] a * v ^ n := by
  simp only [awayEvalD, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.awayLift_mk (v := v) (hv := by simp [map_mul, huv])]
  simp

end Crux

end Belyi.P1
