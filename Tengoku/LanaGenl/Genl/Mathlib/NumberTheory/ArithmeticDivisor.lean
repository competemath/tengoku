/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
import Tengoku.Seed.NumberTheory.NumberField.Completion.FinitePlace
import Tengoku.Seed.NumberTheory.NumberField.InfinitePlace.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Arithmetic divisors on number fields

Following §1 of [mochizuki2010] (cf. also [szpiro1985], §1.1), an *arithmetic divisor* on
a number field `K` is a finite formal sum `∑ c_v ⬝ v` over the valuations `v` of `K`,
where `c_v ∈ ℤ` for the nonarchimedean valuations and `c_v ∈ ℝ` for the archimedean ones.
Arithmetic divisors form a group `ADiv(K)`, realised here as
`NumberField.ArithmeticDivisor K`, built from `NumberField.FinitePlace` and
`NumberField.InfinitePlace`.

The *degree* map `deg : ADiv(K) → ℝ` sends a nonarchimedean valuation `v` to `log q_v`,
where `q_v` is the cardinality of the residue field at `v`, and an archimedean valuation
to `1`. Its normalisation `deg / [K : ℚ]` is invariant under base change to finite
extensions and computes heights of points via pull back of arithmetic line bundles.

## Main definitions

- `NumberField.ArithmeticDivisor K`: the group of arithmetic divisors on `K`.
- `NumberField.ArithmeticDivisor.Effective`: effectivity, i.e. all coefficients are
  nonnegative.
- `NumberField.FinitePlace.logResidueCard`: the local degree `log q_v` of a finite place.
- `NumberField.ArithmeticDivisor.degree`: the degree homomorphism `ADiv(K) →+ ℝ`.
- `NumberField.ArithmeticDivisor.normalizedDegree`: the degree divided by `[K : ℚ]`.

## TODO

- Define the principal arithmetic divisor `ADiv(f)` of `f ∈ K×` and deduce
  `degree (ADiv f) = 0` from the product formula `NumberField.prod_abs_eq_one`.
- Define `APic(Spec 𝓞_K)` as the quotient of `ADiv(K)` by principal divisors and relate
  it to arithmetic line bundles.
- Prove the invariance of `normalizedDegree` under finite extensions `L/K`.

## References

- [mochizuki2010] S. Mochizuki, *Arithmetic elliptic curves in general position*,
  Math. J. Okayama Univ. **52** (2010), 1–28.
- [szpiro1985] L. Szpiro, *Degrés, intersections, hauteurs*,
  Astérisque **127** (1985), 11–28.
-/

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- An arithmetic divisor on a number field `K` is a finite formal sum `∑ c_v ⬝ v` over
the valuations of `K`, with `c_v ∈ ℤ` at the nonarchimedean valuations and `c_v ∈ ℝ` at
the archimedean ones (§1 of [mochizuki2010]). -/
def ArithmeticDivisor : Type _ :=
  (FinitePlace K →₀ ℤ) × (InfinitePlace K → ℝ)

namespace ArithmeticDivisor

noncomputable instance : AddCommGroup (ArithmeticDivisor K) :=
  inferInstanceAs (AddCommGroup ((FinitePlace K →₀ ℤ) × (InfinitePlace K → ℝ)))

noncomputable instance : Inhabited (ArithmeticDivisor K) := ⟨0⟩

variable {K}

/-- The coefficient of an arithmetic divisor at a finite place. -/
def finCoeff (D : ArithmeticDivisor K) : FinitePlace K →₀ ℤ := D.1

/-- The coefficient of an arithmetic divisor at an infinite place. -/
def infCoeff (D : ArithmeticDivisor K) : InfinitePlace K → ℝ := D.2

@[simp] lemma finCoeff_zero : finCoeff (0 : ArithmeticDivisor K) = 0 := rfl

@[simp] lemma infCoeff_zero : infCoeff (0 : ArithmeticDivisor K) = 0 := rfl

@[simp] lemma finCoeff_add (D E : ArithmeticDivisor K) :
    finCoeff (D + E) = finCoeff D + finCoeff E := rfl

@[simp] lemma infCoeff_add (D E : ArithmeticDivisor K) :
    infCoeff (D + E) = infCoeff D + infCoeff E := rfl

@[simp] lemma finCoeff_neg (D : ArithmeticDivisor K) : finCoeff (-D) = -finCoeff D := rfl

@[simp] lemma infCoeff_neg (D : ArithmeticDivisor K) : infCoeff (-D) = -infCoeff D := rfl

/-- An arithmetic divisor is *effective* if all of its coefficients are nonnegative. -/
def Effective (D : ArithmeticDivisor K) : Prop :=
  (∀ v, 0 ≤ D.finCoeff v) ∧ (∀ v, 0 ≤ D.infCoeff v)

theorem Effective.zero : (0 : ArithmeticDivisor K).Effective :=
  ⟨fun _ ↦ le_rfl, fun _ ↦ le_rfl⟩

theorem Effective.add {D E : ArithmeticDivisor K} (hD : D.Effective) (hE : E.Effective) :
    (D + E).Effective :=
  ⟨fun v ↦ by simpa using add_nonneg (hD.1 v) (hE.1 v),
    fun v ↦ by simpa using add_nonneg (hD.2 v) (hE.2 v)⟩

end ArithmeticDivisor

namespace FinitePlace

variable {K}

/-- The local degree `log q_v` of a finite place `v`, where `q_v` is the cardinality of
the residue field at `v`. This is the degree of the arithmetic divisor `1 ⬝ v`. -/
noncomputable def logResidueCard (v : FinitePlace K) : ℝ :=
  Real.log (Ideal.absNorm v.maximalIdeal.asIdeal)

lemma logResidueCard_pos (v : FinitePlace K) : 0 < v.logResidueCard := by
  have h := HeightOneSpectrum.one_lt_absNorm v.maximalIdeal
  exact Real.log_pos (by exact_mod_cast h)

lemma logResidueCard_nonneg (v : FinitePlace K) : 0 ≤ v.logResidueCard :=
  v.logResidueCard_pos.le

end FinitePlace

namespace ArithmeticDivisor

variable {K}

open Finset in
/-- The degree of an arithmetic divisor `∑ c_v ⬝ v`, obtained by sending a nonarchimedean
valuation `v` to `log q_v` and an archimedean valuation to `1`
(§1 of [mochizuki2010]). -/
noncomputable def degree : ArithmeticDivisor K →+ ℝ where
  toFun D := (D.finCoeff.sum fun v n ↦ n * v.logResidueCard) + ∑ v, D.infCoeff v
  map_zero' := by simp
  map_add' D E := by
    rw [finCoeff_add, infCoeff_add,
      Finsupp.sum_add_index' (by simp) (fun v m n ↦ by push_cast; ring)]
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    ring

lemma degree_apply (D : ArithmeticDivisor K) :
    degree D = (D.finCoeff.sum fun v n ↦ n * v.logResidueCard) + ∑ v, D.infCoeff v :=
  rfl

theorem Effective.degree_nonneg {D : ArithmeticDivisor K} (hD : D.Effective) :
    0 ≤ degree D := by
  rw [degree_apply]
  refine add_nonneg (Finsupp.sum_nonneg fun v _ ↦ ?_) (Finset.sum_nonneg fun v _ ↦ hD.2 v)
  exact mul_nonneg (by exact_mod_cast hD.1 v) v.logResidueCard_nonneg

variable (K)

/-- The normalised degree `deg / [K : ℚ]` of arithmetic divisors. In contrast to `degree`
it is invariant under base change to finite extensions of `K`. -/
noncomputable def normalizedDegree (D : ArithmeticDivisor K) : ℝ :=
  degree D / Module.finrank ℚ K

end ArithmeticDivisor

end NumberField
