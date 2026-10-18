/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.P1.BelyiMapBaseChange
import Tengoku.Seed.RingTheory.MvPolynomial.Ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Marked-point matching for the base-change map of the projective line

This file supplies the reverse (fibre-singleton) direction of marked-point transport for the
base-change morphism `Belyi.P1.mapOfAlgebra k₀ K : ℙ¹_K ⟶ ℙ¹_{k₀}` (taxis issue #164, the
last input of the field-extension specialisation of **B2b**, parent #47).

The forward direction (`Belyi.P1.mapOfAlgebra_base_{zero,one,infty}`, issue #110) shows a
marked point maps to the corresponding marked point.  Here we prove the *reverse*: the fibre
of `mapOfAlgebra` over a `k₀`-rational marked point is exactly the corresponding `K`-point:

* `Belyi.P1.mapOfAlgebra_base_eq_zero`, `_one`, `_infty`.

The geometric content is a homogeneous-prime computation.  Writing `J` for the homogeneous
prime of `K[X₀, X₁]` cutting out `y : ℙ¹_K`, the hypothesis `(mapOfAlgebra k₀ K).base y = 0`
unfolds to `J.comap (map (algebraMap k₀ K)) = span {X₀}`, whence `X₀ ∈ J`, and the key
algebra lemma

* `Belyi.P1.eq_span_of_forall_dvd`: a homogeneous prime `J`, not containing the irrelevant
  ideal, that contains a linear form `ℓ` and is *divisible* by `ℓ` on each homogeneous
  component, equals `span {ℓ}`,

gives `J = span {X₀}`, i.e. `y = 0`.  The three marked points use the linear forms
`X₀`, `X₀ - X₁`, `X₁`; the `X₀ - X₁` case is reduced to `X₀` by the `shear` automorphism of
`Belyi/P1/PointsBaseChange.lean`.

Packaging:

* `Belyi.P1.mapsTo_markedPoints`: the marked-point matching hypothesis of
  `Belyi.isBelyiMap_baseChange_of_mapsTo`.
* `Belyi.isBelyiMap_baseChange`: the **unconditional** field-extension specialisation of B2b —
  the base change of a Belyi map along `k₀ ⊆ K` is a Belyi map.

This is the input the forward direction of Belyi's theorem (B8, #51) and the marked-curve API
(#54) consume.
-/

universe u

namespace MvPolynomial

variable {R : Type*} [CommRing R]

/-- Over `Fin 2`, the total degree of a monomial index is the sum of its two coordinates,
read off along any splitting `i ≠ j` of the index set. -/
lemma finTwo_degree_eq_add (e : Fin 2 →₀ ℕ) (i j : Fin 2) (hij : i ≠ j) :
    e.degree = e i + e j := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals omega

end MvPolynomial

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory Limits MvPolynomial ProjectiveSpectrum

attribute [local instance] MvPolynomial.gradedAlgebra

section Field

variable {K : Type u} [Field K]

/-- **Divisibility skeleton.** For a homogeneous polynomial `h` of degree `n` in `K[X₀, X₁]`
and two distinct variables `X i`, `X j`, the variable `X i` divides `h` after subtracting the
single monomial `X j ^ n` carrying its `X j ^ n`-coefficient: every monomial of the remainder
that is not divisible by `X i` must be `X j ^ n`, and there it cancels. -/
lemma X_dvd_sub {n : ℕ} {h : MvPolynomial (Fin 2) K} (hh : h.IsHomogeneous n)
    (i j : Fin 2) (hij : i ≠ j) :
    (X i : MvPolynomial (Fin 2) K) ∣ (h - C (h.coeff (Finsupp.single j n)) * X j ^ n) := by
  rw [show (X i : MvPolynomial (Fin 2) K) = monomial (Finsupp.single i 1) 1 by simp only [X],
    monomial_one_dvd_iff_forall_coeff]
  intro e he
  rw [Finsupp.single_le_iff] at he
  have hei : e i = 0 := by omega
  rw [coeff_sub, coeff_C_mul, coeff_X_pow]
  by_cases hcase : e = Finsupp.single j n
  · subst hcase; simp
  · have hdeg : e.degree ≠ n := by
      rw [finTwo_degree_eq_add e i j hij, hei, zero_add]
      intro hej
      apply hcase
      ext x
      rcases eq_or_ne x j with rfl | hxj
      · rw [Finsupp.single_eq_same, hej]
      · have hxi : x = i := by fin_cases i <;> fin_cases j <;> fin_cases x <;> simp_all
        rw [Finsupp.single_apply, ite_eq_right (fun hjx => hxj hjx.symm), hxi]
        exact hei
    rw [hh.coeff_eq_zero hdeg, ite_eq_right (fun h' => hcase h'.symm)]
    ring

end Field

section Ideal

variable {K : Type u} [Field K]

/-- A positive-degree homogeneous polynomial in `K[X₀, X₁]` lies in the ideal `(X₀, X₁)`:
each of its monomials has a nonzero exponent, hence is divisible by some variable. -/
lemma mem_span_X01 {i : ℕ} (hi : 0 < i) {x : MvPolynomial (Fin 2) K}
    (hx : x ∈ P1Grading K i) :
    x ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) K), X 1} := by
  have hxh : x.IsHomogeneous i := (mem_homogeneousSubmodule _ _).mp hx
  rw [show ({X 0, X 1} : Set (MvPolynomial (Fin 2) K)) = X '' {0, 1} from
      (Set.image_pair X 0 1).symm, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hmd : m.degree = i := by
    by_contra hne; exact (mem_support_iff.mp hm) (hxh.coeff_eq_zero hne)
  have hmne : m ≠ 0 := by
    rintro rfl; rw [map_zero] at hmd; omega
  obtain ⟨t, ht⟩ := Finsupp.ne_iff.mp hmne
  exact ⟨t, by fin_cases t <;> simp, by simpa using ht⟩

/-- Two variables cannot both lie in a relevant homogeneous prime: together they generate the
irrelevant ideal, contradicting `not_irrelevant_le`. -/
lemma X01_not_both_mem (y : P1 K)
    (h0 : (X 0 : MvPolynomial (Fin 2) K) ∈ y.asHomogeneousIdeal.toIdeal)
    (h1 : (X 1 : MvPolynomial (Fin 2) K) ∈ y.asHomogeneousIdeal.toIdeal) : False := by
  refine y.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le (𝒜 := P1Grading K)).mpr
    fun n hn z hz => ?_)
  have hsub : Ideal.span {(X 0 : MvPolynomial (Fin 2) K), X 1} ≤ y.asHomogeneousIdeal.toIdeal :=
    Ideal.span_le.mpr (by rintro w (rfl | rfl) <;> assumption)
  exact HomogeneousIdeal.mem_iff.mp (hsub (mem_span_X01 hn hz))

/-- **Key algebra lemma.** A homogeneous prime `J ⊆ K[X₀, X₁]` containing the variable `X i`
but not `X j` (`i ≠ j`) is divisible by `X i` on every homogeneous element: from
`X_dvd_sub`, the leftover monomial `c · X j ^ n` lies in `J`, and primeness with `X j ∉ J`
forces `c = 0`. -/
lemma dvd_of_isHomog_mem {J : Ideal (MvPolynomial (Fin 2) K)} (hp : J.IsPrime)
    (i j : Fin 2) (hij : i ≠ j) (hXi : (X i : MvPolynomial (Fin 2) K) ∈ J)
    (hXj : (X j : MvPolynomial (Fin 2) K) ∉ J)
    {n : ℕ} {h : MvPolynomial (Fin 2) K} (hh : h.IsHomogeneous n) (hhJ : h ∈ J) :
    (X i : MvPolynomial (Fin 2) K) ∣ h := by
  set c := h.coeff (Finsupp.single j n) with hc
  obtain ⟨g, hg⟩ := X_dvd_sub hh i j hij
  rw [← hc] at hg
  have hmem : C c * X j ^ n ∈ J := by
    have hrw : C c * X j ^ n = h - X i * g := by rw [← hg]; ring
    rw [hrw]; exact J.sub_mem hhJ (J.mul_mem_right g hXi)
  have hc0 : c = 0 := by
    by_contra hcne
    have hunit : IsUnit (C c : MvPolynomial (Fin 2) K) :=
      (isUnit_iff_ne_zero.mpr hcne).map (C : K →+* MvPolynomial (Fin 2) K)
    rcases hp.mem_or_mem hmem with hCc | hXpow
    · exact hp.ne_top (Ideal.eq_top_of_isUnit_mem J hCc hunit)
    · exact hXj (hp.mem_of_pow_mem n hXpow)
  rw [hc0, map_zero, zero_mul, sub_zero] at hg
  exact ⟨g, hg⟩

/-- **Wrapper.** A homogeneous ideal `J` containing a degree-one form `ℓ` and divisible by `ℓ`
on every homogeneous component equals `span {ℓ}`: `⊇` is `ℓ ∈ J`, and `⊆` decomposes each
element into homogeneous components, each divisible by `ℓ`. -/
lemma eq_span_of_forall_dvd {ℓ : MvPolynomial (Fin 2) K} {J : Ideal (MvPolynomial (Fin 2) K)}
    (hhom : J.IsHomogeneous (P1Grading K)) (hℓ1 : ℓ.IsHomogeneous 1) (hℓJ : ℓ ∈ J)
    (hdvd : ∀ (n : ℕ) (h : MvPolynomial (Fin 2) K), h.IsHomogeneous n → h ∈ J → ℓ ∣ h) :
    J = Ideal.span {ℓ} := by
  have hspanhom : (Ideal.span {ℓ}).IsHomogeneous (P1Grading K) :=
    Ideal.homogeneous_span _ _ (by
      rintro x rfl; exact ⟨1, (mem_homogeneousSubmodule _ _).mpr hℓ1⟩)
  refine le_antisymm (fun f hf => ?_)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hℓJ))
  rw [MvPolynomial.mem_iff_homogeneousComponent_mem hspanhom]
  intro n
  exact Ideal.mem_span_singleton.mpr
    (hdvd n _ (homogeneousComponent_isHomogeneous n f)
      (MvPolynomial.homogeneousComponent_mem_of_mem hhom hf n))

end Ideal

section Reverse

variable (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K]

end Reverse

end Belyi.P1

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

variable (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K]

end Belyi
