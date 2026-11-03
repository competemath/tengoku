/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Finsupp.LaurentExponent
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Module.GradedModule.Shift
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.MvPolynomial.Grading

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Laurent exponents of monomial fractions

A degree-zero fraction away from a monomial `Xᵞ` has, by `DegreeZeroLocalization.exists_awayMk`,
the normal form `p / (Xᵞ)ᵐ`. When the numerator is itself a monomial `Xᵝ`, the fraction is
determined by a single Laurent exponent

```
laurentExponent γ m β = β - m • γ  :  ι →₀ ℤ
```

with negative entries allowed exactly on the variables `Xᵞ` inverts. This file constructs that
exponent and proves the three facts that make it an index: it determines the fraction, its
`Finsupp.degree` is the twist `d`, and it is nonnegative off the support of `γ`.

## Main definitions

* `natToIntExponent` — an exponent vector read in `ℤ`;
* `laurentExponent` — the Laurent exponent `β - m • γ` of the fraction `Xᵝ / (Xᵞ)ᵐ`.

## Main statements

* `awayMk_monomial_eq_iff_laurentExponent` — **two monomial fractions over powers of `Xᵞ` are
  equal exactly when their Laurent exponents agree.** This is what makes the exponent an index
  rather than a convenience.
* `degree_laurentExponent` — the exponent has total degree `d`, the twist, with no dependence on
  `m`. Raising the denominator moves `β` and `m • γ` together, so this is the invariant that
  survives.
* `laurentExponent_nonneg_of_apply_eq_zero` — off the support of `γ` the exponent is
  nonnegative. Together with the previous statement this is the index set
  `{α | Finsupp.degree α = d ∧ ∀ j ∉ γ.support, 0 ≤ α j}` that #491's basis is indexed by.
* `exists_sum_awayMk_monomial` — **the monomial fractions span.** Every degree-zero fraction away
  from `Xᵞ` is a finite sum of monomial fractions over one common denominator, and
  `laurentExponent_mem_index` says the exponents they contribute are exactly the admissible ones.

## Implementation notes

The equality criterion descends from `DegreeZeroLocalization.awayMk_eq_awayMk_iff`, which is
where the domain hypothesis is spent, to `MvPolynomial.monomial_eq_monomial_iff`. Only the
`IsDomain R` instance is needed: `Module.IsTorsionFree R R` is already an instance, so the
polynomial case supplies nothing by hand.

`laurentExponent` is stated with `m` and `β` separate rather than packaged, because the caller
that matters — a Čech cochain — produces them separately from `exists_awayMk` and never has the
pair in hand.

## Tags

Laurent monomial, homogeneous localization, projective space
-/

open DirectSum Finsupp GradedModule SetLike

namespace MvPolynomial

universe u

variable {ι : Type u}

/-! ## Monomials as homogeneous denominators and numerators -/

variable {R : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `Xᵞ` is homogeneous of degree `γ.degree`, which is the certificate `awayMk` consumes.
@isnad1 id=mem.0h3v.s8.31c7f543b4f8 from=translated src=- shape=dd915953 vocab=f91b70ce
-/
theorem monomial_one_mem_polynomialGrading (γ : ι →₀ ℕ) :
    (MvPolynomial.monomial γ (1 : R)) ∈ polynomialGrading ι R γ.degree :=
  MvPolynomial.isHomogeneous_monomial 1 rfl

/--
@isnad1 id=eq.0h4v.s8.a436ccdcb825 from=translated src=- shape=2afb12e6 vocab=1ff174ce
-/
theorem monomial_one_pow (γ : ι →₀ ℕ) (m : ℕ) :
    (MvPolynomial.monomial γ (1 : R)) ^ m = MvPolynomial.monomial (m • γ) 1 := by
  rw [MvPolynomial.monomial_pow, one_pow]

/--
@isnad1 id=ne.0h3v.s8.d3ab85d6a625 from=translated src=- shape=dac004ad vocab=2221e885
-/
theorem monomial_one_ne_zero [Nontrivial R] (γ : ι →₀ ℕ) :
    (MvPolynomial.monomial γ (1 : R)) ≠ 0 := by
  simp

/-- A monomial of the right total degree is a legitimate numerator over `(Xᵞ)ᵐ` for the twist
`d`.
@isnad1 id=mem.1h6v.s9.18d5c9743b2a from=translated src=- shape=3bf80443 vocab=a597dd74
-/
theorem monomial_mem_natShift (γ β : ι →₀ ℕ) (d m : ℕ)
    (hβ : β.degree = m • γ.degree + d) :
    (MvPolynomial.monomial β (1 : R)) ∈
      natShift (polynomialGrading ι R) d (m • γ.degree) :=
  MvPolynomial.isHomogeneous_monomial 1 hβ

/-! ## The equality criterion -/

set_option maxHeartbeats 800000 in
/-- Two monomial fractions over powers of `Xᵞ` are equal exactly when they cross-multiply to the
same monomial. This is `awayMk_eq_awayMk_iff` followed by `monomial_eq_monomial_iff`; the
coefficient side of the latter is discharged by `1 ≠ 0`.
@isnad1 id=iff.2h9v.s13.b9e8e8a9e325 from=translated src=- shape=abed595b vocab=c2989b74
-/
theorem awayMk_monomial_eq_iff [IsDomain R] {σM : Type u} [SetLike σM (MvPolynomial ι R)]
    [AddSubgroupClass σM (MvPolynomial ι R)] {𝓜 : ℕ → σM}
    [SetLike.GradedSMul (polynomialGrading ι R) 𝓜] (γ : ι →₀ ℕ) {m m' : ℕ} {β β' : ι →₀ ℕ}
    (hβ : (MvPolynomial.monomial β (1 : R)) ∈ 𝓜 (m • γ.degree))
    (hβ' : (MvPolynomial.monomial β' (1 : R)) ∈ 𝓜 (m' • γ.degree)) :
    DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ) m (MvPolynomial.monomial β 1) hβ =
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ) m' (MvPolynomial.monomial β' 1) hβ' ↔
      m' • γ + β = m • γ + β' := by
  rw [DegreeZeroLocalization.awayMk_eq_awayMk_iff _ (monomial_one_ne_zero (R := R) γ),
    smul_eq_mul, smul_eq_mul, monomial_one_pow, monomial_one_pow,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial, one_mul,
    MvPolynomial.monomial_eq_monomial_iff]
  simp

set_option maxHeartbeats 800000 in
/-- **The Laurent exponent is a complete invariant of a monomial fraction.**

This is the statement #491's basis is built on: the assignment `(m, β) ↦ β - m • γ` separates
distinct fractions and identifies the ones that only differ by a common denominator. Combined
with `degree_laurentExponent` and `laurentExponent_nonneg_of_apply_eq_zero`, it says the monomial
fractions of the twist `d` are indexed by
`{α : ι →₀ ℤ | α.degree = d ∧ ∀ j, γ j = 0 → 0 ≤ α j}`.
@isnad1 id=iff.2h9v.s13.08661908cbc5 from=translated src=- shape=641e7249 vocab=e3b27dc3
-/
theorem awayMk_monomial_eq_iff_laurentExponent [IsDomain R] {σM : Type u}
    [SetLike σM (MvPolynomial ι R)] [AddSubgroupClass σM (MvPolynomial ι R)] {𝓜 : ℕ → σM}
    [SetLike.GradedSMul (polynomialGrading ι R) 𝓜] (γ : ι →₀ ℕ) {m m' : ℕ} {β β' : ι →₀ ℕ}
    (hβ : (MvPolynomial.monomial β (1 : R)) ∈ 𝓜 (m • γ.degree))
    (hβ' : (MvPolynomial.monomial β' (1 : R)) ∈ 𝓜 (m' • γ.degree)) :
    DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ) m (MvPolynomial.monomial β 1) hβ =
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ) m' (MvPolynomial.monomial β' 1) hβ' ↔
      laurentExponent γ m β = laurentExponent γ m' β' :=
  (awayMk_monomial_eq_iff γ hβ hβ').trans (laurentExponent_eq_iff γ m m' β β').symm

/-! ## Spanning

`awayMk_monomial_eq_iff_laurentExponent` says the monomial fractions are indexed by their Laurent
exponents. This section says they exhaust the localization: every degree-zero fraction away from
`Xᵞ` is a *finite* sum of monomial fractions **over one common denominator**.

The route is short because both halves are already available. `exists_awayMk` puts an arbitrary
element in the form `p / (Xᵞ)ᵐ`, `MvPolynomial.as_sum` splits the numerator, and `awayMk_sum`
distributes the fraction over that splitting. No denominators have to be aligned afterwards:
splitting a numerator never touches `m`. -/

/-- `(Xᵞ)ⁿ` is never zero, which is the hypothesis `exists_awayMk` consumes.
@isnad1 id=ne.0h4v.s8.3c0b14d0a2b2 from=translated src=- shape=3e196095 vocab=5eefb408
-/
theorem monomial_one_pow_ne_zero [Nontrivial R] (γ : ι →₀ ℕ) (n : ℕ) :
    (MvPolynomial.monomial γ (1 : R)) ^ n ≠ 0 := by
  rw [monomial_one_pow]; simp

/-! ## Twists of either sign, abstractly

The Laurent argument reads a numerator in exactly one way: an element of `𝓜 n` is a homogeneous
polynomial whose degree exceeds `n` by the twist. `IsPolynomialTwist` isolates that reading, so
that the whole stack above it can be stated once and instantiated at `natShift` for `d : ℕ` and at
`intShift` for `d : ℤ`. Nothing else about the graded module is used, and in particular no step
below needs the twist to be nonnegative.

The `p = 0` disjunct is what makes `intShift` fit: it carries zero in every degree, including the
degrees where `n + d` is negative and there is no graded piece to name. For `natShift` the
disjunct is redundant — zero lies in every homogeneous piece anyway — so the two instances have
the same content. -/

/-- `𝓜` presents the degree-`d` twist of the polynomial grading: membership in `𝓜 n` is
homogeneity in degree `n + d`, read in `ℤ` so that either sign of `d` is expressible.-/
def IsPolynomialTwist {σM : Type u} [SetLike σM (MvPolynomial ι R)]
    (𝓜 : ℕ → σM) (d : ℤ) : Prop :=
  ∀ (n : ℕ) (p : MvPolynomial ι R),
    p ∈ 𝓜 n ↔ p = 0 ∨ ∃ e : ℕ, (e : ℤ) = (n : ℤ) + d ∧ p ∈ polynomialGrading ι R e

/-- A nonnegative twist is a twist: `natShift 𝒜 d n` is literally `𝒜 (n + d)`.
@isnad1 id=ispolyno.0h3v.s7.071998003731 from=translated src=- shape=875c1183 vocab=53d69650
-/
theorem isPolynomialTwist_natShift (d : ℕ) :
    IsPolynomialTwist (natShift (polynomialGrading ι R) d) (d : ℤ) := by
  intro n p
  constructor
  · exact fun hp => Or.inr ⟨n + d, by push_cast; ring, hp⟩
  · rintro (rfl | ⟨e, he, hp⟩)
    · exact zero_mem _
    · obtain rfl : e = n + d := by exact_mod_cast he
      exact hp

/-- An integer twist is a twist, by definition of `intShiftPiece`.
@isnad1 id=ispolyno.0h3v.s7.d213502d3fbe from=translated src=- shape=5659da13 vocab=122e1112
-/
theorem isPolynomialTwist_intShift (d : ℤ) :
    IsPolynomialTwist (intShift (polynomialGrading ι R) d) d := fun _ _ => Iff.rfl

namespace IsPolynomialTwist

variable {σM : Type u} [SetLike σM (MvPolynomial ι R)] {𝓜 : ℕ → σM} {d : ℤ}

/-- Every exponent occurring in a numerator over `(Xᵞ)ᵐ` has total degree `m • γ.degree + d`,
read in `ℤ`. This is homogeneity on the support, for a twist of either sign.
@isnad1 id=eq.3h8v.s7.a39585b0ed19 from=translated src=- shape=10adc8ef vocab=517f220d
-/
theorem degree_eq_of_mem_support (h𝓜 : IsPolynomialTwist 𝓜 d) {n : ℕ}
    {p : MvPolynomial ι R} (hp : p ∈ 𝓜 n) {β : ι →₀ ℕ} (hβ : β ∈ p.support) :
    (β.degree : ℤ) = (n : ℤ) + d := by
  rcases (h𝓜 n p).mp hp with rfl | ⟨e, he, hhom⟩
  · simp at hβ
  · refine he ▸ ?_
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hβ)
      (MvPolynomial.IsHomogeneous.coeff_eq_zero hhom
        (fun hde => hne (by exact_mod_cast congrArg (Nat.cast (R := ℤ)) hde)))

/-- Each monomial of a numerator is itself a numerator, for a twist of either sign.

The statement is for *every* `β`, not only those in the support, because the splitting lemmas
take a total membership hypothesis. Off the support the monomial is zero, which the `p = 0`
disjunct covers.
@isnad1 id=mem.2h8v.s8.c2d269246fa2 from=translated src=- shape=ecabd117 vocab=1ac899ee
-/
theorem monomial_coeff_mem (h𝓜 : IsPolynomialTwist 𝓜 d) {n : ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ 𝓜 n) (β : ι →₀ ℕ) :
    MvPolynomial.monomial β (p.coeff β) ∈ 𝓜 n := by
  by_cases h : p.coeff β = 0
  · rw [h]
    exact (h𝓜 n _).mpr (Or.inl (by simp))
  · have hdeg := h𝓜.degree_eq_of_mem_support hp (MvPolynomial.mem_support_iff.mpr h)
    refine (h𝓜 n _).mpr (Or.inr ⟨β.degree, hdeg, ?_⟩)
    exact MvPolynomial.isHomogeneous_monomial _ rfl

/-- A twist family is closed under the base-ring action: the graded pieces it is built from are
submodules, and the zero disjunct is closed under anything.
@isnad1 id=mem.2h8v.s7.2efcd2ebdf93 from=translated src=- shape=df0a478a vocab=7722cf9b
-/
theorem smul_mem (h𝓜 : IsPolynomialTwist 𝓜 d) {n : ℕ} (c : R) {p : MvPolynomial ι R}
    (hp : p ∈ 𝓜 n) : c • p ∈ 𝓜 n := by
  rcases (h𝓜 n p).mp hp with rfl | ⟨e, he, hhom⟩
  · exact (h𝓜 n _).mpr (Or.inl (by simp))
  · exact (h𝓜 n _).mpr (Or.inr ⟨e, he, Submodule.smul_mem _ c hhom⟩)

/-- The Laurent exponent of a monomial of a numerator has total degree the twist.
@isnad1 id=eq.3h9v.s8.31648ca33963 from=translated src=- shape=33b70132 vocab=363723a9
-/
theorem degree_laurentExponent_of_mem_support (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ : ι →₀ ℕ} {m : ℕ} {p : MvPolynomial ι R} (hp : p ∈ 𝓜 (m • γ.degree))
    {β : ι →₀ ℕ} (hβ : β ∈ p.support) :
    (laurentExponent γ m β).degree = d :=
  degree_laurentExponent_int γ β m d (by
    rw [h𝓜.degree_eq_of_mem_support hp hβ, nsmul_eq_mul, nsmul_eq_mul]
    push_cast [Nat.cast_mul]
    ring)

end IsPolynomialTwist

/-- Every exponent occurring in a numerator of the twist `d` over `(Xᵞ)ᵐ` has total degree
`m • γ.degree + d`. This is homogeneity read on the support.
@isnad1 id=eq.2h7v.s9.8e85e93fd57c from=translated src=- shape=8bbd05b7 vocab=6935a75c
-/
theorem degree_eq_of_mem_support {d m : ℕ} {γ : ι →₀ ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ natShift (polynomialGrading ι R) d (m • γ.degree)) {β : ι →₀ ℕ}
    (hβ : β ∈ p.support) : β.degree = m • γ.degree + d := by
  by_contra h
  exact (MvPolynomial.mem_support_iff.mp hβ) (MvPolynomial.IsHomogeneous.coeff_eq_zero hp h)

/-- Each monomial of a legitimate numerator is itself a legitimate numerator.

The statement is for *every* `β`, not only those in the support, because `awayMk_sum` takes a
total membership hypothesis. Off the support the monomial is zero, which lies in every graded
piece, so nothing is lost.
@isnad1 id=mem.1h7v.s9.8b21c7d3aed1 from=translated src=- shape=26e5c34d vocab=22e82821
-/
theorem monomial_coeff_mem_natShift {d m : ℕ} {γ : ι →₀ ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ natShift (polynomialGrading ι R) d (m • γ.degree)) (β : ι →₀ ℕ) :
    MvPolynomial.monomial β (p.coeff β) ∈
      natShift (polynomialGrading ι R) d (m • γ.degree) := by
  by_cases h : p.coeff β = 0
  · rw [h]; simp
  · exact MvPolynomial.isHomogeneous_monomial _
      (degree_eq_of_mem_support hp (MvPolynomial.mem_support_iff.mpr h))

set_option maxHeartbeats 800000 in
/-- **A fraction splits over the monomials of its numerator**, at a fixed denominator.

Stated for a twist of either sign: `IsPolynomialTwist.monomial_coeff_mem` supplies the numerator
certificate for each monomial, and nothing else here mentions the grading.

The local `hcongr` step is not decoration. `MvPolynomial.as_sum` rewrites `p`, which appears in
the type of `awayMk`'s membership argument, so rewriting it in the goal fails on a
non-type-correct motive. Substituting the equation and appealing to proof irrelevance sidesteps
that; the same obstruction is why `awayMk_sum` itself descends into `LocalizedModule`.
@isnad1 id=eq.2h8v.s14.38b8df1fc992 from=translated src=- shape=2319400c vocab=45c90d54
-/
theorem awayMk_eq_sum_monomial {σM : Type u} [SetLike σM (MvPolynomial ι R)]
    [AddSubgroupClass σM (MvPolynomial ι R)] {𝓜 : ℕ → σM}
    [SetLike.GradedSMul (polynomialGrading ι R) 𝓜] {d : ℤ} (h𝓜 : IsPolynomialTwist 𝓜 d)
    {m : ℕ} (γ : ι →₀ ℕ) (p : MvPolynomial ι R) (hp : p ∈ 𝓜 (m • γ.degree)) :
    DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ) m p hp =
      ∑ β ∈ p.support, DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ) m
        (MvPolynomial.monomial β (p.coeff β)) (h𝓜.monomial_coeff_mem hp β) := by
  have hcongr : ∀ (q : MvPolynomial ι R) (hq : q ∈ 𝓜 (m • γ.degree)), p = q →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ) m p hp =
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ) m q hq := by
    rintro q hq rfl; rfl
  refine (hcongr _ (sum_mem fun b _ => h𝓜.monomial_coeff_mem hp b)
    (MvPolynomial.as_sum p)).trans ?_
  exact DegreeZeroLocalization.awayMk_sum
    (monomial_one_mem_polynomialGrading (R := R) γ) m p.support
    (fun β => MvPolynomial.monomial β (p.coeff β)) (h𝓜.monomial_coeff_mem hp)

set_option maxHeartbeats 800000 in
/-- **The monomial fractions span.** Every degree-zero fraction away from `Xᵞ` is a finite sum of
monomial fractions over a single common denominator `(Xᵞ)ᵐ`.

The denominator is shared across the whole sum, which is what makes this usable: a map defined by
its effect on monomial fractions extends without any further alignment.
@isnad1 id=ex.1h7v.s15.0e7c23569e68 from=translated src=- shape=4a7833d3 vocab=34867b12
-/
theorem exists_sum_awayMk_monomial [Nontrivial R] {σM : Type u}
    [SetLike σM (MvPolynomial ι R)] [AddSubgroupClass σM (MvPolynomial ι R)] {𝓜 : ℕ → σM}
    [SetLike.GradedSMul (polynomialGrading ι R) 𝓜] {d : ℤ} (h𝓜 : IsPolynomialTwist 𝓜 d)
    (γ : ι →₀ ℕ)
    (z : DegreeZeroLocalization (polynomialGrading ι R) 𝓜
      (.powers (MvPolynomial.monomial γ (1 : R)))) :
    ∃ (m : ℕ) (p : MvPolynomial ι R) (hp : p ∈ 𝓜 (m • γ.degree)),
      z = ∑ β ∈ p.support, DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ) m
        (MvPolynomial.monomial β (p.coeff β)) (h𝓜.monomial_coeff_mem hp β) := by
  obtain ⟨m, p, hp, rfl⟩ :=
    DegreeZeroLocalization.exists_awayMk (monomial_one_mem_polynomialGrading (R := R) γ)
      (monomial_one_pow_ne_zero γ) z
  exact ⟨m, p, hp, awayMk_eq_sum_monomial h𝓜 γ p hp⟩

/-- Every exponent occurring in a spanning decomposition lands in the index set: total degree the
twist, and nonnegative off the support of `γ`.

Together with `exists_sum_awayMk_monomial` and `awayMk_monomial_eq_iff_laurentExponent` this is
the spanning half of #491's basis — the monomial fractions exhaust the localization, and the
exponents they contribute are exactly the admissible ones.
@isnad1 id=and.2h7v.s9.83e7424e3ed1 from=translated src=- shape=96ee8a44 vocab=c584e93b
-/
theorem laurentExponent_mem_index {d m : ℕ} {γ : ι →₀ ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ natShift (polynomialGrading ι R) d (m • γ.degree)) {β : ι →₀ ℕ}
    (hβ : β ∈ p.support) :
    (laurentExponent γ m β).degree = d ∧
      ∀ j, γ j = 0 → 0 ≤ laurentExponent γ m β j :=
  ⟨degree_laurentExponent γ β m d (degree_eq_of_mem_support hp hβ),
    fun _ hj => laurentExponent_nonneg_of_apply_eq_zero γ m β hj⟩

/-! ## Independence

Spanning says the monomial fractions reach everything. This section says they do so in exactly one
way at a fixed denominator: a vanishing combination has vanishing coefficients.

`DegreeZeroLocalization.awayMk_eq_zero_iff` does the work by moving the question off the
localization entirely — a fraction is zero exactly when its numerator is — after which it is the
ordinary statement that distinct monomials of `MvPolynomial` are independent. Nothing here needs
the Laurent exponent; it enters only when denominators differ, and there
`awayMk_monomial_eq_iff_laurentExponent` already decides equality. -/

/-- Distinct monomials are independent: a vanishing sum over a `Finset` of exponents has every
coefficient zero.
@isnad1 id=iff.0h4v.s8.d64f0e6bf3a6 from=translated src=- shape=055d7f89 vocab=75dd3e9c
-/
theorem sum_monomial_eq_zero_iff (s : Finset (ι →₀ ℕ)) (c : (ι →₀ ℕ) → R) :
    (∑ β ∈ s, MvPolynomial.monomial β (c β)) = 0 ↔ ∀ β ∈ s, c β = 0 := by
  classical
  constructor
  · intro h β hβ
    have hcoeff := congrArg (MvPolynomial.coeff β) h
    rwa [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero,
      Finset.sum_congr rfl (fun b _ => MvPolynomial.coeff_monomial β b (c b)),
      Finset.sum_ite_eq' s β (fun b => c b), ite_eq_left hβ] at hcoeff
  · intro h
    exact Finset.sum_eq_zero fun β hβ => by rw [h β hβ]; simp

set_option maxHeartbeats 800000 in
/-- **The monomial fractions are independent at a fixed denominator.**

Combined with `exists_sum_awayMk_monomial` this is the basis statement of #491 in usable form:
every element is a monomial combination over a common denominator, and that combination is
unique. A map may therefore be *defined* by its effect on the monomial fractions, which is what
the sign projection of #340's contracting homotopy needs.
@isnad1 id=iff.1h7v.s15.239070bbb127 from=translated src=- shape=bcfbfd9b vocab=905faac0
-/
theorem sum_awayMk_monomial_eq_zero_iff [IsDomain R] {γ : ι →₀ ℕ} {d m : ℕ}
    (s : Finset (ι →₀ ℕ)) (c : (ι →₀ ℕ) → R)
    (hc : ∀ β, MvPolynomial.monomial β (c β) ∈
      natShift (polynomialGrading ι R) d (m • γ.degree)) :
    (∑ β ∈ s, DegreeZeroLocalization.awayMk
        (𝓜 := natShift (polynomialGrading ι R) d)
        (monomial_one_mem_polynomialGrading (R := R) γ) m
        (MvPolynomial.monomial β (c β)) (hc β)) = 0 ↔ ∀ β ∈ s, c β = 0 := by
  rw [← DegreeZeroLocalization.awayMk_sum
      (monomial_one_mem_polynomialGrading (R := R) γ) m s
      (fun β => MvPolynomial.monomial β (c β)) hc,
    DegreeZeroLocalization.awayMk_eq_zero_iff _ (monomial_one_ne_zero (R := R) γ),
    sum_monomial_eq_zero_iff]

end MvPolynomial
