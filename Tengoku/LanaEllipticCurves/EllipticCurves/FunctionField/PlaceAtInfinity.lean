/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FunctionField.CoordinateRingUnits
import Tengoku.LanaEllipticCurves.EllipticCurves.FunctionField.Divisors
import Tengoku.LanaEllipticCurves.EllipticCurves.FunctionField.TranslationPullback
import Tengoku.Seed.RingTheory.Norm.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The place at infinity of a Weierstrass curve

Let `W` be a Weierstrass curve over a field `F`.  The affine coordinate ring `F[W]` is the ring of
functions regular on the *affine* chart, and the height-one primes of `F[W]` — the closed points of
that chart — are the only places seen by the divisor calculus of
`EllipticCurves.FunctionField.Divisors`.  The projective curve has exactly one further point, the
point at infinity `O`, and correspondingly `F(W)` carries one further place, which no affine `ord`
detects.  **This file constructs that place.**

The construction is the classical one and uses no scheme theory.  `F[W]` is a free `F[X]`-module of
rank two with basis `{1, Y}` (Mathlib's `CoordinateRing.basis`), so it has an algebra norm
`N : F[W] → F[X]`, and

* `deg a := (N a).natDegree` is the **order of the pole of `a` at infinity**;
* `deg` is multiplicative (the norm is) and satisfies the ultrametric bound
  `deg (a + b) ≤ max (deg a) (deg b)` (from Mathlib's `degree_norm_smul_basis`, which computes
  `deg (p • 1 + q • Y) = max (2 deg p) (2 deg q + 3)`);
* hence `ordInfty (a / b) := deg b - deg a` is a well-defined `ℤ`-valued additive valuation on
  `F(W)`, the **order of vanishing at infinity**.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.deg` — the degree of an element of `F[W]`;
* `WeierstrassCurve.Affine.ordInfty` — the order of vanishing at the point at infinity, a
  `ℤ`-valued function on `F(W)` (junk value `0` at `f = 0`, matching the convention of `ord`).

## Main results

* `ordInfty_eq_sub` — the defining property: `ordInfty (a / b) = deg b - deg a`; every other
  statement about `ordInfty` below is derived from it;
* `ordInfty_mul`, `ordInfty_inv`, `ordInfty_div`, `ordInfty_pow`, `ordInfty_zpow`,
  `ordInfty_prod`, `le_ordInfty_add` — `ordInfty` is an additive valuation;
* `ordInfty_genX = -2`, `ordInfty_genY = -3` and `ordInfty_genX_div_genY = 1` — the generic
  coordinates have a double and a triple pole at infinity, and `x / y` is a **uniformizer**;
  consequently `ordInfty_surjective`: the place is discrete with value group all of `ℤ`;
* `exists_eq_algebraMap_of_ordInfty_nonneg` — a function regular on the affine chart *and* at
  infinity is a constant.  This is the `H⁰(E, 𝒪) = F` statement in valuation-theoretic form;
* `exists_deg_sub_lt` — two elements of `F[W]` with the *same* pole order at infinity agree to
  leading order: after scaling by one constant of `F`, their difference has a strictly smaller
  pole.  Equivalently, the graded pieces of the pole filtration are at most one-dimensional;
* `exists_const_ordInfty_sub_pos` — its consequence one level up: a function regular at infinity
  (but with arbitrary poles on the affine chart) is a constant plus a function of strictly positive
  order there.  This is "the residue field at infinity is `F`" in valuation-theoretic form, and it
  is what `residueDegreeProj_none_eq_one` (`PlaceResidueDegree`) is proved from;
* `ord_genX_ne_ordInfty_genX` — **the place at infinity is not one of the affine places**: `genX`
  is regular at every height-one prime of `F[W]` (`ord_algebraMap_nonneg`) but has a pole at
  infinity.  So `ordInfty` really is new information, not a repackaging of the affine calculus;
* `deg_ne_one` (Mathlib) together with `exists_deg_eq` pins the image of `deg` down to
  `ℕ \ {1}` — the **Weierstrass semigroup** `⟨2, 3⟩` of a genus-one curve.

## Why this file exists

The affine/projective mismatch is the standing obstruction on the divisor-theoretic Weil-pairing
front of this project.  `EllipticCurves.FunctionField.PrincipalDivisorOfPoint` records it
explicitly: the classical divisor of `f_P` is `n·(P) − n·(O)`, but the `−n·(O)` term "lives off this
chart and is invisible to `divisor W`".  Neither the divisor-level pullback `[n]∗` (project issue
`#414`/`#422`) nor the divisor-pullback-under-translation formula that the alternating property
needs (`#465`) can be stated on the affine chart, since neither `[n]` nor a translation `τ_T`
preserves it.

This file is the first rung of that theory built the function-field way: the missing place, its
uniformizer, and its independence from the affine places.  It does **not** give the degree-zero
theorem; that is the next rung, and it is out of scope here.

⚠️ **This section used to say the two pullbacks *"are blocked on the projective divisor theory"*
and that the degree-zero theorem *"is the natural next rung"*.  Both rungs have been built.**

* The degree-zero theorem `∑_v ord_v(f)·deg(v) + ordInfty(f) = 0` is
  `degDiv_divisor_add_ordInfty` (`EllipticCurves.FunctionField.DivisorDegree`) — **five minutes**
  after this paragraph was written, by pickaxe — and is repackaged as a single equation
  `degProj (divisorProj f) = 0` in `EllipticCurves.FunctionField.ProjectiveDivisor`.  ⚠️ It does
  **not** go through the residue degrees of the affine closed points, as this paragraph predicted:
  `degPt` is `Ideal.natDegreeGenerator (Ideal.relNorm F[X] v.asIdeal)`, a relative ideal norm, and
  the proof is an induction over the prime factorisation using multiplicativity of `relNorm`.  The
  residue degrees exist separately (`residueDegreeProj`,
  `EllipticCurves.FunctionField.PlaceResidueDegree`).  ⚠️ **This bullet used to end** *"and the two
  are known to agree only informally — no file in this tree proves
  `degPt v = residueDegreeProj W (some v)`"*, **which is false**: that equation is
  `degPt_eq_residueDegreeProj`, its projective form is `degProjPt_eq_residueDegreeProj`, and both
  live in `EllipticCurves.FunctionField.PlaceDegreeComparison` carrying `[W.IsElliptic]` and
  `[IsDedekindDomain W.CoordinateRing]` and **no hypothesis on `F` beyond `[Field F]`**.  ⚠️ What
  survives the retirement is this bullet's own opening claim — that `degDiv_divisor_add_ordInfty`
  does **not** go through the residue degrees of the affine closed points — which is a claim about
  the *proof* and is untouched by the two functions turning out to agree.
* `[n]∗` on divisors is `pullbackDivisor` (`EllipticCurves.FunctionField.PullbackDivisor`), with
  the `[2]` instantiation `divisorProj_mulByTwoEndo`, and the divisor pullback under translation is
  `divisorProj_translateEndo` (`EllipticCurves.FunctionField.PlaceOrder`).  Both are statements
  about `divisorProj` on `ProjPoint W`; the *affine* `divisor W` still does not transport, which is
  the mismatch this file exists to dissolve rather than a residue of it.

## Design

`ordInfty` is a plain `ℤ`-valued function with the junk value `0` at `f = 0`, and every
multiplicative statement carries an explicit nonvanishing hypothesis.  This deliberately matches
`WeierstrassCurve.Affine.ord` (`EllipticCurves.FunctionField.Divisors`), so that the affine orders
and the order at infinity can be compared and combined without a `WithTop`/`AddValuation` coercion
layer in between; `le_ordInfty_add` is the ultrametric axiom in that convention.  Packaging
`ordInfty` as a Mathlib `AddValuation W.FunctionField (WithTop ℤ)` is a routine follow-on once
something needs it.

## Scope

`[Field F]` only.  Ward-independent, normality-independent, and `IsDedekindDomain`-independent
except in the final section, where the comparison with the affine places is stated (`ord` is only
defined under that hypothesis).

## ⚠️ One `@[simp]` attribute was removed here, and the lemma kept (`#1278`)

`deg_mk_Y` carried `@[simp]` and **could never fire**: its LHS is `deg W (mk W Y)`, and
`AdjoinRoot.mk_X` — itself `@[simp]` — rewrites `mk W Y` to `AdjoinRoot.root W.polynomial` before
the pattern is tried. Measured with Mathlib's `simpNF` environment linter, which had never been run
on this tree. The lemma is unchanged and still has consumers in
`EllipticCurves.FunctionField.PlaceResidueDegree` and `…ValuationAtInfinity`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.1–II.3.
-/

open Polynomial Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

variable (W) in
/-- The **degree** of an element of the affine coordinate ring `F[W]`: the degree of its norm down
to `F[X]`.  Geometrically it is the order of the pole of the function at the point at infinity.

The value at `0` is junk (`deg 0 = 0`, since `Algebra.norm 0 = 0`), so the multiplicative statements
below carry explicit nonvanishing hypotheses, exactly as `ord` does in
`EllipticCurves.FunctionField.Divisors`. -/
noncomputable def deg (a : W.CoordinateRing) : ℕ := (Algebra.norm F[X] a).natDegree

/-- The norm to `F[X]` of a nonzero element of `F[W]` is nonzero: `F[W]` is a domain, free of
finite rank over `F[X]`. -/
lemma norm_ne_zero {a : W.CoordinateRing} (ha : a ≠ 0) : Algebra.norm F[X] a ≠ 0 :=
  (Algebra.norm_ne_zero_iff_of_basis (CoordinateRing.basis W)).mpr ha

/-- For a nonzero element the `WithBot ℕ`-valued degree of the norm is the natural number `deg`. -/
lemma degree_norm_eq_deg {a : W.CoordinateRing} (ha : a ≠ 0) :
    (Algebra.norm F[X] a).degree = (deg W a : ℕ) :=
  degree_eq_natDegree (norm_ne_zero ha)

/-- Junk value: the degree of `0`. -/
@[simp]
lemma deg_zero : deg W (0 : W.CoordinateRing) = 0 := by
  haveI : Module.Free F[X] W.CoordinateRing := Module.Free.of_basis (CoordinateRing.basis W)
  haveI : Module.Finite F[X] W.CoordinateRing := Module.Finite.of_basis (CoordinateRing.basis W)
  simp [deg]

/-- Constants have no pole at infinity. -/
@[simp]
lemma deg_one : deg W (1 : W.CoordinateRing) = 0 := by
  simp [deg]

/-- **`deg` is additive**, because the norm is multiplicative. -/
lemma deg_mul {a b : W.CoordinateRing} (ha : a ≠ 0) (hb : b ≠ 0) :
    deg W (a * b) = deg W a + deg W b := by
  simp only [deg, map_mul]
  exact natDegree_mul (norm_ne_zero ha) (norm_ne_zero hb)

/-- A nonzero polynomial in `x` alone is nonzero in `F[W]`. -/
lemma mk_C_ne_zero {p : F[X]} (hp : p ≠ 0) : (mk W (C p) : W.CoordinateRing) ≠ 0 := by
  intro h
  refine hp (smul_basis_eq_zero (W' := W) (p := p) (q := 0) ?_).1
  rw [zero_smul, add_zero, smul, mul_one]
  exact h

/-- The coordinate function `y` is nonzero in `F[W]`. -/
lemma mk_Y_ne_zero : (mk W Y : W.CoordinateRing) ≠ 0 := by
  intro h
  have h1 : (0 : F[X]) • (1 : W.CoordinateRing) + (1 : F[X]) • mk W Y = 0 := by
    rw [zero_smul, zero_add, one_smul]; exact h
  exact one_ne_zero (smul_basis_eq_zero h1).2

section AddLe

private lemma two_nsmul_mono {u v : WithBot ℕ} (h : u ≤ v) : (2 : ℕ) • u ≤ (2 : ℕ) • v := by
  rw [two_nsmul, two_nsmul]; exact add_le_add h h

private lemma two_nsmul_max (u v : WithBot ℕ) :
    (2 : ℕ) • max u v = max ((2 : ℕ) • u) ((2 : ℕ) • v) := by
  rcases le_total u v with h | h
  · rw [max_eq_right h, max_eq_right (two_nsmul_mono h)]
  · rw [max_eq_left h, max_eq_left (two_nsmul_mono h)]

private lemma max_add_right (u v c : WithBot ℕ) : max u v + c = max (u + c) (v + c) := by
  rcases le_total u v with h | h
  · rw [max_eq_right h, max_eq_right (add_le_add h (le_refl c))]
  · rw [max_eq_left h, max_eq_left (add_le_add h (le_refl c))]

/-- **The ultrametric bound for the norm degree.**  Both coordinates of `a + b` in the basis
`{1, Y}` are sums of the corresponding coordinates of `a` and of `b`, so the degree formula
`degree_norm_smul_basis` gives the bound termwise. -/
lemma degree_norm_add_le (a b : W.CoordinateRing) :
    (Algebra.norm F[X] (a + b)).degree ≤
      max (Algebra.norm F[X] a).degree (Algebra.norm F[X] b).degree := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
  obtain ⟨p', q', rfl⟩ := exists_smul_basis_eq b
  have hadd : (p • (1 : W.CoordinateRing) + q • mk W Y)
      + (p' • (1 : W.CoordinateRing) + q' • mk W Y)
      = (p + p') • (1 : W.CoordinateRing) + (q + q') • mk W Y := by
    rw [add_smul, add_smul]; ring
  rw [hadd, degree_norm_smul_basis, degree_norm_smul_basis, degree_norm_smul_basis]
  refine max_le ?_ ?_
  · have h1 : (2 : ℕ) • (p + p').degree ≤ max ((2 : ℕ) • p.degree) ((2 : ℕ) • p'.degree) :=
      (two_nsmul_mono (degree_add_le p p')).trans_eq (two_nsmul_max _ _)
    exact h1.trans (max_le_max (le_max_left _ _) (le_max_left _ _))
  · have h2 : (2 : ℕ) • (q + q').degree + 3
        ≤ max ((2 : ℕ) • q.degree + 3) ((2 : ℕ) • q'.degree + 3) := by
      refine le_trans (add_le_add ?_ (le_refl 3)) (max_add_right _ _ 3).le
      exact (two_nsmul_mono (degree_add_le q q')).trans_eq (two_nsmul_max _ _)
    exact h2.trans (max_le_max (le_max_right _ _) (le_max_right _ _))

end AddLe

/-- **`deg` satisfies the ultrametric inequality**: a sum has no worse a pole at infinity than
its worst summand. -/
lemma deg_add_le (a b : W.CoordinateRing) : deg W (a + b) ≤ max (deg W a) (deg W b) := by
  refine natDegree_le_iff_degree_le.mpr ((degree_norm_add_le a b).trans (max_le ?_ ?_))
  · exact degree_le_natDegree.trans (by exact_mod_cast le_max_left (deg W a) (deg W b))
  · exact degree_le_natDegree.trans (by exact_mod_cast le_max_right (deg W a) (deg W b))

/-- The basis expansion of a constant. -/
lemma eq_smul_basis_algebraMap (c : F) :
    algebraMap F W.CoordinateRing c = C c • (1 : W.CoordinateRing) + (0 : F[X]) • mk W Y := by
  rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one,
    IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, ← Polynomial.C_eq_algebraMap]

/-- Constants are regular at infinity. -/
@[simp]
lemma deg_algebraMap (c : F) : deg W (algebraMap F W.CoordinateRing c) = 0 := by
  rw [deg, eq_smul_basis_algebraMap, norm_smul_basis]
  simp

/-- A polynomial in `x` alone has a pole at infinity of **even** order `2 · deg p`. -/
lemma deg_mk_C (p : F[X]) : deg W (mk W (C p)) = 2 * p.natDegree := by
  have h : mk W (C p) = p • (1 : W.CoordinateRing) + (0 : F[X]) • mk W Y := by
    rw [zero_smul, add_zero, smul, mul_one]
  rw [deg, h, norm_smul_basis]
  simp [natDegree_pow]

/-- The coordinate function `y` has a **triple** pole at infinity. -/
lemma deg_mk_Y : deg W (mk W Y) = 3 := by
  have h : mk W Y = (0 : F[X]) • (1 : W.CoordinateRing) + (1 : F[X]) • mk W Y := by
    rw [zero_smul, zero_add, one_smul]
  refine natDegree_eq_of_degree_eq_some ?_
  rw [h, degree_norm_smul_basis]
  simp

/-- **The gap of the Weierstrass semigroup.**  No function on the affine chart has a simple pole
at infinity; this single gap is the genus.  (Mathlib's `natDegree_norm_ne_one`.) -/
lemma deg_ne_one (a : W.CoordinateRing) : deg W a ≠ 1 :=
  natDegree_norm_ne_one a

/-- An element of `F[W]` with no pole at infinity is a constant. -/
theorem exists_eq_algebraMap_of_deg_eq_zero {a : W.CoordinateRing} (ha : a ≠ 0)
    (h : deg W a = 0) : ∃ c : F, c ≠ 0 ∧ a = algebraMap F W.CoordinateRing c := by
  have hdeg0 : (Algebra.norm F[X] a).degree = 0 := by
    rw [degree_norm_eq_deg ha, h]; rfl
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
  rw [degree_norm_smul_basis] at hdeg0
  have hq3 : 2 • q.degree + 3 ≤ (0 : WithBot ℕ) := (le_max_right _ _).trans hdeg0.le
  have hq0 : q = 0 := by
    by_contra hq
    have hqd : (0 : WithBot ℕ) ≤ q.degree := zero_le_degree_iff.mpr hq
    have h2q : (0 : WithBot ℕ) ≤ 2 • q.degree := by
      rw [two_nsmul]; exact add_nonneg hqd hqd
    have h3 : (3 : WithBot ℕ) ≤ 2 • q.degree + 3 := le_add_of_nonneg_left h2q
    exact absurd (h3.trans hq3) (by decide)
  subst hq0
  simp only [degree_zero, two_nsmul, WithBot.bot_add, max_bot_right] at hdeg0
  have hp0 : p.degree = 0 := (Nat.WithBot.add_eq_zero_iff.mp hdeg0).1
  have hp : p = C (p.coeff 0) := eq_C_of_degree_eq_zero hp0
  have hc : p.coeff 0 ≠ 0 := by
    intro hc0
    rw [hc0, map_zero] at hp
    rw [hp, degree_zero] at hp0
    exact absurd hp0 (by simp)
  refine ⟨p.coeff 0, hc, ?_⟩
  rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one,
    IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, ← Polynomial.C_eq_algebraMap, ← hp]

/-- **The functions regular at infinity are the constants.** -/
theorem deg_eq_zero_iff_isUnit {a : W.CoordinateRing} (ha : a ≠ 0) :
    deg W a = 0 ↔ IsUnit a := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := exists_eq_algebraMap_of_deg_eq_zero ha h
    exact (isUnit_iff_exists_eq_algebraMap).mpr ⟨c, hc, rfl⟩
  · obtain ⟨c, _, rfl⟩ := (isUnit_iff_exists_eq_algebraMap).mp h
    exact deg_algebraMap c

/-- **The Weierstrass semigroup of an elliptic curve.** Every natural number except `1` is the
degree of an element of `F[W]`: the pole orders at infinity realised by functions regular on the
affine chart are `0, 2, 3, 4, 5, …`. Together with `deg_ne_one` this determines the image of `deg`
exactly, and the single gap at `1` is the genus. -/
theorem exists_deg_eq {n : ℕ} (hn : n ≠ 1) : ∃ a : W.CoordinateRing, a ≠ 0 ∧ deg W a = n := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    refine ⟨mk W (C (X ^ k)), mk_C_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero), ?_⟩
    rw [deg_mk_C, natDegree_X_pow]
    omega
  · obtain ⟨k, hk⟩ := ho
    have hk1 : k ≠ 0 := by rintro rfl; exact hn (by omega)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hX : (mk W (C (X ^ j)) : W.CoordinateRing) ≠ 0 :=
      mk_C_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
    refine ⟨mk W (C (X ^ j)) * mk W Y, mul_ne_zero hX mk_Y_ne_zero, ?_⟩
    rw [deg_mul hX mk_Y_ne_zero, deg_mk_C, deg_mk_Y, natDegree_X_pow]
    omega

/-! ### Leading coefficients at infinity

Two functions with the *same* pole order at infinity agree to leading order after scaling by one
constant of `F`: their difference has a strictly smaller pole.  Equivalently, the graded pieces of
the pole filtration on `F[W]` are at most one-dimensional over `F`.

This is what makes the residue field at the point at infinity equal to `F` over an **arbitrary**
base field (`residueDegreeProj_none_eq_one`), and the reason it works with no hypothesis on `F` is
a *parity* observation.  Mathlib's `degree_norm_smul_basis` gives, for every `p` and `q`,

```
deg (p • 1 + q • y)  =  max (2 • deg p) (2 • deg q + 3),
```

and the two entries are *even-or-`⊥`* and *odd-or-`⊥`*, so they can never be equal.  The parity of
the pole order therefore selects which of the two coordinates attains it, and the leading
coefficient is a single element of `F`.  A norm-based argument would instead pin the constant down
only up to `c² = lc(N a) / lc(N b)`, leaving a quadratic ambiguity that is not really there. -/

section LeadingCoeff

private lemma two_nsmul_degree_add_eq_iff {p : F[X]} {k n : ℕ} :
    (2 : ℕ) • p.degree + (k : WithBot ℕ) = (n : WithBot ℕ)
      ↔ (p ≠ 0 ∧ 2 * p.natDegree + k = n) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp only [degree_zero, two_nsmul, WithBot.bot_add, ne_eq, not_true_eq_false, false_and,
      iff_false]
    exact WithBot.bot_ne_natCast n
  · rw [degree_eq_natDegree hp, two_nsmul]
    simp only [hp, ne_eq, not_false_eq_true, true_and]
    rw [← Nat.cast_add, ← Nat.cast_add, Nat.cast_inj]
    omega

private lemma two_nsmul_degree_add_lt_iff {p : F[X]} {k n : ℕ} :
    (2 : ℕ) • p.degree + (k : WithBot ℕ) < (n : WithBot ℕ)
      ↔ (p = 0 ∨ 2 * p.natDegree + k < n) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp only [degree_zero, two_nsmul, WithBot.bot_add, true_or, iff_true]
    exact WithBot.bot_lt_coe _
  · rw [degree_eq_natDegree hp, two_nsmul]
    simp only [hp, false_or]
    rw [← Nat.cast_add, ← Nat.cast_add, Nat.cast_lt]
    omega

private lemma two_nsmul_degree_eq_iff {p : F[X]} {n : ℕ} :
    (2 : ℕ) • p.degree = (n : WithBot ℕ) ↔ (p ≠ 0 ∧ 2 * p.natDegree = n) := by
  simpa using two_nsmul_degree_add_eq_iff (p := p) (k := 0) (n := n)

private lemma two_nsmul_degree_lt_iff {p : F[X]} {n : ℕ} :
    (2 : ℕ) • p.degree < (n : WithBot ℕ) ↔ (p = 0 ∨ 2 * p.natDegree < n) := by
  simpa using two_nsmul_degree_add_lt_iff (p := p) (k := 0) (n := n)

/-- **The parity observation.**  Exactly one of the two entries of `degree_norm_smul_basis` attains
their maximum, and which one is decided by the parity of that maximum: `2 • deg p` is even-or-`⊥`
and `2 • deg q + 3` is odd-or-`⊥`, so they are never equal. -/
private lemma max_two_nsmul_degree_cases {p q : F[X]} {n : ℕ}
    (h : max ((2 : ℕ) • p.degree) ((2 : ℕ) • q.degree + 3) = (n : WithBot ℕ)) :
    (p ≠ 0 ∧ 2 * p.natDegree = n ∧ (q = 0 ∨ 2 * q.natDegree + 3 < n)) ∨
      (q ≠ 0 ∧ 2 * q.natDegree + 3 = n ∧ (p = 0 ∨ 2 * p.natDegree < n)) := by
  have hthree : ((3 : ℕ) : WithBot ℕ) = (3 : WithBot ℕ) := by norm_num
  have hp := le_max_left ((2 : ℕ) • p.degree) ((2 : ℕ) • q.degree + 3)
  have hq := le_max_right ((2 : ℕ) • p.degree) ((2 : ℕ) • q.degree + 3)
  rw [h] at hp hq
  rcases max_choice ((2 : ℕ) • p.degree) ((2 : ℕ) • q.degree + 3) with hm | hm
  · rw [hm] at h
    obtain ⟨hp0, hpn⟩ := two_nsmul_degree_eq_iff.1 h
    refine Or.inl ⟨hp0, hpn, ?_⟩
    refine two_nsmul_degree_add_lt_iff.1 (hthree ▸ lt_of_le_of_ne (hthree ▸ hq) fun hcon => ?_)
    obtain ⟨-, hqn⟩ := two_nsmul_degree_add_eq_iff.1 (hthree ▸ hcon)
    omega
  · rw [hm] at h
    obtain ⟨hq0, hqn⟩ := two_nsmul_degree_add_eq_iff.1 (hthree ▸ h)
    refine Or.inr ⟨hq0, hqn, ?_⟩
    refine two_nsmul_degree_lt_iff.1 (lt_of_le_of_ne hp fun hcon => ?_)
    obtain ⟨-, hpn⟩ := two_nsmul_degree_eq_iff.1 hcon
    omega

/-- The half of `exists_deg_sub_lt` that both parity branches share, with the roles of the two
basis coordinates abstracted into `u` (the one carrying the pole order, offset `k`) and `w` (the
one strictly below it, offset `l`).  Written once because the even and the odd branch are the same
argument with `(k, l) = (0, 3)` and `(3, 0)`. -/
private lemma exists_leadingCoeff_ratio {u₁ u₂ w₁ w₂ : F[X]} {n k l : ℕ}
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (hnu₁ : 2 * u₁.natDegree + k = n) (hnu₂ : 2 * u₂.natDegree + k = n)
    (hw₁ : w₁ = 0 ∨ 2 * w₁.natDegree + l < n) (hw₂ : w₂ = 0 ∨ 2 * w₂.natDegree + l < n) :
    ∃ c : F, c ≠ 0 ∧
      (u₁ - C c * u₂ = 0 ∨ 2 * (u₁ - C c * u₂).natDegree + k < n) ∧
      (w₁ - C c * w₂ = 0 ∨ 2 * (w₁ - C c * w₂).natDegree + l < n) := by
  have hdeg : u₁.natDegree = u₂.natDegree := by omega
  set c : F := u₁.leadingCoeff / u₂.leadingCoeff with hc
  have hc0 : c ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.2 hu₁) (leadingCoeff_ne_zero.2 hu₂)
  refine ⟨c, hc0, ?_, ?_⟩
  · rcases eq_or_ne (u₁ - C c * u₂) 0 with h | h
    · exact Or.inl h
    refine Or.inr ?_
    have hlc : u₁.leadingCoeff = (C c * u₂).leadingCoeff := by
      rw [leadingCoeff_mul, leadingCoeff_C, hc, div_mul_cancel₀]
      exact leadingCoeff_ne_zero.2 hu₂
    have hdd : u₁.degree = (C c * u₂).degree := by
      rw [degree_C_mul hc0, degree_eq_natDegree hu₁, degree_eq_natDegree hu₂, hdeg]
    have hlt : (u₁ - C c * u₂).degree < u₁.degree := degree_sub_lt_left hdd hu₁ hlc
    have : (u₁ - C c * u₂).natDegree < u₁.natDegree :=
      natDegree_lt_natDegree h (by rwa [degree_eq_natDegree hu₁] at hlt ⊢)
    omega
  · rcases eq_or_ne (w₁ - C c * w₂) 0 with h | h
    · exact Or.inl h
    refine Or.inr ?_
    have hle : (w₁ - C c * w₂).natDegree ≤ max w₁.natDegree w₂.natDegree :=
      (natDegree_sub_le _ _).trans (max_le_max (le_refl _) (natDegree_C_mul_le c w₂))
    have h₁ : w₁ ≠ 0 ∨ w₂ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h (by rw [hcon.1, hcon.2, mul_zero, sub_zero])
    rcases hw₁ with rfl | hb₁ <;> rcases hw₂ with rfl | hb₂ <;> simp_all <;> omega

/-- The pole order of a basis expansion, as an equation in `WithBot ℕ`.  A restatement of
`degree_norm_smul_basis` in terms of `deg`. -/
private lemma deg_smul_basis_cast {p q : F[X]}
    (h : p • (1 : W.CoordinateRing) + q • mk W Y ≠ 0) :
    ((deg W (p • (1 : W.CoordinateRing) + q • mk W Y) : ℕ) : WithBot ℕ)
      = max ((2 : ℕ) • p.degree) ((2 : ℕ) • q.degree + 3) := by
  rw [← degree_norm_eq_deg h, degree_norm_smul_basis]

/-- **Two functions with the same pole order at infinity agree to leading order.**  If `a` and `b`
are nonzero with `deg a = deg b`, then for one constant `c : F` the difference `a - c · b` either
vanishes or has a *strictly* smaller pole at infinity than `b`.

Equivalently: the graded pieces of the pole filtration on `F[W]` are at most one-dimensional over
`F`.  This is the whole content of "the residue field at the point at infinity is `F`", and it holds
over an arbitrary base field — see the section docstring for why the parity of `deg` rules out the
quadratic ambiguity a norm-based argument would leave.

⚠️ The vanishing case is a genuine disjunct and not a degenerate instance of the other one: `deg`
returns the junk value `0` at `0`, and `deg b = 0` is possible (both `a` and `b` nonzero
constants). -/
theorem exists_deg_sub_lt {a b : W.CoordinateRing} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : deg W a = deg W b) :
    ∃ c : F, a - algebraMap F W.CoordinateRing c * b = 0 ∨
      deg W (a - algebraMap F W.CoordinateRing c * b) < deg W b := by
  obtain ⟨p₁, q₁, rfl⟩ := exists_smul_basis_eq a
  obtain ⟨p₂, q₂, rfl⟩ := exists_smul_basis_eq b
  set n := deg W (p₂ • (1 : W.CoordinateRing) + q₂ • mk W Y) with hn
  have h₁ : max ((2 : ℕ) • p₁.degree) ((2 : ℕ) • q₁.degree + 3) = (n : WithBot ℕ) := by
    rw [← deg_smul_basis_cast ha, h]
  have h₂ : max ((2 : ℕ) • p₂.degree) ((2 : ℕ) • q₂.degree + 3) = (n : WithBot ℕ) :=
    (deg_smul_basis_cast hb).symm
  -- the parity of `n` selects the same basis coordinate on both sides
  obtain ⟨c, hc0, hu, hw⟩ :
      ∃ c : F, c ≠ 0 ∧ (p₁ - C c * p₂ = 0 ∨ 2 * (p₁ - C c * p₂).natDegree < n) ∧
        (q₁ - C c * q₂ = 0 ∨ 2 * (q₁ - C c * q₂).natDegree + 3 < n) := by
    rcases max_two_nsmul_degree_cases h₁ with ⟨hp₁, hn₁, hq₁⟩ | ⟨hq₁, hn₁, hp₁⟩
    · rcases max_two_nsmul_degree_cases h₂ with ⟨hp₂, hn₂, hq₂⟩ | ⟨hq₂, hn₂, -⟩
      · obtain ⟨c, hc0, hu, hw⟩ :=
          exists_leadingCoeff_ratio (k := 0) (l := 3) hp₁ hp₂ (by omega) (by omega) hq₁ hq₂
        exact ⟨c, hc0, by simpa using hu, hw⟩
      · omega
    · rcases max_two_nsmul_degree_cases h₂ with ⟨hp₂, hn₂, -⟩ | ⟨hq₂, hn₂, hp₂⟩
      · omega
      · obtain ⟨c, hc0, hu, hw⟩ :=
          exists_leadingCoeff_ratio (k := 3) (l := 0) hq₁ hq₂ hn₁ hn₂
            (by simpa using hp₁) (by simpa using hp₂)
        exact ⟨c, hc0, by simpa using hw, hu⟩
  -- push the constant multiple through the basis and read off the new pole order
  refine ⟨c, ?_⟩
  have hsub : (p₁ • (1 : W.CoordinateRing) + q₁ • mk W Y)
      - algebraMap F W.CoordinateRing c * (p₂ • (1 : W.CoordinateRing) + q₂ • mk W Y)
      = (p₁ - C c * p₂) • (1 : W.CoordinateRing) + (q₁ - C c * q₂) • mk W Y := by
    rw [eq_smul_basis_algebraMap, zero_smul, add_zero, smul_mul_assoc, one_mul, smul_add,
      smul_smul, smul_smul, sub_smul, sub_smul]
    ring
  rw [hsub]
  rcases eq_or_ne ((p₁ - C c * p₂) • (1 : W.CoordinateRing) + (q₁ - C c * q₂) • mk W Y) 0
    with hz | hz
  · exact Or.inl hz
  refine Or.inr ?_
  rw [← Nat.cast_lt (α := WithBot ℕ), deg_smul_basis_cast hz]
  exact max_lt (two_nsmul_degree_lt_iff.2 hu)
    (by simpa using two_nsmul_degree_add_lt_iff.2 hw)

end LeadingCoeff

end WeierstrassCurve.Affine.CoordinateRing

namespace WeierstrassCurve.Affine

open scoped nonZeroDivisors

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

variable (W) in
/-- The **order of vanishing at the point at infinity** of a rational function. -/
noncomputable def ordInfty (f : W.FunctionField) : ℤ :=
  if f = 0 then 0
  else (deg W (IsLocalization.sec W.CoordinateRing⁰ f).2 : ℤ)
    - (deg W (IsLocalization.sec W.CoordinateRing⁰ f).1 : ℤ)

/-- Junk value: the order at infinity of `0`, matching the convention `ord v 0 = 0`. -/
@[simp]
lemma ordInfty_zero : ordInfty W (0 : W.FunctionField) = 0 := ite_eq_left rfl

/-- **The defining property of `ordInfty`**: on a quotient `f = a / b` of elements of the
coordinate ring it is `deg b - deg a`. -/
theorem ordInfty_eq_sub {f : W.FunctionField} (hf : f ≠ 0) {a b : W.CoordinateRing} (hb : b ≠ 0)
    (h : f * algebraMap W.CoordinateRing W.FunctionField b
      = algebraMap W.CoordinateRing W.FunctionField a) :
    ordInfty W f = (deg W b : ℤ) - deg W a := by
  have hinj : Function.Injective (algebraMap W.CoordinateRing W.FunctionField) :=
    IsFractionRing.injective W.CoordinateRing W.FunctionField
  set n := (IsLocalization.sec W.CoordinateRing⁰ f).1 with hn
  set s := (IsLocalization.sec W.CoordinateRing⁰ f).2 with hs
  have hspec : f * algebraMap W.CoordinateRing W.FunctionField (s : W.CoordinateRing)
      = algebraMap W.CoordinateRing W.FunctionField n := IsLocalization.sec_spec _ f
  have hs0 : (s : W.CoordinateRing) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have ha0 : a ≠ 0 := by
    intro hazero
    rw [hazero, map_zero, mul_eq_zero] at h
    rcases h with h | h
    · exact hf h
    · exact hb (hinj (by rw [h, map_zero]))
  have hn0 : n ≠ 0 := by
    intro hnzero
    rw [hnzero, map_zero, mul_eq_zero] at hspec
    rcases hspec with h' | h'
    · exact hf h'
    · exact hs0 (hinj (by rw [h', map_zero]))
  have hcross : n * b = a * (s : W.CoordinateRing) := by
    refine hinj ?_
    rw [map_mul, map_mul, ← hspec, ← h]
    ring
  have hdeg : deg W n + deg W b = deg W a + deg W (s : W.CoordinateRing) := by
    rw [← deg_mul hn0 hb, ← deg_mul ha0 hs0, hcross]
  rw [ordInfty, ite_eq_right hf, ← hn, ← hs]
  omega

/-- The order at infinity of a nonzero element of the coordinate ring is minus its degree: a
polynomial function has a pole at infinity, of order its degree. -/
@[simp]
theorem ordInfty_algebraMap {a : W.CoordinateRing} (ha : a ≠ 0) :
    ordInfty W (algebraMap W.CoordinateRing W.FunctionField a) = -(deg W a : ℤ) := by
  have hfa : algebraMap W.CoordinateRing W.FunctionField a ≠ 0 := fun h =>
    ha ((IsFractionRing.injective W.CoordinateRing W.FunctionField) (by rw [h, map_zero]))
  rw [ordInfty_eq_sub (a := a) (b := 1) hfa one_ne_zero (by rw [map_one, mul_one]), deg_one]
  simp

/-- The constant `1` is regular and nonvanishing at infinity. -/
@[simp]
lemma ordInfty_one : ordInfty W (1 : W.FunctionField) = 0 := by
  have h := ordInfty_algebraMap (W := W) (a := 1) one_ne_zero
  rwa [map_one, deg_one, Nat.cast_zero, neg_zero] at h

/-- `ordInfty` unfolded at a nonzero argument, in terms of Mathlib's chosen numerator and
denominator `IsLocalization.sec`. -/
lemma ordInfty_of_ne_zero {f : W.FunctionField} (hf : f ≠ 0) :
    ordInfty W f = (deg W (IsLocalization.sec W.CoordinateRing⁰ f).2 : ℤ)
      - deg W (IsLocalization.sec W.CoordinateRing⁰ f).1 := ite_eq_right hf

private lemma sec_fst_ne_zero {f : W.FunctionField} (hf : f ≠ 0) :
    (IsLocalization.sec W.CoordinateRing⁰ f).1 ≠ 0 := by
  intro h
  have hspec := IsLocalization.sec_spec W.CoordinateRing⁰ f
  rw [h, map_zero, mul_eq_zero] at hspec
  rcases hspec with h' | h'
  · exact hf h'
  · exact nonZeroDivisors.coe_ne_zero _
      ((IsFractionRing.injective W.CoordinateRing W.FunctionField) (by rw [h', map_zero]))

/-- **`ordInfty` is additive.** -/
theorem ordInfty_mul {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordInfty W (f * g) = ordInfty W f + ordInfty W g := by
  have hf' := IsLocalization.sec_spec W.CoordinateRing⁰ f
  have hg' := IsLocalization.sec_spec W.CoordinateRing⁰ g
  have hsf : ((IsLocalization.sec W.CoordinateRing⁰ f).2 : W.CoordinateRing) ≠ 0 :=
    nonZeroDivisors.coe_ne_zero _
  have hsg : ((IsLocalization.sec W.CoordinateRing⁰ g).2 : W.CoordinateRing) ≠ 0 :=
    nonZeroDivisors.coe_ne_zero _
  have hprod : (f * g) * algebraMap W.CoordinateRing W.FunctionField
        (((IsLocalization.sec W.CoordinateRing⁰ f).2 : W.CoordinateRing) *
          ((IsLocalization.sec W.CoordinateRing⁰ g).2 : W.CoordinateRing))
      = algebraMap W.CoordinateRing W.FunctionField
        ((IsLocalization.sec W.CoordinateRing⁰ f).1 *
          (IsLocalization.sec W.CoordinateRing⁰ g).1) := by
    rw [map_mul, map_mul, ← hf', ← hg']
    ring
  rw [ordInfty_eq_sub (mul_ne_zero hf hg) (mul_ne_zero hsf hsg) hprod,
    deg_mul hsf hsg, deg_mul (sec_fst_ne_zero hf) (sec_fst_ne_zero hg),
    ordInfty_of_ne_zero hf, ordInfty_of_ne_zero hg]
  push_cast
  ring

/-- **`ordInfty` of an inverse.** -/
theorem ordInfty_inv (f : W.FunctionField) : ordInfty W f⁻¹ = -ordInfty W f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hf' := IsLocalization.sec_spec W.CoordinateRing⁰ f
  have hsf : ((IsLocalization.sec W.CoordinateRing⁰ f).2 : W.CoordinateRing) ≠ 0 :=
    nonZeroDivisors.coe_ne_zero _
  have hinv : f⁻¹ * algebraMap W.CoordinateRing W.FunctionField
        (IsLocalization.sec W.CoordinateRing⁰ f).1
      = algebraMap W.CoordinateRing W.FunctionField
        ((IsLocalization.sec W.CoordinateRing⁰ f).2 : W.CoordinateRing) := by
    rw [← hf', ← mul_assoc, inv_mul_cancel₀ hf, one_mul]
  rw [ordInfty_eq_sub (inv_ne_zero hf) (sec_fst_ne_zero hf) hinv, ordInfty_of_ne_zero hf]
  ring

/-- **`ordInfty` of a quotient.** -/
theorem ordInfty_div {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordInfty W (f / g) = ordInfty W f - ordInfty W g := by
  rw [div_eq_mul_inv, ordInfty_mul hf (inv_ne_zero hg), ordInfty_inv]
  ring

/-- **`ordInfty` of a natural power.** -/
theorem ordInfty_pow (f : W.FunctionField) (n : ℕ) :
    ordInfty W (f ^ n) = n * ordInfty W f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [zero_pow hn.ne']; simp
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, ordInfty_mul (pow_ne_zero k hf) hf, ih]; push_cast; ring

/-- **`ordInfty` of an integer power.** -/
theorem ordInfty_zpow (f : W.FunctionField) (n : ℤ) :
    ordInfty W (f ^ n) = n * ordInfty W f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [zero_zpow n hn]; simp
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, ordInfty_pow]
  · rw [zpow_neg, zpow_natCast, ordInfty_inv, ordInfty_pow]; ring

variable (W) in
/-- **`ordInfty` of a finite product**, the companion of `ordInfty_mul`. -/
theorem ordInfty_prod {ι : Type*} (s : Finset ι) (f : ι → W.FunctionField)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    ordInfty W (∏ i ∈ s, f i) = ∑ i ∈ s, ordInfty W (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hfa : f a ≠ 0 := hf a (Finset.mem_cons_self a s)
    have hmem : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_cons_of_mem hi)
    have hprod : ∏ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.2 hmem
    rw [Finset.prod_cons, Finset.sum_cons, ordInfty_mul hfa hprod, ih hmem]

/-- **The ultrametric inequality at infinity.** -/
theorem le_ordInfty_add {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (ordInfty W f) (ordInfty W g) ≤ ordInfty W (f + g) := by
  set a := (IsLocalization.sec W.CoordinateRing⁰ f).1 with ha
  set s := ((IsLocalization.sec W.CoordinateRing⁰ f).2 : W.CoordinateRing) with hs
  set b := (IsLocalization.sec W.CoordinateRing⁰ g).1 with hb
  set t := ((IsLocalization.sec W.CoordinateRing⁰ g).2 : W.CoordinateRing) with ht
  have hf' : f * algebraMap W.CoordinateRing W.FunctionField s
      = algebraMap W.CoordinateRing W.FunctionField a := IsLocalization.sec_spec _ f
  have hg' : g * algebraMap W.CoordinateRing W.FunctionField t
      = algebraMap W.CoordinateRing W.FunctionField b := IsLocalization.sec_spec _ g
  have hs0 : s ≠ 0 := nonZeroDivisors.coe_ne_zero _
  have ht0 : t ≠ 0 := nonZeroDivisors.coe_ne_zero _
  have hsum : (f + g) * algebraMap W.CoordinateRing W.FunctionField (s * t)
      = algebraMap W.CoordinateRing W.FunctionField (a * t + b * s) := by
    rw [map_mul, map_add, map_mul, map_mul, ← hf', ← hg']
    ring
  have hfeq : ordInfty W f = (deg W (s * t) : ℤ) - deg W (a * t) := by
    refine ordInfty_eq_sub hf (mul_ne_zero hs0 ht0) ?_
    rw [map_mul, map_mul, ← mul_assoc, hf']
  have hgeq : ordInfty W g = (deg W (s * t) : ℤ) - deg W (b * s) := by
    refine ordInfty_eq_sub hg (mul_ne_zero hs0 ht0) ?_
    rw [map_mul, map_mul, show g * (algebraMap W.CoordinateRing W.FunctionField s
      * algebraMap W.CoordinateRing W.FunctionField t)
      = g * algebraMap W.CoordinateRing W.FunctionField t
        * algebraMap W.CoordinateRing W.FunctionField s from by ring, hg']
  rw [ordInfty_eq_sub hfg (mul_ne_zero hs0 ht0) hsum, hfeq, hgeq]
  have hle : deg W (a * t + b * s) ≤ max (deg W (a * t)) (deg W (b * s)) :=
    deg_add_le _ _
  rcases le_total (deg W (a * t)) (deg W (b * s)) with h | h
  · rw [max_eq_right h] at hle
    simp only [min_le_iff]
    omega
  · rw [max_eq_left h] at hle
    simp only [min_le_iff]
    omega

/-! ### The place at infinity is a genuine new place -/

/-- Nonzero constants are regular and nonvanishing at infinity. -/
@[simp]
theorem ordInfty_algebraMap_base {c : F} (hc : c ≠ 0) :
    ordInfty W (algebraMap F W.FunctionField c) = 0 := by
  have h : algebraMap F W.FunctionField c
      = algebraMap W.CoordinateRing W.FunctionField (algebraMap F W.CoordinateRing c) :=
    (IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField c)
  have hne : algebraMap F W.CoordinateRing c ≠ 0 := by
    simpa using (algebraMap F W.CoordinateRing).injective.ne hc
  rw [h, ordInfty_algebraMap hne, deg_algebraMap]
  simp

/-- The generic `x`-coordinate has a **double pole** at infinity. -/
@[simp]
theorem ordInfty_genX : ordInfty W (CoordinateRing.genX W) = -2 := by
  have hne : (CoordinateRing.mk W (C X) : W.CoordinateRing) ≠ 0 :=
    CoordinateRing.mk_C_ne_zero Polynomial.X_ne_zero
  rw [CoordinateRing.genX, CoordinateRing.genPsi, ordInfty_algebraMap hne, deg_mk_C]
  simp

/-- The generic `y`-coordinate has a **triple pole** at infinity. -/
@[simp]
theorem ordInfty_genY : ordInfty W (CoordinateRing.genY W) = -3 := by
  have hroot : AdjoinRoot.root W.polynomial = CoordinateRing.mk W Y := rfl
  have hne : (CoordinateRing.mk W Y : W.CoordinateRing) ≠ 0 := CoordinateRing.mk_Y_ne_zero
  rw [CoordinateRing.genY, CoordinateRing.genPsi, hroot, ordInfty_algebraMap hne, deg_mk_Y]
  norm_num

/-- The generic `x`-coordinate is nonzero. -/
lemma genX_ne_zero : CoordinateRing.genX W ≠ 0 := fun h =>
  CoordinateRing.genX_ne (W := W) 0 (by rw [h, map_zero])

/-- The generic `y`-coordinate is nonzero — it has a pole at infinity, so it is not `0`. -/
lemma genY_ne_zero : CoordinateRing.genY W ≠ 0 := by
  intro h
  have := ordInfty_genY (W := W)
  rw [h, ordInfty_zero] at this
  exact absurd this (by norm_num)

/-- **A uniformizer at infinity.** The function `x / y` vanishes to order exactly `1` at the point
at infinity, so the place at infinity is a *discrete* place of `F(W)` and `ordInfty` is onto `ℤ`
(`ordInfty_surjective`). -/
theorem ordInfty_genX_div_genY :
    ordInfty W (CoordinateRing.genX W / CoordinateRing.genY W) = 1 := by
  rw [ordInfty_div genX_ne_zero genY_ne_zero, ordInfty_genX, ordInfty_genY]
  norm_num

/-- `ordInfty` takes every integer value. -/
theorem ordInfty_surjective (n : ℤ) :
    ∃ f : W.FunctionField, f ≠ 0 ∧ ordInfty W f = n := by
  refine ⟨(CoordinateRing.genX W / CoordinateRing.genY W) ^ n, ?_, ?_⟩
  · exact zpow_ne_zero _ (div_ne_zero genX_ne_zero genY_ne_zero)
  · rw [ordInfty_zpow, ordInfty_genX_div_genY, mul_one]

/-- **Only the constants are regular everywhere.** An element of the coordinate ring — a function
with no poles on the affine chart — which also has no pole at infinity is a constant. -/
theorem exists_eq_algebraMap_of_ordInfty_nonneg {a : W.CoordinateRing} (ha : a ≠ 0)
    (h : 0 ≤ ordInfty W (algebraMap W.CoordinateRing W.FunctionField a)) :
    ∃ c : F, c ≠ 0 ∧ a = algebraMap F W.CoordinateRing c := by
  rw [ordInfty_algebraMap ha, neg_nonneg] at h
  exact exists_eq_algebraMap_of_deg_eq_zero ha (by omega)

/-- **Every function regular at infinity is a constant plus a function vanishing there.**  The
valuation-theoretic form of "the residue field at the point at infinity is `F`": if `0 ≤ ordInfty f`
then `f` is either already a constant, or differs from one by a function of *strictly positive*
order at infinity.

Unlike `exists_eq_algebraMap_of_ordInfty_nonneg`, `f` is only assumed regular **at infinity** — it
may have poles all over the affine chart.  The content is `exists_deg_sub_lt` applied to the
numerator and denominator of `f`, which have equal pole order exactly when `ordInfty f = 0`.

There is no hypothesis on `F`: the point at infinity is rational over any base field. -/
theorem exists_const_ordInfty_sub_pos {f : W.FunctionField} (hf : 0 ≤ ordInfty W f) :
    ∃ c : F, f = algebraMap F W.FunctionField c ∨
      0 < ordInfty W (f - algebraMap F W.FunctionField c) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, Or.inl (map_zero _).symm⟩
  have hinj : Function.Injective (algebraMap W.CoordinateRing W.FunctionField) :=
    IsFractionRing.injective W.CoordinateRing W.FunctionField
  set a := (IsLocalization.sec W.CoordinateRing⁰ f).1 with ha
  set s := (IsLocalization.sec W.CoordinateRing⁰ f).2 with hs
  have hspec : f * algebraMap W.CoordinateRing W.FunctionField (s : W.CoordinateRing)
      = algebraMap W.CoordinateRing W.FunctionField a := IsLocalization.sec_spec _ f
  have hs0 : (s : W.CoordinateRing) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero, mul_eq_zero] at hspec
    rcases hspec with h' | h'
    · exact hf0 h'
    · exact hs0 (hinj (by rw [h', map_zero]))
  have hord : ordInfty W f = (deg W (s : W.CoordinateRing) : ℤ) - deg W a :=
    ordInfty_eq_sub hf0 hs0 hspec
  have hle : deg W a ≤ deg W (s : W.CoordinateRing) := by omega
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact ⟨0, Or.inr (by rw [map_zero, sub_zero]; omega)⟩
  obtain ⟨c, hc⟩ := exists_deg_sub_lt ha0 hs0 heq
  refine ⟨c, ?_⟩
  have hpush : (f - algebraMap F W.FunctionField c)
      * algebraMap W.CoordinateRing W.FunctionField (s : W.CoordinateRing)
      = algebraMap W.CoordinateRing W.FunctionField
        (a - algebraMap F W.CoordinateRing c * (s : W.CoordinateRing)) := by
    rw [map_sub, map_mul, sub_mul, hspec,
      ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]
  rcases eq_or_ne (a - algebraMap F W.CoordinateRing c * (s : W.CoordinateRing)) 0 with hz | hz
  · refine Or.inl ?_
    rw [hz, map_zero] at hpush
    rcases mul_eq_zero.1 hpush with h' | h'
    · exact sub_eq_zero.1 h'
    · exact absurd (hinj (by rw [h', map_zero])) hs0
  · refine Or.inr ?_
    have hdlt : deg W (a - algebraMap F W.CoordinateRing c * (s : W.CoordinateRing))
        < deg W (s : W.CoordinateRing) := hc.resolve_left hz
    have hgne : f - algebraMap F W.FunctionField c ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hpush
      exact hz (hinj (by rw [← hpush, map_zero]))
    rw [ordInfty_eq_sub hgne hs0 hpush]
    omega

section Affine

variable [IsDedekindDomain W.CoordinateRing]

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

/-- A function regular on the affine chart has no pole at any affine closed point. -/
lemma ord_algebraMap_nonneg (v : HeightOneSpectrum W.CoordinateRing) (a : W.CoordinateRing) :
    0 ≤ ord v (algebraMap W.CoordinateRing W.FunctionField a) := by
  rw [ord, ← coeIdeal_span_singleton]
  exact count_coe_nonneg W.FunctionField v _

/-- **The place at infinity is not an affine place.** For every affine closed point `v` there is a
rational function whose order at `v` differs from its order at infinity — the generic
`x`-coordinate, which is regular at `v` but has a double pole at infinity. -/
theorem ord_genX_ne_ordInfty_genX (v : HeightOneSpectrum W.CoordinateRing) :
    ord v (CoordinateRing.genX W) ≠ ordInfty W (CoordinateRing.genX W) := by
  have h := ord_algebraMap_nonneg v (CoordinateRing.mk W (C X))
  rw [ordInfty_genX]
  rw [CoordinateRing.genX, CoordinateRing.genPsi] at *
  omega

end Affine

end WeierstrassCurve.Affine
