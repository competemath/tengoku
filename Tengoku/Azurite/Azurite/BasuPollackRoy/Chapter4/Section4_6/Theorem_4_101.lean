/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_6.Theorem_4_100
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_6.TarskiQuery
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_3.QuadraticForm
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_4.Proposition_2_68
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.RiDecomp
import Tengoku.Seed.LinearAlgebra.Vandermonde

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.6, Theorem 4.101: Multivariate Hermite's quadratic form

Over a real closed field `R`, with `C = R[i] = Ri R`, let `𝒫` be a zero-dimensional system in
`R[X₁, …, X_k]`, `A = R[X]/Ideal(𝒫, R)` and `Q ∈ A`. Then the rank and signature of Hermite's
quadratic form `Her(𝒫, Q)` compute as

* `Rank(Her(𝒫, Q)) = #{x ∈ Zer(𝒫, Cᵏ) | Q(x) ≠ 0}`;
* `Sign(Her(𝒫, Q)) = TaQ(Q, 𝒫)` (the Tarski query — a sum of signs over the real zeros).

The proof transports `Her(𝒫, Q)` to a quadratic form on `Fin N → R` through a basis of `A` and
builds a `DiagonalExpression` of it (§4.3.1), exactly mirroring the univariate Hermite theorem
(BPR Theorem 4.58, `Theorem_4_58.lean`). The diagonal expression is indexed by the distinct zeros
`x ∈ Zer(𝒫, Cᵏ)` at which `Q(x) ≠ 0`; the coefficient of a real zero is the (real) weight
`μ(x) Q(x)`, while a conjugate pair of non-real zeros contributes a difference of two squares of
real linear forms (signature `0`). The linear forms are the evaluations `f ↦ ∑_k f_k ω_k(x)`, whose
linear independence comes from a separating element (Lemma 4.90/4.91) and a Vandermonde argument.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical Matrix
open Azurite.BPR Azurite.BPR.Theorem2_11

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Rank of Hermite's quadratic form** `Rank(Her(𝒫, Q))`: the rank of the quadratic form
`Her(𝒫, Q) = hermiteQuad Ps Q` on `A`, expressed as the sum of its positive and negative inertia
indices (which equals the rank of its Gram matrix in any basis, by Corollary 4.40 / §4.3.1).-/
noncomputable def hermiteFormRank (Ps : Finset (MvPolynomial (Fin k) R)) (Q : quotPolys Ps) : ℕ :=
  sigPos (hermiteQuad Ps Q) + sigNeg (hermiteQuad Ps Q)

/-- **Signature of Hermite's quadratic form** `Sign(Her(𝒫, Q))`: the difference of the positive and
negative inertia indices of `Her(𝒫, Q) = hermiteQuad Ps Q`.-/
noncomputable def hermiteFormSign (Ps : Finset (MvPolynomial (Fin k) R)) (Q : quotPolys Ps) : ℤ :=
  (sigPos (hermiteQuad Ps Q) : ℤ) - sigNeg (hermiteQuad Ps Q)

/-! ## The geometric bridge

Mapping `her(𝒫, Q')(u, w)` into `C = Ri R` gives the geometric sum
`∑_x μ(x) · u(x) · w(x) · Q'(x)` over the zeros. This generalizes `hermite_bridge` (the `Q' = 1`
case) to an arbitrary `Q' ∈ A`. -/

/-! ## Multivariate Hermite data over `C = Ri R` -/

namespace MvHermite

set_option linter.unusedSectionVars false

attribute [local instance] algebraLocalizationAtPoint

/-- Componentwise conjugation of a tuple `x : Fin k → Ri R`.-/
noncomputable def conjTuple (x : Fin k → Ri R) : Fin k → Ri R := fun i => Ri.conj R (x i)

/--
@isnad1 id=eq.0h4v.s10.60298b74f5e0 from=translated src=- shape=81d9eb19 vocab=c70937c9
-/
@[simp] theorem conjTuple_apply (x : Fin k → Ri R) (i : Fin k) :
    conjTuple x i = Ri.conj R (x i) := rfl

/--
@isnad1 id=involuti.0h2v.s5.836518e7c6d2 from=translated src=- shape=b6a0f4e0 vocab=c965d5c5
-/
theorem conjTuple_involutive : Function.Involutive (conjTuple (R := R) (k := k)) := by
  intro x; funext i; simp [conjTuple, Ri.conj_conj]

/--
@isnad1 id=eq.0h3v.s5.a9f80ca3e955 from=translated src=- shape=f114c5ea vocab=d74b385a
-/
@[simp] theorem conjTuple_conjTuple (x : Fin k → Ri R) : conjTuple (conjTuple x) = x :=
  conjTuple_involutive x

/-- `aeval (conjTuple x) P = conj (aeval x P)` for a polynomial `P` with `R`-coefficients.
@isnad1 id=eq.0h4v.s11.52f766752cfe from=translated src=- shape=118a525c vocab=b5a3f5a3
-/
theorem aeval_conjTuple (P : MvPolynomial (Fin k) R) (x : Fin k → Ri R) :
    aeval (conjTuple x) P = Ri.conj R (aeval x P) := by
  have hcomp : (Ri.conj R).comp (aeval x) = aeval (conjTuple x) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    rfl
  have := AlgHom.congr_fun hcomp P
  rw [AlgHom.comp_apply] at this
  exact this.symm

/-- The conjugate of a zero is a zero (the members of `𝒫` have `R`-coefficients).
@isnad1 id=mem.1h4v.s9.a1c3008286b3 from=translated src=- shape=e4adcffb vocab=ac5ede15
-/
theorem conjTuple_mem_zer {Ps : Finset (MvPolynomial (Fin k) R)} {x : Fin k → Ri R}
    (hx : x ∈ zerOfFinset (Ri R) Ps) : conjTuple x ∈ zerOfFinset (Ri R) Ps := by
  intro p hp
  rw [aeval_conjTuple, hx p hp, map_zero]

/--
@isnad1 id=mem.2h4v.s10.55b804b488be from=translated src=- shape=d7d01a73 vocab=114587a3
-/
theorem conjTuple_mem_toFinset {Ps : Finset (MvPolynomial (Fin k) R)}
    (hfin : (zerOfFinset (Ri R) Ps).Finite) {x : Fin k → Ri R}
    (hx : x ∈ hfin.toFinset) : conjTuple x ∈ hfin.toFinset :=
  hfin.mem_toFinset.mpr (conjTuple_mem_zer (hfin.mem_toFinset.mp hx))

/-- The multiplicity `μ(x)` of a tuple `x` (zero outside `Zer(𝒫, Cᵏ)`).-/
noncomputable def mult (Ps : Finset (MvPolynomial (Fin k) R)) (x : Fin k → Ri R) : ℕ :=
  if h : x ∈ zerOfFinset (Ri R) Ps then multiplicityOfZero (Ri R) Ps x h else 0

/-- The weight `μ(x)·Q(x)` of a tuple `x`.-/
noncomputable def mvHerWeight (Ps : Finset (MvPolynomial (Fin k) R))
    (Q : MvPolynomial (Fin k) R) (x : Fin k → Ri R) : Ri R :=
  (mult Ps x) • MvPolynomial.aeval x Q

/-- The finset of distinct zeros over `C` at which `Q` does not vanish.-/
noncomputable def mvHerRoots (Ps : Finset (MvPolynomial (Fin k) R))
    (Q : MvPolynomial (Fin k) R) (hfin : (zerOfFinset (Ri R) Ps).Finite) :
    Finset (Fin k → Ri R) :=
  hfin.toFinset.filter (fun x => MvPolynomial.aeval x Q ≠ 0)

/--
@isnad1 id=iff.1h5v.s11.1ce17747002a from=translated src=- shape=30ac4219 vocab=fe8fc7cc
-/
theorem mem_mvHerRoots_iff {Ps : Finset (MvPolynomial (Fin k) R)}
    {Q : MvPolynomial (Fin k) R} {hfin : (zerOfFinset (Ri R) Ps).Finite} {x : Fin k → Ri R} :
    x ∈ mvHerRoots Ps Q hfin ↔ x ∈ zerOfFinset (Ri R) Ps ∧ MvPolynomial.aeval x Q ≠ 0 := by
  rw [mvHerRoots, Finset.mem_filter, hfin.mem_toFinset]

/-! ### Multiplicity is conjugation invariant (keystone, BPR Route A) -/

/-! ### Real/imaginary arithmetic in `Ri R` (helpers; mirror §4.3) -/

/--
@isnad1 id=eq.1h2v.s12.b15280c0a3de from=translated src=- shape=3bcbbdbc vocab=cbb8d9f3
-/
theorem algebraMap_reL_of_conj_fixed {z : Ri R} (hz : Ri.conj R z = z) :
    algebraMap R (Ri R) (Ri.reL z) = z := by
  obtain ⟨a, hra⟩ := Ri.conj_fixed_mem_range_ordered z hz
  have hreL : Ri.reL z = a := by
    rw [← hra, show algebraMap R (Ri R) a = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a from rfl,
      Ri.reL_of]
  rw [hreL, hra]

/--
@isnad1 id=eq.0h3v.s12.7da6584932ad from=translated src=- shape=0ad65bb7 vocab=d68a30dc
-/
theorem reL_mul (c d : Ri R) :
    Ri.reL (c * d) = Ri.reL c * Ri.reL d - Ri.imL c * Ri.imL d := by
  have hi2 : Ri.i R ^ 2 = -1 := Ri.i_sq R
  conv_lhs => rw [← Ri.of_reL_add_of_imL_mul_i c, ← Ri.of_reL_add_of_imL_mul_i d]
  rw [show (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c)
            + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c) * Ri.i R)
          * (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL d)
            + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL d) * Ri.i R)
        = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c * Ri.reL d - Ri.imL c * Ri.imL d)
          + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c * Ri.imL d + Ri.imL c * Ri.reL d) * Ri.i R
      from by
        simp only [map_sub, map_add, map_mul]
        linear_combination (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c)
          * AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL d)) * hi2]
  rw [Ri.reL_lin]

/--
@isnad1 id=eq.0h3v.s12.d21c6b43fc9e from=translated src=- shape=062b6080 vocab=8bf67038
-/
theorem imL_mul (c d : Ri R) :
    Ri.imL (c * d) = Ri.reL c * Ri.imL d + Ri.imL c * Ri.reL d := by
  have hi2 : Ri.i R ^ 2 = -1 := Ri.i_sq R
  conv_lhs => rw [← Ri.of_reL_add_of_imL_mul_i c, ← Ri.of_reL_add_of_imL_mul_i d]
  rw [show (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c)
            + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c) * Ri.i R)
          * (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL d)
            + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL d) * Ri.i R)
        = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c * Ri.reL d - Ri.imL c * Ri.imL d)
          + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c * Ri.imL d + Ri.imL c * Ri.reL d) * Ri.i R
      from by
        simp only [map_sub, map_add, map_mul]
        linear_combination (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c)
          * AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL d)) * hi2]
  rw [Ri.imL_lin]

/--
@isnad1 id=eq.0h2v.s12.cf1bce9a3f0d from=translated src=- shape=2d70ef43 vocab=10fbb0df
-/
theorem conj_add_self (c : Ri R) :
    c + Ri.conj R c = algebraMap R (Ri R) (2 * Ri.reL c) := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists c
  have hreL : Ri.reL c = a := by
    rw [hab, show algebraMap R (Ri R) a = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a from rfl,
      show algebraMap R (Ri R) b = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) b from rfl, Ri.reL_lin]
  rw [hreL, hab, Ri.conj_repr, two_mul, map_add]
  ring

/--
@isnad1 id=eq.0h2v.s11.65bd50ce1581 from=translated src=- shape=2bcdabf6 vocab=2718bc3e
-/
theorem reL_sq (c : Ri R) : Ri.reL (c ^ 2) = Ri.reL c ^ 2 - Ri.imL c ^ 2 := by
  rw [show (c : Ri R) ^ 2 = c * c from pow_two c, reL_mul]; ring

/--
@isnad1 id=eq.0h2v.s11.b691ae76812c from=translated src=- shape=7633a0ce vocab=70de2984
-/
theorem reL_conj (c : Ri R) : Ri.reL (Ri.conj R c) = Ri.reL c := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists c
  have hreL : Ri.reL c = a := by
    rw [hab, show algebraMap R (Ri R) a = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a from rfl,
      show algebraMap R (Ri R) b = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) b from rfl, Ri.reL_lin]
  rw [hreL, hab, Ri.conj_repr]
  rw [show algebraMap R (Ri R) a = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a from rfl,
    show algebraMap R (Ri R) b = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) b from rfl]
  rw [sub_eq_add_neg, ← neg_mul, ← map_neg]
  rw [Ri.reL_lin a (-b)]

/--
@isnad1 id=eq.0h2v.s11.79b60d7ce8de from=translated src=- shape=e0fb0bb3 vocab=3875d030
-/
theorem imL_conj (x : Ri R) : Ri.imL (Ri.conj R x) = - Ri.imL x := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists x
  rw [hab, Ri.conj_repr]
  rw [show algebraMap R (Ri R) a = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a from rfl,
    show algebraMap R (Ri R) b = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) b from rfl]
  rw [sub_eq_add_neg, ← neg_mul, ← map_neg]
  rw [Ri.imL_lin a b, Ri.imL_lin a (-b)]

/--
@isnad1 id=ne.1h2v.s11.278f04654acb from=translated src=- shape=654a8285 vocab=45409256
-/
theorem imL_ne_zero_of_not_real {x : Ri R} (hx : Ri.conj R x ≠ x) : Ri.imL x ≠ 0 := by
  intro h
  apply hx
  obtain ⟨a, b, hab⟩ := Ri.repr_exists x
  have hb : b = 0 := by
    have := hab ▸ h
    rwa [show algebraMap R (Ri R) a = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a from rfl,
      show algebraMap R (Ri R) b = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) b from rfl,
      Ri.imL_lin a b] at this
  rw [hab, hb, map_zero, zero_mul, add_zero, Ri.conj_algebraMap_ordered]

/-! ### A separating element and the conjugate-pair selector -/

/-- A chosen separating polynomial for `𝒫` over `C = Ri R` (Lemma 4.90).-/
noncomputable def sepElt (Ps : Finset (MvPolynomial (Fin k) R))
    [CharZero R] (hfin : (zerOfFinset (Ri R) Ps).Finite) : MvPolynomial (Fin k) R :=
  linearForm (K := R) (lemma_4_90 (K := R) (Ri R) Ps hfin).choose

/-- The chosen separating element separates the zeros: distinct zeros get distinct values.
@isnad1 id=eq.4h5v.s11.9893f8a2ad5c from=translated src=- shape=c6371b68 vocab=bcd3792e
-/
theorem sepElt_separating (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    (hfin : (zerOfFinset (Ri R) Ps).Finite) {x y : Fin k → Ri R}
    (hx : x ∈ zerOfFinset (Ri R) Ps) (hy : y ∈ zerOfFinset (Ri R) Ps)
    (h : MvPolynomial.aeval x (sepElt Ps hfin) = MvPolynomial.aeval y (sepElt Ps hfin)) :
    x = y := by
  have hsep := (lemma_4_90 (K := R) (Ri R) Ps hfin).choose_spec.2
  have := hsep x hx y hy
  rw [valueAt_mk, valueAt_mk] at this
  exact this h

/-- The conjugate-pair selector: `posRep x` holds when the separating value `a(x)` has positive
imaginary part. For a non-real zero `x` it holds for exactly one of `x`, `conjTuple x`.-/
noncomputable def posRep (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    (hfin : (zerOfFinset (Ri R) Ps).Finite) (x : Fin k → Ri R) : Prop :=
  0 < Ri.imL (MvPolynomial.aeval x (sepElt Ps hfin))

/-- For a non-real zero `x`, the separating value `a(x)` is non-real.
@isnad1 id=ne.3h4v.s11.2a56bdf88beb from=translated src=- shape=b79ac889 vocab=2d29bf63
-/
theorem imL_sepVal_ne_zero (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    (hfin : (zerOfFinset (Ri R) Ps).Finite) {x : Fin k → Ri R}
    (hx : x ∈ zerOfFinset (Ri R) Ps) (hxr : conjTuple x ≠ x) :
    Ri.imL (MvPolynomial.aeval x (sepElt Ps hfin)) ≠ 0 := by
  apply imL_ne_zero_of_not_real
  intro hfix
  apply hxr
  -- `a(x)` conj-fixed ⟹ `a(conjTuple x) = a(x)` ⟹ `conjTuple x = x` by separation
  have hcx : conjTuple x ∈ zerOfFinset (Ri R) Ps := conjTuple_mem_zer hx
  have hval : MvPolynomial.aeval (conjTuple x) (sepElt Ps hfin)
      = MvPolynomial.aeval x (sepElt Ps hfin) := by
    rw [aeval_conjTuple, hfix]
  exact sepElt_separating Ps hfin hcx hx hval

/-- The selector splits a non-real conjugate pair: `posRep x ↔ ¬ posRep (conjTuple x)`.
@isnad1 id=iff.3h4v.s9.ea8dc2c67481 from=translated src=- shape=5f6bf0a1 vocab=b8276487
-/
theorem posRep_conjTuple_iff (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    (hfin : (zerOfFinset (Ri R) Ps).Finite) {x : Fin k → Ri R}
    (hx : x ∈ zerOfFinset (Ri R) Ps) (hxr : conjTuple x ≠ x) :
    posRep Ps hfin x ↔ ¬ posRep Ps hfin (conjTuple x) := by
  unfold posRep
  rw [aeval_conjTuple, imL_conj]
  have hne := imL_sepVal_ne_zero Ps hfin hx hxr
  constructor
  · intro h; rw [not_lt]; exact (neg_nonpos.mpr h.le)
  · intro h
    rw [not_lt, neg_le, neg_zero] at h
    exact lt_of_le_of_ne h (Ne.symm hne)

/-! ### Basis of `A` and polynomial representatives -/

/-- The rank `N = dim_R A`.-/
noncomputable def mvN (Ps : Finset (MvPolynomial (Fin k) R)) : ℕ :=
  Module.finrank R (quotPolys Ps)

/-- A chosen `R`-basis of `A = quotPolys Ps`, indexed by `Fin N`.-/
noncomputable def mvBasis (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] : Module.Basis (Fin (mvN Ps)) R (quotPolys Ps) :=
  Module.finBasis R (quotPolys Ps)

/-- Polynomial representatives `ω j` of the basis elements: `mk (ω j) = B j`.-/
noncomputable def mvRep (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] (j : Fin (mvN Ps)) : MvPolynomial (Fin k) R :=
  (Ideal.Quotient.mk_surjective (mvBasis Ps j)).choose

/--
@isnad1 id=eq.0h4v.s10.9d4a84f79a67 from=translated src=- shape=69beec84 vocab=2000c535
-/
theorem mvRep_spec (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] (j : Fin (mvN Ps)) :
    Ideal.Quotient.mk (idealOfPolys Ps) (mvRep Ps j) = mvBasis Ps j :=
  (Ideal.Quotient.mk_surjective (mvBasis Ps j)).choose_spec

/-- `valueAt (B j) x = aeval x (ω j)`.
@isnad1 id=eq.1h5v.s11.47cd03b1bd95 from=translated src=- shape=5515d27c vocab=27e85cb9
-/
theorem valueAt_mvBasis (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] {x : Fin k → Ri R} (hx : x ∈ zerOfFinset (Ri R) Ps)
    (j : Fin (mvN Ps)) :
    valueAt (Ri R) Ps (mvBasis Ps j) x hx = MvPolynomial.aeval x (mvRep Ps j) := by
  rw [← mvRep_spec Ps j, valueAt_mk]

/-- `valueAt` of any `g ∈ A` expands over the basis: `g(x) = ∑_j (B.repr g j) · ω_j(x)`.
@isnad1 id=eq.1h5v.s12.ca752b7f5f67 from=translated src=- shape=7901641f vocab=cd28ab95
-/
theorem valueAt_eq_sum (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] {x : Fin k → Ri R} (hx : x ∈ zerOfFinset (Ri R) Ps)
    (g : quotPolys Ps) :
    valueAt (Ri R) Ps g x hx
      = ∑ j, algebraMap R (Ri R) ((mvBasis Ps).repr g j) * MvPolynomial.aeval x (mvRep Ps j) := by
  set φ : quotPolys Ps →+* Ri R := (evalBar (Ri R) Ps x hx).comp (inclExt (Ri R) Ps) with hφ
  have hval : ∀ g', valueAt (Ri R) Ps g' x hx = φ g' := fun g' => rfl
  -- `φ` sends `algebraMap R c` to `algebraMap R (Ri R) c`
  have hφalg : ∀ c : R, φ (algebraMap R (quotPolys Ps) c) = algebraMap R (Ri R) c := by
    intro c
    rw [← hval, show algebraMap R (quotPolys Ps) c = Ideal.Quotient.mk _ (MvPolynomial.C c) from rfl,
      valueAt_mk, MvPolynomial.aeval_C]
  -- `φ` pushes through `R`-scalars
  have hφsmul : ∀ (c : R) (a : quotPolys Ps), φ (c • a) = algebraMap R (Ri R) c * φ a := by
    intro c a
    rw [Algebra.smul_def (R := R) (A := quotPolys Ps), map_mul, hφalg]
  rw [hval]
  conv_lhs => rw [← (mvBasis Ps).sum_repr g]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hφsmul, ← hval (mvBasis Ps j), valueAt_mvBasis Ps hx j]

/-! ### Hermite coefficients and form vectors -/

/-- A chosen square root in `C = Ri R` of the weight `μ(x)·Q(x)`.-/
noncomputable def mvHerSqrt (Ps : Finset (MvPolynomial (Fin k) R))
    (Q : MvPolynomial (Fin k) R) (x : Fin k → Ri R) : Ri R :=
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  (IsAlgClosed.exists_pow_nat_eq (mvHerWeight Ps Q x) (n := 2) (by norm_num)).choose

/-- The coefficient attached to a zero `x`:
* real `x` (`conjTuple x = x`): the real weight `reL (μ(x)·Q(x))`;
* non-real `x` with `posRep`: `+2`; otherwise `-2`.-/
noncomputable def mvHerCoeff (Ps : Finset (MvPolynomial (Fin k) R))
    (Q : MvPolynomial (Fin k) R) (hfin : (zerOfFinset (Ri R) Ps).Finite)
    (x : Fin k → Ri R) : R :=
  if conjTuple x = x then Ri.reL (mvHerWeight Ps Q x)
  else if posRep Ps hfin x then 2 else -2

/-- The coefficient vector (in `R^N`) of the linear form attached to a zero `x`, mirroring §4.3
`herFormVec` with `x^k` replaced by `ω_j(x)`.-/
noncomputable def mvHerFormVec (Ps : Finset (MvPolynomial (Fin k) R))
    (Q : MvPolynomial (Fin k) R) (hfin : (zerOfFinset (Ri R) Ps).Finite)
    [Module.Finite R (quotPolys Ps)] (x : Fin k → Ri R) : Fin (mvN Ps) → R :=
  if conjTuple x = x then fun j => Ri.reL (MvPolynomial.aeval x (mvRep Ps j))
  else if posRep Ps hfin x then
    (fun j => Ri.reL (mvHerSqrt Ps Q x) * Ri.reL (MvPolynomial.aeval x (mvRep Ps j))
                - Ri.imL (mvHerSqrt Ps Q x) * Ri.imL (MvPolynomial.aeval x (mvRep Ps j)))
  else
    (fun j => Ri.reL (mvHerSqrt Ps Q (conjTuple x)) * Ri.imL (MvPolynomial.aeval (conjTuple x) (mvRep Ps j))
                + Ri.imL (mvHerSqrt Ps Q (conjTuple x)) * Ri.reL (MvPolynomial.aeval (conjTuple x) (mvRep Ps j)))

/-- The linear form `f ↦ v ⬝ᵥ f` with coefficient vector `v`.-/
def mvHerDotLM {N : ℕ} (v : Fin N → R) : (Fin N → R) →ₗ[R] R where
  toFun f := v ⬝ᵥ f
  map_add' := dotProduct_add v
  map_smul' c f := by simp [dotProduct_smul]

/--
@isnad1 id=eq.0h4v.s8.c3044151ae0b from=translated src=- shape=5d7c26cd vocab=27f87ee8
-/
theorem mvHerDotLM_apply {N : ℕ} (v f : Fin N → R) : mvHerDotLM v f = v ⬝ᵥ f := rfl

/-! ### Conjugation facts on `mvHerRoots` -/

/-- Conjugation maps `mvHerRoots` to itself.
@isnad1 id=mem.2h5v.s9.c55ae02209ad from=translated src=- shape=0867b59e vocab=6ea0105d
-/
theorem conjTuple_mem_mvHerRoots {Ps : Finset (MvPolynomial (Fin k) R)}
    {Q : MvPolynomial (Fin k) R} {hfin : (zerOfFinset (Ri R) Ps).Finite} {x : Fin k → Ri R}
    (hx : x ∈ mvHerRoots Ps Q hfin) : conjTuple x ∈ mvHerRoots Ps Q hfin := by
  rw [mem_mvHerRoots_iff] at hx ⊢
  refine ⟨conjTuple_mem_zer hx.1, ?_⟩
  rw [aeval_conjTuple]
  intro h
  exact hx.2 (by have := congrArg (Ri.conj R) h; rwa [Ri.conj_conj, map_zero] at this)

/-! ### Independence via a separating element -/

/-- The number of distinct zeros in `mvHerRoots` is at most `#zeros = n`.
@isnad1 id=le.1h4v.s9.485d75c913bf from=translated src=- shape=71b58f3b vocab=5e6d4de7
-/
theorem card_mvHerRoots_le (Ps : Finset (MvPolynomial (Fin k) R))
    (Q : MvPolynomial (Fin k) R) (hfin : (zerOfFinset (Ri R) Ps).Finite) :
    (mvHerRoots Ps Q hfin).card ≤ hfin.toFinset.card := by
  rw [mvHerRoots]
  exact Finset.card_filter_le _ _

/-- **Independence of the evaluation vectors.** The vectors `(j ↦ ω_j(x))` for the distinct zeros
`x ∈ mvHerRoots` are `Ri R`-linearly independent. (Separation makes the values `a(x)` distinct, so
a Vandermonde argument in `a(x)` forces all coefficients to vanish.)
@isnad1 id=linearin.1h4v.s11.e6ef63ef3651 from=translated src=- shape=1b5a684d vocab=55724a56
-/
theorem mvEval_indep (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R)
    (hfin : (zerOfFinset (Ri R) Ps).Finite) :
    LinearIndependent (Ri R)
      (fun j : Fin (mvHerRoots Ps Q hfin).card =>
        (fun l : Fin (mvN Ps) =>
          MvPolynomial.aeval ((mvHerRoots Ps Q hfin).equivFin.symm j : Fin k → Ri R)
            (mvRep Ps l))) := by
  classical
  have : IsAlgClosed (Ri R) := isAlgClosed_Ri
  have : CharZero (Ri R) := charZero_of_injective_algebraMap (algebraMap R (Ri R)).injective
  set r := (mvHerRoots Ps Q hfin).card with hr
  set xs : Fin r → (Fin k → Ri R) :=
    fun j => ((mvHerRoots Ps Q hfin).equivFin.symm j : Fin k → Ri R) with hxs
  -- each `xs j` is a zero
  have hxmem : ∀ j, xs j ∈ zerOfFinset (Ri R) Ps := fun j =>
    (mem_mvHerRoots_iff.mp ((mvHerRoots Ps Q hfin).equivFin.symm j).2).1
  -- separating values
  set av : Fin r → Ri R := fun j => MvPolynomial.aeval (xs j) (sepElt Ps hfin) with hav
  have hav_inj : Function.Injective av := by
    intro a b hab
    have := sepElt_separating Ps hfin (hxmem a) (hxmem b) hab
    exact (mvHerRoots Ps Q hfin).equivFin.symm.injective (Subtype.ext this)
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- `hc` : for all l, ∑ j, c j • (ω_l (xs j)) = 0
  have hcl : ∀ l : Fin (mvN Ps), ∑ j, c j * MvPolynomial.aeval (xs j) (mvRep Ps l) = 0 := by
    intro l
    have := congrFun hc l
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
  -- for any `g ∈ A`, ∑ j, c j • valueAt(g, xs j) = 0
  have hg : ∀ g : quotPolys Ps,
      ∑ j, c j * valueAt (Ri R) Ps g (xs j) (hxmem j) = 0 := by
    intro g
    have hexp : ∀ j, valueAt (Ri R) Ps g (xs j) (hxmem j)
        = ∑ l, algebraMap R (Ri R) ((mvBasis Ps).repr g l)
            * MvPolynomial.aeval (xs j) (mvRep Ps l) :=
      fun j => valueAt_eq_sum Ps (hxmem j) g
    calc ∑ j, c j * valueAt (Ri R) Ps g (xs j) (hxmem j)
        = ∑ j, ∑ l, c j * (algebraMap R (Ri R) ((mvBasis Ps).repr g l)
            * MvPolynomial.aeval (xs j) (mvRep Ps l)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hexp j, Finset.mul_sum]
      _ = ∑ l, algebraMap R (Ri R) ((mvBasis Ps).repr g l)
            * ∑ j, c j * MvPolynomial.aeval (xs j) (mvRep Ps l) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 0 := by
          refine Finset.sum_eq_zero fun l _ => ?_
          rw [hcl l, mul_zero]
  -- apply with `g = a^i`
  set a : quotPolys Ps := Ideal.Quotient.mk _ (sepElt Ps hfin) with ha
  have hpow : ∀ (i : Fin r) (j : Fin r),
      valueAt (Ri R) Ps (a ^ (i : ℕ)) (xs j) (hxmem j) = av j ^ (i : ℕ) := by
    intro i j
    rw [ha, ← map_pow, valueAt_mk, hav, ← map_pow]
  have hvand : ∀ i : Fin r, ∑ j, c j * av j ^ (i : ℕ) = 0 := by
    intro i
    have := hg (a ^ (i : ℕ))
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hpow i j]
  exact congrFun (Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hav_inj hvand)

/-! ### The transported quadratic form and its diagonal expression -/

/-- The Hermite form transported to `Fin N → R` via the basis.-/
noncomputable def mvHerQuad (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R) :
    QuadraticForm R (Fin (mvN Ps) → R) :=
  (hermiteQuad Ps (Ideal.Quotient.mk (idealOfPolys Ps) Q)).basisRepr (mvBasis Ps)

/-- `hermiteQuad Ps Q' g = hermiteBilin Ps Q' g g`.
@isnad1 id=eq.0h5v.s11.409d23aeb9b3 from=translated src=- shape=f1b68d00 vocab=9d5385aa
-/
theorem hermiteQuad_eq_bilin (Ps : Finset (MvPolynomial (Fin k) R)) (Q' g : quotPolys Ps) :
    hermiteQuad Ps Q' g = hermiteBilin Ps Q' g g := by
  rw [hermiteQuad, LinearMap.BilinMap.toQuadraticMap_apply]

/-- The isometry between `hermiteQuad Ps (mk Q)` and its basis representation `mvHerQuad`.
@isnad1 id=equivale.0h4v.s10.2fdc373951e8 from=translated src=- shape=5d02f9cc vocab=38e3ff6b
-/
theorem mvHerQuad_equiv (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R) :
    QuadraticMap.Equivalent (hermiteQuad Ps (Ideal.Quotient.mk (idealOfPolys Ps) Q))
      (mvHerQuad Ps Q) :=
  ⟨QuadraticMap.isometryEquivBasisRepr _ (mvBasis Ps)⟩

/-- Reindexing helper (local copy of §4.3 `card_filter_equivFin`).
@isnad1 id=eq.0h3v.s8.9873fb4213b0 from=translated src=- shape=4663cf80 vocab=d5b744fe
-/
theorem card_filter_equivFin {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun j : Fin s.card => P (s.equivFin.symm j : α))).card
      = (s.filter P).card := by
  classical
  refine Finset.card_bij' (fun j _ => (s.equivFin.symm j : α))
    (fun a ha => s.equivFin ⟨a, (Finset.mem_filter.mp ha).1⟩) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨(s.equivFin.symm j).2, hj.2⟩
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact ha.2
  · intro j _
    rw [Equiv.apply_symm_apply]
  · intro a ha
    simp

/-- Local copy of §4.3 `card_pos_sub_card_neg_eq_sum_sign`.
@isnad1 id=eq.1h4v.s8.d512016295b6 from=translated src=- shape=66ff54ed vocab=eb8c9fff
-/
theorem card_pos_sub_card_neg_eq_sum_sign {α : Type*} (s : Finset α) (c : α → R)
    (hc : ∀ x ∈ s, c x ≠ 0) :
    ((s.filter (fun x => 0 < c x)).card : ℤ) - (s.filter (fun x => c x < 0)).card
      = ∑ x ∈ s, (SignType.sign (c x) : ℤ) := by
  classical
  rw [Finset.card_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rcases lt_or_gt_of_ne (hc x hx) with hneg | hpos
  · rw [ite_eq_right (not_lt.mpr hneg.le), ite_eq_left hneg, sign_neg hneg]; simp
  · rw [ite_eq_left hpos, ite_eq_right (not_lt.mpr hpos.le), sign_pos hpos]; simp

/-! ### The signature sum equals the Tarski query -/

/-- A conj-fixed tuple has each coordinate conj-fixed, hence comes from a real point.
@isnad1 id=eq.1h4v.s11.60b391810c13 from=translated src=- shape=209c1793 vocab=9af18ce1
-/
theorem algebraMap_reL_tuple_of_conj_fixed {x : Fin k → Ri R} (hxr : conjTuple x = x) (i : Fin k) :
    algebraMap R (Ri R) (Ri.reL (x i)) = x i := by
  apply algebraMap_reL_of_conj_fixed
  have := congrFun hxr i
  rwa [conjTuple_apply] at this

omit [IsRealClosed R] in
/-- `aeval (algebraMap ∘ y) P = algebraMap (aeval y P)` for `y : Fin k → R`.
@isnad1 id=eq.0h4v.s12.cf681fd099c7 from=translated src=- shape=a6eb14e9 vocab=1d02820e
-/
theorem aeval_algebraMap_tuple (P : MvPolynomial (Fin k) R) (y : Fin k → R) :
    MvPolynomial.aeval (fun i => algebraMap R (Ri R) (y i)) P
      = algebraMap R (Ri R) (MvPolynomial.aeval y P) := by
  have hcomp : (IsScalarTower.toAlgHom R R (Ri R)).comp (MvPolynomial.aeval y)
      = MvPolynomial.aeval (fun i => algebraMap R (Ri R) (y i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      IsScalarTower.toAlgHom_apply]
  have := AlgHom.congr_fun hcomp P
  rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] at this
  exact this.symm

/-- A real zero `y` over `R` gives a conj-fixed zero `algebraMap ∘ y` over `C`.
@isnad1 id=mem.1h4v.s11.131f93a76c67 from=translated src=- shape=62c00c83 vocab=a4c98a53
-/
theorem algebraMap_tuple_mem_zer {Ps : Finset (MvPolynomial (Fin k) R)} {y : Fin k → R}
    (hy : y ∈ zerOfFinset R Ps) :
    (fun i => algebraMap R (Ri R) (y i)) ∈ zerOfFinset (Ri R) Ps := by
  intro p hp
  rw [aeval_algebraMap_tuple, hy p hp, map_zero]

end MvHermite

/-- **Finiteness of the complex zero set from finite-dimensionality.** When `A = R[X]/Ideal(𝒫, R)`
is finite-dimensional, the set `Zer(𝒫, Cᵏ)` of zeros over the algebraic closure `C = Ri R` is
finite. This is the `R`-finiteness direction of Theorem 4.86 (`FiniteDimensional R A ↔
Zer(𝒫, Cᵏ).Finite`), so `hfinC` need not be assumed separately.
@isnad1 id=finite.0h3v.s9.cab442aa73fa from=translated src=- shape=20db9345 vocab=f686441c
-/
theorem zerOfFinset_finite_of_moduleFinite (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] : (zerOfFinset (Ri R) Ps).Finite := by
  have : IsAlgClosed (Ri R) := isAlgClosed_Ri
  have : CharZero R := inferInstance
  have hfd : FiniteDimensional R (quotPolys Ps) ↔ (zerOfFinset (Ri R) Ps).Finite := by
    rw [(lemma_4_88 (Ri R) Ps).2, finiteDimensional_ext_iff_isIntegral, isIntegral_iff_finite]
  exact hfd.mp inferInstance

end Azurite.BPR.Chapter4
