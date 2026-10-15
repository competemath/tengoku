/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Caleb L. Geiger
-/
module

public import Tengoku

/-!
# The quadratic order `O_d` — definition and power basis

**Thesis.** §1.2 (Notation) and §3.2, the order
`O = O_d = ℤ[(d + √d)/2] ≅ ℤ[x]/(x² − dx + (d² − d)/4)`.

**This file defines the core object** and its most basic structure:

* `poly d`            — the defining polynomial `X² − dX + (d² − d)/4`
* `QuadraticOrder d`  — the order, as `AdjoinRoot (poly d)`
* `tau`               — the root `τ = (d + √d)/2`
* `tau_minimal_poly`  — `τ` satisfies its defining polynomial
* `basis`             — the rank-2 `ℤ`-power basis `{1, τ}`, with the
  `basis_repr_*` coordinate-extraction helpers
* `dvd_four_of_valid_disc` — `4 ∣ d² − d` under `d ≡ 0, 1 (mod 4)` (shared by
  the discriminant computations downstream)

The norm form lives in `Norm.lean`; the discriminant identity `(τ − tauConj)² = d`
in `Discriminant.lean`.

**Divergence from thesis.** The thesis works over an honest discriminant `d`
(so `d ≡ 0, 1 (mod 4)`). Here `QuadraticOrder d` is *defined for every* `d : ℤ`
via Euclidean division in the constant term; the congruence hypothesis is
introduced only where it is actually needed (see `Discriminant.lean`). For
`d ≢ 0, 1 (mod 4)` the object is still a well-defined quadratic `ℤ`-algebra but
no longer matches the order of discriminant `d`.
-/

@[expose] public section

open scoped Polynomial

/-- The defining polynomial of `QuadraticOrder d`. -/
noncomputable def poly (d : ℤ) : ℤ[X] :=
  Polynomial.X ^ 2 - Polynomial.C d * Polynomial.X + Polynomial.C ((d ^ 2 - d) / 4)

/--
`QuadraticOrder d` is the quadratic `ℤ`-algebra
`ℤ[x] / (x^2 - d * x + (d^2 - d) / 4)`, where the constant term is formed
using Euclidean division in `ℤ`.

For integers `d` with `d ≡ 0, 1 (mod 4)`, this ring coincides with the
(imaginary) quadratic order of discriminant `d` in the quadratic field
`ℚ(√d)`. When `d` does not satisfy these congruence conditions, this
definition should simply be understood as this explicit quadratic
quotient ring over `ℤ`.
-/
abbrev QuadraticOrder (d : ℤ) : Type :=
  AdjoinRoot (poly d)

namespace QuadraticOrder

/-! ### Defining polynomial

We define `poly` before the `variable` command so the auto-binder does not
add a second implicit `d` to its signature. -/

/-- The defining polynomial is monic of degree 2.
@isnad1 id=monic.0h1v.s2.3992cda4a20c from=translated src=- shape=6da4ece3 vocab=da749727
-/
lemma poly_monic (d : ℤ) : (poly d).Monic := by
  have heq : poly d =
      Polynomial.X ^ 2 -
      (Polynomial.C d * Polynomial.X - Polynomial.C ((d ^ 2 - d) / 4)) := by
    unfold poly; ring
  rw [heq]
  apply Polynomial.monic_X_pow_sub
  apply (Polynomial.degree_sub_le _ _).trans_lt
  apply max_lt
  · exact (Polynomial.degree_C_mul_X_le d).trans_lt (by norm_cast)
  · exact Polynomial.degree_C_le.trans_lt (by norm_cast)

/-- The natural degree of the defining polynomial is `2`.
@isnad1 id=eq.0h1v.s3.44bf13a5410d from=translated src=- shape=fcff7bf0 vocab=7d7f8911
-/
lemma poly_natDegree (d : ℤ) : (poly d).natDegree = 2 := by
  unfold poly; compute_degree!

/-- The degree of the defining polynomial is `2`.
@isnad1 id=eq.0h1v.s4.f9671b946acb from=translated src=- shape=a947dcc4 vocab=d6eeb199
-/
lemma poly_degree (d : ℤ) : (poly d).degree = 2 := by
  rw [Polynomial.degree_eq_natDegree (poly_monic d).ne_zero, poly_natDegree]
  rfl

variable {d : ℤ}

/-- The element `τ` corresponding to `(d + √d)/2` in the order. -/
noncomputable def tau : QuadraticOrder d :=
  AdjoinRoot.root _

/-! ### Layer 1: Basic algebraic properties -/

/-- `τ` is a root of the defining polynomial `X² - dX + (d²-d)/4`.

Proof sketch: `aeval τ (poly d) = mk (poly d) (poly d) = 0` by
`AdjoinRoot.aeval_eq` and `AdjoinRoot.mk_self`.
@isnad1 id=eq.0h1v.s7.ea405f9398de from=translated src=- shape=10a7bac9 vocab=eb359f3a
-/
lemma tau_minimal_poly :
    tau ^ 2 - d • tau + ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) = 0 := by
  have h : Polynomial.aeval (tau (d := d)) (poly d) = 0 := by
    unfold tau
    simp_all
  simp only [poly, map_sub, map_add, map_mul, map_pow,
             Polynomial.aeval_X, Polynomial.aeval_C,
             Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
  exact h

/-- `τ` is a root of the defining polynomial `poly d` in `QuadraticOrder d`.
@isnad1 id=eq.0h1v.s7.bc308ee6bae2 from=translated src=- shape=7c273e83 vocab=d0298c99
-/
@[simp] lemma poly_aeval_tau :
    Polynomial.aeval (tau (d := d)) (poly d) = 0 := by
  unfold tau
  simp_all

/-- `QuadraticOrder d` has a `ℤ`-module power basis `{1, τ}` of rank 2. -/
noncomputable def basis : PowerBasis ℤ (QuadraticOrder d) :=
  AdjoinRoot.powerBasis' (poly_monic d)

/-- For an honest discriminant (`d ≡ 0 ∨ 1 (mod 4)`), `4 ∣ d² − d`. This is the
shared arithmetic fact underlying the discriminant computations in
`Discriminant.lean` and `Prime/PolyMod.lean`.
@isnad1 id=dvd.1h1v.s6.46dd38ca53ec from=translated src=- shape=00e4885b vocab=34efd7e3
-/
lemma dvd_four_of_valid_disc (hd : d % 4 = 0 ∨ d % 4 = 1) : (4 : ℤ) ∣ d ^ 2 - d := by
  have hdd : d ^ 2 - d = d * (d - 1) := by ring
  rw [hdd]
  rcases hd with h | h
  · exact Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero h) _
  · exact Dvd.dvd.mul_left (Int.dvd_of_emod_eq_zero (by omega)) _

/-! ### Basis helpers

These extract `(basis.basis.repr α) i` — the τ-component (or 1-component) of a
ring element — via the `modByMonic` representation underlying `AdjoinRoot`'s
`powerBasis'`. -/

/-- The dimension of the power basis equals the degree of the defining
polynomial, namely `2`.
@isnad1 id=eq.0h1v.s5.ed9e93038272 from=translated src=- shape=e716a5af vocab=f2ffce66
-/
@[simp] lemma basis_dim : (basis (d := d)).dim = 2 := poly_natDegree d

/-- The basis-representation coefficient at index `i` is the `i`-th coefficient
of the unique polynomial of degree `< 2` representing `α` (its `modByMonic`
remainder).
@isnad1 id=eq.0h3v.s10.bf22eafe2dab from=translated src=- shape=a57ade31 vocab=edb573c1
-/
lemma basis_repr_apply (α : QuadraticOrder d) (i : Fin (basis (d := d)).dim) :
    (basis.basis.repr α) i =
      (AdjoinRoot.modByMonicHom (poly_monic d) α).coeff i.val :=
  AdjoinRoot.powerBasisAux'_repr_apply_to_fun _ _ _

/-- The τ-coefficient (index `1`) of `τ` itself is `1`.
@isnad1 id=eq.0h1v.s10.2e0479e2a353 from=translated src=- shape=c5204de7 vocab=c089f6e4
-/
lemma basis_repr_tau_one :
    (basis.basis.repr (tau (d := d))) ⟨1, by simp⟩ = 1 := by
  rw [basis_repr_apply]
  have htau_eq : (tau (d := d)) = AdjoinRoot.mk (poly d) Polynomial.X := rfl
  rw [htau_eq, AdjoinRoot.modByMonicHom_mk]
  have hX_mod : Polynomial.X %ₘ poly d = (Polynomial.X : ℤ[X]) := by
    rw [Polynomial.modByMonic_eq_self_iff (poly_monic d), poly_degree,
        Polynomial.degree_X]
    decide
  simp_all

end QuadraticOrder
