/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Polynomial.Div
import Tengoku.Seed.Algebra.Polynomial.Lifts
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# algebraic input for Hensel's lemma

This file records the residue-polynomial data used at the start of the
proof of Hensel's lemma.  The analytic convergence step is kept separate; the
lemmas here are the initial lifts and congruences.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- Polynomial coefficient maps distribute over `f - g*h`, the first Hensel
congruence expression.
@isnad1 id=eq.0h6v.s8.5c5405d782c2 from=translated src=- shape=d744ed54 vocab=97ee786c
-/
theorem henselFactorization_map_sub_mul
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    (f g h : R[X]) :
    (f - g * h).map φ = f.map φ - g.map φ * h.map φ := by
  simp [Polynomial.map_sub, Polynomial.map_mul]

/-- Polynomial coefficient maps distribute over `g*q - A`, the product
congruence used to bound the high coefficients of the quotient.
@isnad1 id=eq.0h6v.s8.d05de3c8ee83 from=translated src=- shape=be064508 vocab=97ee786c
-/
theorem henselFactorization_map_mul_sub
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    (g q A : R[X]) :
    (g * q - A).map φ = g.map φ * q.map φ - A.map φ := by
  simp [Polynomial.map_sub, Polynomial.map_mul]

/-- Polynomial coefficient maps distribute over the Hensel correction expression
`g*q + h*p - fn`.
@isnad1 id=eq.0h8v.s8.ee1261a3bdb6 from=translated src=- shape=e9ccf6c9 vocab=bc21d3ac
-/
theorem henselFactorization_map_mul_add_mul_sub
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    (g h q p fn : R[X]) :
    (g * q + h * p - fn).map φ =
      g.map φ * q.map φ + h.map φ * p.map φ - fn.map φ := by
  simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul]

/-- unit-leading input: a lift with the same natural degree as
a nonzero residual polynomial has unit leading coefficient.
@isnad1 id=isunit.3h3v.s7.1fb36c363da0 from=translated src=- shape=8fa093b3 vocab=1b1a36c1
-/
theorem henselFactorization_lift_leadingCoeff_isUnit_of_natDegree_eq
    {R : Type*} [CommRing R] [IsLocalRing R]
    {g0 : R[X]} {gbar : (IsLocalRing.ResidueField R)[X]}
    (hg0 : g0.map (IsLocalRing.residue R) = gbar)
    (hdegree : g0.natDegree = gbar.natDegree)
    (hlead : gbar.leadingCoeff ≠ 0) :
    IsUnit g0.leadingCoeff := by
  have hcoeff :=
    congrArg (fun P : (IsLocalRing.ResidueField R)[X] =>
      P.coeff gbar.natDegree) hg0
  have hres_lead :
      IsLocalRing.residue R g0.leadingCoeff = gbar.leadingCoeff := by
    change (g0.map (IsLocalRing.residue R)).coeff gbar.natDegree =
      gbar.coeff gbar.natDegree at hcoeff
    rw [Polynomial.coeff_map] at hcoeff
    change IsLocalRing.residue R (g0.coeff g0.natDegree) =
      gbar.coeff gbar.natDegree
    rw [hdegree]
    exact hcoeff
  have hres_ne : IsLocalRing.residue R g0.leadingCoeff ≠ 0 := by
    rw [hres_lead]
    exact hlead
  exact (IsLocalRing.residue_ne_zero_iff_isUnit g0.leadingCoeff).1 hres_ne

/-- unit-leading normalization: a polynomial whose leading
coefficient is a unit becomes monic after multiplying by the inverse leading
coefficient, and this normalization preserves degree.
@isnad1 id=ex.1h2v.s9.5d6a1414bac5 from=translated src=- shape=9c41def5 vocab=364c2c4d
-/
theorem henselFactorization_monic_normalization_of_unit_leadingCoeff
    {R : Type*} [CommRing R] {g : R[X]} (hunit : IsUnit g.leadingCoeff) :
    ∃ u : Rˣ,
      (u : R) = g.leadingCoeff ∧
        (Polynomial.C ((u⁻¹ : Rˣ) : R) * g).Monic ∧
          (Polynomial.C ((u⁻¹ : Rˣ) : R) * g).degree = g.degree ∧
            (Polynomial.C ((u⁻¹ : Rˣ) : R) * g).natDegree = g.natDegree := by
  rcases hunit with ⟨u, hu⟩
  have hinvUnit : IsUnit (((u⁻¹ : Rˣ) : R)) := ⟨u⁻¹, rfl⟩
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · exact Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
      (p := g) (b := ((u⁻¹ : Rˣ) : R)) (Units.inv_mul_of_eq (u := u) hu)
  · exact Polynomial.degree_C_mul_of_isUnit hinvUnit g
  · exact Polynomial.natDegree_C_mul_of_isUnit hinvUnit g

/-- A polynomial maps to zero iff all of its coefficients lie in the kernel of
the coefficient map.  This is the coefficientwise form used by the Hensel
correction congruences.
@isnad1 id=iff.0h4v.s7.f41f25a984b6 from=translated src=- shape=4b0a141d vocab=cdf16fe6
-/
theorem henselFactorization_map_eq_zero_iff_coeff_mem_ker
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k) (P : R[X]) :
    P.map φ = 0 ↔ ∀ n : ℕ, P.coeff n ∈ RingHom.ker φ := by
  constructor
  · intro h n
    rw [RingHom.mem_ker]
    have hcoeff := congrArg (fun Q : k[X] => Q.coeff n) h
    simpa [Polynomial.coeff_map] using hcoeff
  · intro h
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact RingHom.mem_ker.mp (h n)

/-- Polynomial coefficient maps are equal iff every coefficient of the
difference lies in the kernel.
@isnad1 id=iff.0h5v.s7.e5a3435e54a9 from=translated src=- shape=c68626ab vocab=202ee3a7
-/
theorem henselFactorization_map_eq_iff_sub_coeff_mem_ker
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k) (P Q : R[X]) :
    P.map φ = Q.map φ ↔ ∀ n : ℕ, (P - Q).coeff n ∈ RingHom.ker φ := by
  rw [← sub_eq_zero, ← Polynomial.map_sub]
  exact henselFactorization_map_eq_zero_iff_coeff_mem_ker φ (P - Q)

/-- The kernel of the quotient map `R -> R/I` is exactly `I`.
@isnad1 id=iff.0h3v.s8.3d115f4bd71f from=translated src=- shape=423df497 vocab=d9773be3
-/
theorem henselFactorization_mem_ker_quotient_mk_iff
    {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
    x ∈ RingHom.ker (Ideal.Quotient.mk I) ↔ x ∈ I := by
  rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- Specialization of the coefficientwise zero criterion to quotient maps:
a polynomial maps to zero in `(R/I)[X]` iff all of its coefficients lie in
`I`.
@isnad1 id=iff.0h3v.s7.1216a75d96ab from=translated src=- shape=b0dbd1ce vocab=a75fff3b
-/
theorem henselFactorization_map_quotient_eq_zero_iff_coeff_mem
    {R : Type*} [CommRing R] (I : Ideal R) (P : R[X]) :
    P.map (Ideal.Quotient.mk I) = 0 ↔ ∀ n : ℕ, P.coeff n ∈ I := by
  rw [henselFactorization_map_eq_zero_iff_coeff_mem_ker]
  constructor
  · intro h n
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact RingHom.mem_ker.mp (h n)
  · intro h n
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h n)

/-- Coefficientwise form of
`henselFactorization_map_quotient_eq_zero_iff_coeff_mem`.
@isnad1 id=iff.0h4v.s7.926a37bc3c2c from=translated src=- shape=7c06a7fe vocab=a75fff3b
-/
theorem henselFactorization_quotient_map_coeff_eq_zero_iff_coeff_mem
    {R : Type*} [CommRing R] (I : Ideal R) (P : R[X]) (n : ℕ) :
    (P.map (Ideal.Quotient.mk I)).coeff n = 0 ↔ P.coeff n ∈ I := by
  rw [Polynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]

/-- Equality after quotienting coefficients is the same as coefficientwise
membership of the difference in the quotient ideal.
@isnad1 id=iff.0h4v.s7.5bac3f30f108 from=translated src=- shape=c19157ff vocab=a7ba14fa
-/
theorem henselFactorization_map_quotient_eq_iff_sub_coeff_mem
    {R : Type*} [CommRing R] (I : Ideal R) (P Q : R[X]) :
    P.map (Ideal.Quotient.mk I) = Q.map (Ideal.Quotient.mk I) ↔
      ∀ n : ℕ, (P - Q).coeff n ∈ I := by
  rw [henselFactorization_map_eq_iff_sub_coeff_mem_ker]
  constructor
  · intro h n
    exact (henselFactorization_mem_ker_quotient_mk_iff I _).1 (h n)
  · intro h n
    exact (henselFactorization_mem_ker_quotient_mk_iff I _).2 (h n)

/-- division step: division by a monic polynomial gives the
quotient and remainder used in the correction construction, with remainder
degree strictly smaller than the divisor degree.
@isnad1 id=ex.1h3v.s7.baf80fb7d9f8 from=translated src=- shape=ceee6e34 vocab=317799c9
-/
theorem henselFactorization_division_by_monic_degree_lt
    {R : Type*} [CommRing R] [Nontrivial R] (F g : R[X]) (hg : g.Monic) :
    ∃ q p : R[X], F = g * q + p ∧ p.degree < g.degree := by
  refine ⟨F /ₘ g, F %ₘ g, ?_, ?_⟩
  · calc
      F = F %ₘ g + g * (F /ₘ g) := by
        exact (Polynomial.modByMonic_add_div F g).symm
      _ = g * (F /ₘ g) + F %ₘ g := by
        ring
  · exact Polynomial.degree_modByMonic_lt F hg

/-- division by a unit-leading divisor: the division step used
in the Hensel correction construction does not require the chosen lift `g0` to
be monic; a unit leading coefficient is enough.
@isnad1 id=ex.1h3v.s7.2b1a416eef3d from=translated src=- shape=0e992791 vocab=cf574bfe
-/
theorem henselFactorization_division_by_unit_leading_degree_lt
    {R : Type*} [CommRing R] [Nontrivial R] (F g : R[X])
    (hunit : IsUnit g.leadingCoeff) :
    ∃ q p : R[X], F = g * q + p ∧ p.degree < g.degree := by
  rcases henselFactorization_monic_normalization_of_unit_leadingCoeff
    (g := g) hunit with
    ⟨u, _hu, hmonic, hdegree, _hnatDegree⟩
  rcases henselFactorization_division_by_monic_degree_lt F
    (Polynomial.C ((u⁻¹ : Rˣ) : R) * g) hmonic with
    ⟨q, p, hdiv, hpdeg⟩
  refine ⟨Polynomial.C ((u⁻¹ : Rˣ) : R) * q, p, ?_, ?_⟩
  · calc
      F = (Polynomial.C ((u⁻¹ : Rˣ) : R) * g) * q + p := hdiv
      _ = g * (Polynomial.C ((u⁻¹ : Rˣ) : R) * q) + p := by
        ring
  · rwa [hdegree] at hpdeg

/-- division by a lifted residual factor: if `g0` lifts
`gbar` with the same degree and `gbar` is nonzero in leading coefficient, then
the construction division step `F = g0 q + p`, `deg p < deg g0`, is available in the
valuation ring.
@isnad1 id=ex.3h4v.s8.72014881fde9 from=translated src=- shape=640b9bd6 vocab=f973f782
-/
theorem henselFactorization_division_by_lifted_factor_degree_lt
    {R : Type*} [CommRing R] [IsLocalRing R]
    {g0 : R[X]} {gbar : (IsLocalRing.ResidueField R)[X]}
    (hg0 : g0.map (IsLocalRing.residue R) = gbar)
    (hdegree : g0.natDegree = gbar.natDegree)
    (hlead : gbar.leadingCoeff ≠ 0) (F : R[X]) :
    ∃ q p : R[X], F = g0 * q + p ∧ p.degree < g0.degree := by
  exact henselFactorization_division_by_unit_leading_degree_lt F g0
    (henselFactorization_lift_leadingCoeff_isUnit_of_natDegree_eq hg0 hdegree hlead)

/-- Algebra identity behind the Hensel correction step after the division
`b * fn = g0 * q + p`.
@isnad1 id=eq.1h8v.s8.6202df4cb15b from=translated src=- shape=9cf7ff96 vocab=edd6ac77
-/
theorem henselFactorization_correction_identity_after_division
    {R : Type*} [CommSemiring R] {a b g0 h0 fn q p : R[X]}
    (hdiv : b * fn = g0 * q + p) :
    g0 * (a * fn + h0 * q) + h0 * p = (a * g0 + b * h0) * fn := by
  calc
    g0 * (a * fn + h0 * q) + h0 * p =
        a * g0 * fn + h0 * (g0 * q + p) := by
      ring
    _ = a * g0 * fn + h0 * (b * fn) := by
      rw [← hdiv]
    _ = (a * g0 + b * h0) * fn := by
      ring

/-- correction congruence after division, read directly
modulo the principal ideal `(π)`: if the lifted Bezout error has a displayed
`C π` factor, then the divided correction represents `fn` modulo `(π)`.
@isnad1 id=mem.2h11v.s9.1a2a55db6e01 from=translated src=- shape=75a1bf27 vocab=ba199c20
-/
theorem henselFactorization_correction_congruence_span_singleton_after_division
    {R : Type*} [CommRing R] {π : R}
    {a b g0 h0 fn q p e : R[X]}
    (hbez : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hdiv : b * fn = g0 * q + p) :
    ∀ n : ℕ,
      (g0 * (a * fn + h0 * q) + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R) := by
  have halg :=
    henselFactorization_correction_identity_after_division
      (a := a) (h0 := h0) hdiv
  have hfactor :
      g0 * (a * fn + h0 * q) + h0 * p - fn =
        Polynomial.C π * (e * fn) := by
    calc
      g0 * (a * fn + h0 * q) + h0 * p - fn =
          (a * g0 + b * h0 - 1) * fn := by
        rw [halg]
        ring
      _ = Polynomial.C π * (e * fn) := by
        rw [hbez]
        ring
  intro n
  rw [hfactor, Polynomial.coeff_C_mul, Ideal.mem_span_singleton]
  exact dvd_mul_right π ((e * fn).coeff n)

end Valuations
end AlgebraicNumberTheory

end
