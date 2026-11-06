/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# coefficient truncation for the Hensel correction step

This file contains the finite coefficient-cutting step used in the
proof of Hensel's lemma: after the division step, coefficients already zero in
the residue field may be omitted to impose the required degree bound.
-/

noncomputable section

open scoped Polynomial
open scoped BigOperators

namespace AlgebraicNumberTheory
namespace Valuations

/-- low-degree part of a polynomial up to degree `N`.-/
def henselFactorization_lowPart {R : Type*} [Semiring R] (N : ℕ) (P : R[X]) : R[X] :=
  Finset.sum (Finset.range (N + 1)) fun i => Polynomial.monomial i (P.coeff i)

/-- coefficients at degrees kept by `lowPart`.
@isnad1 id=eq.1h4v.s5.f9cf1c94f4f2 from=translated src=- shape=3b450f5e vocab=5d8398d5
-/
theorem henselFactorization_lowPart_coeff_of_le
    {R : Type*} [Semiring R] {N n : ℕ} (P : R[X]) (hn : n ≤ N) :
    (henselFactorization_lowPart N P).coeff n = P.coeff n := by
  classical
  unfold henselFactorization_lowPart
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single n]
  · exact Polynomial.coeff_monomial_same n (P.coeff n)
  · intro b _hb hbn
    rw [Polynomial.coeff_monomial, ite_eq_right hbn]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

/-- coefficients above the cutoff vanish in `lowPart`.
@isnad1 id=eq.1h4v.s5.a2837809aa98 from=translated src=- shape=10faf318 vocab=9c2ce07c
-/
theorem henselFactorization_lowPart_coeff_eq_zero_of_lt
    {R : Type*} [Semiring R] {N n : ℕ} (P : R[X]) (hn : N < n) :
    (henselFactorization_lowPart N P).coeff n = 0 := by
  classical
  unfold henselFactorization_lowPart
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero ?_
  intro b hb
  have hbn : b ≠ n := by
    intro hbn
    have hn_le : n ≤ N := Nat.lt_succ_iff.mp (by simpa [hbn] using hb)
    exact (Nat.not_lt_of_ge hn_le) hn
  simp [Polynomial.coeff_monomial, hbn]

/-- `lowPart` has the intended degree bound.
@isnad1 id=le.0h3v.s4.c93202a68445 from=translated src=- shape=61b1528c vocab=80e6b54c
-/
theorem henselFactorization_lowPart_natDegree_le
    {R : Type*} [Semiring R] (N : ℕ) (P : R[X]) :
    (henselFactorization_lowPart N P).natDegree ≤ N := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  exact henselFactorization_lowPart_coeff_eq_zero_of_lt (P := P) hn

/-- omitting high coefficients already in the kernel does not
change the residual polynomial.
@isnad1 id=eq.1h5v.s7.ed1c39454205 from=translated src=- shape=b0033600 vocab=e7ab775f
-/
theorem henselFactorization_lowPart_map_eq_of_high_coeff_mem_ker
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    (N : ℕ) (P : R[X])
    (hhigh : ∀ n : ℕ, N < n → P.coeff n ∈ RingHom.ker φ) :
    (henselFactorization_lowPart N P).map φ = P.map φ := by
  ext n
  by_cases hn : n ≤ N
  · rw [Polynomial.coeff_map, Polynomial.coeff_map,
      henselFactorization_lowPart_coeff_of_le (P := P) hn]
  · have hlt : N < n := Nat.lt_of_not_ge hn
    have hker := hhigh n hlt
    rw [Polynomial.coeff_map, Polynomial.coeff_map,
      henselFactorization_lowPart_coeff_eq_zero_of_lt (P := P) hlt]
    rw [RingHom.mem_ker] at hker
    simpa using hker.symm

/-- kernel-level truncation: the correction congruence
survives replacing a provisional correction polynomial by its low-degree part
when the omitted coefficients already lie in the same coefficient-map kernel.
@isnad1 id=and.2h9v.s9.4fde041fa1ad from=translated src=- shape=7faaa20a vocab=92aa131d
-/
theorem henselFactorization_correction_after_lowPart_ker
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    {g0 h0 fn p Q : R[X]} (N : ℕ)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈ RingHom.ker φ)
    (hhigh : ∀ n : ℕ, N < n → Q.coeff n ∈ RingHom.ker φ) :
    (henselFactorization_lowPart N Q).natDegree ≤ N ∧
      ∀ n : ℕ,
        (g0 * henselFactorization_lowPart N Q + h0 * p - fn).coeff n ∈
          RingHom.ker φ := by
  refine ⟨henselFactorization_lowPart_natDegree_le N Q, ?_⟩
  have hmapQ :=
    henselFactorization_lowPart_map_eq_of_high_coeff_mem_ker φ N Q hhigh
  have hmapOld :
      (g0 * Q + h0 * p - fn).map φ = 0 := by
    exact (henselFactorization_map_eq_zero_iff_coeff_mem_ker
      φ (g0 * Q + h0 * p - fn)).2 hcorr
  have hmapNew :
      (g0 * henselFactorization_lowPart N Q + h0 * p - fn).map φ = 0 := by
    calc
      (g0 * henselFactorization_lowPart N Q + h0 * p - fn).map φ =
          g0.map φ * (henselFactorization_lowPart N Q).map φ +
            h0.map φ * p.map φ - fn.map φ := by
        exact henselFactorization_map_mul_add_mul_sub φ g0 h0
          (henselFactorization_lowPart N Q) p fn
      _ = g0.map φ * Q.map φ + h0.map φ * p.map φ - fn.map φ := by
        rw [hmapQ]
      _ = (g0 * Q + h0 * p - fn).map φ := by
        exact (henselFactorization_map_mul_add_mul_sub φ g0 h0 Q p fn).symm
      _ = 0 := hmapOld
  intro n
  exact (henselFactorization_map_eq_zero_iff_coeff_mem_ker
    φ (g0 * henselFactorization_lowPart N Q + h0 * p - fn)).1 hmapNew n

/-- ideal-level truncation: the correction congruence survives
replacing a provisional correction polynomial by its low-degree part when the
omitted coefficients already lie in the same ideal.
@isnad1 id=and.2h8v.s9.f375e18d3e78 from=translated src=- shape=74630f02 vocab=67bdc3af
-/
theorem henselFactorization_correction_after_lowPart_ideal
    {R : Type*} [CommRing R] {I : Ideal R}
    {g0 h0 fn p Q : R[X]} (N : ℕ)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈ I)
    (hhigh : ∀ n : ℕ, N < n → Q.coeff n ∈ I) :
    (henselFactorization_lowPart N Q).natDegree ≤ N ∧
      ∀ n : ℕ,
        (g0 * henselFactorization_lowPart N Q + h0 * p - fn).coeff n ∈ I := by
  let φ : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hcorrKer :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈ RingHom.ker φ := by
    intro n
    exact (henselFactorization_mem_ker_quotient_mk_iff I _).2 (hcorr n)
  have hhighKer :
      ∀ n : ℕ, N < n → Q.coeff n ∈ RingHom.ker φ := by
    intro n hn
    exact (henselFactorization_mem_ker_quotient_mk_iff I _).2 (hhigh n hn)
  rcases henselFactorization_correction_after_lowPart_ker
      φ (N := N) (g0 := g0) (h0 := h0) (fn := fn)
      (p := p) (Q := Q) hcorrKer hhighKer with
    ⟨hdeg, hker⟩
  refine ⟨hdeg, ?_⟩
  intro n
  exact (henselFactorization_mem_ker_quotient_mk_iff I _).1 (hker n)

/-- principal-ideal truncation: if the provisional correction
is congruent modulo `(π)` and all omitted coefficients are divisible by `π`,
then the truncated correction keeps the same congruence modulo `(π)`.
@isnad1 id=and.2h8v.s9.dc3fb83091d1 from=translated src=- shape=4657771a vocab=2c0fb80d
-/
theorem henselFactorization_correction_after_lowPart_span_singleton
    {R : Type*} [CommRing R] {π : R}
    {g0 h0 fn p Q : R[X]} (N : ℕ)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R))
    (hhigh : ∀ n : ℕ, N < n → Q.coeff n ∈
      Ideal.span ({π} : Set R)) :
    (henselFactorization_lowPart N Q).natDegree ≤ N ∧
      ∀ n : ℕ,
        (g0 * henselFactorization_lowPart N Q + h0 * p - fn).coeff n ∈
          Ideal.span ({π} : Set R) := by
  exact henselFactorization_correction_after_lowPart_ideal
    (I := Ideal.span ({π} : Set R)) N hcorr hhigh

/-- unit-leading degree division over an arbitrary
commutative ring: if the product with a degree-`m` polynomial whose leading
coefficient is a unit has degree at most `d`, then the right factor has degree
at most `d - m`.  This is the form needed over `O/(π)` in the iterative proof.
@isnad1 id=le.3h5v.s6.6825b9954161 from=translated src=- shape=9cd2bc11 vocab=a2c7af42
-/
theorem henselFactorization_natDegree_right_le_tsub_of_unit_leading_mul_natDegree_le
    {R : Type*} [CommRing R] {g Q : R[X]} {m d : ℕ}
    (hgunit : IsUnit g.leadingCoeff) (hgdeg : g.natDegree = m)
    (hprod : (g * Q).natDegree ≤ d) :
    Q.natDegree ≤ d - m := by
  by_cases hQ : Q = 0
  · simp [hQ]
  rcases henselFactorization_monic_normalization_of_unit_leadingCoeff
      (g := g) hgunit with
    ⟨u, _hu, hmonic, _hdegree, hnatDegree⟩
  let G : R[X] := Polynomial.C (((u⁻¹ : Rˣ) : R)) * g
  have hGmonic : G.Monic := by
    simpa [G] using hmonic
  have hGnat : G.natDegree = m := by
    simpa [G, hgdeg] using hnatDegree
  have hinvUnit : IsUnit (((u⁻¹ : Rˣ) : R)) := ⟨u⁻¹, rfl⟩
  have hGprod : (G * Q).natDegree ≤ d := by
    have hrewrite :
        G * Q = Polynomial.C (((u⁻¹ : Rˣ) : R)) * (g * Q) := by
      dsimp [G]
      ring
    rw [hrewrite, Polynomial.natDegree_C_mul_of_isUnit hinvUnit]
    exact hprod
  have hsum : m + Q.natDegree ≤ d := by
    have hmul := hGmonic.natDegree_mul' hQ
    rw [hGnat] at hmul
    simpa [hmul] using hGprod
  exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hsum)

/-- a unit-leading polynomial remains unit-leading with the
same natural degree after mapping to a nontrivial target ring.  This supplies
the unit-leading input used over `O/(π)`.
@isnad1 id=and.2h5v.s7.f4c6abc098b2 from=translated src=- shape=36927698 vocab=689bfd7e
-/
theorem henselFactorization_map_unit_leadingCoeff_natDegree_eq
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (φ : R →+* S) {g : R[X]} {m : ℕ}
    (hgunit : IsUnit g.leadingCoeff) (hgdeg : g.natDegree = m) :
    IsUnit (g.map φ).leadingCoeff ∧ (g.map φ).natDegree = m := by
  have hlead :
      (g.map φ).leadingCoeff = φ g.leadingCoeff :=
    Polynomial.leadingCoeff_map_eq_of_isUnit_leadingCoeff φ hgunit
  have hnat :
      (g.map φ).natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff φ hgunit
  exact ⟨by
    rw [hlead]
    exact IsUnit.map φ hgunit, by
    rw [hnat, hgdeg]⟩

/-- quotient specialization of
`henselFactorization_map_unit_leadingCoeff_natDegree_eq`.
@isnad1 id=and.2h4v.s7.150f8cacb088 from=translated src=- shape=c616e997 vocab=a30b7fd3
-/
theorem henselFactorization_quotient_unit_leadingCoeff_natDegree_eq
    {R : Type*} [CommRing R] {I : Ideal R} [Nontrivial (R ⧸ I)]
    {g : R[X]} {m : ℕ}
    (hgunit : IsUnit g.leadingCoeff) (hgdeg : g.natDegree = m) :
    IsUnit (g.map (Ideal.Quotient.mk I)).leadingCoeff ∧
      (g.map (Ideal.Quotient.mk I)).natDegree = m :=
  henselFactorization_map_unit_leadingCoeff_natDegree_eq
    (Ideal.Quotient.mk I) hgunit hgdeg

/-- if `π` lies in the maximal ideal of a local ring, then
the quotient `O/(π)` is nontrivial.  This is the displayed-factor source for the
nontriviality needed in the degree argument modulo `(π)`.
@isnad1 id=nontrivi.1h2v.s6.07504ad9dbde from=translated src=- shape=4447d75b vocab=cffebe2a
-/
theorem henselFactorization_span_singleton_quotient_nontrivial_of_mem_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    (hπ : π ∈ IsLocalRing.maximalIdeal R) :
    Nontrivial (R ⧸ Ideal.span ({π} : Set R)) := by
  rw [Ideal.Quotient.nontrivial_iff]
  intro htop
  have hle : Ideal.span ({π} : Set R) ≤ IsLocalRing.maximalIdeal R := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    simpa [hx] using hπ
  have htop_le :
      (⊤ : Ideal R) ≤ IsLocalRing.maximalIdeal R := by
    simpa [htop] using hle
  have hmaxTop : IsLocalRing.maximalIdeal R = ⊤ :=
    le_antisymm le_top htop_le
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hmaxTop

/-- local-ring specialization: a unit-leading polynomial of
degree `m` stays unit-leading of degree `m` after reducing modulo `(π)`, for
`π` in the maximal ideal.
@isnad1 id=and.3h4v.s8.0a9810acda62 from=translated src=- shape=c9b6a0cd vocab=b847be3f
-/
theorem henselFactorization_span_singleton_quotient_unit_leadingCoeff_natDegree_eq
    {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    {g : R[X]} {m : ℕ}
    (hπ : π ∈ IsLocalRing.maximalIdeal R)
    (hgunit : IsUnit g.leadingCoeff) (hgdeg : g.natDegree = m) :
    IsUnit
        ((g.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).leadingCoeff) ∧
      (g.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree = m := by
  let : Nontrivial (R ⧸ Ideal.span ({π} : Set R)) :=
    henselFactorization_span_singleton_quotient_nontrivial_of_mem_maximalIdeal hπ
  exact henselFactorization_quotient_unit_leadingCoeff_natDegree_eq
    (I := Ideal.span ({π} : Set R)) hgunit hgdeg

/-- mapped degree bound for the polynomial `fn - h0*p` from
degree bounds already available before mapping.  This is the quotient-level
replacement for the residue-field degree bound in the principal `(π)` route.
@isnad1 id=le.4h9v.s7.b5f9f9ba667a from=translated src=- shape=1ab848fd vocab=f8932919
-/
theorem henselFactorization_map_sub_mul_natDegree_le_of_degree_bounds
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {fn h0 P : R[X]} {a b d : ℕ}
    (hfn : fn.natDegree ≤ d)
    (hh0 : h0.natDegree ≤ a)
    (hP : P.natDegree ≤ b)
    (hab : a + b ≤ d) :
    ((fn - h0 * P).map φ).natDegree ≤ d := by
  have hfnmap : (fn.map φ).natDegree ≤ d :=
    Polynomial.natDegree_map_le.trans hfn
  have hh0map : (h0.map φ).natDegree ≤ a :=
    Polynomial.natDegree_map_le.trans hh0
  have hPmap : (P.map φ).natDegree ≤ b :=
    Polynomial.natDegree_map_le.trans hP
  have hmul :
      (h0.map φ * P.map φ).natDegree ≤ d :=
    (Polynomial.natDegree_mul_le_of_le hh0map hPmap).trans hab
  have hmap :
      (fn - h0 * P).map φ =
        fn.map φ - h0.map φ * P.map φ := by
    exact henselFactorization_map_sub_mul φ fn h0 P
  rw [hmap]
  simpa using
    (Polynomial.natDegree_sub_le_of_le
      (p := fn.map φ) (q := h0.map φ * P.map φ) hfnmap hmul)

/-- quotient specialization of the degree bound for
`fn - h0*p` used before truncating the Hensel correction.
@isnad1 id=le.4h8v.s8.3d8eec6c5732 from=translated src=- shape=f25059ff vocab=f4973e91
-/
theorem henselFactorization_span_singleton_quotient_sub_mul_natDegree_le_of_degree_bounds
    {R : Type*} [CommRing R] {π : R}
    {fn h0 P : R[X]} {a b d : ℕ}
    (hfn : fn.natDegree ≤ d)
    (hh0 : h0.natDegree ≤ a)
    (hP : P.natDegree ≤ b)
    (hab : a + b ≤ d) :
    ((fn - h0 * P).map
      (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d :=
  henselFactorization_map_sub_mul_natDegree_le_of_degree_bounds
    (Ideal.Quotient.mk (Ideal.span ({π} : Set R))) hfn hh0 hP hab

/-- high-coefficient source modulo `(π)`: if `g0 * Q` is
congruent to a polynomial of degree at most `d` modulo `(π)`, and `g0` has
degree `m` with unit leading coefficient after reduction modulo `(π)`, then
every coefficient of `Q` above `d - m` is divisible by `π`.
@isnad1 id=mem.5h8v.s9.1a06a68a91b9 from=translated src=- shape=bc990399 vocab=8926e680
-/
theorem henselFactorization_high_coeff_mem_span_singleton_of_product_congruence_degree
    {R : Type*} [CommRing R] {π : R}
    {g0 Q A : R[X]} {m d : ℕ}
    (hgunit :
      IsUnit
        ((g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).leadingCoeff))
    (hgdeg :
      (g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree = m)
    (hcong : ∀ n : ℕ, (g0 * Q - A).coeff n ∈
      Ideal.span ({π} : Set R))
    (hAdeg :
      (A.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d) :
    ∀ n : ℕ, d - m < n → Q.coeff n ∈ Ideal.span ({π} : Set R) := by
  let φ : R →+* R ⧸ Ideal.span ({π} : Set R) :=
    Ideal.Quotient.mk (Ideal.span ({π} : Set R))
  have hmap :
      (g0 * Q - A).map φ = 0 := by
    simpa [φ] using
      (henselFactorization_map_quotient_eq_zero_iff_coeff_mem
        (Ideal.span ({π} : Set R)) (g0 * Q - A)).2 hcong
  have hsub :
      g0.map φ * Q.map φ - A.map φ = 0 := by
    simpa [henselFactorization_map_mul_sub] using hmap
  have hprod_eq : g0.map φ * Q.map φ = A.map φ :=
    sub_eq_zero.mp hsub
  have hprod_degree : (g0.map φ * Q.map φ).natDegree ≤ d := by
    rw [hprod_eq]
    exact hAdeg
  have hQdeg :
      (Q.map φ).natDegree ≤ d - m :=
    henselFactorization_natDegree_right_le_tsub_of_unit_leading_mul_natDegree_le
      (g := g0.map φ) (Q := Q.map φ) (m := m) (d := d)
      (by simpa [φ] using hgunit) (by simpa [φ] using hgdeg) hprod_degree
  intro n hn
  have hcoeff : (Q.map φ).coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQdeg hn)
  exact
    (henselFactorization_quotient_map_coeff_eq_zero_iff_coeff_mem
      (Ideal.span ({π} : Set R)) Q n).1 (by simpa [φ] using hcoeff)

/-- high-coefficient source modulo `(π)` specialized to the
correction congruence produced by the division step.
@isnad1 id=mem.5h10v.s9.496ac5520168 from=translated src=- shape=fa2fac90 vocab=bc2883ce
-/
theorem henselFactorization_high_coeff_mem_span_singleton_of_correction_degree
    {R : Type*} [CommRing R] {π : R}
    {g0 h0 fn p Q : R[X]} {m d : ℕ}
    (hgunit :
      IsUnit
        ((g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).leadingCoeff))
    (hgdeg :
      (g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree = m)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R))
    (hAdeg :
      ((fn - h0 * p).map
        (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d) :
    ∀ n : ℕ, d - m < n → Q.coeff n ∈ Ideal.span ({π} : Set R) := by
  have hcong :
      ∀ n : ℕ, (g0 * Q - (fn - h0 * p)).coeff n ∈
        Ideal.span ({π} : Set R) := by
    intro n
    have heq : g0 * Q - (fn - h0 * p) = g0 * Q + h0 * p - fn := by
      ring
    rw [heq]
    exact hcorr n
  exact henselFactorization_high_coeff_mem_span_singleton_of_product_congruence_degree
    (π := π) (g0 := g0) (Q := Q) (A := fn - h0 * p)
    (m := m) (d := d) hgunit hgdeg hcong hAdeg

/-- one-step degree truncation modulo `(π)`: under the
principal correction congruence, the quotient-degree bound for `fn - h0*p`,
and the unit-leading degree data for `g0` modulo `(π)`, the low-degree part of
`Q` has degree at most `d-m` and keeps the correction congruence modulo `(π)`.
@isnad1 id=and.4h9v.s10.06733af1239f from=translated src=- shape=6380330a vocab=851e0cac
-/
theorem henselFactorization_correction_after_degree_truncation_span_singleton
    {R : Type*} [CommRing R] {π : R}
    {g0 h0 fn p Q : R[X]} {m d : ℕ}
    (hgunit :
      IsUnit
        ((g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).leadingCoeff))
    (hgdeg :
      (g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree = m)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R))
    (hAdeg :
      ((fn - h0 * p).map
        (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d) :
    (henselFactorization_lowPart (d - m) Q).natDegree ≤ d - m ∧
      ∀ n : ℕ,
        (g0 * henselFactorization_lowPart (d - m) Q + h0 * p - fn).coeff n ∈
          Ideal.span ({π} : Set R) := by
  exact henselFactorization_correction_after_lowPart_span_singleton
    (π := π) (N := d - m) hcorr
    (henselFactorization_high_coeff_mem_span_singleton_of_correction_degree
      (π := π) (g0 := g0) (h0 := h0) (fn := fn) (p := p)
      (Q := Q) (m := m) (d := d) hgunit hgdeg hcorr hAdeg)

/-- principal-ideal one-step correction after Bezout and
division.  This is the displayed-factor route: the displayed factor
`a*g0 + b*h0 - 1 = C π * e`, not an equality `m = (π)`, supplies the
correction congruence modulo `(π)`.
@isnad1 id=and.9h12v.s10.48a1b660570a from=translated src=- shape=77ad3bb9 vocab=45e7b331
-/
theorem henselFactorization_correction_after_division_degree_truncation_span_singleton
    {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    {a b g0 h0 fn q p e : R[X]} {m d : ℕ}
    (hπ : π ∈ IsLocalRing.maximalIdeal R)
    (hgunit : IsUnit g0.leadingCoeff)
    (hg0nat : g0.natDegree = m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hdiv : b * fn = g0 * q + p)
    (hfn : fn.natDegree ≤ d)
    (hh0 : h0.natDegree ≤ d - m)
    (hp : p.natDegree ≤ m)
    (hmd : m ≤ d) :
    (henselFactorization_lowPart (d - m) (a * fn + h0 * q)).natDegree ≤ d - m ∧
      ∀ n : ℕ,
        (g0 * henselFactorization_lowPart (d - m) (a * fn + h0 * q) +
            h0 * p - fn).coeff n ∈ Ideal.span ({π} : Set R) := by
  rcases henselFactorization_span_singleton_quotient_unit_leadingCoeff_natDegree_eq
      (π := π) hπ hgunit hg0nat with
    ⟨hgunitQuot, hgdegQuot⟩
  have hcorr :
      ∀ n : ℕ, (g0 * (a * fn + h0 * q) + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R) :=
    henselFactorization_correction_congruence_span_singleton_after_division
      (π := π) hbezFactor hdiv
  have hAdeg :
      ((fn - h0 * p).map
        (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d :=
    henselFactorization_span_singleton_quotient_sub_mul_natDegree_le_of_degree_bounds
      (π := π) (fn := fn) (h0 := h0) (P := p)
      (a := d - m) (b := m) (d := d) hfn hh0 hp (by
        rw [Nat.sub_add_cancel hmd])
  exact henselFactorization_correction_after_degree_truncation_span_singleton
    (π := π) (g0 := g0) (h0 := h0) (fn := fn) (p := p)
    (Q := a * fn + h0 * q) (m := m) (d := d)
    hgunitQuot hgdegQuot hcorr hAdeg

/-- principal-ideal version of replacement of the initial
lifted factors by the current inductive approximants.  If `g` and `h` are
still congruent to `g0` and `h0` modulo `(π)`, then a correction congruence
for `g0,h0` modulo `(π)` is also one for `g,h`.
@isnad1 id=mem.3h10v.s9.f3de216f1c69 from=translated src=- shape=feda1c9b vocab=b4648c09
-/
theorem henselFactorization_correction_congruence_replace_initial_factors_span_singleton
    {R : Type*} [CommRing R] {π : R}
    {g0 h0 g h fn p q : R[X]}
    (hg : ∀ n : ℕ, (g - g0).coeff n ∈ Ideal.span ({π} : Set R))
    (hh : ∀ n : ℕ, (h - h0).coeff n ∈ Ideal.span ({π} : Set R))
    (hcorr :
      ∀ n : ℕ, (g0 * q + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R)) :
    ∀ n : ℕ, (g * q + h * p - fn).coeff n ∈
      Ideal.span ({π} : Set R) := by
  let φ : R →+* R ⧸ Ideal.span ({π} : Set R) :=
    Ideal.Quotient.mk (Ideal.span ({π} : Set R))
  have hgmap : g.map φ = g0.map φ := by
    simpa [φ] using
      (henselFactorization_map_quotient_eq_iff_sub_coeff_mem
        (Ideal.span ({π} : Set R)) g g0).2 hg
  have hhmap : h.map φ = h0.map φ := by
    simpa [φ] using
      (henselFactorization_map_quotient_eq_iff_sub_coeff_mem
        (Ideal.span ({π} : Set R)) h h0).2 hh
  have hcorrMap : (g0 * q + h0 * p - fn).map φ = 0 := by
    simpa [φ] using
      (henselFactorization_map_quotient_eq_zero_iff_coeff_mem
        (Ideal.span ({π} : Set R)) (g0 * q + h0 * p - fn)).2 hcorr
  have hmap : (g * q + h * p - fn).map φ = 0 := by
    calc
      (g * q + h * p - fn).map φ =
          g.map φ * q.map φ + h.map φ * p.map φ - fn.map φ := by
        exact henselFactorization_map_mul_add_mul_sub φ g h q p fn
      _ = g0.map φ * q.map φ + h0.map φ * p.map φ - fn.map φ := by
        rw [hgmap, hhmap]
      _ = (g0 * q + h0 * p - fn).map φ := by
        exact (henselFactorization_map_mul_add_mul_sub φ g0 h0 q p fn).symm
      _ = 0 := hcorrMap
  intro n
  exact
    (henselFactorization_map_quotient_eq_zero_iff_coeff_mem
      (Ideal.span ({π} : Set R)) (g * q + h * p - fn)).1
      (by simpa [φ] using hmap) n

end Valuations
end AlgebraicNumberTheory

end
