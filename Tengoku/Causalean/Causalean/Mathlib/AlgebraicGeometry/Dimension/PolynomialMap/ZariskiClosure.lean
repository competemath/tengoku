/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku

/-!
# Affine Zariski closure over the complex numbers

This file defines affine Zariski closure by the vanishing ideal and proves its
elementary closure laws, including finite unions and density of principal open
sets.
-/

@[expose] public section

namespace Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

noncomputable section

/-- For [a coordinate index set](hyp:ι) and [a subset $A$ of the corresponding complex affine space](hyp:A),
[its affine Zariski closure](goal) is the set of all points at which every complex multivariate
polynomial that vanishes on every point of $A$ also vanishes.

Algebraic closure in a complex affine space. -/
def affineZariskiClosure {ι : Type*} (A : Set (ι → ℂ)) : Set (ι → ℂ) :=
  MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ A)

/-- Every set is contained in its affine Zariski closure.
@isnad1 id=le.0h2v.s4.3613c058aa7c from=translated src=- shape=f3308a8d vocab=e9d1cd04
-/
lemma affineZariskiClosure_extensive {ι : Type*} (A : Set (ι → ℂ)) :
    A ⊆ affineZariskiClosure A :=
  MvPolynomial.zeroLocus_vanishingIdeal_le A

/-- Affine Zariski closure is monotone.
@isnad1 id=le.1h3v.s5.b2afeec66544 from=translated src=- shape=0e502c56 vocab=e9d1cd04
-/
lemma affineZariskiClosure_mono {ι : Type*} {A B : Set (ι → ℂ)} (h : A ⊆ B) :
    affineZariskiClosure A ⊆ affineZariskiClosure B := by
  exact MvPolynomial.zeroLocus_anti_mono
    (MvPolynomial.vanishingIdeal_anti_mono h)

/-- Affine Zariski closure is idempotent.
@isnad1 id=eq.0h2v.s4.379adc232698 from=translated src=- shape=2d9855c8 vocab=ef90d02d
-/
lemma affineZariskiClosure_idem {ι : Type*} (A : Set (ι → ℂ)) :
    affineZariskiClosure (affineZariskiClosure A) = affineZariskiClosure A := by
  apply Set.Subset.antisymm
  · intro x hx P hP
    exact hx P (fun y hy => hy P hP)
  · exact affineZariskiClosure_extensive _

/-- A closed affine set is the zero locus of its vanishing ideal.
@isnad1 id=eq.1h2v.s5.f375f5dd72c8 from=translated src=- shape=3469ab18 vocab=80d14f23
-/
lemma affineZariskiClosure_eq_zeroLocus {ι : Type*}
    {Z : Set (ι → ℂ)} (hZ : affineZariskiClosure Z = Z) :
    Z = MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ Z) := by
  exact hZ.symm

/-- The intersection of two affine-closed sets is affine-closed.
@isnad1 id=eq.2h3v.s5.2a899cd86e77 from=translated src=- shape=d805468e vocab=79552554
-/
lemma affineZariskiClosure_inter {ι : Type*}
    {A B : Set (ι → ℂ)}
    (hA : affineZariskiClosure A = A) (hB : affineZariskiClosure B = B) :
    affineZariskiClosure (A ∩ B) = A ∩ B := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨hA ▸ affineZariskiClosure_mono Set.inter_subset_left hx,
      hB ▸ affineZariskiClosure_mono Set.inter_subset_right hx⟩
  · exact affineZariskiClosure_extensive _

/-- The zero set of one multivariate polynomial is affine-closed.
@isnad1 id=eq.0h2v.s7.647dbb277d6b from=translated src=- shape=48781381 vocab=a4fb1378
-/
lemma affineZariskiClosure_zero_of_polynomial {ι : Type*}
    (P : MvPolynomial ι ℂ) :
    affineZariskiClosure {x | MvPolynomial.eval x P = 0} =
      {x | MvPolynomial.eval x P = 0} := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx P (fun y hy => by simpa [MvPolynomial.aeval_def] using hy)
  · exact affineZariskiClosure_extensive _

/-- The union of two affine-closed sets is affine-closed.
@isnad1 id=eq.2h3v.s5.2707b54bdb3e from=translated src=- shape=d805468e vocab=79c5b5d8
-/
lemma affineZariskiClosure_union {ι : Type*} {A B : Set (ι → ℂ)}
    (hA : affineZariskiClosure A = A) (hB : affineZariskiClosure B = B) :
    affineZariskiClosure (A ∪ B) = A ∪ B := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hnot
    have hxA : x ∉ A := fun h => hnot (Or.inl h)
    have hxB : x ∉ B := fun h => hnot (Or.inr h)
    have hxAc : x ∉ affineZariskiClosure A := by simpa [hA] using hxA
    have hxBc : x ∉ affineZariskiClosure B := by simpa [hB] using hxB
    simp only [affineZariskiClosure, MvPolynomial.mem_zeroLocus_iff,
      MvPolynomial.aeval_def] at hxAc hxBc
    push_neg at hxAc hxBc
    obtain ⟨P, hPA, hPx⟩ := hxAc
    obtain ⟨Q, hQB, hQx⟩ := hxBc
    have hpq : P * Q ∈ MvPolynomial.vanishingIdeal ℂ (A ∪ B) := by
      intro y hy
      rcases hy with hy | hy
      · rw [map_mul, hPA y hy, zero_mul]
      · rw [map_mul, hQB y hy, mul_zero]
    have := hx (P * Q) hpq
    rw [map_mul] at this
    exact mul_ne_zero hPx hQx this
  · exact affineZariskiClosure_extensive _

/-- For a polynomial `P` in coordinates indexed by `ι`, if [`P` is not the zero
polynomial](hyp:hP), then [the set of points where `P` does not vanish is
Zariski-dense in the whole affine space](goal).
@isnad1 id=eq.1h2v.s7.a35c3a4b4b83 from=translated src=- shape=cdb0b37f vocab=ec978faf
-/
lemma affineZariskiClosure_nonvanishing_eq_univ {ι : Type*}
    (P : MvPolynomial ι ℂ) (hP : P ≠ 0) :
    affineZariskiClosure {x : ι → ℂ | MvPolynomial.eval x P ≠ 0} = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x Q hQ
  have hmul_eval : ∀ y : ι → ℂ, MvPolynomial.eval y (Q * P) = 0 := by
    intro y
    by_cases hy : MvPolynomial.eval y P = 0
    · simp [hy]
    · rw [map_mul]
      have hQy : MvPolynomial.eval y Q = 0 := by
        simpa [MvPolynomial.aeval_def, MvPolynomial.eval₂_id] using hQ y hy
      rw [hQy, zero_mul]
  have hmul : Q * P = 0 := by
    apply MvPolynomial.funext
    exact hmul_eval
  have hQzero : Q = 0 := (mul_eq_zero.mp hmul).resolve_right hP
  simp [hQzero]

end

end Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
