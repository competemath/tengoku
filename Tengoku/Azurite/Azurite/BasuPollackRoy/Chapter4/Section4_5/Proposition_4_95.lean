/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.SimpleZero
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.NonsingularZero
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Definitions
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Proposition_4_92
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Proposition_4_93
import Tengoku.Seed.RingTheory.Nullstellensatz
import Tengoku.Seed.Data.List.TFAE
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
import Tengoku.Seed.RingTheory.Localization.Basic
import Tengoku.Seed.RingTheory.Finiteness.Ideal
import Tengoku.Seed.RingTheory.Nilpotent.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.5, Proposition 4.95: characterizations of a non-singular / simple zero

For a zero-dimensional system `𝒫 = {P₁, …, P_k} ⊂ K[X₁, …, X_k]` and a zero `x ∈ Cᵏ`, the
following are equivalent:
* (a) `x` is a non-singular zero of `𝒫`;
* (b) `x` is simple (multiplicity `1`, `Ā_x = C`);
* (c) `M_x ⊆ Ideal(𝒫, C) + M_x²`, where `M_x` is the ideal of elements of `C[X₁, …, X_k]`
  vanishing at `x`.

(Statement only for now; the proof — a TFAE chain — is to follow.)
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical

variable {k : ℕ} {K : Type*} [Field K]

section NonsingularImpCotangent

variable {R : Type*} [Field R]

/-- The generator `X i - C (x i)` of the maximal ideal `M_x`.-/
private noncomputable def gen (x : Fin k → R) (i : Fin k) : MvPolynomial (Fin k) R :=
  (X i : MvPolynomial (Fin k) R) - C (x i)

private theorem gen_mem_vanishing (x : Fin k → R) (i : Fin k) :
    gen x i ∈ MvPolynomial.vanishingIdeal R ({x} : Set (Fin k → R)) := by
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  simp [gen, map_sub]

/-- **Step A.** `M_x` is the span of the generators `X i - C (x i)`.-/
private theorem vanishing_eq_span (x : Fin k → R) :
    MvPolynomial.vanishingIdeal R ({x} : Set (Fin k → R))
      = Ideal.span (Set.range (gen x)) := by
  apply le_antisymm
  · -- M ≤ span
    have sub_const_mem_span : ∀ p : MvPolynomial (Fin k) R,
        p - C (MvPolynomial.aeval x p) ∈ Ideal.span (Set.range (gen x)) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq =>
          have : (p + q) - C (MvPolynomial.aeval x (p + q))
              = (p - C (MvPolynomial.aeval x p)) + (q - C (MvPolynomial.aeval x q)) := by
            rw [map_add, map_add]; ring
          rw [this]
          exact Ideal.add_mem _ hp hq
      | mul_X p j hp =>
          have hgenj : gen x j ∈ Ideal.span (Set.range (gen x)) :=
            Ideal.subset_span ⟨j, rfl⟩
          have key : p * X j - C (MvPolynomial.aeval x (p * X j))
              = (p - C (MvPolynomial.aeval x p)) * X j
                + C (MvPolynomial.aeval x p) * gen x j := by
            simp only [gen, map_mul, aeval_X]
            ring
          rw [key]
          exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp)
            (Ideal.mul_mem_left _ _ hgenj)
    intro p hp
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hp
    have hpx : MvPolynomial.aeval x p = 0 := hp x (Set.mem_singleton _)
    have := sub_const_mem_span p
    rwa [hpx, map_zero, sub_zero] at this
  · -- span ≤ M
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact gen_mem_vanishing x i

/-- **Step B (Taylor remainder).** For any `p`, the first-order Taylor remainder of `p` at `x`
lies in `M_x²`.-/
private theorem taylor_mem (x : Fin k → R) (p : MvPolynomial (Fin k) R) :
    p - C (MvPolynomial.aeval x p)
        - ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i p)) * gen x i
      ∈ (MvPolynomial.vanishingIdeal R ({x} : Set (Fin k → R))) ^ 2 := by
  set M := MvPolynomial.vanishingIdeal R ({x} : Set (Fin k → R)) with hM
  have hMsq : M ^ 2 = M * M := sq M
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      have heq : (p + q) - C (MvPolynomial.aeval x (p + q))
            - ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i (p + q))) * gen x i
          = (p - C (MvPolynomial.aeval x p)
              - ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i p)) * gen x i)
            + (q - C (MvPolynomial.aeval x q)
              - ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i q)) * gen x i) := by
        have hsum : ∀ r s : MvPolynomial (Fin k) R,
            ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i (r + s))) * gen x i
            = (∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i r)) * gen x i)
              + ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i s)) * gen x i := by
          intro r s
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_add, map_add, map_add, add_mul]
        rw [hsum, map_add, map_add]
        ring
      rw [heq]
      exact Ideal.add_mem _ hp hq
  | mul_X p j hp =>
      -- abbreviations
      set a := MvPolynomial.aeval x p with ha
      set b : Fin k → R := fun i => MvPolynomial.aeval x (MvPolynomial.pderiv i p) with hb
      -- the Taylor remainder of `p` (the IH term)
      set S : MvPolynomial (Fin k) R := ∑ i, C (b i) * gen x i with hS
      set E : MvPolynomial (Fin k) R := p - C a - S with hE
      -- aeval of derivative of `p * X j`
      have hderiv : ∀ i, MvPolynomial.aeval x (MvPolynomial.pderiv i (p * X j))
          = b i * x j + (if i = j then a else 0) := by
        intro i
        rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, aeval_X]
        by_cases hij : i = j
        · subst hij
          rw [MvPolynomial.pderiv_X_self, map_one, ite_eq_left rfl, mul_one, ← ha]
        · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij), map_zero, mul_zero, add_zero, ite_eq_right hij,
            add_zero]
      have haevalmul : MvPolynomial.aeval x (p * X j) = a * x j := by
        rw [map_mul, aeval_X]
      -- rewrite the sum of derivative-terms as `C (x j) * S + C a * gen j`
      have hsumderiv :
          ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i (p * X j))) * gen x i
          = C (x j) * S + C a * gen x j := by
        have step : ∀ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i (p * X j))) * gen x i
            = C (x j) * (C (b i) * gen x i) + (if i = j then C a * gen x j else 0) := by
          intro i
          rw [hderiv, map_add, add_mul]
          by_cases hij : i = j
          · subst hij
            rw [ite_eq_left rfl, ite_eq_left rfl, map_mul]; ring
          · rw [ite_eq_right hij, ite_eq_right hij, map_zero, zero_mul, add_zero, map_mul]; ring
        rw [Finset.sum_congr rfl (fun i _ => step i), Finset.sum_add_distrib,
          Finset.sum_ite_eq' Finset.univ j (fun _ => C a * gen x j)]
        rw [ite_eq_left (Finset.mem_univ j), ← Finset.mul_sum]
      -- the main polynomial identity
      have hSgenj : (∑ i, C (b i) * (gen x i * gen x j)) = S * gen x j := by
        rw [hS, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => by ring
      have key : (p * X j) - C (MvPolynomial.aeval x (p * X j))
          - ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i (p * X j))) * gen x i
          = (∑ i, C (b i) * (gen x i * gen x j)) + E * X j := by
        rw [hsumderiv, haevalmul, hSgenj, hE]
        have hgenj : gen x j = X j - C (x j) := rfl
        have hCmul : (C (a * x j) : MvPolynomial (Fin k) R) = C a * C (x j) := by rw [map_mul]
        rw [hgenj, hCmul]
        ring
      rw [key]
      -- both summands lie in M²
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hp)
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hMsq]
      exact Ideal.mul_mem_left _ _
        (Ideal.mul_mem_mul (gen_mem_vanishing x i) (gen_mem_vanishing x j))

end NonsingularImpCotangent

/-- **BPR Proposition 4.95, implication (a) ⟹ (c).** If `x` is a non-singular zero of the
extended system `map(P₁), …, map(P_k)` over `C`, then the maximal ideal `M_x` of `x` is contained
in `Ideal(𝒫, C) + M_x²`. (No `IsAlgClosed`/`CharZero` is needed for this direction.)
@isnad1 id=le.1h5v.s10.191328684cfa from=translated src=- shape=72d7e523 vocab=44789a47
-/
theorem nonsingular_imp_cotangent {C : Type*} [Field C] [Algebra K C]
    (P : Fin k → MvPolynomial (Fin k) K) (x : Fin k → C)
    (ha : IsNonsingularZero (fun i => MvPolynomial.map (algebraMap K C) (P i)) x) :
    MvPolynomial.vanishingIdeal C ({x} : Set (Fin k → C))
      ≤ idealOfPolysExt C (Finset.univ.image P)
        + (MvPolynomial.vanishingIdeal C ({x} : Set (Fin k → C))) ^ 2 := by
  classical
  set M := MvPolynomial.vanishingIdeal C ({x} : Set (Fin k → C)) with hM
  set I := idealOfPolysExt C (Finset.univ.image P) + M ^ 2 with hI
  -- The Jacobian of the extended system at `x`.
  set Pt : Fin k → MvPolynomial (Fin k) C :=
    fun i => MvPolynomial.map (algebraMap K C) (P i) with hPt
  set J := jacobian Pt x with hJ
  obtain ⟨hzero, hdet⟩ := ha
  -- `J.det` is a unit, so `J` is invertible.
  have hunit : IsUnit J.det := (isUnit_iff_ne_zero).2 hdet
  -- Each `Pt j` is a generator of `Ideal(𝒫, C)`.
  have hPt_mem : ∀ j, Pt j ∈ idealOfPolysExt C (Finset.univ.image P) := by
    intro j
    refine Ideal.subset_span ?_
    rw [Finset.coe_image, Set.mem_image]
    exact ⟨P j, by rw [Finset.coe_image, Set.mem_image]; exact ⟨j, Finset.mem_univ j, rfl⟩, rfl⟩
  -- Step C, part 1: `∑ i, C (J j i) * gen i ∈ I` for each `j`.
  have hw : ∀ j, (∑ i, MvPolynomial.C (J j i) * gen x i) ∈ I := by
    intro j
    have htay := taylor_mem x (Pt j)
    -- `aeval x (Pt j) = 0`
    have h0 : MvPolynomial.aeval x (Pt j) = 0 := hzero j
    -- `aeval x (pderiv i (Pt j)) = J j i`
    have hderiv : ∀ i, MvPolynomial.aeval x (MvPolynomial.pderiv i (Pt j)) = J j i := by
      intro i; rfl
    rw [h0, map_zero, sub_zero] at htay
    rw [Finset.sum_congr rfl (fun i _ => by rw [hderiv i] :
      ∀ i ∈ Finset.univ,
        MvPolynomial.C (MvPolynomial.aeval x (MvPolynomial.pderiv i (Pt j))) * gen x i
          = MvPolynomial.C (J j i) * gen x i)] at htay
    -- `Pt j - ∑ ... ∈ M²`, and `Pt j ∈ Ideal(𝒫,C)`, so the sum `∈ I`.
    have h1 : Pt j ∈ I := Ideal.mem_sup_left (hPt_mem j)
    have h2 : Pt j - ∑ i, MvPolynomial.C (J j i) * gen x i ∈ I :=
      Ideal.mem_sup_right htay
    have : (∑ i, MvPolynomial.C (J j i) * gen x i)
        = Pt j - (Pt j - ∑ i, MvPolynomial.C (J j i) * gen x i) := by ring
    rw [this]
    exact Ideal.sub_mem _ h1 h2
  -- Step C, part 2: each `gen i ∈ I`, via the inverse of `J`.
  have hgen : ∀ i, gen x i ∈ I := by
    intro i
    have hexpand : gen x i
        = ∑ j, MvPolynomial.C (J⁻¹ i j) * (∑ l, MvPolynomial.C (J j l) * gen x l) := by
      have hstep1 : (∑ j, MvPolynomial.C (J⁻¹ i j) * (∑ l, MvPolynomial.C (J j l) * gen x l))
          = ∑ l, MvPolynomial.C ((J⁻¹ * J) i l) * gen x l := by
        rw [Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum] :
          ∀ j ∈ Finset.univ,
            MvPolynomial.C (J⁻¹ i j) * (∑ l, MvPolynomial.C (J j l) * gen x l)
              = ∑ l, MvPolynomial.C (J⁻¹ i j) * (MvPolynomial.C (J j l) * gen x l))]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]; ring
      rw [hstep1, Matrix.nonsing_inv_mul J hunit]
      rw [Finset.sum_congr rfl (fun l _ => by rw [Matrix.one_apply] :
        ∀ l ∈ Finset.univ,
          MvPolynomial.C ((1 : Matrix (Fin k) (Fin k) C) i l) * gen x l
            = MvPolynomial.C (if i = l then 1 else 0) * gen x l)]
      rw [Finset.sum_congr rfl (fun l _ => by
        by_cases h : i = l
        · rw [ite_eq_left h, ite_eq_left h, map_one, one_mul]
        · rw [ite_eq_right h, ite_eq_right h, map_zero, zero_mul] :
        ∀ l ∈ Finset.univ,
          MvPolynomial.C (if i = l then 1 else 0) * gen x l
            = (if i = l then gen x l else 0))]
      rw [Finset.sum_ite_eq Finset.univ i (gen x), ite_eq_left (Finset.mem_univ i)]
    rw [hexpand]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Ideal.mul_mem_left _ _ (hw j)
  -- Assembly: `M = span (gen)` and every generator is in `I`.
  rw [hM, vanishing_eq_span]
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact hgen i

section CotangentImpSimple

variable {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]

end CotangentImpSimple

end Azurite.BPR.Chapter4
