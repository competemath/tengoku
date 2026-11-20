/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoRootFinite
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

theorem normTwoRoot_dominant_moment
    {n : ℕ} (L : PDUnimodularLattice n)
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (θ : NormTwoRoot L) (hθ : 0 < f θ.1)
    (hdom : ∀ r : NormTwoRoot L, 0 < f r.1 → 0 ≤ L.pairing r.1 θ.1) :
    (∑ r : NormTwoRoot L, (L.pairing r.1 θ.1) ^ 2) =
      2 * (∑ r : NormTwoRoot L with 0 < f r.1, L.pairing r.1 θ.1) + 4 := by
  classical
  let p : NormTwoRoot L → ℤ := fun r => L.pairing r.1 θ.1
  have hneg :
      (∑ r : NormTwoRoot L, if 0 < f r.1 then 0 else (p r) ^ 2) =
      (∑ r : NormTwoRoot L, if 0 < f r.1 then (p r) ^ 2 else 0) := by
    rw [← Equiv.sum_comp (Equiv.neg (NormTwoRoot L))
      (fun r => if 0 < f r.1 then 0 else (p r) ^ 2)]
    apply Finset.sum_congr rfl
    intro r _
    have hr := hf r
    simp only [Equiv.neg_apply, NormTwoRoot.coe_neg, map_neg, p, LinearMap.neg_apply,
      neg_sq]
    by_cases h : 0 < f r.1
    · simp only [ite_eq_left h, ite_eq_right (show ¬ 0 < -f r.1 by omega)]
    · simp only [ite_eq_right h, ite_eq_left (show 0 < -f r.1 by omega)]
  have hsplit : (∑ r : NormTwoRoot L, (p r) ^ 2) =
      2 * (∑ r : NormTwoRoot L, if 0 < f r.1 then (p r) ^ 2 else 0) := by
    calc
      _ = (∑ r : NormTwoRoot L, if 0 < f r.1 then (p r) ^ 2 else 0) +
          (∑ r : NormTwoRoot L, if 0 < f r.1 then 0 else (p r) ^ 2) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r _
        split_ifs <;> simp
      _ = _ := by rw [hneg]; ring
  have hpoint (r : NormTwoRoot L) :
      (if 0 < f r.1 then (p r) ^ 2 else 0) =
      (if 0 < f r.1 then p r else 0) + (if r = θ then 2 else 0) := by
    by_cases heq : r = θ
    · subst r
      simp [p, θ.2, hθ]
    · have hne : r.1 - θ.1 ≠ 0 := by
        intro h
        exact heq (Subtype.ext (sub_eq_zero.mp h))
      have hb := L.positiveDefinite (r.1 - θ.1) hne
      have hs := L.symmetric.eq θ.1 r.1
      simp only [map_sub, LinearMap.sub_apply, r.2, θ.2, hs] at hb
      by_cases h : 0 < f r.1
      · have hn := hdom r h
        have hv : p r = 0 ∨ p r = 1 := by dsimp [p]; omega
        rcases hv with hv | hv <;> simp [h, heq, hv]
      · simp [h, heq]
  have hpos :
      (∑ r : NormTwoRoot L, if 0 < f r.1 then (p r) ^ 2 else 0) =
      (∑ r : NormTwoRoot L with 0 < f r.1, p r) + 2 := by
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_filter]
  change (∑ r : NormTwoRoot L, (p r) ^ 2) = _
  rw [hsplit, hpos]
  dsimp [p]
  ring

theorem normTwoRoot_dominant_positive_sum
    {n : ℕ} (L : PDUnimodularLattice n)
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (θ : NormTwoRoot L) (hθ : 0 < f θ.1)
    (hdom : ∀ r : NormTwoRoot L, 0 < f r.1 → 0 ≤ L.pairing r.1 θ.1)
    (c : ℤ)
    (hm : (∑ r : NormTwoRoot L, (L.pairing r.1 θ.1) ^ 2) = 2 * c) :
    (∑ r : NormTwoRoot L with 0 < f r.1, L.pairing r.1 θ.1) = c - 2 := by
  have h := normTwoRoot_dominant_moment L f hf θ hθ hdom
  rw [hm] at h
  omega

end SRG266.Lattice
