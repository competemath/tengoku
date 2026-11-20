/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SimpleRootFirstMoment
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.DominantRootMoment

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

theorem normTwoRoot_positive_sum_pairing_combination
    {n : ℕ} (L : PDUnimodularLattice n)
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (z : simpleRootSet f → ℤ) :
    (∑ r : NormTwoRoot L with 0 < f r.1, L.pairing r.1 (simpleRootCombination f z)) =
      2 * (∑ s, z s) := by
  classical
  calc
    _ = ∑ s : simpleRootSet f, z s *
        (∑ r : NormTwoRoot L with 0 < f r.1, L.pairing r.1 s.1.1) := by
      simp only [simpleRootCombination, Fintype.linearCombination_apply, map_sum,
        map_smul, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ s : simpleRootSet f, z s * 2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [normTwoRoot_positive_sum_pairing_simple L f hf s.1 s.2]
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem normTwoRoot_scalar_eq_twice_dominant_height
    {n : ℕ} (L : PDUnimodularLattice n)
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (θ : NormTwoRoot L) (hθ : 0 < f θ.1)
    (hdom : ∀ r : NormTwoRoot L, 0 < f r.1 → 0 ≤ L.pairing r.1 θ.1)
    (z : simpleRootSet f → ℤ) (hz : simpleRootCombination f z = θ.1)
    (c : ℤ)
    (hm : (∑ r : NormTwoRoot L, (L.pairing r.1 θ.1) ^ 2) = 2 * c) :
    c = 2 * ((∑ s, z s) + 1) := by
  have hfirst := normTwoRoot_positive_sum_pairing_combination L f hf z
  rw [hz] at hfirst
  have hdomsum := normTwoRoot_dominant_positive_sum L f hf θ hθ hdom c hm
  omega

theorem normTwoRoot_dominant_of_simple_pairings
    {n : ℕ} (L : PDUnimodularLattice n)
    (f : L.carrier →+ ℤ) (θ : NormTwoRoot L)
    (hdom : ∀ s : simpleRootSet f, 0 ≤ L.pairing s.1.1 θ.1) :
    ∀ r : NormTwoRoot L, 0 < f r.1 → 0 ≤ L.pairing r.1 θ.1 := by
  intro r hr
  have hclosure : ∀ x,
      x ∈ AddSubmonoid.closure (normTwoRootVal '' simpleRootSet f) →
      0 ≤ L.pairing x θ.1 := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
        obtain ⟨s, hs, rfl⟩ := hx
        exact hdom ⟨s, hs⟩
    | zero => simp
    | add x y _ _ hx hy =>
        simpa only [map_add, LinearMap.add_apply] using add_nonneg hx hy
  exact hclosure r.1 (positiveRoot_mem_simpleRootClosure f hr)

end SRG266.Lattice
