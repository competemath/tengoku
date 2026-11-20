/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PDTransport
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.RootSecondMoment
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoRootSeparator
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.DominantRootHeight

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators Classical

variable {X : Type*} [AddCommGroup X] [Module ℚ X]
variable {F : LinearMap.BilinForm ℚ X} {H : Submodule ℤ X}

/--
@isnad1 id=ex.8h6v.s12.6925dd47b547 from=translated src=- shape=e2904977 vocab=7eb8a061
-/
theorem exists_integral_simple_root_data {n : ℕ}
    (hs : F.IsSymm) (hpd : ∀ x : X, x ≠ 0 → 0 < F x x)
    (hrank : Module.finrank ℚ X = n) (hl : IsLattice ℚ H)
    (hself : F.dualSubmodule H = H)
    (R : Finset X) (hR : ∀ r, r ∈ R ↔ r ∈ H ∧ F r r = 2)
    (c : ℤ) (hc : c ≠ 0)
    (hm : ∀ x y : X, (∑ r ∈ R, F r x * F r y) = (c : ℚ) * F x y) :
    ∃ (N : PDUnimodularLattice n) (e : H ≃ₗ[ℤ] N.carrier),
      (∀ u v : H, ((N.pairing (e u) (e v) : ℤ) : ℚ) = F (u : X) (v : X)) ∧
      Fintype.card (NormTwoRoot N) = R.card ∧
      RootSecondMomentIdentity N c ∧
      (∃ f : N.carrier →+ ℤ,
        (∀ r : NormTwoRoot N, f r.1 ≠ 0) ∧
        Fintype.card (simpleRootSet f) = n ∧
        IsPositiveCartan (simpleRootGraph f) ∧
        (∀ (θ : NormTwoRoot N) (z : simpleRootSet f → ℤ),
          simpleRootCombination f z = θ.1 → 0 < f θ.1 →
          (∀ s : simpleRootSet f, 0 ≤ N.pairing s.1.1 θ.1) →
          c = 2 * ((∑ s, z s) + 1))) := by
  classical
  obtain ⟨N, e, hpair⟩ := exists_pdUnimodularLattice hs hpd hrank hl hself
  let value : NormTwoRoot N → X := fun r => (e.symm r.1 : X)
  have hinj : Function.Injective value := by
    intro r s h
    apply Subtype.ext
    apply e.symm.injective
    exact Subtype.ext h
  let R' : Finset X := Finset.univ.map ⟨value, hinj⟩
  have hcomplete (x : X) : x ∈ R' ↔ x ∈ H ∧ F x x = 2 := by
    constructor
    · intro hx
      obtain ⟨r, _, rfl⟩ := Finset.mem_map.mp hx
      refine ⟨(e.symm r.1).property, ?_⟩
      change F (e.symm r.1 : X) (e.symm r.1 : X) = 2
      have h := hpair (e.symm r.1) (e.symm r.1)
      simpa only [LinearEquiv.apply_symm_apply, r.2, Int.cast_ofNat] using h.symm
    · rintro ⟨hx, hn⟩
      have hnorm : N.pairing (e ⟨x, hx⟩) (e ⟨x, hx⟩) = 2 := by
        have hQ := (hpair ⟨x, hx⟩ ⟨x, hx⟩).trans hn
        exact_mod_cast hQ
      refine Finset.mem_map.mpr ⟨⟨e ⟨x, hx⟩, hnorm⟩, Finset.mem_univ _, ?_⟩
      simp [value]
  have hRR : R' = R := Finset.ext fun x => (hcomplete x).trans (hR x).symm
  have hcard : Fintype.card (NormTwoRoot N) = R.card := by
    rw [← hRR]
    simp [R']
  have hp (r : NormTwoRoot N) (x : N.carrier) :
      ((N.pairing r.1 x : ℤ) : ℚ) = F (value r) (e.symm x : X) := by
    simpa only [LinearEquiv.apply_symm_apply] using hpair (e.symm r.1) (e.symm x)
  have hsum (x y : X) : (∑ r ∈ R, F r x * F r y) =
      ∑ r : NormTwoRoot N, F (value r) x * F (value r) y := by
    rw [← hRR]
    simp [R']
  have hmoment : RootSecondMomentIdentity N c := by
    intro x y
    have h := hm (e.symm x : X) (e.symm y : X)
    rw [hsum, ← hpair (e.symm x) (e.symm y)] at h
    simp_rw [← hp] at h
    simp only [LinearEquiv.apply_symm_apply] at h
    exact_mod_cast h
  obtain ⟨f, hf⟩ := exists_rootSeparatingFunctional N
  have hfull := normTwoRoots_fullRank_of_secondMoment N hc hmoment
  refine ⟨N, e, hpair, hcard, hmoment, f, hf,
    card_simpleRootSet_eq_of_fullRank f hf hfull, simpleRootGraph_isPositiveCartan f hf, ?_⟩
  intro θ z hz hθ hd
  apply normTwoRoot_scalar_eq_twice_dominant_height N f hf θ hθ
    (normTwoRoot_dominant_of_simple_pairings N f θ hd) z hz c
  have h := hmoment θ.1 θ.1
  simpa only [← pow_two, θ.2, mul_comm] using h

end SRG266.Lattice
