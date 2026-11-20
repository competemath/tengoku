/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.DRootCoordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Glue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]
variable {B : LinearMap.BilinForm ℚ W} {C : LinearMap.BilinForm ℚ U}

theorem card_eq_288_of_isolated_d7
    (L : Submodule ℤ ((W × (Fin 7 → ℚ)) × U))
    (R : Finset ((W × (Fin 7 → ℚ)) × U))
    (hR : ∀ r, r ∈ R ↔ r ∈ L ∧ prodForm (prodForm B (standardRatForm 7)) C r r = 2)
    (hD7 : ∀ a, (((0 : W), a), (0 : U)) ∈ L ↔ a ∈ evenCoordinateLattice 7)
    (hsep : ∀ r ∈ R, r.1.2 = 0 ∨ (r.1.1 = 0 ∧ r.2 = 0))
    (hm : ∀ x y, 12 * (∑ r ∈ R,
        prodForm (prodForm B (standardRatForm 7)) C r x *
          prodForm (prodForm B (standardRatForm 7)) C r y) =
        (R.card : ℚ) * prodForm (prodForm B (standardRatForm 7)) C x y) :
    R.card = 288 := by
  classical
  let embed : DRoot 7 → (W × (Fin 7 → ℚ)) × U := fun r => ((0, r.ratVector), 0)
  have hinj : Function.Injective embed := by
    intro r s h
    exact DRoot.ratVector_injective (congrArg (fun z => z.1.2) h)
  let D : Finset ((W × (Fin 7 → ℚ)) × U) := Finset.univ.map ⟨embed, hinj⟩
  have hD : D ⊆ R := by
    intro z hz
    obtain ⟨r, _, rfl⟩ := Finset.mem_map.mp hz
    apply (hR _).mpr
    refine ⟨(hD7 _).mpr r.ratVector_mem_even, ?_⟩
    change B 0 0 + standardRatForm 7 r.ratVector r.ratVector + C 0 0 = 2
    simp only [map_zero, zero_add, add_zero, r.ratVector_norm]
  have hrest : ∀ r ∈ R, r ∉ D → (r.1.2 0) ^ 2 = 0 := by
    rintro ⟨⟨y, a⟩, z⟩ hr hnot
    rcases hsep _ hr with ha | ⟨hy, hz⟩
    · change a = 0 at ha
      simp [ha]
    · change y = 0 at hy
      change z = 0 at hz
      subst y
      subst z
      obtain ⟨hrL, hrnorm⟩ := (hR _).mp hr
      have hanorm : standardRatForm 7 a a = 2 := by
        simpa only [prodForm_apply, map_zero, LinearMap.zero_apply, zero_add, add_zero] using hrnorm
      obtain ⟨r, heq⟩ := DRoot.exists_ratVector_of_norm_two ((hD7 a).mp hrL) hanorm
      exfalso
      apply hnot
      refine Finset.mem_map.mpr ⟨r, Finset.mem_univ _, ?_⟩
      change ((0, r.ratVector), 0) = ((0, a), 0)
      rw [heq]
  have hsum : (∑ r ∈ R, (r.1.2 0) ^ 2) = 24 := by
    calc
      _ = ∑ r ∈ D, (r.1.2 0) ^ 2 := (Finset.sum_subset hD hrest).symm
      _ = ∑ r : DRoot 7, (r.ratVector 0) ^ 2 := by simp [D, embed]
      _ = 24 := (dRoot_rat_coordinate_zero_secondMoment 6).trans (by norm_num)
  let q : (W × (Fin 7 → ℚ)) × U := ((0, Pi.single 0 1), 0)
  have hpair (r) : prodForm (prodForm B (standardRatForm 7)) C r q = r.1.2 0 := by
    simp [q, prodForm_apply, standardRatForm_apply, Pi.single_apply, mul_ite]
  have hq : prodForm (prodForm B (standardRatForm 7)) C q q = 1 := by
    rw [hpair]
    simp [q]
  have h := hm q q
  rw [hq] at h
  simp only [hpair, ← pow_two, hsum, mul_one] at h
  have hc : (R.card : ℚ) = 288 := by linarith
  exact_mod_cast hc

end SRG266.Lattice
