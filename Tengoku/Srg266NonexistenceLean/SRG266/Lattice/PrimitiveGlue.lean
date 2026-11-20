/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Glue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W U ι : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]
variable {B : LinearMap.BilinForm ℚ W} {C : LinearMap.BilinForm ℚ U}
variable {N : Submodule ℤ W} {M : Submodule ℤ U} {u : ι → W} {v : ι → U}

theorem mem_glueLattice_left_iff_of_complete_dual
    (hs : B.IsSymm) (hnd : B.Nondegenerate) (hl : IsLattice ℚ N)
    (hi : IsIntegral (prodForm B C) (glueLattice N M (fun i => (u i, v i))))
    (hd : B.dualSubmodule N = N ⊔ Submodule.span ℤ (Set.range u)) (x : W) :
    (x, (0 : U)) ∈ glueLattice N M (fun i => (u i, v i)) ↔ x ∈ N := by
  constructor
  · intro hx
    have hle : B.dualSubmodule N ≤ rightIntegral B x := by
      rw [hd]
      refine sup_le ?_ (Submodule.span_le.mpr ?_)
      · intro z hz
        change B x z ∈ (1 : Submodule ℤ ℚ)
        have hpair := hi hx (z, 0) (prod_le_glueLattice ⟨hz, zero_mem _⟩)
        simpa [prodForm_apply] using hpair
      · rintro _ ⟨i, rfl⟩
        change B x (u i) ∈ (1 : Submodule ℤ ℚ)
        have hpair := hi hx (u i, v i) (gen_mem_glueLattice i)
        simpa [prodForm_apply] using hpair
    have hdd : x ∈ B.dualSubmodule (B.dualSubmodule N) := fun _ hz => hle hz
    rwa [dual_dual B hl hnd hs] at hdd
  · intro hx
    exact prod_le_glueLattice ⟨hx, zero_mem _⟩

theorem mem_glueLattice_right_iff_of_complete_dual
    (hs : C.IsSymm) (hnd : C.Nondegenerate) (hl : IsLattice ℚ M)
    (hi : IsIntegral (prodForm B C) (glueLattice N M (fun i => (u i, v i))))
    (hd : C.dualSubmodule M = M ⊔ Submodule.span ℤ (Set.range v)) (x : U) :
    ((0 : W), x) ∈ glueLattice N M (fun i => (u i, v i)) ↔ x ∈ M := by
  constructor
  · intro hx
    have hle : C.dualSubmodule M ≤ rightIntegral C x := by
      rw [hd]
      refine sup_le ?_ (Submodule.span_le.mpr ?_)
      · intro z hz
        change C x z ∈ (1 : Submodule ℤ ℚ)
        have hpair := hi hx (0, z) (prod_le_glueLattice ⟨zero_mem _, hz⟩)
        simpa [prodForm_apply] using hpair
      · rintro _ ⟨i, rfl⟩
        change C x (v i) ∈ (1 : Submodule ℤ ℚ)
        have hpair := hi hx (u i, v i) (gen_mem_glueLattice i)
        simpa [prodForm_apply] using hpair
    have hdd : x ∈ C.dualSubmodule (C.dualSubmodule M) := fun _ hz => hle hz
    rwa [dual_dual C hl hnd hs] at hdd
  · intro hx
    exact prod_le_glueLattice ⟨zero_mem _, hx⟩

end SRG266.Lattice
