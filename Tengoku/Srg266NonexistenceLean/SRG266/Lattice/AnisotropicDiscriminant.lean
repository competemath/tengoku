/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Discriminant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {P : Submodule ℤ W}

/--
@isnad1 id=mem.4h4v.s8.dff9bf283b15 from=translated src=- shape=1b152c21 vocab=e937d607
-/
theorem IsMaximalIntegral.mem_of_dual_of_integral_norm
    (hmax : IsMaximalIntegral B P) (hsymm : B.IsSymm) {y : W}
    (hy : y ∈ B.dualSubmodule P) (hnorm : B y y ∈ (1 : Submodule ℤ ℚ)) : y ∈ P := by
  have heq := hmax.maximal (P ⊔ Submodule.span ℤ {y}) le_sup_left
    (isIntegral_sup_span_singleton B hsymm hmax.integral hy hnorm)
  have hmem : y ∈ P ⊔ Submodule.span ℤ {y} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  rwa [heq] at hmem

/--
@isnad1 id=iff.3h5v.s11.5b597ed4dcac from=translated src=- shape=1962aa2d vocab=0f487544
-/
theorem discPairing_self_eq_zero_iff_of_maximal {p : ℕ} (hp : p ≠ 0)
    (hsymm : B.IsSymm) (hmax : IsMaximalIntegral B P) (d : discGroup B P p) :
    discPairing B P p hsymm d d = 0 ↔ d = 0 := by
  constructor
  · intro hd
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ d
    rw [discPairing_mk] at hd
    apply discGroup_mk_eq_zero_iff.mpr
    apply hmax.mem_of_dual_of_integral_norm hsymm (torsion_mem_dual y)
    exact mem_one_of_dvd_discNum hp (torsion_mem_dual y) (torsion_zsmul_mem y)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd)
  · rintro rfl
    simp

end SRG266.Lattice
