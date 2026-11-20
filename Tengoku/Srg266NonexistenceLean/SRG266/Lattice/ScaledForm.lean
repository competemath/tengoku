/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Even

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {N : Submodule ℤ W}

theorem isSymm_smul_form (hB : B.IsSymm) (a : ℚ) : (a • B).IsSymm := by
  constructor
  intro x y
  change a * B x y = a * B y x
  rw [hB.eq x y]

theorem posDef_smul_form {a : ℚ} (ha : 0 < a)
    (hB : ∀ x : W, x ≠ 0 → 0 < B x x) :
    ∀ x : W, x ≠ 0 → 0 < (a • B) x x := by
  intro x hx
  exact mul_pos ha (hB x hx)

theorem isIntegral_int_smul_form (hB : IsIntegral B N) (m : ℤ) :
    IsIntegral ((m : ℚ) • B) N := by
  intro x hx y hy
  change (m : ℚ) * B x y ∈ (1 : Submodule ℤ ℚ)
  simpa only [zsmul_eq_mul] using (1 : Submodule ℤ ℚ).smul_mem m (hB hx y hy)

theorem isEven_int_smul_form (hB : IsEven B N) (m : ℤ) :
    IsEven ((m : ℚ) • B) N := by
  intro x hx
  obtain ⟨k, hk⟩ := hB x hx
  refine ⟨m * k, ?_⟩
  change (m : ℚ) * B x x = 2 * ((m * k : ℤ) : ℚ)
  rw [hk]
  push_cast
  ring

theorem isEven_even_smul_form (hB : IsIntegral B N) {m : ℤ} (hm : Even m) :
    IsEven ((m : ℚ) • B) N := by
  intro x hx
  obtain ⟨a, ha⟩ := hm
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp (hB hx x hx)
  have hk' : (k : ℚ) = B x x := by simpa using hk
  refine ⟨a * k, ?_⟩
  change (m : ℚ) * B x x = 2 * ((a * k : ℤ) : ℚ)
  rw [← hk', ha]
  push_cast
  ring

theorem mem_dual_smul_form_iff (a : ℚ) (x : W) :
    x ∈ (a • B).dualSubmodule N ↔ a • x ∈ B.dualSubmodule N := by
  constructor <;> intro h y hy <;>
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul] using h y hy

end SRG266.Lattice
