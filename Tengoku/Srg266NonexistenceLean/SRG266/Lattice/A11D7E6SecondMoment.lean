/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.A11D7E6RootPlacement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

theorem a11D7E6D7Projection_A11Lift (u : Fin 11 → ℚ) :
    a11D7E6D7Projection (a11D7E6A11Lift u) = 0 := by
  ext i
  simp only [a11D7E6D7Projection, LinearMap.coe_mk, AddHom.coe_mk,
    a11D7E6D7Scalar, a11D7E6A11Lift, Pi.zero_apply]
  rcases finADEBlockEquiv a11D7E6Types i with j | (j | (j | j)) <;>
    simp [a11D7E6D7BlockScalar]

theorem a11D7E6D7Projection_E6Lift (u : Fin 6 → ℚ) :
    a11D7E6D7Projection (a11D7E6E6Lift u) = 0 := by
  ext i
  simp only [a11D7E6D7Projection, LinearMap.coe_mk, AddHom.coe_mk,
    a11D7E6D7Scalar, a11D7E6E6Lift, Pi.zero_apply]
  rcases finADEBlockEquiv a11D7E6Types i with j | (j | (j | j)) <;>
    simp [a11D7E6D7BlockScalar]
  exact j.elim

variable {W U Y : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]
  [AddCommGroup Y] [Module ℚ Y]

theorem marked_product_frame_moment_bound {ι : Type*} [Fintype ι]
    (B : LinearMap.BilinForm ℚ W) (C : LinearMap.BilinForm ℚ U)
    (g : ι → W) (s : Fin 7 → ℚ) (a : ℚ) (ha : 0 ≤ a)
    (hC : ∀ u, 0 ≤ C u u) (hm : ∀ w, (∑ i, (B w (g i))^2) ≤ a*B w w)
    (r : (W × (Fin 7 → ℚ)) × U) (hr : r.1.2 = 0) :
    (∑ i, (prodForm (prodForm B (standardRatForm 7)) C r ((g i, s), 0))^2) ≤
      a*prodForm (prodForm B (standardRatForm 7)) C r r := by
  simp only [prodForm_apply, hr, map_zero, LinearMap.zero_apply, add_zero]
  have h := hm r.1.1
  have hp := mul_nonneg ha (hC r.2)
  linarith

end SRG266.Lattice
