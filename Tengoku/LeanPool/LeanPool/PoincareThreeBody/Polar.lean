/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
module

public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.Delaunay
public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.Core
public import Tengoku

/-!
# Polar canonical coordinates for the rotating Kepler limit

This file defines the standard canonical polar-coordinate map and verifies directly that it sends
the zero-mass Cartesian Hamiltonian to the rotating Kepler Hamiltonian. This is the first coordinate
change on the route to Delaunay action-angle variables.
-/

@[expose] public section

namespace LeanPool.PoincareThreeBody

/-- Polar canonical state ordered as `(r, φ, pᵣ, pφ)`. -/
abbrev PolarState := Fin 4 → ℝ

/-- The canonical polar-to-Cartesian coordinate map. -/
noncomputable def polarToCartesian (state : PolarState) : PhaseSpace :=
  ![state 0 * Real.cos (state 1),
    state 0 * Real.sin (state 1),
    state 2 * Real.cos (state 1) - state 3 / state 0 * Real.sin (state 1),
    state 2 * Real.sin (state 1) + state 3 / state 0 * Real.cos (state 1)]

/-- The rotating Kepler Hamiltonian in canonical polar coordinates. -/
noncomputable def polarKeplerHamiltonian (state : PolarState) : ℝ :=
  ((state 2) ^ 2 + (state 3) ^ 2 / (state 0) ^ 2) / 2 - 1 / state 0 - state 3

/-- The inertial Kepler energy in canonical polar coordinates. -/
noncomputable def polarKeplerEnergy (state : PolarState) : ℝ :=
  ((state 2) ^ 2 + (state 3) ^ 2 / (state 0) ^ 2) / 2 - 1 / state 0

/-- The squared radial momentum prescribed by a Kepler energy
`-1 / (2 * firstAction²)` and angular momentum `secondAction`. -/
noncomputable def delaunayRadialMomentumSq
    (radius firstAction secondAction : ℝ) : ℝ :=
  2 / radius - 1 / firstAction ^ 2 - secondAction ^ 2 / radius ^ 2

/--
@isnad1 id=eq.0h1v.s5.036271a5f08f from=translated src=- shape=6dbec89c vocab=df0ed99e
-/
lemma polarKeplerHamiltonian_eq_energy_sub_angularMomentum (state : PolarState) :
    polarKeplerHamiltonian state = polarKeplerEnergy state - state 3 := by
  rfl

/-- On a negative Kepler energy shell, the radial momentum satisfies the radicand appearing in
the Delaunay generating function.
@isnad1 id=iff.2h4v.s7.555543be0c41 from=translated src=- shape=e4fd5cb7 vocab=f6e9af60
-/
theorem polarKeplerEnergy_eq_delaunay_iff {radius radialMomentum firstAction secondAction : ℝ}
    (hradius : radius ≠ 0) (hfirstAction : firstAction ≠ 0) :
    (radialMomentum ^ 2 + secondAction ^ 2 / radius ^ 2) / 2 - 1 / radius =
        -1 / (2 * firstAction ^ 2) ↔
      radialMomentum ^ 2 =
        delaunayRadialMomentumSq radius firstAction secondAction := by
  unfold delaunayRadialMomentumSq
  field_simp [hradius, hfirstAction]
  constructor <;> intro h <;> linarith

/-- The Delaunay Hamiltonian is the inertial Kepler energy minus angular momentum.
@isnad1 id=eq.0h2v.s6.8bafbaf51c7e from=translated src=- shape=572abad3 vocab=289dcb93
-/
lemma delaunayHamiltonian_eq_keplerEnergy_sub_angularMomentum
    (firstAction secondAction : ℝ) :
    delaunayHamiltonian ![firstAction, secondAction] =
      -1 / (2 * firstAction ^ 2) - secondAction := by
  rfl

/--
@isnad1 id=eq.0h1v.s6.8ee81a0bd7e2 from=translated src=- shape=f253f201 vocab=39de2887
-/
lemma polar_position_sq (state : PolarState) :
    (polarToCartesian state 0) ^ 2 + (polarToCartesian state 1) ^ 2 = (state 0) ^ 2 := by
  simp only [polarToCartesian, Matrix.cons_val_zero, Matrix.cons_val_one]
  have htrig := Real.sin_sq_add_cos_sq (state 1)
  nlinarith

/--
@isnad1 id=eq.1h1v.s7.43e93f1b219c from=translated src=- shape=8ce46588 vocab=e6cf33bf
-/
lemma polar_momentum_sq {state : PolarState} (hr : state 0 ≠ 0) :
    (polarToCartesian state 2) ^ 2 + (polarToCartesian state 3) ^ 2 =
      (state 2) ^ 2 + (state 3) ^ 2 / (state 0) ^ 2 := by
  simp [polarToCartesian]
  have htrig := Real.sin_sq_add_cos_sq (state 1)
  field_simp [hr]
  linear_combination ((state 2) ^ 2 * (state 0) ^ 2 + (state 3) ^ 2) * htrig

/--
@isnad1 id=eq.1h1v.s7.8dabe4bf5a1b from=translated src=- shape=8c81aa09 vocab=08227827
-/
lemma polar_angular_term {state : PolarState} (hr : state 0 ≠ 0) :
    polarToCartesian state 2 * polarToCartesian state 1 -
        polarToCartesian state 3 * polarToCartesian state 0 = -state 3 := by
  simp [polarToCartesian]
  have htrig := Real.sin_sq_add_cos_sq (state 1)
  field_simp [hr]
  linear_combination (-state 3) * htrig

/-- The Cartesian momentum paired with the radial coordinate differential is `pᵣ`.
@isnad1 id=eq.1h1v.s7.ab0136deae88 from=translated src=- shape=db996fda vocab=5dc94e23
-/
lemma polar_radial_momentum_identity {state : PolarState} (hr : state 0 ≠ 0) :
    polarToCartesian state 2 * Real.cos (state 1) +
        polarToCartesian state 3 * Real.sin (state 1) = state 2 := by
  simp [polarToCartesian]
  have htrig := Real.sin_sq_add_cos_sq (state 1)
  field_simp [hr]
  linear_combination (state 0 * state 2) * htrig

/-- The Cartesian momentum paired with the angular coordinate differential is `pφ`. Together with
`polar_radial_momentum_identity`, this verifies the canonical one-form under the polar formulas.
@isnad1 id=eq.1h1v.s7.4705e1a647f6 from=translated src=- shape=26b37d46 vocab=856dc45c
-/
lemma polar_angular_momentum_identity {state : PolarState} (hr : state 0 ≠ 0) :
    polarToCartesian state 2 * (-state 0 * Real.sin (state 1)) +
        polarToCartesian state 3 * (state 0 * Real.cos (state 1)) = state 3 := by
  simp [polarToCartesian]
  have htrig := Real.sin_sq_add_cos_sq (state 1)
  field_simp [hr]
  linear_combination (state 3) * htrig

/-- The Cartesian zero-mass Hamiltonian becomes the rotating Kepler Hamiltonian under the canonical
polar-coordinate formulas.
@isnad1 id=eq.1h1v.s5.45a7f9938d67 from=translated src=- shape=e3688150 vocab=c8b71da7
-/
theorem hamiltonian_zero_comp_polarToCartesian {state : PolarState} (hr : 0 < state 0) :
    hamiltonian 0 (polarToCartesian state) = polarKeplerHamiltonian state := by
  rw [hamiltonian_zero, polar_momentum_sq hr.ne', polar_position_sq]
  have hangular := polar_angular_term (state := state) hr.ne'
  have hsqrt : Real.sqrt ((state 0) ^ 2) = state 0 := by
    simpa [abs_of_pos hr] using Real.sqrt_sq_eq_abs (state 0)
  rw [hsqrt]
  unfold polarKeplerHamiltonian
  linarith

end LeanPool.PoincareThreeBody
