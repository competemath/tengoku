/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormShell
import Tengoku.Seed.Data.Complex.Basic
import Tengoku.Seed.RingTheory.PowerSeries.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

noncomputable def harmonicThetaCoefficient
    (N : PDUnimodularLattice 24) (x y : N.carrier) (k : ℕ) : ℤ :=
  ∑ v : NormShell N (2 * k),
    (24 * N.pairing v.1 x * N.pairing v.1 y -
      N.pairing x y * N.pairing v.1 v.1)

noncomputable def harmonicThetaSeries
    (N : PDUnimodularLattice 24) (x y : N.carrier) : PowerSeries ℂ :=
  PowerSeries.mk fun k => (harmonicThetaCoefficient N x y k : ℂ)

@[simp]
theorem harmonicThetaSeries_coeff
    (N : PDUnimodularLattice 24) (x y : N.carrier) (k : ℕ) :
    (harmonicThetaSeries N x y).coeff k =
      (harmonicThetaCoefficient N x y k : ℂ) := by
  simp [harmonicThetaSeries]

end SRG266.Lattice
