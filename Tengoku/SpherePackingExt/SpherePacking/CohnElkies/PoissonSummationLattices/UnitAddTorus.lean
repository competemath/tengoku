module
public import Tengoku.Seed.Analysis.Complex.Exponential
public import Tengoku.Seed.Analysis.Fourier.AddCircleMulti
public import Tengoku.Seed.Analysis.InnerProductSpace.PiL2
public import Tengoku.Seed.MeasureTheory.Constructions.Pi
public import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
public import Tengoku.Seed.MeasureTheory.Integral.Pi
public import Tengoku.Seed.MeasureTheory.Measure.Haar.InnerProductSpace
public import Tengoku.Seed.Topology.Algebra.Group.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Helper lemmas about the quotient map `(Fin n → ℝ) → (ℝ/ℤ)^n` used in the Poisson summation
development.
-/

open scoped BigOperators Real
open MeasureTheory

namespace SchwartzMap.UnitAddTorus

/-- The coordinatewise quotient map `(Fin n → ℝ) → (ℝ/ℤ)^n`.-/
@[expose] public def coeFun (n : ℕ) : (Fin n → ℝ) → UnitAddTorus (Fin n) :=
  fun x i => (x i : UnitAddCircle)

/-- A homeomorphism `α × (Fin n → α) ≃ (Fin (n+1) → α)`, specialized to constant families.-/
def finSuccPiHomeomorph (α : Type*) [TopologicalSpace α] (n : ℕ) :
    (α × (Fin n → α)) ≃ₜ (Fin n.succ → α) where
  toEquiv := Fin.consEquiv (fun _ ↦ α)
  continuous_toFun := by
    simpa [Fin.consEquiv] using Continuous.finCons (by fun_prop) (by fun_prop)
  continuous_invFun := by fun_prop

theorem mFourier_apply_coeFun (n : ℕ) (k : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier k (coeFun n x) =
      Complex.exp
        (2 * π * Complex.I *
          (∑ i : Fin n, (k i : ℝ) * x i)) := by
  -- Unfold, then rewrite `fourier` explicitly on real representatives and use `exp_sum`.
  simpa [UnitAddTorus.mFourier, ContinuousMap.coe_mk, coeFun, fourier_coe_apply, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using
    (Complex.exp_sum (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => 2 * π * Complex.I * ((k i : ℝ) * x i))).symm

end SchwartzMap.UnitAddTorus
