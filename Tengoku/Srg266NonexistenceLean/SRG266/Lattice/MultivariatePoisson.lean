/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.Analysis.Fourier.AddCircleMulti
import Tengoku.Seed.Analysis.Fourier.FourierTransform
import Tengoku.Seed.Analysis.Distribution.SchwartzSpace.Fourier
import Tengoku.Seed.Algebra.Module.ZLattice.Summable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace SRG266.Lattice

open scoped FourierTransform RealInnerProductSpace SchwartzMap

open Filter Asymptotics

theorem SchwartzMap.summable_zlattice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ProperSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (f : 𝓢(E, ℂ)) : Summable fun z : L => f z := by
  let r : ℝ := -(Module.finrank ℤ L : ℝ) - 1
  have hr : r < -(Module.finrank ℤ L : ℝ) := by
    dsimp only [r]
    linarith
  have hclosed : IsClosed (L : Set E) :=
    @AddSubgroup.isClosed_of_discrete E _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  have htend : Tendsto ((↑) : L → E) cofinite (cocompact E) :=
    hclosed.tendsto_coe_cofinite_of_isDiscrete DiscreteTopology.isDiscrete
  exact summable_of_isBigO (ZLattice.summable_norm_rpow L r hr)
    ((f.isBigO_cocompact_rpow r).comp_tendsto htend)

def intVectorToReal {n : ℕ} (z : Fin n → ℤ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => z i

def realVectorToUnitTorus {n : ℕ} (x : Fin n → ℝ) :
    UnitAddTorus (Fin n) :=
  fun i => (x i : UnitAddCircle)

structure PiPoissonPeriodizationData {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ) where

  periodization : C(UnitAddTorus (Fin n), ℂ)

  periodization_zero :
    periodization 0 = ∑' z : Fin n → ℤ, f (intVectorToReal z)

  fourierCoeff : ∀ m : Fin n → ℤ,
    UnitAddTorus.mFourierCoeff periodization m =
      𝓕 f (intVectorToReal m)

  latticeSummable : Summable fun z : Fin n → ℤ => f (intVectorToReal z)

  fourierSummable : Summable fun m : Fin n → ℤ =>
    𝓕 f (intVectorToReal m)

theorem piPoisson_of_periodization {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (P : PiPoissonPeriodizationData f) :
    (∑' z : Fin n → ℤ, f (intVectorToReal z)) =
      ∑' m : Fin n → ℤ, 𝓕 f (intVectorToReal m) := by
  have hcoeffSummable :
      Summable (UnitAddTorus.mFourierCoeff P.periodization) :=
    P.fourierSummable.congr fun m => (P.fourierCoeff m).symm
  have hseries := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    hcoeffSummable (0 : UnitAddTorus (Fin n))
  have hcoeffSeries :
      HasSum (UnitAddTorus.mFourierCoeff P.periodization)
        (P.periodization 0) := by
    refine hseries.congr_fun fun m => ?_
    simp [UnitAddTorus.mFourier]
  have hfourierSeries :
      HasSum (fun m : Fin n → ℤ => 𝓕 f (intVectorToReal m))
        (P.periodization 0) :=
    hcoeffSeries.congr_fun fun m => (P.fourierCoeff m).symm
  calc
    (∑' z : Fin n → ℤ, f (intVectorToReal z)) =
        P.periodization 0 := P.periodization_zero.symm
    _ = ∑' m : Fin n → ℤ, 𝓕 f (intVectorToReal m) :=
      hfourierSeries.tsum_eq.symm

end SRG266.Lattice
