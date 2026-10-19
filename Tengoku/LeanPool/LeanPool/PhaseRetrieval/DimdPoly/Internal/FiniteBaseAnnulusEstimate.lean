/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
module

public import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Definitions
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.FiniteBaseCircleEstimate
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.BlockLocalization
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ImportedAnalyticInputs
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ProductAnnulusCircle
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ProductBasisAndAnnuli
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.ProductAnnulusLocalization
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.TensorBasis
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Combinatorics.Matroid.Init
import Tengoku.Seed.Data.Nat.Factorial.DoubleFactorial
import Tengoku.Seed.Tactic.NormNum.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # FiniteBaseAnnulusEstimate -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace DimdPolyLEAN

/-!
# FiniteBaseAnnulusEstimate

Finite annulus-side transfer theorem for a normalized base point in `Pkappa`.
-/

private def mulCircleLIE_annulus (ω : _root_.Circle) : ℂ ≃ₗᵢ[ℝ] ℂ := by
  refine LinearIsometryEquiv.mk
    (LinearEquiv.ofBijective
      (LinearMap.mulLeft ℝ ((ω : ℂ)))
      ?_)
    ?_
  · refine ⟨?inj, ?surj⟩
    · intro x y hxy
      exact mul_left_cancel₀ (Circle.coe_ne_zero ω) (by simpa using hxy)
    · intro z
      refine ⟨((ω⁻¹ : _root_.Circle) : ℂ) * z, ?_⟩
      simp
  · intro x
    change ‖(ω : ℂ) * x‖ = ‖x‖
    have hω : ‖(ω : ℂ)‖ = 1 := Circle.norm_coe ω
    rw [norm_mul, hω, one_mul]

private theorem exists_maxCoord_annulus
    {d : Nat} (hd : 0 < d) (j : Idx d) :
    ∃ q0 : Fin d, ∀ q : Fin d, j q ≤ j q0 := by
  let q0 : Fin d := ⟨0, hd⟩
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨q0, Finset.mem_univ q0⟩
  rcases Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin d))) hne
      (f := fun q : Fin d => j q) with ⟨qmax, hqmax, hsup⟩
  refine ⟨qmax, ?_⟩
  intro q
  have hq_le : j q ≤ (Finset.univ : Finset (Fin d)).sup (fun r : Fin d => j r) :=
    Finset.le_sup (s := Finset.univ) (f := fun r : Fin d => j r) (by simp)
  simpa [hsup] using hq_le

private noncomputable def maxCoordAnnulus
    {d : Nat} (hd : 0 < d) (j : Idx d) : Fin d :=
  Classical.choose (exists_maxCoord_annulus hd j)

private def annulusBandStart
    {d : Nat} (j : Idx d) (q : Fin d) (M : Nat) : Nat :=
  (max (j q) M - M) ^ 2

private def annulusBandLength
    {d : Nat} (j : Idx d) (q : Fin d) (M : Nat) : Nat :=
  (j q + M + 1) ^ 2 - annulusBandStart j q M

private def localPartPkappa
    {d : Nat} {kappa : MultiIndex d}
    (j : Idx d) (M : Nat) (G : Pkappa d kappa) : Pkappa d kappa :=
  (Hermite1DimdLEAN.localPart j M ⟨G⟩).coeff

private def remainderPartPkappa
    {d : Nat} {kappa : MultiIndex d}
    (j : Idx d) (M : Nat) (G : Pkappa d kappa) : Pkappa d kappa :=
  (Hermite1DimdLEAN.remainderPart j M ⟨G⟩).coeff

private def baseDefectAnnulusMass
    {d : Nat} (kappa : MultiIndex d) (j : Idx d)
    (F G : Pkappa d kappa) : ℝ :=
  ∫ z, Set.indicator (productAnnulus j)
    (fun w => (‖evalPkappa kappa F w + evalPkappa kappa G w‖ -
      ‖evalPkappa kappa F w‖) ^ 2) z ∂ gammaD d

private def fiberIndexLow
    {d : Nat} (q0 : Fin d) (D : Nat) (alpha : Idx d) : Fin (D + 1) :=
  if h : alpha q0 ≤ D then ⟨alpha q0, Nat.lt_succ_of_le h⟩ else 0

private noncomputable def fiberCoeffLow
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (D : Nat) (F : Pkappa d kappa) (z : Cd d) :
    Fin (D + 1) → ℂ :=
  fun n =>
    ∑ alpha ∈ F.support.filter (fun alpha => fiberIndexLow q0 D alpha = n),
      F alpha * Phi kappa alpha z

private noncomputable def baseCoordDegree
    {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : Nat :=
  F.support.sup fun alpha => (Finset.univ : Finset (Fin d)).sup fun q => alpha q

private def fiberIndexBand
    {d : Nat} (q0 : Fin d) (N L : Nat) (hL : 1 ≤ L) (alpha : Idx d) : Fin L :=
  if h : alpha q0 < N + L then
    ⟨alpha q0 - N, by omega⟩
  else
    ⟨0, by omega⟩

private noncomputable def fiberCoeffBand
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (N L : Nat) (hL : 1 ≤ L) (H : Pkappa d kappa) (z : Cd d) :
    Fin L → ℂ :=
  fun m =>
    ∑ alpha ∈ H.support.filter (fun alpha => fiberIndexBand q0 N L hL alpha = m),
      H alpha * Phi kappa alpha z

end DimdPolyLEAN
