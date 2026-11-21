import Tengoku.RainichKaluzaReconstruction.RainichKaluza.DifferentialCoupling

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bilinear differential-coupling invariant

Let `X=d𝓕` and `Y=v∧𝓕`.  On the generic branch the rescaled Bianchi equation
is `2X=aY`.  If the Lorentzian pairing of the three-form `Y` with itself is
nonzero, the signed coupling and its orientation-independent square are

`a = 2⟪X,Y⟫ / ⟪Y,Y⟫`,
`a² = 4⟪X,X⟫ / ⟪Y,Y⟫`.

The proofs below require only a real bilinear pairing, so they apply to an
indefinite Lorentzian form.  The non-null denominator is an explicit generic
branch assumption.  Reconstructing `X`, `Y`, and their pairing from curvature
is a later geometric step.
-/

namespace RainichKaluza

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Signed coupling extracted using a bilinear pairing.-/
noncomputable def couplingFromPairing
    (pairing : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (X Y : W) : ℝ :=
  2 * pairing X Y / pairing Y Y

/-- Orientation-independent squared coupling extracted using a bilinear
pairing.-/
noncomputable def couplingSqFromPairing
    (pairing : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (X Y : W) : ℝ :=
  4 * pairing X X / pairing Y Y

/-- The pairing ratio recovers the signed coupling from `2X=aY`.-/
theorem couplingFromPairing_eq_of_smul
    (pairing : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (X Y : W) (a : ℝ)
    (hscale : (2 : ℝ) • X = a • Y)
    (hnonnull : pairing Y Y ≠ 0) :
    couplingFromPairing pairing X Y = a := by
  have hpaired := congrArg (fun Z => pairing Z Y) hscale
  simp at hpaired
  unfold couplingFromPairing
  exact (div_eq_iff hnonnull).2 hpaired

/-- The quadratic pairing ratio recovers `a²` directly, without fixing the
orientation of `Y`.-/
theorem couplingSqFromPairing_eq_of_smul
    (pairing : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (X Y : W) (a : ℝ)
    (hscale : (2 : ℝ) • X = a • Y)
    (hnonnull : pairing Y Y ≠ 0) :
    couplingSqFromPairing pairing X Y = a ^ 2 := by
  have hpaired := congrArg (fun Z => pairing Z Z) hscale
  simp at hpaired
  unfold couplingSqFromPairing
  apply (div_eq_iff hnonnull).2
  nlinarith

/-- Reversing the scalar orientation reverses the signed pairing formula.-/
theorem couplingFromPairing_neg_source
    (pairing : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (X Y : W) :
    couplingFromPairing pairing X (-Y) =
      -couplingFromPairing pairing X Y := by
  simpa [couplingFromPairing] using
    (neg_div (pairing Y Y) (2 * pairing X Y))

/-- The squared pairing formula is invariant under scalar-orientation
reversal.-/
theorem couplingSqFromPairing_neg_source
    (pairing : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (X Y : W) :
    couplingSqFromPairing pairing X (-Y) =
      couplingSqFromPairing pairing X Y := by
  simp [couplingSqFromPairing]

/-- The primal and dual rescaled Maxwell channels yield the same `a²` whenever
they satisfy the common coupling equations and both pairing denominators are
non-null.-/
theorem couplingSqFromPairing_primal_dual_agree
    (pairing : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (dF dStarF vWedgeF vWedgeStarF : W) (a : ℝ)
    (h : CouplingCompatible a dF dStarF vWedgeF vWedgeStarF)
    (hprimal : pairing vWedgeF vWedgeF ≠ 0)
    (hdual : pairing vWedgeStarF vWedgeStarF ≠ 0) :
    couplingSqFromPairing pairing dF vWedgeF =
      couplingSqFromPairing pairing dStarF vWedgeStarF := by
  rw [couplingSqFromPairing_eq_of_smul pairing dF vWedgeF a h.1 hprimal]
  have hdualScale : (2 : ℝ) • dStarF = (-a) • vWedgeStarF := h.2
  rw [couplingSqFromPairing_eq_of_smul pairing dStarF vWedgeStarF
    (-a) hdualScale hdual]
  ring

end RainichKaluza
