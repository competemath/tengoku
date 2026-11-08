module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.HadamardCongruence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Worked models for the parameterised congruence

Every statement in `AISafetyAtlas.SingularLearning.HadamardCongruence` is an existence statement
under hypotheses, and each set of hypotheses that could be jointly empty is witnessed here rather
than assumed to be satisfiable.

* The **congruence over an arbitrary parameter** is fired at `P = ℝ`, `E = ℝ` with the family
  `B p w w' = (1 + p ^ 2) * w * w'`, which genuinely moves with the parameter — a constant family
  would witness nothing, since the identity would already be a congruence for it.

* The **Morse–Bott normal form** is fired at `W = V = ℝ` with `f (η, ζ) = η * η`. This is the
  smallest function satisfying all three hypotheses at once: it vanishes on `{0} × V`, its
  `W`-derivative vanishes there, and its `W`-block Hessian at the origin is doubling, which is
  invertible. Without a witness of this shape the Morse–Bott statement would be a theorem about
  nothing — the three hypotheses could in principle contradict each other, and no other check in
  the repository would notice.

* The **finite-dimensional Morse lemma** is fired at `EuclideanSpace ℝ (Fin 1)` with the same
  square, to check that the classical nondegeneracy hypothesis — the Hessian form annihilating no
  nonzero vector — is dischargeable in the coordinates a matrix consumer works in.

The derivative computations all go through one generic square: for a continuous linear functional
`c`, the function `y ↦ c y * c y` has first derivative `(2 * c y) • c` and constant second
derivative `((2 : ℝ) • c).smulRight c`. Instantiating that at `c = ContinuousLinearMap.fst` on
`ℝ × ℝ` and at `c = EuclideanSpace.proj 0` on `EuclideanSpace ℝ (Fin 1)` is what makes the two
models cheap.
-/

noncomputable section

open scoped ContDiff

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

section Square

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The square of a continuous linear functional is differentiable, with the expected
derivative.-/
private theorem hasFDerivAt_sq (c : X →L[ℝ] ℝ) (x : X) :
    HasFDerivAt (fun y : X ↦ c y * c y) ((2 * c x) • c) x := by
  have hsmul : (2 * c x) • c = c x • (c : X →L[ℝ] ℝ) + c x • c := by
    rw [two_mul, add_smul]
  rw [hsmul]
  exact c.hasFDerivAt.mul c.hasFDerivAt

private theorem fderiv_sq (c : X →L[ℝ] ℝ) :
    fderiv ℝ (fun y : X ↦ c y * c y) = fun x ↦ (2 * c x) • c :=
  funext fun x ↦ (hasFDerivAt_sq c x).fderiv

private theorem fderiv_fderiv_sq (c : X →L[ℝ] ℝ) (x : X) :
    fderiv ℝ (fderiv ℝ fun y : X ↦ c y * c y) x = ((2 : ℝ) • c).smulRight c := by
  have hfun : (fun x : X ↦ (2 * c x) • (c : X →L[ℝ] ℝ))
      = ⇑(((2 : ℝ) • c).smulRight c) := by
    funext y
    simp
  rw [fderiv_sq, hfun]
  exact (ContinuousLinearMap.hasFDerivAt _).fderiv

private theorem contDiff_sq (c : X →L[ℝ] ℝ) : ContDiff ℝ ∞ fun y : X ↦ c y * c y :=
  c.contDiff.mul c.contDiff

/-- The same computations for a sum of two squares, which is the shape of the model with a
nonvanishing germ on the fibre.-/
private theorem fderiv_sq_add (c d : X →L[ℝ] ℝ) :
    fderiv ℝ (fun y : X ↦ c y * c y + d y * d y) = fun x ↦ (2 * c x) • c + (2 * d x) • d :=
  funext fun x ↦ ((hasFDerivAt_sq c x).add (hasFDerivAt_sq d x)).fderiv

private theorem fderiv_fderiv_sq_add (c d : X →L[ℝ] ℝ) (x : X) :
    fderiv ℝ (fderiv ℝ fun y : X ↦ c y * c y + d y * d y) x
      = ((2 : ℝ) • c).smulRight c + ((2 : ℝ) • d).smulRight d := by
  have hfun : (fun x : X ↦ (2 * c x) • (c : X →L[ℝ] ℝ) + (2 * d x) • d)
      = ⇑(((2 : ℝ) • c).smulRight c + ((2 : ℝ) • d).smulRight d) := by
    funext y
    simp
  rw [fderiv_sq_add, hfun]
  exact (ContinuousLinearMap.hasFDerivAt _).fderiv

private theorem contDiff_sq_add (c d : X →L[ℝ] ℝ) :
    ContDiff ℝ ∞ fun y : X ↦ c y * c y + d y * d y :=
  (c.contDiff.mul c.contDiff).add (d.contDiff.mul d.contDiff)

end Square

/-! ## The congruence over an arbitrary parameter -/

/-- Multiplication on `ℝ`, as an equivalence onto the dual.-/
private def qOne : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)) (fun _ ↦ by simp) (fun _ ↦ by ext; simp [mul_comm])

private theorem coe_qOne : (qOne : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) = ContinuousLinearMap.mul ℝ ℝ := rfl

/-- Doubled multiplication on `ℝ`, as an equivalence onto the dual. This is the `W`-block Hessian
of the model loss below.-/
private def qTwo : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ) :=
  ContinuousLinearEquiv.equivOfInverse ((2 : ℝ) • ContinuousLinearMap.mul ℝ ℝ)
    ((2⁻¹ : ℝ) • ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)) (fun _ ↦ by simp)
    (fun _ ↦ by ext; simp [mul_comm])

private theorem coe_qTwo :
    (qTwo : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) = (2 : ℝ) • ContinuousLinearMap.mul ℝ ℝ := rfl

/-- A family of symmetric forms on `ℝ` that genuinely moves with a real parameter.-/
private def movingForm (p : ℝ) : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  (1 + p ^ 2) • ContinuousLinearMap.mul ℝ ℝ

private theorem movingForm_apply (p w w' : ℝ) :
    movingForm p w w' = (1 + p ^ 2) * (w * w') := by
  simp [movingForm]

private theorem contDiff_movingForm : ContDiff ℝ ∞ movingForm := by
  have hbdd : IsBoundedSMul ℝ (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) :=
    @NormedSpace.toIsBoundedSMul ℝ (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) _ _ _
  exact (contDiff_const.add (contDiff_id.pow 2)).smul contDiff_const

private theorem symm_movingForm (p w w' : ℝ) : movingForm p w w' = movingForm p w' w := by
  simp only [movingForm_apply]
  ring

private theorem coe_qOne_eq : (qOne : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) = movingForm 0 := by
  rw [coe_qOne]
  simp [movingForm]

/-! ## The Morse–Bott normal form -/

/-- The model loss on `ℝ × ℝ`: the square of the first coordinate. Its critical set is the whole
second axis, on which it vanishes identically — the Morse–Bott setting.-/
private def sqFst (p : ℝ × ℝ) : ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ p * ContinuousLinearMap.fst ℝ ℝ ℝ p

private theorem sqFst_def : sqFst = fun p : ℝ × ℝ ↦
    ContinuousLinearMap.fst ℝ ℝ ℝ p * ContinuousLinearMap.fst ℝ ℝ ℝ p := rfl

/-- A model with a **nonvanishing germ on the fibre**: `f (η, ζ) = η * η + ζ * ζ`. Its
`W`-directional derivative still vanishes along `{0} × ℝ`, and its `W`-block Hessian at the
origin is still doubling, but `f (0, ζ) = ζ * ζ` is not identically zero.-/
private def sumSq (p : ℝ × ℝ) : ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ p * ContinuousLinearMap.fst ℝ ℝ ℝ p +
    ContinuousLinearMap.snd ℝ ℝ ℝ p * ContinuousLinearMap.snd ℝ ℝ ℝ p

/-! ## The finite-dimensional Morse lemma -/

/-- The model on `EuclideanSpace ℝ (Fin 1)`: the square of the single coordinate.-/
private def sqCoord (v : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  EuclideanSpace.proj (0 : Fin 1) v * EuclideanSpace.proj (0 : Fin 1) v

private theorem sqCoord_def : sqCoord = fun v : EuclideanSpace ℝ (Fin 1) ↦
    EuclideanSpace.proj (0 : Fin 1) v * EuclideanSpace.proj (0 : Fin 1) v := rfl

end AISafetyAtlas.Examples.SingularLearning

end
