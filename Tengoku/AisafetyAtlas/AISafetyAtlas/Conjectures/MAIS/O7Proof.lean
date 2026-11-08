module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Conjectures.MAIS.O7
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.ChartGerm
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.StratumTransport
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.OrbitTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# MAIS-O7 — unconditional verification of the scalar counterexample

This module proves the issue #5 candidate at the two-sided volume-order level,
in both its strict and weak threshold conventions.  There is no literature
frontier, eigenvalue-law assumption, analytic Morse lemma, or candidate-shaped
hypothesis.

At the origin the centered loss is locally comparable to the absolute dot
product; `IndefiniteQuadratic.lean` proves that germ has pair `(1,1)` by an
explicit integral.  On the terminal fiber the residual block in the atlas's
elimination chart is empty, so the existing chart and orbit transports give
`(1/2,1)` unconditionally at every factorization.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.SingularLearning
open Set Filter Topology
open scoped Matrix

@[simp] public theorem residualAmplitude_zero : residualAmplitude 0 = 0 := by
  simp [residualAmplitude, residualX, residualY]

private theorem hasLocalVolumeOrder_o7_canonical :
    HasLocalVolumeOrder
      (fun x => rrrLoss (partialIdMatrix 1 1 1)
        ((matrixPairEquiv 1 1 2).symm x).1
        ((matrixPairEquiv 1 1 2).symm x).2)
      (matrixPairCoords (canonicalA 1 2 1 1 1) (canonicalB 1 2 1 1))
      (1 / 2) 1 := by
  have hchart : HasLocalVolumeOrder
      (chartGerm (elimQ 1 1 1 1) (elimP 1 1) (elimH 2 1 1 1)
        (elimN 1 1) (elimGauge 1 1 2 1 1 1)) 0
      ((elimQ 1 1 1 1 : ℝ) / 2) 1 :=
    hasLocalVolumeOrder_chartGerm_residual_zero (by norm_num [elimQ])
      (Or.inl (by norm_num [elimP]))
  have h := hasLocalVolumeOrder_rrrLoss_canonical
    (M := 1) (N := 1) (H := 2) (r := 1) (a := 1) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hchart
  norm_num [elimQ] at h
  exact h

private theorem o7_factorization_of_terminal {s : ℝ} {w : O7Space}
    (hw : w ∈ o7TerminalRung s) :
    residualY 1 1 2 w * residualX 1 1 2 w = o7Target s := by
  ext i j
  fin_cases i
  fin_cases j
  simpa [o7TerminalRung, residualAmplitude, o7Target, partialIdMatrix]
    using hw

private theorem o7_terminal_nonempty {s : ℝ} :
    (o7TerminalRung s).Nonempty := by
  let A := canonicalA 1 2 1 1 1
  let B := s • canonicalB 1 2 1 1
  refine ⟨matrixPairCoords A B, ?_⟩
  have hBA : B * A = o7Target s := by
    rw [show B = s • canonicalB 1 2 1 1 from rfl,
      Matrix.smul_mul, canonicalB_mul_canonicalA (by norm_num) (by norm_num)
        (by norm_num)]
    rfl
  have hamp : residualAmplitude (matrixPairCoords A B) = s := by
    have hentry := congrFun (congrFun hBA 0) 0
    simpa [residualAmplitude, matrixPairCoords, residualX, residualY, o7Target,
      partialIdMatrix]
      using hentry
  exact hamp

private theorem hasO7PairAt_of_volumeOrder {s lam : ℝ} {w : O7Space} {m : ℕ}
    (h : HasLocalVolumeOrder (centeredBandGerm (o7Loss s) w) w lam m) :
    HasO7PairAt s w lam m :=
  ⟨h, hasStrictLocalVolumeOrder_of_hasLocalVolumeOrder h⟩

private theorem o7RungExponents_eq_singleton {s lam : ℝ} {C : Set O7Space}
    (hne : C.Nonempty)
    (hpair : ∀ w ∈ C, HasO7PairAt s w lam 1) :
    o7RungExponents s C = {lam} := by
  ext lam'
  constructor
  · rintro ⟨w, hw, m, hm⟩
    have hu := volumeOrder_unique hm.1 (hpair w hw).1
    simpa using hu.1
  · intro hlam'
    have heq : lam' = lam := by simpa using hlam'
    subst lam'
    obtain ⟨w, hw⟩ := hne
    exact ⟨w, hw, 1, hpair w hw⟩

end AISafetyAtlas.Conjectures.MAIS
