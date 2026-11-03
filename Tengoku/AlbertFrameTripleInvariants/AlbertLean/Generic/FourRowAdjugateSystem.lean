import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowAdjoint
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowNormalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms componentSolution_of_adjugate_equations` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms adjugate_equations_of_componentSolution` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Raw adjugate equations and normalized reconstruction

This composes the ordinary matrix lemmas. The three cyclic adjugate equations
supply determinant equality and inverse-adjugate coordinates, so neither is
an additional premise. It does not identify these equations with Albert frames.
-/

noncomputable section
namespace AlbertLean.Generic.FourRowAdjugateSystem

open FourRowFrameReduction FourRowComponents FourRowNormalization
open FourRowUniqueness (reconstructionDenominator)

variable {K : Type*} [Field K]

/-- Raw cyclic equations and zero component sums imply the normalized system.
Only the three second matrices are assumed invertible.-/
theorem componentSolution_of_adjugate_equations
    (a b c : Fin 3 → Mat3 K)
    (hb : ∀ i, (b i).det ≠ 0)
    (heq : ∀ i, (a i).adjugate = b i * c i ∧
      (c i).adjugate = a i * b i ∧ (b i).adjugate = c i * a i)
    (hbsum : b 0 + b 1 + b 2 = 0) (hcsum : c 0 + c 1 + c 2 = 0)
    (hden : (reconstructionDenominator (componentU (a 0) (a 1) (a 2))
      (componentV (a 0) (a 1)) ((a 1).det / (a 0).det) ((a 2).det / (a 0).det)
      (Matrix.trace (normalizedX (a 0) (b 0) (b 1)))).det ≠ 0) :
    ComponentSolution (a 0) (a 1) (a 2) (normalizedX (a 0) (b 0) (b 1)) := by
  have hp (i : Fin 3) :=
    (FourRowAdjoint.parametrized_iff_adjugate_equations (a i) (b i) (c i) (hb i)).mpr
      (heq i)
  have ha (i : Fin 3) : (a i).det ≠ 0 := (hp i).1 ▸ hb i
  apply componentSolution_of_raw (a 0) (a 1) (a 2) (b 0) (b 1) (b 2)
    (ha 0) (ha 1) (ha 2) (hp 0).1 (hp 1).1 (hp 2).1 hbsum _ hden
  simpa only [cslotSum, ← (hp 0).2, ← (hp 1).2, ← (hp 2).2] using hcsum

/-- Reconstructed normalized components satisfy all cyclic adjugate equations
and both zero-sum laws. The fixed first matrices may be supplied separately
with trace-one and sum-identity hypotheses at a later model interface.-/
theorem adjugate_equations_of_componentSolution
    (a0 a1 a2 X : Mat3 K)
    (ha0 : a0.det ≠ 0) (ha1 : a1.det ≠ 0) (ha2 : a2.det ≠ 0)
    (hX : ComponentSolution a0 a1 a2 X) :
    let a : Fin 3 → Mat3 K := ![a0, a1, a2]
    let b : Fin 3 → Mat3 K := ![a0, X * a0, -(1 + X) * a0]
    let c : Fin 3 → Mat3 K := fun i => (b i)⁻¹ * (a i).adjugate
    (∀ i, (a i).adjugate = b i * c i ∧
      (c i).adjugate = a i * b i ∧ (b i).adjugate = c i * a i) ∧
      b 0 + b 1 + b 2 = 0 ∧ c 0 + c 1 + c 2 = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact FourRowAdjoint.parametrized_adjugate_equations a0 a0 ha0 rfl
    · exact FourRowAdjoint.parametrized_adjugate_equations a1 (X * a0)
        (hX.det_b1 ▸ ha1) hX.det_b1
    · exact FourRowAdjoint.parametrized_adjugate_equations a2 (-(1 + X) * a0)
        (hX.det_b2 ▸ ha2) hX.det_b2
  · change a0 + X * a0 + -(1 + X) * a0 = 0
    simp only [neg_mul, add_mul, one_mul]
    abel
  · exact hX.inverse_adjugate_sum

end AlbertLean.Generic.FourRowAdjugateSystem
