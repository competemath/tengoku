import Tengoku.RainichKaluzaReconstruction.RainichKaluza.ReconstructionEquation
import Tengoku.Seed.Tactic.NoncommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basis-independent spectral reflections

An idempotent spectral projector determines an involutive reflection without
choosing eigenvectors.  When the projector commutes with the Ricci
endomorphism, this reflection lies in the Ricci centralizer and acts on the
space of reconstruction-equation solutions by conjugation.
-/

namespace RainichKaluza

/-- Reflection associated with an idempotent algebra element.-/
def reflectionOfIdempotent {A : Type*} [Ring A] (P : A) : A :=
  1 - 2 * P

/-- A reflection constructed from an idempotent is involutive.-/
theorem reflectionOfIdempotent_sq
    {A : Type*} [Ring A] (P : A) (hP : P * P = P) :
    reflectionOfIdempotent P * reflectionOfIdempotent P = 1 := by
  unfold reflectionOfIdempotent
  calc
    (1 - 2 * P) * (1 - 2 * P) = 1 - 4 * P + 4 * (P * P) := by
      noncomm_ring
    _ = 1 := by rw [hP]; noncomm_ring

/-- If a projector commutes with `R`, so does its reflection.-/
theorem reflectionOfIdempotent_commutes
    {A : Type*} [Ring A] (P R : A)
    (hPR : P * R = R * P) :
    reflectionOfIdempotent P * R = R * reflectionOfIdempotent P := by
  unfold reflectionOfIdempotent
  calc
    (1 - 2 * P) * R = R - 2 * (P * R) := by noncomm_ring
    _ = R - 2 * (R * P) := by rw [hPR]
    _ = R * (1 - 2 * P) := by noncomm_ring

/-- Conjugation by an idempotent reflection preserves every commuting Ricci
element.-/
theorem reflectionOfIdempotent_preserves
    {A : Type*} [Ring A] (P R : A)
    (hP : P * P = P)
    (hPR : P * R = R * P) :
    reflectionOfIdempotent P * R * reflectionOfIdempotent P = R := by
  rw [reflectionOfIdempotent_commutes P R hPR]
  rw [mul_assoc, reflectionOfIdempotent_sq P hP, mul_one]

/-- **Basis-independent spectral-orbit theorem.** A commuting idempotent
projector produces another reconstruction solution by reflecting the proposed
scalar tensor.-/
theorem reconstructionEquation_reflectionOfIdempotent
    {A : Type*} [Ring A] [Algebra ℝ A]
    (R V P : A) (traceV qSq : ℝ)
    (hP : P * P = P)
    (hPR : P * R = R * P)
    (hV : R * V + V * R - traceV • V =
      R * R - qSq • (1 : A)) :
    let J := reflectionOfIdempotent P
    R * (J * V * J) + (J * V * J) * R - traceV • (J * V * J) =
      R * R - qSq • (1 : A) := by
  dsimp
  exact reconstructionEquation_conjugation_invariant R V
    (reflectionOfIdempotent P) traceV qSq
    (reflectionOfIdempotent_sq P hP)
    (reflectionOfIdempotent_commutes P R hPR) hV

end RainichKaluza
