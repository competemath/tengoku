import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Comparison.GenericProductTransport
import Tengoku.Seed.Algebra.MvPolynomial.Eval
import Tengoku.Seed.RingTheory.Ideal.Maps
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms equations_vanishAlong_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rawFrameIdeal_le_ker_iff` (it only prints; the queue checks the axioms of every declaration). -/

/-! Independent raw equations for three labelled complete frames in the
frozen 27-coordinate F0 algebra. No chart or orbit enters the definition. -/

noncomputable section
namespace AlbertLean.Generic.AlbertRawFrameIdeal

open scoped BigOperators
open AlbertLean Generated
open AlbertLean.Comparison.GenericF0
open AlbertLean.Comparison.GenericProductTransport
open AlbertLean.Triality.GenericCoordinates

inductive Coordinate
  | entry (frame projector : Fin 3) (coord : Fin 27)
  deriving DecidableEq

abbrev CoordinateRing (k : Type*) [Field k] [CharZero k] :=
  MvPolynomial Coordinate k

variable {k L : Type*} [Field k] [CharZero k] [Field L] [CharZero L]

def universalVector (frame projector : Fin 3) : F0Coord (CoordinateRing k) :=
  fun coord => MvPolynomial.X (.entry frame projector coord)

/-- One coordinate of the product, written directly from the frozen rational
tensor rather than by extending the field-only source product to rings.-/
def productCoordinate (x y : F0Coord (CoordinateRing k)) (c : Fin 27) :
    CoordinateRing k :=
  ∑ a : Fin 27, ∑ b : Fin 27,
    x a * y b * MvPolynomial.C (algebraMap ℚ k (tensorCoeff a b c))

def unitCoordinate (c : Fin 27) : CoordinateRing k :=
  if c = 0 ∨ c = 1 ∨ c = 2 then 1 else 0

inductive EquationIndex
  | idempotence (frame projector : Fin 3) (coord : Fin 27)
  | traceOne (frame projector : Fin 3)
  | sumOne (frame : Fin 3) (coord : Fin 27)

def equation : EquationIndex → CoordinateRing k
  | .idempotence r i c =>
      productCoordinate (universalVector r i) (universalVector r i) c -
        universalVector r i c
  | .traceOne r i =>
      universalVector r i 0 + universalVector r i 1 + universalVector r i 2 - 1
  | .sumOne r c =>
      (∑ i : Fin 3, universalVector r i c) - unitCoordinate c

def rawFrameIdeal : Ideal (CoordinateRing k) := Ideal.span (Set.range equation)

structure IsRawFrameFamily (P : Fin 3 → Fin 3 → F0Coord L) : Prop where
  idempotent : ∀ r i, f0ProductK (P r i) (P r i) = P r i
  trace_one : ∀ r i, f0TraceK (P r i) = 1
  sum_one : ∀ r, ∑ i : Fin 3, P r i = f0OneK

def evaluationAlong (f : k →+* L) (P : Fin 3 → Fin 3 → F0Coord L) :
    CoordinateRing k →+* L :=
  MvPolynomial.eval₂Hom f (fun x => match x with
    | .entry r i c => P r i c)

/--
@isnad1 id=eq.0h7v.s7.bda9ba341792 from=translated src=- shape=6185ebb0 vocab=214fb76e
-/
@[simp] theorem evaluationAlong_universalVector
    (f : k →+* L) (P : Fin 3 → Fin 3 → F0Coord L)
    (r i : Fin 3) (c : Fin 27) :
    evaluationAlong f P (universalVector r i c) = P r i c := by
  simp [evaluationAlong, universalVector]

/--
@isnad1 id=eq.0h7v.s8.997f08aab97e from=translated src=- shape=7a22356b vocab=55ace303
-/
@[simp] theorem evaluationAlong_productCoordinate
    (f : k →+* L) (P : Fin 3 → Fin 3 → F0Coord L)
    (x y : F0Coord (CoordinateRing k)) (c : Fin 27) :
    evaluationAlong f P (productCoordinate x y c) =
      ∑ a : Fin 27, ∑ b : Fin 27,
        evaluationAlong f P (x a) * evaluationAlong f P (y b) *
          tensorCoeffK a b c := by
  simp [productCoordinate, tensorCoeffK, evaluationAlong]

/--
@isnad1 id=iff.0h4v.s7.be1f767769c9 from=translated src=- shape=31de057a vocab=df98203d
-/
theorem equations_vanishAlong_iff
    (f : k →+* L) (P : Fin 3 → Fin 3 → F0Coord L) :
    (∀ q, evaluationAlong f P (equation q) = 0) ↔ IsRawFrameFamily P := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro r i
      funext c
      simpa [equation, f0ProductK, sub_eq_zero] using
        h (.idempotence r i c)
    · intro r i
      simpa [equation, f0TraceK, sub_eq_zero] using h (.traceOne r i)
    · intro r
      funext c
      have hc := h (.sumOne r c)
      fin_cases c <;>
        simpa [equation, unitCoordinate, f0OneK, sub_eq_zero,
          Finset.sum_apply] using hc
  · intro h q
    cases q with
    | idempotence r i c =>
        have hc := congrFun (h.idempotent r i) c
        simpa [equation, f0ProductK, sub_eq_zero] using hc
    | traceOne r i =>
        simpa [equation, f0TraceK, sub_eq_zero] using h.trace_one r i
    | sumOne r c =>
        have hc := congrFun (h.sum_one r) c
        fin_cases c <;>
          simpa [equation, unitCoordinate, f0OneK, sub_eq_zero,
            Finset.sum_apply] using hc

/--
@isnad1 id=iff.0h4v.s8.b40cdeb6752a from=translated src=- shape=04ee3d4c vocab=7aad2b62
-/
theorem rawFrameIdeal_le_ker_iff
    (f : k →+* L) (P : Fin 3 → Fin 3 → F0Coord L) :
    rawFrameIdeal (k := k) ≤ RingHom.ker (evaluationAlong f P) ↔
      IsRawFrameFamily P := by
  rw [← equations_vanishAlong_iff f P]
  constructor
  · intro h q
    exact RingHom.mem_ker.mp (h (Ideal.subset_span (Set.mem_range_self q)))
  · intro h
    exact Ideal.span_le.2 (fun p hp => by
      rcases hp with ⟨q, rfl⟩
      exact RingHom.mem_ker.mpr (h q))

end AlbertLean.Generic.AlbertRawFrameIdeal
