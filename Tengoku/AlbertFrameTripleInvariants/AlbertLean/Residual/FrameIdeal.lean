import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.TrialitySquares
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms explicitFrameEquationValues_eq_source` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms equationsVanish_iff_source_fixedSpectrum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms RootSwapFixesExplicitFrameEquationValues` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Explicit fixed-spectrum frame equations on the residual chart

This module expands the six scalar equations `T = 0`, `S = -1`, `N = 0`
for two source encoders whose vector components lie in the selected
hyperbolic gauge plane.  The result depends only on the diagonal
coefficients, the gauge/Gram data, and entries of the evaluation matrix
`M = A X`.  Two additional root labels are then exchanged, and the six
values are proved unchanged.

This is a theorem about an explicit chart record.  It does not define the
manuscript's polynomial coordinate ring or generated frame ideal, and it
does not prove invariant-theoretic descent, invariant-field generation,
generic nontriviality, or identify this swap with a deck involution.
-/

namespace AlbertLean.Residual.FrameIdeal

open AlbertLean.Triality
open ExteriorSix CoordinateTensor StructuredCubic
open AlbertLean.Residual.TrialitySquares

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Source coordinates retained by the explicit residual chart.  The
orientation lift `kappa` and the four gauge coordinates are stored
separately; no denominator or gauge-section existence claim is hidden in
this record.-/
@[ext]
structure ExplicitFrameChart (K : Type u) [Field K] [CharZero K] where
  diagA : Fin 3 → K
  diagB : Fin 3 → K
  r1 : K
  z1 : K
  r2 : K
  z2 : K
  kappa : K
  s1 : SCoord K
  s2 : SCoord K
  c1 : CCoord K
  c2 : CCoord K

/-- First vector component in the fixed hyperbolic gauge plane.-/
def vectorA (x : ExplicitFrameChart K) : VCoord K :=
  { r := x.r1, z := x.z1, omega := 0 }

/-- Second vector component in the fixed hyperbolic gauge plane.-/
def vectorB (x : ExplicitFrameChart K) : VCoord K :=
  { r := x.r2, z := x.z2, omega := 0 }

/-- First source encoder represented by the chart.-/
def encoderA (x : ExplicitFrameChart K) : JCoord K :=
  { d1 := x.diagA 0
    d2 := x.diagA 1
    d3 := x.diagA 2
    v := vectorA x
    s := x.s1
    c := x.c1 }

/-- Second source encoder represented by the chart.-/
def encoderB (x : ExplicitFrameChart K) : JCoord K :=
  { d1 := x.diagB 0
    d2 := x.diagB 1
    d3 := x.diagB 2
    v := vectorB x
    s := x.s2
    c := x.c2 }

/-- The frozen evaluation matrix with rows `phi1, phi2, psi1, psi2` and
columns `p1, p2, q1, q2`.-/
def matrixM (x : ExplicitFrameChart K) : Matrix (Fin 4) (Fin 4) K :=
  momentMatrix x.s1 x.s2 x.c1 x.c2

/-! The following four values make the vector Gram/orientation data
explicit without dividing by two or by a chart pivot. -/

def gramV11 (x : ExplicitFrameChart K) : K := 2 * x.r1 * x.z1

def gramV12 (x : ExplicitFrameChart K) : K := x.r1 * x.z2 + x.r2 * x.z1

def gramV22 (x : ExplicitFrameChart K) : K := 2 * x.r2 * x.z2

def orientation (x : ExplicitFrameChart K) : K := x.r1 * x.z2 - x.r2 * x.z1

/-- The selected lift condition; it is data, not an existence theorem.-/
def IsKappaLift (x : ExplicitFrameChart K) : Prop :=
  orientation x = x.kappa

/-- The Gram discriminant identity is a formal consequence of the four
gauge coordinates.
@isnad1 id=eq.0h2v.s7.a74f1c798071 from=translated src=- shape=06a23341 vocab=5226ff1a
-/
theorem orientation_sq (x : ExplicitFrameChart K) :
    orientation x ^ 2 =
      gramV12 x ^ 2 - gramV11 x * gramV22 x := by
  simp [orientation, gramV11, gramV12, gramV22]
  ring

/-- A selected `kappa` lift obeys the locked Gram square relation.
@isnad1 id=eq.1h2v.s7.fd2b837b1816 from=translated src=- shape=d1545d8c vocab=4c9493e3
-/
theorem kappa_sq_of_isKappaLift (x : ExplicitFrameChart K)
    (h : IsKappaLift x) :
    x.kappa ^ 2 = gramV12 x ^ 2 - gramV11 x * gramV22 x := by
  rw [← h]
  exact orientation_sq x

/-- The six polynomial values whose simultaneous vanishing is the two-copy
fixed-spectrum condition.  The spur rows include `+1`, so they vanish
precisely when the source spur is `-1`.

The only matrix entries in the norm rows are `M13`, `M31`, `M24`, and
`M42` (using one-based manuscript indices).-/
@[ext]
structure FrameEquationValues (K : Type u) where
  traceA : K
  spurA : K
  normA : K
  traceB : K
  spurB : K
  normB : K

/-- Fully expanded residual-chart values.  Neither determinant-root label
occurs in this definition.-/
def explicitFrameEquationValues (x : ExplicitFrameChart K) :
    FrameEquationValues K where
  traceA := x.diagA 0 + x.diagA 1 + x.diagA 2
  spurA :=
    x.diagA 0 * x.diagA 1 + x.diagA 0 * x.diagA 2 +
      x.diagA 1 * x.diagA 2 - x.r1 * x.z1 -
      matrixM x 0 0 - matrixM x 2 2 + 1
  normA :=
    x.diagA 0 * x.diagA 1 * x.diagA 2 -
      x.diagA 0 * (x.r1 * x.z1) -
      x.diagA 1 * matrixM x 0 0 -
      x.diagA 2 * matrixM x 2 2 +
      x.r1 * matrixM x 0 2 + x.z1 * matrixM x 2 0
  traceB := x.diagB 0 + x.diagB 1 + x.diagB 2
  spurB :=
    x.diagB 0 * x.diagB 1 + x.diagB 0 * x.diagB 2 +
      x.diagB 1 * x.diagB 2 - x.r2 * x.z2 -
      matrixM x 1 1 - matrixM x 3 3 + 1
  normB :=
    x.diagB 0 * x.diagB 1 * x.diagB 2 -
      x.diagB 0 * (x.r2 * x.z2) -
      x.diagB 1 * matrixM x 1 1 -
      x.diagB 2 * matrixM x 3 3 +
      x.r2 * matrixM x 1 3 + x.z2 * matrixM x 3 1

/-- The same six values expressed directly through the accepted source
trace, spur, and norm.-/
def sourceFrameEquationValues (x : ExplicitFrameChart K) :
    FrameEquationValues K where
  traceA := sourceTrace (encoderA x)
  spurA := sourceSpur (encoderA x) + 1
  normA := sourceNorm (encoderA x)
  traceB := sourceTrace (encoderB x)
  spurB := sourceSpur (encoderB x) + 1
  normB := sourceNorm (encoderB x)

/-- Exact source expansion: the explicit six chart values are the accepted
source fixed-spectrum equations.
@isnad1 id=eq.0h2v.s5.2e282ea0f22a from=translated src=- shape=a8464171 vocab=a9952693
-/
theorem explicitFrameEquationValues_eq_source (x : ExplicitFrameChart K) :
    explicitFrameEquationValues x = sourceFrameEquationValues x := by
  apply FrameEquationValues.ext <;>
    simp [explicitFrameEquationValues, sourceFrameEquationValues,
      encoderA, encoderB, vectorA, vectorB, matrixM, momentMatrix,
      sourceTrace, sourceSpur, sourceNorm, nV, pf_coordinate, nS, nC,
      triality, BW, pairW] <;>
    ring

/-- Simultaneous vanishing of the six displayed values.-/
def EquationsVanish (v : FrameEquationValues K) : Prop :=
  v.traceA = 0 ∧ v.spurA = 0 ∧ v.normA = 0 ∧
    v.traceB = 0 ∧ v.spurB = 0 ∧ v.normB = 0

/-- The expanded equations vanish exactly when both source encoders have
the fixed spectrum `(T,S,N) = (0,-1,0)`.
@isnad1 id=iff.0h2v.s7.a02ba652ab95 from=translated src=- shape=427dc1c7 vocab=777b97b1
-/
theorem equationsVanish_iff_source_fixedSpectrum
    (x : ExplicitFrameChart K) :
    EquationsVanish (explicitFrameEquationValues x) ↔
      (sourceTrace (encoderA x) = 0 ∧
       sourceSpur (encoderA x) = -1 ∧
       sourceNorm (encoderA x) = 0 ∧
       sourceTrace (encoderB x) = 0 ∧
       sourceSpur (encoderB x) = -1 ∧
       sourceNorm (encoderB x) = 0) := by
  rw [explicitFrameEquationValues_eq_source]
  simp only [EquationsVanish, sourceFrameEquationValues]
  constructor
  · rintro ⟨hTa, hSa, hNa, hTb, hSb, hNb⟩
    refine ⟨hTa, ?_, hNa, hTb, ?_, hNb⟩
    · linear_combination hSa
    · linear_combination hSb
  · rintro ⟨hTa, hSa, hNa, hTb, hSb, hNb⟩
    refine ⟨hTa, ?_, hNa, hTb, ?_, hNb⟩
    · linear_combination hSa
    · linear_combination hSb

/-- Add the two determinant-root labels without changing the frozen chart
coordinates.-/
@[ext]
structure RootedExplicitFrameChart (K : Type u) [Field K] [CharZero K]
    extends ExplicitFrameChart K where
  delta : K
  deltaStar : K

/-- Chart-level exchange of the two root labels.-/
def rootSwap (x : RootedExplicitFrameChart K) :
    RootedExplicitFrameChart K where
  toExplicitFrameChart := x.toExplicitFrameChart
  delta := x.deltaStar
  deltaStar := x.delta

/--
@isnad1 id=eq.0h2v.s5.ecc7ceaebe74 from=translated src=- shape=9aae1eb9 vocab=2eac3ba6
-/
@[simp] theorem rootSwap_base (x : RootedExplicitFrameChart K) :
    (rootSwap x).toExplicitFrameChart = x.toExplicitFrameChart := rfl

/--
@isnad1 id=eq.0h2v.s5.d779e081b3c7 from=translated src=- shape=5a39ce4c vocab=fb1b36bd
-/
@[simp] theorem rootSwap_delta (x : RootedExplicitFrameChart K) :
    (rootSwap x).delta = x.deltaStar := rfl

/--
@isnad1 id=eq.0h2v.s5.af30470741cb from=translated src=- shape=5a39ce4c vocab=fb1b36bd
-/
@[simp] theorem rootSwap_deltaStar (x : RootedExplicitFrameChart K) :
    (rootSwap x).deltaStar = x.delta := rfl

/-- The chart-level root exchange is involutive.
@isnad1 id=eq.0h2v.s5.945adc1fc664 from=translated src=- shape=e17ccb0b vocab=ac3661c7
-/
@[simp] theorem rootSwap_involutive (x : RootedExplicitFrameChart K) :
    rootSwap (rootSwap x) = x := by
  cases x
  rfl

/-- Read the six explicit values from a rooted chart.-/
def rootedFrameEquationValues (x : RootedExplicitFrameChart K) :
    FrameEquationValues K :=
  explicitFrameEquationValues x.toExplicitFrameChart

/-- Exchanging the two determinant-root labels fixes every explicit
fixed-spectrum equation value.
@isnad1 id=eq.0h2v.s5.f8ff1b03ce07 from=translated src=- shape=9aae1eb9 vocab=8c1f4550
-/
@[simp] theorem rootSwap_fixes_frameEquationValues
    (x : RootedExplicitFrameChart K) :
    rootedFrameEquationValues (rootSwap x) = rootedFrameEquationValues x := rfl

/-- Consequently the simultaneous-vanishing predicate is root-swap stable
at the explicit record level.
@isnad1 id=iff.0h2v.s5.594eb40202e9 from=translated src=- shape=c9e914df vocab=8e56ce53
-/
theorem equationsVanish_rootSwap_iff (x : RootedExplicitFrameChart K) :
    EquationsVanish (rootedFrameEquationValues (rootSwap x)) ↔
      EquationsVanish (rootedFrameEquationValues x) := by
  rw [rootSwap_fixes_frameEquationValues]

/-- Fixed-equation comparison.  This is deliberately named for fixed equation values,
not for a polynomial ideal or a descended quotient.
@isnad1 id=and.0h2v.s5.a61ca049eb6a from=translated src=- shape=1099e765 vocab=6087868c
-/
theorem RootSwapFixesExplicitFrameEquationValues
    (x : RootedExplicitFrameChart K) :
    rootedFrameEquationValues (rootSwap x) = rootedFrameEquationValues x ∧
      (EquationsVanish (rootedFrameEquationValues (rootSwap x)) ↔
        EquationsVanish (rootedFrameEquationValues x)) := by
  exact ⟨rootSwap_fixes_frameEquationValues x, equationsVanish_rootSwap_iff x⟩

end AlbertLean.Residual.FrameIdeal
