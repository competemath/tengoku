import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ProductDiagonal
import Tengoku.Seed.Algebra.Field.Subfield.Basic
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms power_eq_weighted_projectors` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms diagonal_projectors` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms power_diagonal_mem` (it only prints; the queue checks the axioms of every declaration). -/

/-!
The generic source-coordinate version of the
literal 54-cell ledger and its fixed linear change to power moments.
No frame equations, coverage, invariant-field generation or degree premise.
-/

noncomputable section
namespace AlbertLean.Generic.ResidualLedgerPower

open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Residual.TrialitySquares
open AlbertLean.Generic.ProductDiagonal

variable {K : Type*} [Field K] [CharZero K]

def spectralProjector (a : JCoord K) : Fin 3 → JCoord K :=
  ![(2 : K)⁻¹ • (sourceSquare a - a), sourceOne - sourceSquare a,
    (2 : K)⁻¹ • (sourceSquare a + a)]

def power (a : JCoord K) : Fin 3 → JCoord K := ![sourceOne, a, sourceSquare a]

def powerWeight : Fin 3 → Fin 3 → K := ![![1, 1, 1], ![-1, 0, 1], ![1, 0, 1]]

/-- This inverse is a polynomial identity; lawful-frame premises are unnecessary.
@isnad1 id=eq.0h3v.s7.78c0b10ffee5 from=translated src=- shape=bf310a91 vocab=9bfab547
-/
theorem power_eq_weighted_projectors (a : JCoord K) (p : Fin 3) :
    power a p = ∑ j, powerWeight (K := K) p j • spectralProjector a j := by
  fin_cases p <;>
    simp [power, powerWeight, spectralProjector, Fin.sum_univ_succ] <;> module

/--
@isnad1 id=mem.0h4v.s5.313fcb0035fa from=translated src=- shape=af9af94b vocab=97c868b6
-/
theorem powerWeight_mem (F : Subfield K) (p j : Fin 3) :
    powerWeight p j ∈ F := by
  fin_cases p <;> fin_cases j <;> simp [powerWeight, F.zero_mem, F.one_mem, F.neg_mem]

def diagLinear (i : Fin 3) : JCoord K →ₗ[K] K where
  toFun x := ![x.d1, x.d2, x.d3] i
  map_add' := by intro x y; fin_cases i <;> rfl
  map_smul' := by intro r x; fin_cases i <;> rfl

def diagonalUnit (i : Fin 3) : JCoord K :=
  diagonal (if i = 0 then 1 else 0) (if i = 1 then 1 else 0)
    (if i = 2 then 1 else 0)

/--
@isnad1 id=eq.0h3v.s7.0d923aac3099 from=translated src=- shape=bb0a9f06 vocab=2ba0d523
-/
theorem diagonal_trace (i : Fin 3) (x : JCoord K) :
    sourceTraceForm (diagonalUnit i) x = diagLinear i x := by
  rw [diagonalUnit, sourceTraceForm_diagonal_left]
  fin_cases i <;> simp [diagLinear]

@[simp] private theorem sub_d1 (x y : JCoord K) : (x - y).d1 = x.d1 - y.d1 := rfl
@[simp] private theorem sub_d2 (x y : JCoord K) : (x - y).d2 = x.d2 - y.d2 := rfl
@[simp] private theorem sub_d3 (x y : JCoord K) : (x - y).d3 = x.d3 - y.d3 := rfl
@[simp] private theorem sub_v (x y : JCoord K) : (x - y).v = x.v - y.v := rfl
@[simp] private theorem sub_s (x y : JCoord K) : (x - y).s = x.s - y.s := rfl
@[simp] private theorem sub_c (x y : JCoord K) : (x - y).c = x.c - y.c := rfl

/--
@isnad1 id=eq.0h2v.s6.eeabd7fa3e1f from=translated src=- shape=56c340bf vocab=3af8afd3
-/
theorem diagonal_projectors (i : Fin 3) :
    spectralProjector (diagonal (-1 : K) 0 1) i = diagonalUnit i := by
  fin_cases i <;> apply JCoord.ext <;>
    norm_num [spectralProjector, sourceSquare_formula, diagonalUnit, diagonal,
      sourceOne, nS, nC, nV, pf_coordinate, normalizedMuV, muV,
      sourceMuS, sourceMuC, evalU, wedge2, dualWedge2, hodgeStar]

  all_goals first
    | decide
    | (apply VCoord.ext <;> first | rfl | (funext i; cases i <;>
        simp [wedge2, dualWedge2, hodgeStar]))
    | (apply SCoord.ext <;> funext i <;> fin_cases i <;> rfl)
    | (apply CCoord.ext <;> funext i <;> fin_cases i <;> rfl)

/-- Source-product diagonal entry as a curried bilinear form.-/
def diagonalProduct (i : Fin 3) : JCoord K →ₗ[K] JCoord K →ₗ[K] K where
  toFun x := (diagLinear i).comp (sourceProductLinear x)
  map_add' := by
    intro x y
    ext z
    simp [sourceProductLinear, sourceProduct_add_left]
  map_smul' := by
    intro r x
    ext z
    simp [sourceProductLinear, sourceProduct_smul_left]

/--
@isnad1 id=eq.0h4v.s10.7288d431988f from=translated src=- shape=49673f2d vocab=ca9419af
-/
@[simp] theorem diagonalProduct_apply (i : Fin 3) (x y : JCoord K) :
    diagonalProduct i x y = diagLinear i (sourceProduct x y) := rfl

/-- Reusable tensor change of basis for any bilinear scalar measurement.
@isnad1 id=mem.1h7v.s11.c138805fb01f from=translated src=- shape=07f7d8fb vocab=00547978
-/
theorem power_pair_mem (F : Subfield K)
    (B : JCoord K →ₗ[K] JCoord K →ₗ[K] K) (a b : JCoord K)
    (h : ∀ j l, B (spectralProjector a j) (spectralProjector b l) ∈ F)
    (p q : Fin 3) : B (power a p) (power b q) ∈ F := by
  rw [power_eq_weighted_projectors a p, power_eq_weighted_projectors b q]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  apply F.sum_mem
  intro j hj
  apply F.mul_mem (powerWeight_mem F q j)
  apply F.sum_mem
  intro l hl
  exact F.mul_mem (powerWeight_mem F p l) (h l j)

@[ext] structure SourceLedger (K : Type*) where
  P : Fin 3 → Fin 3 → K
  Q : Fin 3 → Fin 3 → K
  R : Fin 3 → Fin 3 → K
  C0 : Fin 3 → Fin 3 → Fin 3 → K

/-- Same slots and centering as Challenge.ledger; E is the fixed labelled
diagonal frame. Rational public compatibility is a separate adapter.-/
def sourceLedger (a b : JCoord K) : SourceLedger K :=
  let f := spectralProjector a
  let k := spectralProjector b
  let P := fun i j => sourceTraceForm (diagonalUnit i) (f j)
  let Q := fun j l => sourceTraceForm (f j) (k l)
  let R := fun l i => sourceTraceForm (k l) (diagonalUnit i)
  ⟨P, Q, R, fun i j l => sourceTraceForm (diagonalUnit i)
    (sourceProduct (f j) (k l)) - (P i j + Q j l + R l i) / 3 + 2 / 9⟩

def LedgerIn (F : Subfield K) (L : SourceLedger K) : Prop :=
  (∀ i j, L.P i j ∈ F) ∧ (∀ j l, L.Q j l ∈ F) ∧
  (∀ l i, L.R l i ∈ F) ∧ (∀ i j l, L.C0 i j l ∈ F)

/-- Undo the public centering using the three retained pair tables.
@isnad1 id=mem.1h7v.s10.adf00f52abf2 from=translated src=- shape=11bc097f vocab=856a70fb
-/
theorem rawJoint_mem (F : Subfield K) (a b : JCoord K)
    (h : LedgerIn F (sourceLedger a b)) (i j l : Fin 3) :
    diagonalProduct i (spectralProjector a j) (spectralProjector b l) ∈ F := by
  rcases h with ⟨hP, hQ, hR, hC⟩
  have h3 : (3 : K) ∈ F := natCast_mem F 3
  have h29 : (2 / 9 : K) ∈ F := F.div_mem (natCast_mem F 2) (natCast_mem F 9)
  have hc := hC i j l
  change sourceTraceForm (diagonalUnit i)
    (sourceProduct (spectralProjector a j) (spectralProjector b l)) -
      ((sourceLedger a b).P i j + (sourceLedger a b).Q j l +
        (sourceLedger a b).R l i) / 3 + 2 / 9 ∈ F at hc
  have hh := F.sub_mem
    (F.add_mem hc (F.div_mem (F.add_mem (F.add_mem (hP i j) (hQ j l))
      (hR l i)) h3)) h29
  have heq :
      sourceTraceForm (diagonalUnit i)
        (sourceProduct (spectralProjector a j) (spectralProjector b l)) -
        ((sourceLedger a b).P i j + (sourceLedger a b).Q j l +
          (sourceLedger a b).R l i) / 3 + 2 / 9 +
        ((sourceLedger a b).P i j + (sourceLedger a b).Q j l +
          (sourceLedger a b).R l i) / 3 - 2 / 9 =
      diagonalProduct i (spectralProjector a j) (spectralProjector b l) := by
    rw [diagonal_trace, diagonalProduct_apply]
    ring
  rwa [heq] at hh

/-- All 27 diagonal power-product values are in the literal ledger field.
@isnad1 id=mem.1h7v.s8.e324e93c9f61 from=translated src=- shape=b8fe01ca vocab=dbf56e71
-/
theorem power_diagonal_mem (F : Subfield K) (a b : JCoord K)
    (h : LedgerIn F (sourceLedger a b)) (i p q : Fin 3) :
    diagLinear i (sourceProduct (power a p) (power b q)) ∈ F :=
  power_pair_mem F (diagonalProduct i) a b (rawJoint_mem F a b h i) p q

end AlbertLean.Generic.ResidualLedgerPower
