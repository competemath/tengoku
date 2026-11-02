import Tengoku.Seed.Algebra.Module.Equiv.Defs
import Tengoku.Seed.Algebra.Module.Pi
import Tengoku.Seed.Algebra.Algebra.Rat
import Tengoku.Seed.Data.Fintype.Basic
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms wedge2_swap` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms BW_nondegenerate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms wedge_dual_pairing` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms hodgeStar_involutive` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pf_coordinate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pf_polar` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms decomposable_pf_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms BS_self_eq_two_nS` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mutationWitness_BW_i13_i24` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mutationWitness_pf_i12_add_i34` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mutationWitness_pf_normalization` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Six-coordinate exterior kernel

This file records a bounded coordinate model for `Λ²(K⁴)` and its dual.
The coordinate order is

`12, 13, 14, 23, 24, 34`.

`U` and `Udual`, and likewise `W` and `Wdual`, are coordinate abbreviations
for definitionally equal function carriers.  The names record the intended
input and output roles; they do not construct distinct bundled dual spaces.

**Source relationship.**  The exterior formulas are coordinate expansions
derived from `eq:sl4forms`, with the relative star normalization supplied by
the exported exterior identity.  The coordinate basis functions and tables,
the nondegeneracy proof, the diagonal witness vectors, and the mutation
witnesses are supporting constructions and lemmas.  They are bounded coordinate
consequences, not additional representation identifications.
-/

namespace AlbertLean.Triality.ExteriorSix

/-- The fixed order of the six exterior coordinates.-/
inductive WIdx
  | i12
  | i13
  | i14
  | i23
  | i24
  | i34
  deriving DecidableEq

/-- The six exterior coordinates in their literal basis order.  This explicit
instance avoids a generated-enumeration transparency mismatch across Lean
toolchain revisions.-/
instance : Fintype WIdx where
  elems := {.i12, .i13, .i14, .i23, .i24, .i34}
  complete i := by cases i <;> simp

abbrev U (K : Type*) := Fin 4 → K
abbrev Udual (K : Type*) := Fin 4 → K
abbrev W (K : Type*) := WIdx → K
abbrev Wdual (K : Type*) := WIdx → K

section Coordinates

variable {K : Type*} [CommRing K]

/-- a standard coordinate vector in `K⁴`.-/
def uBasis (i : Fin 4) : U K := fun j => if j = i then 1 else 0

/--
a standard coordinate covector.  Its separate name
records an interface role; its carrier is definitionally equal to `U K`.-/
def uDualBasis (i : Fin 4) : Udual K := fun j => if j = i then 1 else 0

/-- a standard vector in the fixed coordinate order.-/
def wBasis (i : WIdx) : W K := fun j => if j = i then 1 else 0

/--
a standard covector in the fixed coordinate order.
Its carrier is definitionally equal to `W K`.-/
def wDualBasis (i : WIdx) : Wdual K := fun j => if j = i then 1 else 0

/--
Coordinate exterior product derived from `eq:sl4forms`, in the order
`12, 13, 14, 23, 24, 34`.-/
def wedge2 (p q : U K) : W K
  | .i12 => p 0 * q 1 - p 1 * q 0
  | .i13 => p 0 * q 2 - p 2 * q 0
  | .i14 => p 0 * q 3 - p 3 * q 0
  | .i23 => p 1 * q 2 - p 2 * q 1
  | .i24 => p 1 * q 3 - p 3 * q 1
  | .i34 => p 2 * q 3 - p 3 * q 2

/--
Coordinate dual exterior product derived from the exterior terms in
`eq:sl4forms`, in the same fixed order.-/
def dualWedge2 (phi psi : Udual K) : Wdual K
  | .i12 => phi 0 * psi 1 - phi 1 * psi 0
  | .i13 => phi 0 * psi 2 - phi 2 * psi 0
  | .i14 => phi 0 * psi 3 - phi 3 * psi 0
  | .i23 => phi 1 * psi 2 - phi 2 * psi 1
  | .i24 => phi 1 * psi 3 - phi 3 * psi 1
  | .i34 => phi 2 * psi 3 - phi 3 * psi 2

theorem wedge2_add_left (p q r : U K) :
    wedge2 (p + q) r = wedge2 p r + wedge2 q r := by
  funext i
  fin_cases i <;> simp [wedge2] <;> ring

theorem wedge2_add_right (p q r : U K) :
    wedge2 p (q + r) = wedge2 p q + wedge2 p r := by
  funext i
  fin_cases i <;> simp [wedge2] <;> ring

theorem wedge2_smul_left (a : K) (p q : U K) :
    wedge2 (a • p) q = a • wedge2 p q := by
  funext i
  fin_cases i <;> simp [wedge2] <;> ring

theorem wedge2_smul_right (a : K) (p q : U K) :
    wedge2 p (a • q) = a • wedge2 p q := by
  funext i
  fin_cases i <;> simp [wedge2] <;> ring

theorem wedge2_self (p : U K) : wedge2 p p = 0 := by
  funext i
  fin_cases i <;> simp [wedge2] <;> ring

/-- Equivalent spelling of the alternating law.-/
theorem wedge2_alternating (p : U K) : wedge2 p p = 0 := wedge2_self p

theorem wedge2_swap (p q : U K) : wedge2 q p = -wedge2 p q := by
  funext i
  fin_cases i <;> simp [wedge2] <;> ring

theorem dualWedge2_add_left (phi psi chi : Udual K) :
    dualWedge2 (phi + psi) chi = dualWedge2 phi chi + dualWedge2 psi chi := by
  funext i
  fin_cases i <;> simp [dualWedge2] <;> ring

theorem dualWedge2_add_right (phi psi chi : Udual K) :
    dualWedge2 phi (psi + chi) = dualWedge2 phi psi + dualWedge2 phi chi := by
  funext i
  fin_cases i <;> simp [dualWedge2] <;> ring

theorem dualWedge2_self (phi : Udual K) : dualWedge2 phi phi = 0 := by
  funext i
  fin_cases i <;> simp [dualWedge2] <;> ring

theorem dualWedge2_swap (phi psi : Udual K) :
    dualWedge2 psi phi = -dualWedge2 phi psi := by
  funext i
  fin_cases i <;> simp [dualWedge2] <;> ring

/-!
The following coordinate table is explicit; it makes the frozen
order executable without treating enumeration order as mathematical data.
-/

theorem wedge2_basis_i12 :
    wedge2 (uBasis 0 : U K) (uBasis 1) = (wBasis .i12 : W K) := by
  funext i
  fin_cases i <;> simp [wedge2, uBasis, wBasis]

theorem wedge2_basis_i13 :
    wedge2 (uBasis 0 : U K) (uBasis 2) = (wBasis .i13 : W K) := by
  funext i
  fin_cases i <;> simp [wedge2, uBasis, wBasis]

theorem wedge2_basis_i14 :
    wedge2 (uBasis 0 : U K) (uBasis 3) = (wBasis .i14 : W K) := by
  funext i
  fin_cases i <;> simp [wedge2, uBasis, wBasis]

theorem wedge2_basis_i23 :
    wedge2 (uBasis 1 : U K) (uBasis 2) = (wBasis .i23 : W K) := by
  funext i
  fin_cases i <;> simp [wedge2, uBasis, wBasis]

theorem wedge2_basis_i24 :
    wedge2 (uBasis 1 : U K) (uBasis 3) = (wBasis .i24 : W K) := by
  funext i
  fin_cases i <;> simp [wedge2, uBasis, wBasis]

theorem wedge2_basis_i34 :
    wedge2 (uBasis 2 : U K) (uBasis 3) = (wBasis .i34 : W K) := by
  funext i
  fin_cases i <;> simp [wedge2, uBasis, wBasis]

/-- Coordinate evaluation between `K⁴` and its coordinate dual.-/
def evalU (phi : Udual K) (p : U K) : K :=
  phi 0 * p 0 + phi 1 * p 1 + phi 2 * p 2 + phi 3 * p 3

/--
Coordinate evaluation between the six-coordinate roles, derived from the
pairing term in `eq:sl4forms`.-/
def pairW (w : W K) (zeta : Wdual K) : K :=
  w .i12 * zeta .i12 + w .i13 * zeta .i13 + w .i14 * zeta .i14 +
    w .i23 * zeta .i23 + w .i24 * zeta .i24 + w .i34 * zeta .i34

/--
The symmetric exterior pairing derived from `eq:sl4forms`, with signs
`+, -, +` on complementary pairs in the fixed volume orientation.-/
def BW (w v : W K) : K :=
  w .i12 * v .i34 + w .i34 * v .i12 -
    w .i13 * v .i24 - w .i24 * v .i13 +
    w .i14 * v .i23 + w .i23 * v .i14

theorem BW_add_left (u v w : W K) : BW (u + v) w = BW u w + BW v w := by
  simp [BW]
  ring

theorem BW_add_right (u v w : W K) : BW u (v + w) = BW u v + BW u w := by
  simp [BW]
  ring

theorem BW_smul_left (a : K) (u v : W K) : BW (a • u) v = a * BW u v := by
  simp [BW]
  ring

theorem BW_smul_right (a : K) (u v : W K) : BW u (a • v) = a * BW u v := by
  simp [BW]
  ring

theorem BW_symmetric (w v : W K) : BW w v = BW v w := by
  simp [BW]
  ring

/-!
The six ordered nonzero complementary pairings below are an
explicit coordinate table.
-/

theorem BW_basis_i12_i34 :
    BW (wBasis .i12 : W K) (wBasis .i34) = 1 := by
  simp [BW, wBasis]

theorem BW_basis_i13_i24 :
    BW (wBasis .i13 : W K) (wBasis .i24) = -1 := by
  simp [BW, wBasis]

theorem BW_basis_i14_i23 :
    BW (wBasis .i14 : W K) (wBasis .i23) = 1 := by
  simp [BW, wBasis]

theorem BW_basis_i34_i12 :
    BW (wBasis .i34 : W K) (wBasis .i12) = 1 := by
  simp [BW, wBasis]

theorem BW_basis_i24_i13 :
    BW (wBasis .i24 : W K) (wBasis .i13) = -1 := by
  simp [BW, wBasis]

theorem BW_basis_i23_i14 :
    BW (wBasis .i23 : W K) (wBasis .i14) = 1 := by
  simp [BW, wBasis]

/--
the displayed coordinate pairing is nondegenerate.-/
theorem BW_nondegenerate {w : W K} (h : ∀ v : W K, BW w v = 0) : w = 0 := by
  have h12 : w .i12 = 0 := by
    simpa [BW, wBasis] using h (wBasis .i34)
  have h13 : w .i13 = 0 := by
    have hi := h (wBasis .i24)
    simp [BW, wBasis] at hi
    exact hi
  have h14 : w .i14 = 0 := by
    simpa [BW, wBasis] using h (wBasis .i23)
  have h23 : w .i23 = 0 := by
    simpa [BW, wBasis] using h (wBasis .i14)
  have h24 : w .i24 = 0 := by
    have hi := h (wBasis .i13)
    simp [BW, wBasis] at hi
    exact hi
  have h34 : w .i34 = 0 := by
    simpa [BW, wBasis] using h (wBasis .i12)
  funext i
  fin_cases i <;> simp [h12, h13, h14, h23, h24, h34]

/-- The duality identity for two exterior products.-/
theorem wedge_dual_pairing (p q : U K) (phi psi : Udual K) :
    pairW (wedge2 p q) (dualWedge2 phi psi) =
      evalU phi p * evalU psi q - evalU phi q * evalU psi p := by
  simp [pairW, wedge2, dualWedge2, evalU]
  ring

/--
Coordinate Hodge star derived from the exterior identity following
`eq:sl4forms`, fixed by `BW (star zeta) w = pairW w zeta`.-/
def hodgeStar (zeta : Wdual K) : W K
  | .i12 => zeta .i34
  | .i13 => -zeta .i24
  | .i14 => zeta .i23
  | .i23 => zeta .i14
  | .i24 => -zeta .i13
  | .i34 => zeta .i12

theorem BW_hodgeStar (zeta : Wdual K) (w : W K) :
    BW (hodgeStar zeta) w = pairW w zeta := by
  simp [BW, hodgeStar, pairW]
  ring

/--
The self-composition here uses the bounded, definitional identification of the
`W` and `Wdual` function carriers.  In this coordinate model, involutivity
fixes the relative dual-volume normalization used by `hodgeStar`; it is not a
basis-free identification of separately bundled spaces.-/
theorem hodgeStar_involutive (zeta : Wdual K) :
    hodgeStar (hodgeStar zeta) = zeta := by
  funext i
  fin_cases i <;> simp [hodgeStar]

theorem hodgeStar_injective : Function.Injective (hodgeStar : Wdual K → W K) := by
  intro zeta eta h
  have := congrArg hodgeStar h
  simpa [hodgeStar_involutive] using this

/-!
The star basis table below is explicit and exposes every relative
sign fixed by the chosen dual-volume normalization.
-/

theorem hodgeStar_basis_i12 :
    hodgeStar (wDualBasis .i12 : Wdual K) = (wBasis .i34 : W K) := by
  funext i
  fin_cases i <;> simp [hodgeStar, wDualBasis, wBasis]

theorem hodgeStar_basis_i13 :
    hodgeStar (wDualBasis .i13 : Wdual K) = -(wBasis .i24 : W K) := by
  funext i
  fin_cases i <;> simp [hodgeStar, wDualBasis, wBasis]

theorem hodgeStar_basis_i14 :
    hodgeStar (wDualBasis .i14 : Wdual K) = (wBasis .i23 : W K) := by
  funext i
  fin_cases i <;> simp [hodgeStar, wDualBasis, wBasis]

theorem hodgeStar_basis_i23 :
    hodgeStar (wDualBasis .i23 : Wdual K) = (wBasis .i14 : W K) := by
  funext i
  fin_cases i <;> simp [hodgeStar, wDualBasis, wBasis]

theorem hodgeStar_basis_i24 :
    hodgeStar (wDualBasis .i24 : Wdual K) = -(wBasis .i13 : W K) := by
  funext i
  fin_cases i <;> simp [hodgeStar, wDualBasis, wBasis]

theorem hodgeStar_basis_i34 :
    hodgeStar (wDualBasis .i34 : Wdual K) = (wBasis .i12 : W K) := by
  funext i
  fin_cases i <;> simp [hodgeStar, wDualBasis, wBasis]

end Coordinates

section Pfaffian

variable {K : Type*} [CommRing K] [Algebra ℚ K] [Invertible (2 : K)]

/--
Pfaffian derived from `eq:sl4forms`, normalized as one half of the exterior
self-pairing.-/
def Pf (w : W K) : K := ⅟ (2 : K) * BW w w

theorem pf_eq_half_BW_self (w : W K) : Pf w = ⅟ (2 : K) * BW w w := rfl

theorem pf_coordinate (w : W K) :
    Pf w = w .i12 * w .i34 - w .i13 * w .i24 + w .i14 * w .i23 := by
  unfold Pf
  rw [show BW w w =
      2 * (w .i12 * w .i34 - w .i13 * w .i24 + w .i14 * w .i23) by
    simp [BW]
    ring]
  rw [← mul_assoc, invOf_mul_self, one_mul]

theorem pf_zero : Pf (0 : W K) = 0 := by
  simp [pf_coordinate]

theorem pf_smul (a : K) (w : W K) : Pf (a • w) = a ^ 2 * Pf w := by
  rw [pf_coordinate, pf_coordinate]
  simp
  ring

theorem pf_polar (w v : W K) : Pf (w + v) = Pf w + Pf v + BW w v := by
  rw [pf_coordinate, pf_coordinate, pf_coordinate]
  simp [BW]
  ring

/-- Every displayed decomposable exterior two-vector has zero Pfaffian.-/
theorem decomposable_pf_zero (p q : U K) : Pf (wedge2 p q) = 0 := by
  rw [pf_coordinate]
  simp [wedge2]
  ring

theorem pf_basis_i12_add_i34 : Pf (wBasis .i12 + wBasis .i34 : W K) = 1 := by
  rw [pf_coordinate]
  simp [wBasis]

end Pfaffian

section TypedPairings

variable {K : Type*} [CommRing K]

/-- One typed pair of four-coordinate slots.-/
@[ext]
structure SCoord (K : Type*) where
  p : U K
  phi : Udual K

/-- The other typed pair of four-coordinate slots.-/
@[ext]
structure CCoord (K : Type*) where
  q : U K
  psi : Udual K

/-- Quadratic coordinate pairing on `SCoord`.-/
def nS (s : SCoord K) : K := evalU s.phi s.p

/-- Quadratic coordinate pairing on `CCoord`.-/
def nC (c : CCoord K) : K := evalU c.psi c.q

/-- Symmetric polarization on `SCoord`.-/
def BS (s t : SCoord K) : K := evalU s.phi t.p + evalU t.phi s.p

/-- Symmetric polarization on `CCoord`.-/
def BC (c d : CCoord K) : K := evalU c.psi d.q + evalU d.psi c.q

theorem BS_symmetric (s t : SCoord K) : BS s t = BS t s := by
  simp [BS, add_comm]

theorem BC_symmetric (c d : CCoord K) : BC c d = BC d c := by
  simp [BC, add_comm]

theorem BS_self_eq_two_nS (s : SCoord K) : BS s s = 2 * nS s := by
  simp [BS, nS]
  ring

theorem BC_self_eq_two_nC (c : CCoord K) : BC c c = 2 * nC c := by
  simp [BC, nC]
  ring

/--
one of four diagonal norm-one witness vectors.  The
four values of this function are not asserted to be a basis of `SCoord K`.-/
def sBasis (i : Fin 4) : SCoord K :=
  { p := uBasis i, phi := uDualBasis i }

/--
one of four diagonal norm-one witness vectors.  The
four values of this function are not asserted to be a basis of `CCoord K`.-/
def cBasis (i : Fin 4) : CCoord K :=
  { q := uBasis i, psi := uDualBasis i }

theorem nS_basis (i : Fin 4) : nS (sBasis i : SCoord K) = 1 := by
  fin_cases i <;> simp [nS, sBasis, evalU, uBasis, uDualBasis]

theorem nC_basis (i : Fin 4) : nC (cBasis i : CCoord K) = 1 := by
  fin_cases i <;> simp [nC, cBasis, evalU, uBasis, uDualBasis]

end TypedPairings

section MutationWitnesses

variable {K : Type*} [CommRing K]

/-!
All declarations in this section are universal identities.  Executable mutation replay refutes the corresponding
altered universal statements using a characteristic-zero instance (for
example `K = ℚ`).  In characteristic two alone, `-1 = 1`, so a sign witness by
itself cannot distinguish the two conventions; the ordering and normalization
gates remain separate.
-/

/-- Rejects a sign flip in the `13|24` complementary pair.-/
theorem mutationWitness_BW_i13_i24 :
    BW (wBasis .i13 : W K) (wBasis .i24) = -1 := BW_basis_i13_i24

/-- Rejects exchanging the `14` coordinate with the adjacent `23` coordinate.-/
theorem mutationWitness_wedge_i14 :
    wedge2 (uBasis 0 : U K) (uBasis 3) = wBasis .i14 := wedge2_basis_i14

/-- Rejects the same exchange from the other side of the ordered list.-/
theorem mutationWitness_wedge_i23 :
    wedge2 (uBasis 1 : U K) (uBasis 2) = wBasis .i23 := wedge2_basis_i23

/-- Rejects the missing minus sign in the `13` Hodge-star coordinate.-/
theorem mutationWitness_hodge_i13 :
    hodgeStar (wDualBasis .i13 : Wdual K) = -wBasis .i24 := hodgeStar_basis_i13

variable [Algebra ℚ K] [Invertible (2 : K)]

/-- Rejects either the Pfaffian normalization or the `12|34` sign.-/
theorem mutationWitness_pf_i12_add_i34 :
    Pf (wBasis .i12 + wBasis .i34 : W K) = 1 := pf_basis_i12_add_i34

/-- The same witness exposes the value `2` before Pfaffian halving.-/
theorem mutationWitness_pf_normalization :
    BW (wBasis .i12 + wBasis .i34 : W K)
        (wBasis .i12 + wBasis .i34) = 2 ∧
      Pf (wBasis .i12 + wBasis .i34 : W K) = 1 := by
  constructor
  · simp [BW, wBasis]
    ring
  · exact pf_basis_i12_add_i34

end MutationWitnesses

end AlbertLean.Triality.ExteriorSix
