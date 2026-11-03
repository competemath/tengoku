import Tengoku
import Tengoku.Seed.Algebra.Field.Rat
import Tengoku.Seed.Algebra.Module.Equiv.Defs

/-!
# An earlier compact presentation of the rational example (superseded)

Namespace `CompactOneBit` is an earlier, self-contained presentation of the rational
example: two fixed rational frame triples with the same 54 recorded traces but unequal
detector values, with the coordinate product identified with Tau Ceti's split Albert
algebra. It is **not** the public statement of record and none of its declarations is
selected for comparison. The public statement is the root `Challenge.lean`
(namespace `OneBit` at the released commit), whose finite theorems
`OneBit.rationalWitness` and `OneBit.rationalWitness_not_equivalent_under_relabelling` are
proved in `OneBit/Closeout/`. These files are retained because later modules
(`AlbertLean/Generic/CubicAutomorphismCompact.lean`, `AlbertLean/Generic/TauTransport.lean`)
import them. No generic, scalar-extension, relabelling or primitivity claim is made here.

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
-/
noncomputable section
namespace CompactOneBit
open scoped BigOperators
/-- The source rational vector space, in the literal ordered 27-coordinate basis.-/
abbrev Coord := Fin 27 → ℚ
local instance : Invertible (2 : ℚ) := invertibleOfNonzero (by decide)

/-- Source unit in the fixed 27-coordinate basis.-/
def unit : Coord := fun i => if i.val < 3 then 1 else 0
/-- The exact exported cubic, retaining all 45 signed monomials in order.-/
def cubic (x : Coord) : ℚ :=
  x 0 * x 1 * x 2 - x 0 * x 3 * x 4 - x 0 * x 5 * x 10
  + x 0 * x 6 * x 9 - x 0 * x 7 * x 8 - x 1 * x 11 * x 15
  - x 1 * x 12 * x 16 - x 1 * x 13 * x 17 - x 1 * x 14 * x 18
  - x 2 * x 19 * x 23 - x 2 * x 20 * x 24 - x 2 * x 21 * x 25
  - x 2 * x 22 * x 26 + x 3 * x 15 * x 19 + x 3 * x 16 * x 20
  + x 3 * x 17 * x 21 + x 3 * x 18 * x 22 + x 4 * x 11 * x 23
  + x 4 * x 12 * x 24 + x 4 * x 13 * x 25 + x 4 * x 14 * x 26
  + x 5 * x 13 * x 22 - x 5 * x 14 * x 21 + x 5 * x 15 * x 24
  - x 5 * x 16 * x 23 - x 6 * x 12 * x 22 + x 6 * x 14 * x 20
  + x 6 * x 15 * x 25 - x 6 * x 17 * x 23 + x 7 * x 12 * x 21
  - x 7 * x 13 * x 20 + x 7 * x 15 * x 26 - x 7 * x 18 * x 23
  + x 8 * x 11 * x 22 - x 8 * x 14 * x 19 + x 8 * x 16 * x 25
  - x 8 * x 17 * x 24 - x 9 * x 11 * x 21 + x 9 * x 13 * x 19
  + x 9 * x 16 * x 26 - x 9 * x 18 * x 24 + x 10 * x 11 * x 20
  - x 10 * x 12 * x 19 + x 10 * x 17 * x 26 - x 10 * x 18 * x 25
/-- Full cubic polarization, with no factorial normalization.-/
def polar (x y z : Coord) : ℚ :=
  cubic (x+y+z) - cubic (x+y) - cubic (x+z) - cubic (y+z)
    + cubic x + cubic y + cubic z - cubic 0
/-- The linear trace determined by the cubic and source unit.-/
def trace (x : Coord) : ℚ := polar unit unit x / 2
/-- Quadratic coefficient of the cubic characteristic polynomial.-/
def spur (x : Coord) : ℚ := polar unit x x / 2
/-- The symmetric trace pairing determined by the cubic and unit.-/
def pairing (x y : Coord) : ℚ := trace x * trace y - polar unit x y
/-- The inverse trace Gram matrix as its explicit signed coordinate permutation.-/
def dual (x : Coord) : Coord :=
  ![x 0, x 1, x 2, x 4, x 3, x 10, -x 9, x 8, x 7, -x 6, x 5,
    x 15, x 16, x 17, x 18, x 11, x 12, x 13, x 14,
    x 23, x 24, x 25, x 26, x 19, x 20, x 21, x 22]
/-- Source adjoint obtained by trace-dualizing the cubic differential.-/
def adjoint (x : Coord) : Coord := dual (fun j => polar x x (Pi.single j 1) / 2)
/-- The source Springer product; it is not defined by transport from Tau Ceti.-/
def product (x y : Coord) : Coord := (2 : ℚ)⁻¹ •
  (adjoint (x+y) - adjoint x - adjoint y + trace x • y + trace y • x
    - polar unit x y • unit)
local infixl:70 " ⋄ " => product
/-- Normalized trace of left multiplication, in the source coordinate basis.-/
def operatorTrace (x : Coord) : ℚ := (∑ i : Fin 27, (x ⋄ Pi.single i 1) i) / 9
/-- Quadratic coefficient recovered from the normalized operator trace.-/
def operatorSpur (x : Coord) : ℚ := (operatorTrace x ^ 2 - operatorTrace (x ⋄ x)) / 2
/-- Cubic coefficient recovered from the normalized operator trace.-/
def operatorNorm (x : Coord) : ℚ := operatorTrace x ^ 3 / 6
  - operatorTrace x * operatorTrace (x ⋄ x) / 2 + operatorTrace (x ⋄ (x ⋄ x)) / 3

/-- Three ordered encoders, with indices 0, 1, 2 representing E, F, K.-/
abbrev Triple := Fin 3 → Coord
/-- Spectral projectors, ordered by eigenvalues -1, 0, 1.-/
def projector (x : Coord) : Fin 3 → Coord :=
  ![(2 : ℚ)⁻¹ • (x ⋄ x - x), unit - x ⋄ x, (2 : ℚ)⁻¹ • (x ⋄ x + x)]
/-- Three nonzero trace-one orthogonal idempotents, with their encoder identities.-/
def Frame (x : Coord) : Prop :=
  trace x = 0 ∧ spur x = -1 ∧ cubic x = 0 ∧
  (∀ i, projector x i ⋄ projector x i = projector x i ∧ trace (projector x i) = 1) ∧
  (∀ i j, i ≠ j → projector x i ⋄ projector x j = 0) ∧
  projector x 0 + projector x 1 + projector x 2 = unit ∧ projector x 2 - projector x 0 = x
/-- Cyclic pair tables: r=0,1,2 are P(E,F), Q(F,K), R(K,E), respectively.-/
def pairs (X : Triple) (r i j : Fin 3) : ℚ :=
  pairing (projector (X r) i) (projector (X (r+1)) j)
/-- The complete 27-entry centered joint table.-/
def centered (X : Triple) (i j k : Fin 3) : ℚ :=
  pairing (projector (X 0) i) (projector (X 1) j ⋄ projector (X 2) k)
    - (pairs X 0 i j + pairs X 1 j k + pairs X 2 k i) / 3 + 2 / 9
/-- Product word measuring the commutator of left multiplication by E and F on K.-/
def word (X : Triple) : Coord := X 0 ⋄ (X 1 ⋄ X 2) - X 1 ⋄ (X 0 ⋄ X 2)
/-- The trace-cube detector, with the source trace normalization.-/
def detector (X : Triple) : ℚ := pairing (word X) (word X ⋄ word X)

/-- Encoder of the common first frame.-/
def E : Coord := ![-1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Second encoder of the first witness, in the fixed source basis.-/
def F : Coord := ![-1/3, -1, 4/3, 1, 0, 0, 0, 0, 0, 0, 0,
  1, 0, 0, 0, 3/2, -2, -245/54, -3/2, 0, 0, 1, 0, 0, -2, -35/18, 2]
/-- Third encoder of the first witness.-/
def K : Coord := ![-1/3, -1, 4/3, 0, 1, 0, 0, 0, 0, 0, 0,
  0, 1, 0, 0, -2, 1, -3/2, 1, 0, 0, 0, 1, 3/2, -91/27, 0, -13/9]
/-- Second witness's second encoder: exactly two coordinates differ from F.-/
def F' : Coord := Function.update (Function.update F 18 (-8748/410231)) 26 (11664/410231)
/-- Second witness's third encoder: exactly three coordinates differ from K.-/
def K' : Coord := Function.update
  (Function.update (Function.update K 18 (5832/410231)) 22 (410231/5832)) 26 (-8424/410231)
/-- The first ordered encoder triple.-/
def first : Triple := ![E, F, K]
/-- The second ordered encoder triple; labels and frame order are fixed.-/
def second : Triple := ![E, F', K']

/-- Rational-linear unital product automorphism; detector preservation is not assumed.-/
structure Aut where
  linear : Coord ≃ₗ[ℚ] Coord
  unit : linear CompactOneBit.unit = CompactOneBit.unit
  product : ∀ x y, linear (x ⋄ y) = linear x ⋄ linear y
/-- A transporter respects all three ordered encoders.-/
def Transports (g : Aut) (X Y : Triple) : Prop := ∀ r, g.linear (X r) = Y r

end CompactOneBit
