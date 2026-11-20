import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Clifford's circle theorems (first and second)

Put the common point `M` of the circles at the origin of `ℂ`.  The circle through `M` with
centre `c = p + q i` is `x² + y² = 2 (p x + q y)`, i.e. `z * conj z = conj c * z + c * conj z`.

* `second c d` is the second intersection of the circles with centres `c`, `d`;
* `OnCircle3 z₁ z₂ z₃ z`: `z` lies on the circle through `z₁, z₂, z₃` (for three non-collinear
  points that circle is unique, so this is Mathlib's `Cospherical {z₁, z₂, z₃, z}`);
* `miquel c₁ c₂ c₃ c₄` is an explicit point (a ratio of two 4×4 determinants in the centres
  and their conjugates).

`clifford_one` (Clifford's first theorem, `n = 4`): `miquel c₁ c₂ c₃ c₄` lies on the four circles
`Γ_ijk` through `P_ij, P_ik, P_jk`.

`clifford_two` (Clifford's second theorem, `n = 5`): the five points `P_S = miquel (c_S)`, one for
each 4-subset `S` of five circles, are concyclic (`Cospherical` in Mathlib's sense).

All algebra is done once over an arbitrary commutative ring (variables `xᵢ` for the centres,
`yᵢ` for their conjugates) and then specialised; the five 4-subsets are handled by permuting the
variables of a single certificate.
-/

namespace Clifford

open Complex ComplexConjugate

/-! ## Polynomial certificates over a commutative ring -/

section Poly

variable {R : Type*} [CommRing R]

/-- Laplace expansion of a 3×3 determinant (rows `a`, `b`, `c`).-/
def det3 (a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ : R) : R :=
  a₁ * (b₂ * c₃ - b₃ * c₂) - a₂ * (b₁ * c₃ - b₃ * c₁) + a₃ * (b₁ * c₂ - b₂ * c₁)

/-- Laplace expansion of a 4×4 determinant along the first row.-/
def det4 (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ d₁ d₂ d₃ d₄ : R) : R :=
  a₁ * det3 b₂ b₃ b₄ c₂ c₃ c₄ d₂ d₃ d₄ - a₂ * det3 b₁ b₃ b₄ c₁ c₃ c₄ d₁ d₃ d₄ +
    a₃ * det3 b₁ b₂ b₄ c₁ c₂ c₄ d₁ d₂ d₄ - a₄ * det3 b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃

/-- Laplace expansion of a 5×5 determinant along the first row.-/
def det5 (a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ : R) : R :=
  a₁ * det4 b₂ b₃ b₄ b₅ c₂ c₃ c₄ c₅ d₂ d₃ d₄ d₅ e₂ e₃ e₄ e₅ -
    a₂ * det4 b₁ b₃ b₄ b₅ c₁ c₃ c₄ c₅ d₁ d₃ d₄ d₅ e₁ e₃ e₄ e₅ +
    a₃ * det4 b₁ b₂ b₄ b₅ c₁ c₂ c₄ c₅ d₁ d₂ d₄ d₅ e₁ e₂ e₄ e₅ -
    a₄ * det4 b₁ b₂ b₃ b₅ c₁ c₂ c₃ c₅ d₁ d₂ d₃ d₅ e₁ e₂ e₃ e₅ +
    a₅ * det4 b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ d₁ d₂ d₃ d₄ e₁ e₂ e₃ e₄

/-- `crs`: with `xᵢ = cᵢ`, `yᵢ = conj cᵢ` this is `conj c₁ c₂ - c₁ conj c₂`, which vanishes iff
`M = 0`, `c₁`, `c₂` are collinear.-/
def crs (x₁ x₂ y₁ y₂ : R) : R := y₁ * x₂ - x₁ * y₂

/-- Vanishes iff the three centres are collinear.-/
def triP (x₁ x₂ x₃ y₁ y₂ y₃ : R) : R := det3 1 x₁ y₁ 1 x₂ y₂ 1 x₃ y₃

/-- Vanishes iff `M = 0` lies on the circle through the three centres (or they are collinear
with `M`).-/
def cycP (x₁ x₂ x₃ y₁ y₂ y₃ : R) : R := det3 x₁ (y₁ * x₁) y₁ x₂ (y₂ * x₂) y₂ x₃ (y₃ * x₃) y₃

/-- Numerator of the Miquel point of four circles.-/
def mN (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R) : R :=
  det4 y₁ (y₁ ^ 2) (y₁ * x₁) (x₁ ^ 2) y₂ (y₂ ^ 2) (y₂ * x₂) (x₂ ^ 2)
    y₃ (y₃ ^ 2) (y₃ * x₃) (x₃ ^ 2) y₄ (y₄ ^ 2) (y₄ * x₄) (x₄ ^ 2)

/-- Denominator of the Miquel point of four circles.-/
def mD (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R) : R :=
  det4 y₁ (y₁ ^ 2) (y₁ * x₁) x₁ y₂ (y₂ ^ 2) (y₂ * x₂) x₂
    y₃ (y₃ ^ 2) (y₃ * x₃) x₃ y₄ (y₄ ^ 2) (y₄ * x₄) x₄

/-- Equation (in `z`, `Z = conj z`) of the circle `Γ₁₂₃` through `P₁₂, P₁₃, P₂₃`
(up to a nonzero factor, see `det4_sec`).-/
def gq (x₁ x₂ x₃ y₁ y₂ y₃ z Z : R) : R :=
  det3 (x₁ * (x₁ - z)) (y₁ * x₁) (y₁ * (y₁ - Z)) (x₂ * (x₂ - z)) (y₂ * x₂) (y₂ * (y₂ - Z))
    (x₃ * (x₃ - z)) (y₃ * x₃) (y₃ * (y₃ - Z))

def gq0 (x₁ x₂ x₃ y₁ y₂ y₃ : R) : R :=
  det3 (x₁ ^ 2) (y₁ * x₁) (y₁ ^ 2) (x₂ ^ 2) (y₂ * x₂) (y₂ ^ 2) (x₃ ^ 2) (y₃ * x₃) (y₃ ^ 2)
def gq1 (x₁ x₂ x₃ y₁ y₂ y₃ : R) : R :=
  det3 x₁ (y₁ * x₁) (y₁ ^ 2) x₂ (y₂ * x₂) (y₂ ^ 2) x₃ (y₃ * x₃) (y₃ ^ 2)
def gq2 (x₁ x₂ x₃ y₁ y₂ y₃ : R) : R :=
  det3 (x₁ ^ 2) (y₁ * x₁) y₁ (x₂ ^ 2) (y₂ * x₂) y₂ (x₃ ^ 2) (y₃ * x₃) y₃

theorem gq_expand (x₁ x₂ x₃ y₁ y₂ y₃ z Z : R) :
    gq x₁ x₂ x₃ y₁ y₂ y₃ z Z = gq0 x₁ x₂ x₃ y₁ y₂ y₃ - z * gq1 x₁ x₂ x₃ y₁ y₂ y₃
      - Z * gq2 x₁ x₂ x₃ y₁ y₂ y₃ + z * Z * cycP x₁ x₂ x₃ y₁ y₂ y₃ := by
  unfold gq gq0 gq1 gq2 cycP det3; ring

/-- Certificate for Clifford's first theorem, part 1.-/
theorem certA₁ (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R) :
    mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ * gq0 x₁ x₂ x₃ y₁ y₂ y₃ -
      mN x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ * gq1 x₁ x₂ x₃ y₁ y₂ y₃ =
      mN y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄ * (y₁ * y₂ * y₃ * triP x₁ x₂ x₃ y₁ y₂ y₃) := by
  unfold mD mN gq0 gq1 triP det4 det3; ring

/-- Certificate for Clifford's first theorem, part 2.-/
theorem certA₂ (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R) :
    mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ * gq2 x₁ x₂ x₃ y₁ y₂ y₃ -
      mN x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ * cycP x₁ x₂ x₃ y₁ y₂ y₃ =
      mD y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄ * (y₁ * y₂ * y₃ * triP x₁ x₂ x₃ y₁ y₂ y₃) := by
  unfold mD mN gq2 cycP triP det4 det3; ring

/-- Elimination identity behind `resD`.-/
theorem resD_id (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R) :
    let a := det4 y₁ (y₁ ^ 2) (y₁ * x₁) x₁ y₂ (y₂ ^ 2) (y₂ * x₂) x₂ y₃ (y₃ ^ 2) (y₃ * x₃) x₃ 0 0 y₄ 1
    let b := det4 y₁ (y₁ ^ 2) (y₁ * x₁) x₁ y₂ (y₂ ^ 2) (y₂ * x₂) x₂ y₃ (y₃ ^ 2) (y₃ * x₃) x₃ y₄ (y₄ ^ 2) 0 0
    let e₂ := det4 x₁ (x₁ ^ 2) (x₁ * y₁) y₁ x₂ (x₂ ^ 2) (x₂ * y₂) y₂ x₃ (x₃ ^ 2) (x₃ * y₃) y₃ 0 1 0 0
    let e₁ := det4 x₁ (x₁ ^ 2) (x₁ * y₁) y₁ x₂ (x₂ ^ 2) (x₂ * y₂) y₂ x₃ (x₃ ^ 2) (x₃ * y₃) y₃ 1 0 y₄ 0
    a ^ 2 * mD y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄ - mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ * (e₂ * (a * x₄ - b) + e₁ * a) =
      y₄ * (y₁ - y₄) * (y₂ - y₄) * (y₃ - y₄) * crs x₁ x₂ y₁ y₂ * crs x₁ x₃ y₁ y₃ *
        crs x₂ x₃ y₂ y₃ * triP x₁ x₂ x₃ y₁ y₂ y₃ * cycP x₁ x₂ x₃ y₁ y₂ y₃ := by
  intro a b e₂ e₁
  simp only [a, b, e₂, e₁, mD, crs, triP, cycP, det4, det3]
  ring

/-- `mD` and its conjugate cannot vanish together in general position.-/
theorem resD {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R} (h₁ : mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ = 0)
    (h₂ : mD y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄ = 0) :
    y₄ * (y₁ - y₄) * (y₂ - y₄) * (y₃ - y₄) * crs x₁ x₂ y₁ y₂ * crs x₁ x₃ y₁ y₃ *
      crs x₂ x₃ y₂ y₃ * triP x₁ x₂ x₃ y₁ y₂ y₃ * cycP x₁ x₂ x₃ y₁ y₂ y₃ = 0 := by
  rw [← resD_id, h₁, h₂]; ring

/-- Constant coefficient of the Clifford circle.-/
def k0 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) : R :=
  det5 (x₁ * y₁) (x₁ ^ 2 * y₁) (x₁ * y₁ ^ 2) (x₁ ^ 3) (y₁ ^ 3)
    (x₂ * y₂) (x₂ ^ 2 * y₂) (x₂ * y₂ ^ 2) (x₂ ^ 3) (y₂ ^ 3)
    (x₃ * y₃) (x₃ ^ 2 * y₃) (x₃ * y₃ ^ 2) (x₃ ^ 3) (y₃ ^ 3)
    (x₄ * y₄) (x₄ ^ 2 * y₄) (x₄ * y₄ ^ 2) (x₄ ^ 3) (y₄ ^ 3)
    (x₅ * y₅) (x₅ ^ 2 * y₅) (x₅ * y₅ ^ 2) (x₅ ^ 3) (y₅ ^ 3)

/-- Coefficient of `-z` of the Clifford circle.-/
def k1 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) : R :=
  det5 (x₁ * y₁) (x₁ ^ 2 * y₁) (x₁ * y₁ ^ 2) (x₁ ^ 2) (y₁ ^ 3)
    (x₂ * y₂) (x₂ ^ 2 * y₂) (x₂ * y₂ ^ 2) (x₂ ^ 2) (y₂ ^ 3)
    (x₃ * y₃) (x₃ ^ 2 * y₃) (x₃ * y₃ ^ 2) (x₃ ^ 2) (y₃ ^ 3)
    (x₄ * y₄) (x₄ ^ 2 * y₄) (x₄ * y₄ ^ 2) (x₄ ^ 2) (y₄ ^ 3)
    (x₅ * y₅) (x₅ ^ 2 * y₅) (x₅ * y₅ ^ 2) (x₅ ^ 2) (y₅ ^ 3)

/-- Coefficient of `-conj z` of the Clifford circle.-/
def k2 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) : R :=
  det5 (x₁ * y₁) (x₁ ^ 2 * y₁) (x₁ * y₁ ^ 2) (x₁ ^ 3) (y₁ ^ 2)
    (x₂ * y₂) (x₂ ^ 2 * y₂) (x₂ * y₂ ^ 2) (x₂ ^ 3) (y₂ ^ 2)
    (x₃ * y₃) (x₃ ^ 2 * y₃) (x₃ * y₃ ^ 2) (x₃ ^ 3) (y₃ ^ 2)
    (x₄ * y₄) (x₄ ^ 2 * y₄) (x₄ * y₄ ^ 2) (x₄ ^ 3) (y₄ ^ 2)
    (x₅ * y₅) (x₅ ^ 2 * y₅) (x₅ * y₅ ^ 2) (x₅ ^ 3) (y₅ ^ 2)

/-- Coefficient of `z * conj z` of the Clifford circle.-/
def k3 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) : R :=
  det5 (x₁ * y₁) (x₁ ^ 2 * y₁) (x₁ * y₁ ^ 2) (x₁ ^ 2) (y₁ ^ 2)
    (x₂ * y₂) (x₂ ^ 2 * y₂) (x₂ * y₂ ^ 2) (x₂ ^ 2) (y₂ ^ 2)
    (x₃ * y₃) (x₃ ^ 2 * y₃) (x₃ * y₃ ^ 2) (x₃ ^ 2) (y₃ ^ 2)
    (x₄ * y₄) (x₄ ^ 2 * y₄) (x₄ * y₄ ^ 2) (x₄ ^ 2) (y₄ ^ 2)
    (x₅ * y₅) (x₅ ^ 2 * y₅) (x₅ * y₅ ^ 2) (x₅ ^ 2) (y₅ ^ 2)

/-- Equation (in `z`, `Z = conj z`) of the Clifford circle of five circles.-/
def kK (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ z Z : R) : R :=
  det5 (x₁ * y₁) (x₁ ^ 2 * y₁) (x₁ * y₁ ^ 2) (x₁ ^ 2 * (x₁ - z)) (y₁ ^ 2 * (y₁ - Z))
    (x₂ * y₂) (x₂ ^ 2 * y₂) (x₂ * y₂ ^ 2) (x₂ ^ 2 * (x₂ - z)) (y₂ ^ 2 * (y₂ - Z))
    (x₃ * y₃) (x₃ ^ 2 * y₃) (x₃ * y₃ ^ 2) (x₃ ^ 2 * (x₃ - z)) (y₃ ^ 2 * (y₃ - Z))
    (x₄ * y₄) (x₄ ^ 2 * y₄) (x₄ * y₄ ^ 2) (x₄ ^ 2 * (x₄ - z)) (y₄ ^ 2 * (y₄ - Z))
    (x₅ * y₅) (x₅ ^ 2 * y₅) (x₅ * y₅ ^ 2) (x₅ ^ 2 * (x₅ - z)) (y₅ ^ 2 * (y₅ - Z))

theorem kK_expand (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ z Z : R) :
    kK x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ z Z = k0 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ - z * k1 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ - Z * k2 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ + z * Z * k3 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ := by
  unfold kK k0 k1 k2 k3 det5 det4 det3; ring

/-- Desnanot–Jacobi (Sylvester) identity for a 5×5 determinant: bordering the 3×3 block in the
top-left corner.-/
theorem det5_mul_det3 (a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ : R) :
    det5 a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ *
      det3 a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ =
      det4 a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ d₁ d₂ d₃ d₄ *
        det4 a₁ a₂ a₃ a₅ b₁ b₂ b₃ b₅ c₁ c₂ c₃ c₅ e₁ e₂ e₃ e₅ -
      det4 a₁ a₂ a₃ a₅ b₁ b₂ b₃ b₅ c₁ c₂ c₃ c₅ d₁ d₂ d₃ d₅ *
        det4 a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ := by
  unfold det5 det4 det3; ring

theorem det5_p12354 (a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ : R) :
    det5 a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ d₁ d₂ d₃ d₄ d₅ =
      -det5 a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ := by
  unfold det5 det4 det3; ring

theorem kK_p12354 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ z Z : R) :
    kK x₁ x₂ x₃ x₅ x₄ y₁ y₂ y₃ y₅ y₄ z Z =
      -kK x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ z Z := by
  unfold kK; exact det5_p12354 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem det5_p12453 (a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ : R) :
    det5 a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ c₁ c₂ c₃ c₄ c₅ =
      det5 a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ := by
  unfold det5 det4 det3; ring

theorem kK_p12453 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ z Z : R) :
    kK x₁ x₂ x₄ x₅ x₃ y₁ y₂ y₄ y₅ y₃ z Z =
      kK x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ z Z := by
  unfold kK; exact det5_p12453 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem det5_p13452 (a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ : R) :
    det5 a₁ a₂ a₃ a₄ a₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ b₁ b₂ b₃ b₄ b₅ =
      -det5 a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ := by
  unfold det5 det4 det3; ring

theorem kK_p13452 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ z Z : R) :
    kK x₁ x₃ x₄ x₅ x₂ y₁ y₃ y₄ y₅ y₂ z Z =
      -kK x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ z Z := by
  unfold kK; exact det5_p13452 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem det5_p23451 (a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ : R) :
    det5 b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ a₁ a₂ a₃ a₄ a₅ =
      det5 a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ := by
  unfold det5 det4 det3; ring

theorem kK_p23451 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ z Z : R) :
    kK x₂ x₃ x₄ x₅ x₁ y₂ y₃ y₄ y₅ y₁ z Z =
      kK x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ z Z := by
  unfold kK; exact det5_p23451 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem mN_p1243 (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R) :
    mN x₁ x₂ x₄ x₃ y₁ y₂ y₄ y₃ = -mN x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ := by
  unfold mN det4 det3; ring

theorem mD_p1243 (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R) :
    mD x₁ x₂ x₄ x₃ y₁ y₂ y₄ y₃ = -mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ := by
  unfold mD det4 det3; ring

theorem mN_p1342 (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R) :
    mN x₁ x₃ x₄ x₂ y₁ y₃ y₄ y₂ = mN x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ := by
  unfold mN det4 det3; ring

theorem mD_p1342 (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R) :
    mD x₁ x₃ x₄ x₂ y₁ y₃ y₄ y₂ = mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ := by
  unfold mD det4 det3; ring

theorem mN_p2341 (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R) :
    mN x₂ x₃ x₄ x₁ y₂ y₃ y₄ y₁ = -mN x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ := by
  unfold mN det4 det3; ring

theorem mD_p2341 (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R) :
    mD x₂ x₃ x₄ x₁ y₂ y₃ y₄ y₁ = -mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ := by
  unfold mD det4 det3; ring

theorem detU (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ z : R) :
    det4 (x₁ * y₁) (x₁ ^ 2 * y₁) (x₁ * y₁ ^ 2) (x₁ ^ 2 * (x₁ - z)) (x₂ * y₂) (x₂ ^ 2 * y₂)
      (x₂ * y₂ ^ 2) (x₂ ^ 2 * (x₂ - z)) (x₃ * y₃) (x₃ ^ 2 * y₃) (x₃ * y₃ ^ 2) (x₃ ^ 2 * (x₃ - z))
      (x₄ * y₄) (x₄ ^ 2 * y₄) (x₄ * y₄ ^ 2) (x₄ ^ 2 * (x₄ - z)) =
      -(x₁ * x₂ * x₃ * x₄) * (mN x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ - z * mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄) := by
  unfold mN mD det4 det3; ring

theorem detV (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ Z : R) :
    det4 (x₁ * y₁) (x₁ ^ 2 * y₁) (x₁ * y₁ ^ 2) (y₁ ^ 2 * (y₁ - Z)) (x₂ * y₂) (x₂ ^ 2 * y₂)
      (x₂ * y₂ ^ 2) (y₂ ^ 2 * (y₂ - Z)) (x₃ * y₃) (x₃ ^ 2 * y₃) (x₃ * y₃ ^ 2) (y₃ ^ 2 * (y₃ - Z))
      (x₄ * y₄) (x₄ ^ 2 * y₄) (x₄ * y₄ ^ 2) (y₄ ^ 2 * (y₄ - Z)) =
      y₁ * y₂ * y₃ * y₄ * (mN y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄ - Z * mD y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄) := by
  unfold mN mD det4 det3; ring

theorem detT (x₁ x₂ x₃ y₁ y₂ y₃ : R) :
    det3 (x₁ * y₁) (x₁ ^ 2 * y₁) (x₁ * y₁ ^ 2) (x₂ * y₂) (x₂ ^ 2 * y₂) (x₂ * y₂ ^ 2)
      (x₃ * y₃) (x₃ ^ 2 * y₃) (x₃ * y₃ ^ 2) =
      x₁ * y₁ * x₂ * y₂ * x₃ * y₃ * triP x₁ x₂ x₃ y₁ y₂ y₃ := by
  unfold triP det3; ring

/-- The Clifford circle `kK` restricted to the two Miquel points of `{1,2,3,4}` and `{1,2,3,5}`
(Desnanot–Jacobi applied to the defining 5×5 determinant).-/
theorem kK_dj (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ z Z : R) :
    kK x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ z Z * (x₁ * y₁ * x₂ * y₂ * x₃ * y₃ * triP x₁ x₂ x₃ y₁ y₂ y₃) =
      (-(x₁ * x₂ * x₃ * x₄) * (mN x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ - z * mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄)) *
        (y₁ * y₂ * y₃ * y₅ * (mN y₁ y₂ y₃ y₅ x₁ x₂ x₃ x₅ - Z * mD y₁ y₂ y₃ y₅ x₁ x₂ x₃ x₅)) -
      (y₁ * y₂ * y₃ * y₄ * (mN y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄ - Z * mD y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄)) *
        (-(x₁ * x₂ * x₃ * x₅) * (mN x₁ x₂ x₃ x₅ y₁ y₂ y₃ y₅ - z * mD x₁ x₂ x₃ x₅ y₁ y₂ y₃ y₅)) := by
  have h := det5_mul_det3 (x₁ * y₁) (x₁ ^ 2 * y₁) (x₁ * y₁ ^ 2) (x₁ ^ 2 * (x₁ - z)) (y₁ ^ 2 * (y₁ - Z)) (x₂ * y₂) (x₂ ^ 2 * y₂) (x₂ * y₂ ^ 2) (x₂ ^ 2 * (x₂ - z)) (y₂ ^ 2 * (y₂ - Z)) (x₃ * y₃) (x₃ ^ 2 * y₃) (x₃ * y₃ ^ 2) (x₃ ^ 2 * (x₃ - z)) (y₃ ^ 2 * (y₃ - Z)) (x₄ * y₄) (x₄ ^ 2 * y₄) (x₄ * y₄ ^ 2) (x₄ ^ 2 * (x₄ - z)) (y₄ ^ 2 * (y₄ - Z)) (x₅ * y₅) (x₅ ^ 2 * y₅) (x₅ * y₅ ^ 2) (x₅ ^ 2 * (x₅ - z)) (y₅ ^ 2 * (y₅ - Z))
  rw [detU, detU, detV, detV, detT] at h
  exact h

theorem k3_swap (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) : k3 y₁ y₂ y₃ y₄ y₅ x₁ x₂ x₃ x₄ x₅ = k3 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ := by
  unfold k3 det5 det4 det3; ring

theorem k0_swap (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) : k0 y₁ y₂ y₃ y₄ y₅ x₁ x₂ x₃ x₄ x₅ = k0 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ := by
  unfold k0 det5 det4 det3; ring

theorem k2_swap (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) : k2 y₁ y₂ y₃ y₄ y₅ x₁ x₂ x₃ x₄ x₅ = k1 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ := by
  unfold k1 k2 det5 det4 det3; ring

theorem cycP_swap (x₁ x₂ x₃ y₁ y₂ y₃ : R) : cycP y₁ y₂ y₃ x₁ x₂ x₃ = -cycP x₁ x₂ x₃ y₁ y₂ y₃ := by
  unfold cycP det3; ring

theorem gq2_swap (x₁ x₂ x₃ y₁ y₂ y₃ : R) : gq2 y₁ y₂ y₃ x₁ x₂ x₃ = -gq1 x₁ x₂ x₃ y₁ y₂ y₃ := by
  unfold gq1 gq2 det3; ring

theorem gq0_swap (x₁ x₂ x₃ y₁ y₂ y₃ : R) : gq0 y₁ y₂ y₃ x₁ x₂ x₃ = -gq0 x₁ x₂ x₃ y₁ y₂ y₃ := by
  unfold gq0 det3; ring

/-- The second intersection `P_12` lies on `Γ₁₂₃` (cleared denominators).-/
theorem gq_P12 (x₁ x₂ x₃ y₁ y₂ y₃ : R) :
    gq0 x₁ x₂ x₃ y₁ y₂ y₃ * ((y₁ - y₂) * (x₁ - x₂)) - gq1 x₁ x₂ x₃ y₁ y₂ y₃ * ((y₁ * x₂ - x₁ * y₂) * (x₁ - x₂)) -
      gq2 x₁ x₂ x₃ y₁ y₂ y₃ * ((x₁ * y₂ - y₁ * x₂) * (y₁ - y₂)) + cycP x₁ x₂ x₃ y₁ y₂ y₃ * ((y₁ * x₂ - x₁ * y₂) * (x₁ * y₂ - y₁ * x₂)) = 0 := by
  unfold gq0 gq1 gq2 cycP det3; ring

/-- The second intersection `P_13` lies on `Γ₁₂₃` (cleared denominators).-/
theorem gq_P13 (x₁ x₂ x₃ y₁ y₂ y₃ : R) :
    gq0 x₁ x₂ x₃ y₁ y₂ y₃ * ((y₁ - y₃) * (x₁ - x₃)) - gq1 x₁ x₂ x₃ y₁ y₂ y₃ * ((y₁ * x₃ - x₁ * y₃) * (x₁ - x₃)) -
      gq2 x₁ x₂ x₃ y₁ y₂ y₃ * ((x₁ * y₃ - y₁ * x₃) * (y₁ - y₃)) + cycP x₁ x₂ x₃ y₁ y₂ y₃ * ((y₁ * x₃ - x₁ * y₃) * (x₁ * y₃ - y₁ * x₃)) = 0 := by
  unfold gq0 gq1 gq2 cycP det3; ring

/-- The second intersection `P_23` lies on `Γ₁₂₃` (cleared denominators).-/
theorem gq_P23 (x₁ x₂ x₃ y₁ y₂ y₃ : R) :
    gq0 x₁ x₂ x₃ y₁ y₂ y₃ * ((y₂ - y₃) * (x₂ - x₃)) - gq1 x₁ x₂ x₃ y₁ y₂ y₃ * ((y₂ * x₃ - x₂ * y₃) * (x₂ - x₃)) -
      gq2 x₁ x₂ x₃ y₁ y₂ y₃ * ((x₂ * y₃ - y₂ * x₃) * (y₂ - y₃)) + cycP x₁ x₂ x₃ y₁ y₂ y₃ * ((y₂ * x₃ - x₂ * y₃) * (x₂ * y₃ - y₂ * x₃)) = 0 := by
  unfold gq0 gq1 gq2 cycP det3; ring

end Poly

section Map

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem map_det3 (a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ : R) :
    f (det3 a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃) =
      det3 (f a₁) (f a₂) (f a₃) (f b₁) (f b₂) (f b₃) (f c₁) (f c₂) (f c₃) := by
  simp [det3]

theorem map_det4 (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ d₁ d₂ d₃ d₄ : R) :
    f (det4 a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ d₁ d₂ d₃ d₄) =
      det4 (f a₁) (f a₂) (f a₃) (f a₄) (f b₁) (f b₂) (f b₃) (f b₄) (f c₁) (f c₂) (f c₃) (f c₄) (f d₁) (f d₂) (f d₃) (f d₄) := by
  simp [det4, map_det3]

theorem map_det5 (a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅ : R) :
    f (det5 a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ d₁ d₂ d₃ d₄ d₅ e₁ e₂ e₃ e₄ e₅) =
      det5 (f a₁) (f a₂) (f a₃) (f a₄) (f a₅) (f b₁) (f b₂) (f b₃) (f b₄) (f b₅) (f c₁) (f c₂) (f c₃) (f c₄) (f c₅) (f d₁) (f d₂) (f d₃) (f d₄) (f d₅) (f e₁) (f e₂) (f e₃) (f e₄) (f e₅) := by
  simp [det5, map_det4]

theorem map_mN (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R) :
    f (mN x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄) = mN (f x₁) (f x₂) (f x₃) (f x₄) (f y₁) (f y₂) (f y₃) (f y₄) := by
  simp [mN, map_det4]

theorem map_mD (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R) :
    f (mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄) = mD (f x₁) (f x₂) (f x₃) (f x₄) (f y₁) (f y₂) (f y₃) (f y₄) := by
  simp [mD, map_det4]

theorem map_k0 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) :
    f (k0 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅) = k0 (f x₁) (f x₂) (f x₃) (f x₄) (f x₅) (f y₁) (f y₂) (f y₃) (f y₄) (f y₅) := by
  simp [k0, map_det5]

theorem map_k1 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) :
    f (k1 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅) = k1 (f x₁) (f x₂) (f x₃) (f x₄) (f x₅) (f y₁) (f y₂) (f y₃) (f y₄) (f y₅) := by
  simp [k1, map_det5]

theorem map_k2 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) :
    f (k2 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅) = k2 (f x₁) (f x₂) (f x₃) (f x₄) (f x₅) (f y₁) (f y₂) (f y₃) (f y₄) (f y₅) := by
  simp [k2, map_det5]

theorem map_k3 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) :
    f (k3 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅) = k3 (f x₁) (f x₂) (f x₃) (f x₄) (f x₅) (f y₁) (f y₂) (f y₃) (f y₄) (f y₅) := by
  simp [k3, map_det5]

theorem map_cycP (x₁ x₂ x₃ y₁ y₂ y₃ : R) :
    f (cycP x₁ x₂ x₃ y₁ y₂ y₃) = cycP (f x₁) (f x₂) (f x₃) (f y₁) (f y₂) (f y₃) := by
  simp [cycP, map_det3]

theorem map_gq0 (x₁ x₂ x₃ y₁ y₂ y₃ : R) :
    f (gq0 x₁ x₂ x₃ y₁ y₂ y₃) = gq0 (f x₁) (f x₂) (f x₃) (f y₁) (f y₂) (f y₃) := by
  simp [gq0, map_det3]

theorem map_gq1 (x₁ x₂ x₃ y₁ y₂ y₃ : R) :
    f (gq1 x₁ x₂ x₃ y₁ y₂ y₃) = gq1 (f x₁) (f x₂) (f x₃) (f y₁) (f y₂) (f y₃) := by
  simp [gq1, map_det3]

theorem map_gq2 (x₁ x₂ x₃ y₁ y₂ y₃ : R) :
    f (gq2 x₁ x₂ x₃ y₁ y₂ y₃) = gq2 (f x₁) (f x₂) (f x₃) (f y₁) (f y₂) (f y₃) := by
  simp [gq2, map_det3]

end Map

/-! ## Geometry in `ℂ` (the common point `M` is the origin) -/

section Geometry

open EuclideanGeometry

/-- `z` lies on the circle through `M = 0` with centre `c = p + q i`: `x² + y² = 2 (p x + q y)`.-/
def OnCircleM (c z : ℂ) : Prop := z.re ^ 2 + z.im ^ 2 = 2 * (c.re * z.re + c.im * z.im)

theorem onCircleM_iff (c z : ℂ) : OnCircleM c z ↔ z * conj z = conj c * z + c * conj z := by
  rw [OnCircleM, Complex.ext_iff]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re,
    Complex.add_im]
  constructor
  · intro h; exact ⟨by linear_combination h, by ring⟩
  · rintro ⟨h, -⟩; linear_combination h

/-- Second intersection (other than `M = 0`) of the circles through `M` with centres `c`, `d`.-/
noncomputable def second (c d : ℂ) : ℂ := (conj c * d - c * conj d) / (conj c - conj d)

/-- The circles with centres `c`, `d` through `M` meet transversally, i.e. `M`, `c`, `d` are not
collinear (equivalently: the second intersection exists and differs from `M`).-/
def Transversal (c d : ℂ) : Prop := conj c * d ≠ c * conj d

/-- A triple of circles is in general position: the centres are not collinear and the three second
intersection points are not collinear (so the circle `Γ` through them exists).-/
def GenTriple (a b c : ℂ) : Prop :=
  triP a b c (conj a) (conj b) (conj c) ≠ 0 ∧ cycP a b c (conj a) (conj b) (conj c) ≠ 0

/-- The common point of the four circles `Γ_ijk` (Clifford's first theorem), as an explicit ratio of
determinants in the centres and their conjugates.-/
noncomputable def miquel (a b c d : ℂ) : ℂ :=
  mN a b c d (conj a) (conj b) (conj c) (conj d) / mD a b c d (conj a) (conj b) (conj c) (conj d)

theorem Transversal.ne {c d : ℂ} (h : Transversal c d) : c ≠ d := by
  rintro rfl; exact h (mul_comm _ _)

theorem Transversal.left_ne_zero {c d : ℂ} (h : Transversal c d) : c ≠ 0 := by
  rintro rfl; exact h (by simp)

theorem Transversal.right_ne_zero {c d : ℂ} (h : Transversal c d) : d ≠ 0 := by
  rintro rfl; exact h (by simp)

theorem conj_sub_ne_zero {c d : ℂ} (h : c ≠ d) : conj c - conj d ≠ 0 := by
  rw [← map_sub]; exact (map_ne_zero _).2 (sub_ne_zero.2 h)

/-- `second` agrees with the real-coordinate formula: with `a = pᵢ - pⱼ`, `b = qᵢ - qⱼ`,
`λ = 2 (qᵢ a - pᵢ b) / (a² + b²)` the second intersection is `(λ (-b), λ a)`.-/
theorem second_eq_coords {c d : ℂ} (h : c ≠ d) :
    second c d =
      ⟨2 * (c.im * (c.re - d.re) - c.re * (c.im - d.im)) / ((c.re - d.re) ^ 2 + (c.im - d.im) ^ 2) *
          -(c.im - d.im),
        2 * (c.im * (c.re - d.re) - c.re * (c.im - d.im)) / ((c.re - d.re) ^ 2 + (c.im - d.im) ^ 2) *
          (c.re - d.re)⟩ := by
  have hn : (c.re - d.re) ^ 2 + (c.im - d.im) ^ 2 ≠ 0 := by
    intro h0
    have h1 : c.re - d.re = 0 := by nlinarith [sq_nonneg (c.re - d.re), sq_nonneg (c.im - d.im)]
    have h2 : c.im - d.im = 0 := by nlinarith [sq_nonneg (c.re - d.re), sq_nonneg (c.im - d.im)]
    exact h (Complex.ext (sub_eq_zero.1 h1) (sub_eq_zero.1 h2))
  have hd := conj_sub_ne_zero h
  rw [second, div_eq_iff hd]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
      Complex.conj_im] <;>
    field_simp <;> ring

theorem conj_second (c d : ℂ) : conj (second c d) = (c * conj d - conj c * d) / (c - d) := by
  unfold second; rw [map_div₀]; simp only [map_sub, map_mul, starRingEnd_self_apply]

theorem second_onCircleM_left {c d : ℂ} (h : c ≠ d) : OnCircleM c (second c d) := by
  have hd := conj_sub_ne_zero h; have he := sub_ne_zero.2 h
  rw [onCircleM_iff, conj_second, second]; field_simp; ring

theorem second_onCircleM_right {c d : ℂ} (h : c ≠ d) : OnCircleM d (second c d) := by
  have hd := conj_sub_ne_zero h; have he := sub_ne_zero.2 h
  rw [onCircleM_iff, conj_second, second]; field_simp; ring

theorem second_ne_zero {c d : ℂ} (h : Transversal c d) : second c d ≠ 0 := by
  unfold second
  exact div_ne_zero (sub_ne_zero.2 h) (conj_sub_ne_zero h.ne)

/-- `z` lies on the circle through `z₁, z₂, z₃`. When `z₁, z₂, z₃` are not collinear (guaranteed
for the second-intersection points by `GenTriple`) this circle is unique.-/
def OnCircle3 (z₁ z₂ z₃ z : ℂ) : Prop := Cospherical ({z₁, z₂, z₃, z} : Set ℂ)

/-! ### Generic circle lemmas -/

theorem circ_of_eq {g₀ g₁ g₂ cy z Z : ℂ} (hcy : cy ≠ 0) (h : g₀ - z * g₁ - Z * g₂ + z * Z * cy = 0) :
    (z - g₂ / cy) * (Z - g₁ / cy) = (g₁ * g₂ - g₀ * cy) / cy ^ 2 := by
  have e : (z - g₂ / cy) * (Z - g₁ / cy) - (g₁ * g₂ - g₀ * cy) / cy ^ 2 =
      (g₀ - z * g₁ - Z * g₂ + z * Z * cy) / cy := by
    field_simp; ring
  rw [h, zero_div, sub_eq_zero] at e; exact e

/-- If every point of `s` satisfies `g₀ - z g₁ - z̄ g₂ + z z̄ cy = 0` (a genuine circle equation:
`cy ≠ 0`, centre `g₂ / cy` with conjugate `g₁ / cy`), then `s` is cospherical.-/
theorem cospherical_of_eq {s : Set ℂ} {g₀ g₁ g₂ cy : ℂ} (hcy : cy ≠ 0)
    (ho : conj (g₂ / cy) = g₁ / cy)
    (hs : ∀ z ∈ s, g₀ - z * g₁ - conj z * g₂ + z * conj z * cy = 0) : Cospherical s := by
  refine ⟨g₂ / cy, √(((g₁ * g₂ - g₀ * cy) / cy ^ 2).re), fun z hz => ?_⟩
  have h1 := circ_of_eq hcy (hs z hz)
  rw [← ho, ← map_sub, Complex.mul_conj] at h1
  rw [Complex.dist_eq, Complex.norm_def, ← h1, Complex.ofReal_re]

theorem second_on {g₀ g₁ g₂ cy c d : ℂ} (hcd : c ≠ d)
    (h : g₀ * ((conj c - conj d) * (c - d)) - g₁ * ((conj c * d - c * conj d) * (c - d)) -
      g₂ * ((c * conj d - conj c * d) * (conj c - conj d)) +
      cy * ((conj c * d - c * conj d) * (c * conj d - conj c * d)) = 0) :
    g₀ - second c d * g₁ - conj (second c d) * g₂ + second c d * conj (second c d) * cy = 0 := by
  have hd := conj_sub_ne_zero hcd; have he := sub_ne_zero.2 hcd
  have key : g₀ - second c d * g₁ - conj (second c d) * g₂ + second c d * conj (second c d) * cy =
      (g₀ * ((conj c - conj d) * (c - d)) - g₁ * ((conj c * d - c * conj d) * (c - d)) -
      g₂ * ((c * conj d - conj c * d) * (conj c - conj d)) +
      cy * ((conj c * d - c * conj d) * (c * conj d - conj c * d))) /
        ((conj c - conj d) * (c - d)) := by
    rw [conj_second, second]; field_simp
  rw [key, h, zero_div]

theorem ratio_on {g₀ g₁ g₂ cy N D Nb Db q : ℂ} (hD : D ≠ 0) (hDb : Db ≠ 0)
    (h₁ : D * g₀ - N * g₁ = Nb * q) (h₂ : D * g₂ - N * cy = Db * q) :
    g₀ - N / D * g₁ - Nb / Db * g₂ + N / D * (Nb / Db) * cy = 0 := by
  have e : g₀ - N / D * g₁ - Nb / Db * g₂ + N / D * (Nb / Db) * cy =
      (Db * (D * g₀ - N * g₁) - Nb * (D * g₂ - N * cy)) / (D * Db) := by
    field_simp; ring
  rw [e, h₁, h₂]; ring

/-! ### Conjugation -/

theorem conj_mN (a b c d : ℂ) :
    conj (mN a b c d (conj a) (conj b) (conj c) (conj d)) =
      mN (conj a) (conj b) (conj c) (conj d) a b c d := by
  rw [map_mN]; simp only [starRingEnd_self_apply]

theorem conj_mD (a b c d : ℂ) :
    conj (mD a b c d (conj a) (conj b) (conj c) (conj d)) =
      mD (conj a) (conj b) (conj c) (conj d) a b c d := by
  rw [map_mD]; simp only [starRingEnd_self_apply]

theorem conj_miquel (a b c d : ℂ) :
    conj (miquel a b c d) =
      mN (conj a) (conj b) (conj c) (conj d) a b c d / mD (conj a) (conj b) (conj c) (conj d) a b c d := by
  rw [miquel, map_div₀, conj_mN, conj_mD]

/-- In general position the Miquel denominator does not vanish.-/
theorem mD_ne_zero {a b c d : ℂ} (hab : Transversal a b) (hac : Transversal a c)
    (hbc : Transversal b c) (had : Transversal a d) (hbd : Transversal b d) (hcd : Transversal c d)
    (ht : GenTriple a b c) : mD a b c d (conj a) (conj b) (conj c) (conj d) ≠ 0 := by
  intro h
  have h' : mD (conj a) (conj b) (conj c) (conj d) a b c d = 0 := by rw [← conj_mD, h, map_zero]
  have := resD h h'
  have hd : conj d ≠ 0 := (map_ne_zero _).2 hcd.right_ne_zero
  refine absurd this ?_
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero hd (conj_sub_ne_zero had.ne)) (conj_sub_ne_zero hbd.ne)) (conj_sub_ne_zero hcd.ne))
    ?_) ?_) ?_) ht.1) ht.2
  · exact sub_ne_zero.2 hab
  · exact sub_ne_zero.2 hac
  · exact sub_ne_zero.2 hbc

theorem miquel_mul (a b c d : ℂ) (hD : mD a b c d (conj a) (conj b) (conj c) (conj d) ≠ 0) :
    mN a b c d (conj a) (conj b) (conj c) (conj d) -
      miquel a b c d * mD a b c d (conj a) (conj b) (conj c) (conj d) = 0 := by
  rw [miquel, div_mul_cancel₀ _ hD, sub_self]

theorem conj_miquel_mul (a b c d : ℂ) (hD : mD a b c d (conj a) (conj b) (conj c) (conj d) ≠ 0) :
    mN (conj a) (conj b) (conj c) (conj d) a b c d -
      conj (miquel a b c d) * mD (conj a) (conj b) (conj c) (conj d) a b c d = 0 := by
  have hDb : mD (conj a) (conj b) (conj c) (conj d) a b c d ≠ 0 := by
    rw [← conj_mD]; exact (map_ne_zero _).2 hD
  rw [conj_miquel, div_mul_cancel₀ _ hDb, sub_self]

theorem cd_symm {c d : ℂ} (h : Transversal c d) : Transversal d c := by
  intro h'; apply h; rw [mul_comm, ← h', mul_comm]

/-! ### Clifford's first theorem -/

theorem miquel_p1243 (a b c d : ℂ) : miquel a b d c = miquel a b c d := by
  unfold miquel; rw [mN_p1243, mD_p1243, neg_div_neg_eq]

theorem miquel_p1342 (a b c d : ℂ) : miquel a c d b = miquel a b c d := by
  unfold miquel; rw [mN_p1342, mD_p1342]

theorem miquel_p2341 (a b c d : ℂ) : miquel b c d a = miquel a b c d := by
  unfold miquel; rw [mN_p2341, mD_p2341, neg_div_neg_eq]

/-- The circle `Γ_abc` through the second intersections `P_ab, P_ac, P_bc` passes through
`miquel a b c d`.-/
theorem gamma_cospherical {a b c d : ℂ} (hab : Transversal a b) (hac : Transversal a c)
    (hbc : Transversal b c) (ht : GenTriple a b c)
    (hD : mD a b c d (conj a) (conj b) (conj c) (conj d) ≠ 0) :
    Cospherical ({second a b, second a c, second b c, miquel a b c d} : Set ℂ) := by
  have hDb : mD (conj a) (conj b) (conj c) (conj d) a b c d ≠ 0 := by
    rw [← conj_mD]; exact (map_ne_zero _).2 hD
  refine cospherical_of_eq (g₀ := gq0 a b c (conj a) (conj b) (conj c))
    (g₁ := gq1 a b c (conj a) (conj b) (conj c)) (g₂ := gq2 a b c (conj a) (conj b) (conj c))
    ht.2 ?_ ?_
  · rw [map_div₀, map_gq2, map_cycP]
    simp only [starRingEnd_self_apply]
    rw [gq2_swap, cycP_swap, neg_div_neg_eq]
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact second_on hab.ne (gq_P12 a b c (conj a) (conj b) (conj c))
    · exact second_on hac.ne (gq_P13 a b c (conj a) (conj b) (conj c))
    · exact second_on hbc.ne (gq_P23 a b c (conj a) (conj b) (conj c))
    · rw [conj_miquel]
      exact ratio_on hD hDb (certA₁ _ _ _ _ _ _ _ _) (certA₂ _ _ _ _ _ _ _ _)

/-- Four circles through `M` in general position: pairwise transversal, and each triple in general
position (centres not collinear, second intersections not collinear).-/
structure GenPos4 (a b c d : ℂ) : Prop where
  ab : Transversal a b
  ac : Transversal a c
  ad : Transversal a d
  bc : Transversal b c
  bd : Transversal b d
  cd : Transversal c d
  abc : GenTriple a b c
  abd : GenTriple a b d
  acd : GenTriple a c d
  bcd : GenTriple b c d

/-- **Clifford's first theorem** (`n = 4`). For four circles through `M` with centres `a, b, c, d`
in general position, the four circles `Γ_ijk` through the second intersection points
`P_ij, P_ik, P_jk` all pass through the single point `miquel a b c d`.-/
theorem clifford_one {a b c d : ℂ} (h : GenPos4 a b c d) :
    OnCircle3 (second a b) (second a c) (second b c) (miquel a b c d) ∧
    OnCircle3 (second a b) (second a d) (second b d) (miquel a b c d) ∧
    OnCircle3 (second a c) (second a d) (second c d) (miquel a b c d) ∧
    OnCircle3 (second b c) (second b d) (second c d) (miquel a b c d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact gamma_cospherical h.ab h.ac h.bc h.abc
      (mD_ne_zero h.ab h.ac h.bc h.ad h.bd h.cd h.abc)
  · rw [← miquel_p1243]
    exact gamma_cospherical h.ab h.ad h.bd h.abd
      (mD_ne_zero h.ab h.ad h.bd h.ac h.bc (cd_symm h.cd) h.abd)
  · rw [← miquel_p1342]
    exact gamma_cospherical h.ac h.ad h.cd h.acd
      (mD_ne_zero h.ac h.ad h.cd h.ab (cd_symm h.bc) (cd_symm h.bd) h.acd)
  · rw [← miquel_p2341]
    exact gamma_cospherical h.bc h.bd h.cd h.bcd
      (mD_ne_zero h.bc h.bd h.cd (cd_symm h.ab) (cd_symm h.ac) (cd_symm h.ad) h.bcd)

/-! ### Clifford's second theorem -/

/-- The Clifford circle of five circles with centres `a, …, e` (in `z`, `conj z`).-/
noncomputable def cliffordEq (a b c d e z : ℂ) : ℂ :=
  kK a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) z (conj z)

theorem conj_ne_zero' {c : ℂ} (h : c ≠ 0) : conj c ≠ 0 := (map_ne_zero _).2 h

/-- The Miquel point of the first four circles lies on the Clifford circle (Desnanot–Jacobi).-/
theorem cliffordEq_miquel {a b c d e : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ht : triP a b c (conj a) (conj b) (conj c) ≠ 0)
    (hD : mD a b c d (conj a) (conj b) (conj c) (conj d) ≠ 0) :
    cliffordEq a b c d e (miquel a b c d) = 0 := by
  have h := kK_dj a b c d e (conj a) (conj b) (conj c) (conj d) (conj e)
    (miquel a b c d) (conj (miquel a b c d))
  rw [miquel_mul a b c d hD, conj_miquel_mul a b c d hD] at h
  simp only [mul_zero, zero_mul, sub_zero] at h
  have hne : a * conj a * b * conj b * c * conj c * triP a b c (conj a) (conj b) (conj c) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha
      (conj_ne_zero' ha)) hb) (conj_ne_zero' hb)) hc) (conj_ne_zero' hc)) ht
  exact (mul_eq_zero.1 h).resolve_right hne

/-- Five circles through `M` in general position: pairwise transversal and every triple in general
position.-/
structure GenPos5 (a b c d e : ℂ) : Prop where
  ab : Transversal a b
  ac : Transversal a c
  ad : Transversal a d
  ae : Transversal a e
  bc : Transversal b c
  bd : Transversal b d
  be : Transversal b e
  cd : Transversal c d
  ce : Transversal c e
  de : Transversal d e
  abc : GenTriple a b c
  abd : GenTriple a b d
  abe : GenTriple a b e
  acd : GenTriple a c d
  ace : GenTriple a c e
  ade : GenTriple a d e
  bcd : GenTriple b c d
  bce : GenTriple b c e
  bde : GenTriple b d e
  cde : GenTriple c d e

/-- Non-degeneracy of the Clifford circle: the coefficient of `z * conj z` in `cliffordEq` is
nonzero (when it vanishes, the "circle" through the five points degenerates to a line).-/
def CliffordNondeg (a b c d e : ℂ) : Prop :=
  k3 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) ≠ 0

theorem GenPos5.pos4_abcd {a b c d e : ℂ} (h : GenPos5 a b c d e) : GenPos4 a b c d :=
  ⟨h.ab, h.ac, h.ad, h.bc, h.bd, h.cd, h.abc, h.abd, h.acd, h.bcd⟩
theorem GenPos5.pos4_abce {a b c d e : ℂ} (h : GenPos5 a b c d e) : GenPos4 a b c e :=
  ⟨h.ab, h.ac, h.ae, h.bc, h.be, h.ce, h.abc, h.abe, h.ace, h.bce⟩
theorem GenPos5.pos4_abde {a b c d e : ℂ} (h : GenPos5 a b c d e) : GenPos4 a b d e :=
  ⟨h.ab, h.ad, h.ae, h.bd, h.be, h.de, h.abd, h.abe, h.ade, h.bde⟩
theorem GenPos5.pos4_acde {a b c d e : ℂ} (h : GenPos5 a b c d e) : GenPos4 a c d e :=
  ⟨h.ac, h.ad, h.ae, h.cd, h.ce, h.de, h.acd, h.ace, h.ade, h.cde⟩
theorem GenPos5.pos4_bcde {a b c d e : ℂ} (h : GenPos5 a b c d e) : GenPos4 b c d e :=
  ⟨h.bc, h.bd, h.be, h.cd, h.ce, h.de, h.bcd, h.bce, h.bde, h.cde⟩

theorem GenPos4.mD_ne_zero {a b c d : ℂ} (h : GenPos4 a b c d) :
    mD a b c d (conj a) (conj b) (conj c) (conj d) ≠ 0 :=
  Clifford.mD_ne_zero h.ab h.ac h.bc h.ad h.bd h.cd h.abc

theorem GenPos4.cliffordEq_miquel {a b c d : ℂ} (h : GenPos4 a b c d) (e : ℂ) :
    cliffordEq a b c d e (miquel a b c d) = 0 :=
  Clifford.cliffordEq_miquel h.ab.left_ne_zero h.bc.left_ne_zero h.cd.left_ne_zero h.abc.1
    h.mD_ne_zero

/-- **Clifford's second theorem** (`n = 5`). For five circles through `M` with centres
`a, b, c, d, e` in general position, the five points `P_S` given by Clifford's first theorem
(`clifford_one`), one for each 4-element subset `S`, lie on one circle.-/
theorem clifford_two {a b c d e : ℂ} (h : GenPos5 a b c d e) (hk : CliffordNondeg a b c d e) :
    Cospherical ({miquel a b c d, miquel a b c e, miquel a b d e, miquel a c d e, miquel b c d e} :
      Set ℂ) := by
  refine cospherical_of_eq (g₀ := k0 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e))
    (g₁ := k1 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e))
    (g₂ := k2 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e)) hk ?_ ?_
  · rw [map_div₀, map_k2, map_k3]
    simp only [starRingEnd_self_apply]
    rw [k2_swap, k3_swap]
  · have key : ∀ z, cliffordEq a b c d e z = 0 →
        k0 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) -
          z * k1 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) -
          conj z * k2 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) +
          z * conj z * k3 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) = 0 := by
      intro z hz; rw [cliffordEq, kK_expand] at hz; exact hz
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    apply key
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact h.pos4_abcd.cliffordEq_miquel e
    · have h1 := h.pos4_abce.cliffordEq_miquel d
      rw [cliffordEq, kK_p12354, neg_eq_zero] at h1; exact h1
    · have h1 := h.pos4_abde.cliffordEq_miquel c
      rw [cliffordEq, kK_p12453] at h1; exact h1
    · have h1 := h.pos4_acde.cliffordEq_miquel b
      rw [cliffordEq, kK_p13452, neg_eq_zero] at h1; exact h1
    · have h1 := h.pos4_bcde.cliffordEq_miquel a
      rw [cliffordEq, kK_p23451] at h1; exact h1

end Geometry

end Clifford
