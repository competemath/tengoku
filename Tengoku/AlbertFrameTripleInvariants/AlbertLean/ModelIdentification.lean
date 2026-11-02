import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Challenge
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.SplitAlbert
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The 27 coordinates as a Hermitian matrix over the split octonions

`coordToHermitian` reads a coordinate vector as the Hermitian 3×3 Zorn matrix used in
`examples/exact-witness/README.md`: diagonal entries x₀, x₁, x₂ and the three octonion
entries `coordV`, `coordS`, `coordC`, every sign explicit. `hermitianToCoord` is its
inverse. The theorems show the map is a linear bijection, sends the coordinate unit to the
identity matrix, and carries the 45-term cubic norm to the Hermitian determinant;
`AlbertLean/ModelProduct.lean` completes this to the product
(`conventionalSplitAlbertIdentification`). The identification with Tau Ceti's algebra used
by the selected theorem `OneBit.splitAlbertModel` is a separate map, in `OneBit/Bridge.lean`.
-/

namespace AlbertLean

-- PALOMAR_MODEL_STATEMENT_BEGIN

def coordV (x : Coord) : Zorn :=
  ⟨v x 3,
   ⟨-v x 8, v x 6, -v x 5⟩,
   ⟨v x 7, v x 9, v x 10⟩,
   v x 4⟩

def coordS (x : Coord) : Zorn :=
  ⟨v x 18,
   ⟨v x 15, v x 16, v x 17⟩,
   ⟨-v x 11, -v x 12, -v x 13⟩,
   v x 14⟩

def coordC (x : Coord) : Zorn :=
  ⟨v x 22,
   ⟨-v x 23, -v x 24, -v x 25⟩,
   ⟨v x 19, v x 20, v x 21⟩,
   v x 26⟩

/-- The frozen C0 coordinates interpreted as a Hermitian Zorn matrix.-/
def coordToHermitian (x : Coord) : Hermitian3 :=
  ⟨v x 0, v x 1, v x 2, coordV x, coordS x, coordC x⟩

/-- The inverse coordinate reader, with every permutation and sign visible.-/
def hermitianToCoord (x : Hermitian3) : Coord := fun i =>
  match i.val with
  | 0 => x.diag1
  | 1 => x.diag2
  | 2 => x.diag3
  | 3 => x.off23.upperLeft
  | 4 => x.off23.lowerRight
  | 5 => -x.off23.upperRight.z
  | 6 => x.off23.upperRight.y
  | 7 => x.off23.lowerLeft.x
  | 8 => -x.off23.upperRight.x
  | 9 => x.off23.lowerLeft.y
  | 10 => x.off23.lowerLeft.z
  | 11 => -x.off31.lowerLeft.x
  | 12 => -x.off31.lowerLeft.y
  | 13 => -x.off31.lowerLeft.z
  | 14 => x.off31.lowerRight
  | 15 => x.off31.upperRight.x
  | 16 => x.off31.upperRight.y
  | 17 => x.off31.upperRight.z
  | 18 => x.off31.upperLeft
  | 19 => x.off12.lowerLeft.x
  | 20 => x.off12.lowerLeft.y
  | 21 => x.off12.lowerLeft.z
  | 22 => x.off12.upperLeft
  | 23 => -x.off12.upperRight.x
  | 24 => -x.off12.upperRight.y
  | 25 => -x.off12.upperRight.z
  | 26 => x.off12.lowerRight
  | _ => 0

/-- The exact data constituting the conventional split-Albert identification.-/
structure ConventionalSplitAlbertIdentification : Prop where
  leftInverse : Function.LeftInverse hermitianToCoord coordToHermitian
  rightInverse : Function.RightInverse hermitianToCoord coordToHermitian
  mapAdd : ∀ x y, coordToHermitian (x + y) =
    Hermitian3.add (coordToHermitian x) (coordToHermitian y)
  mapSMul : ∀ a x, coordToHermitian (a • x) =
    Hermitian3.smul a (coordToHermitian x)
  mapsOne : coordToHermitian AlbertLean.one = Hermitian3.one
  preservesCubic : ∀ x, Hermitian3.cubicNorm (coordToHermitian x) = cubicNorm x
  preservesProduct : ∀ x y,
    coordToHermitian (structuredProduct x y) =
      Hermitian3.jordan (coordToHermitian x) (coordToHermitian y)

-- PALOMAR_MODEL_STATEMENT_END

theorem hermitianToCoord_coordToHermitian (x : Coord) :
    hermitianToCoord (coordToHermitian x) = x := by
  funext i
  fin_cases i <;>
    simp [hermitianToCoord, coordToHermitian, coordV, coordS, coordC, v]

theorem coordToHermitian_hermitianToCoord (x : Hermitian3) :
    coordToHermitian (hermitianToCoord x) = x := by
  rcases x with
    ⟨d₁, d₂, d₃,
      ⟨va, ⟨vu₁, vu₂, vu₃⟩, ⟨vv₁, vv₂, vv₃⟩, vb⟩,
      ⟨sa, ⟨su₁, su₂, su₃⟩, ⟨sv₁, sv₂, sv₃⟩, sb⟩,
      ⟨ca, ⟨cu₁, cu₂, cu₃⟩, ⟨cv₁, cv₂, cv₃⟩, cb⟩⟩
  simp [coordToHermitian, hermitianToCoord, coordV, coordS, coordC, v]

theorem coordToHermitian_add (x y : Coord) :
    coordToHermitian (x + y) =
      Hermitian3.add (coordToHermitian x) (coordToHermitian y) := by
  apply Hermitian3.ext
  all_goals try apply Zorn.ext
  all_goals try apply Vec3.ext
  all_goals
    simp [coordToHermitian, coordV, coordS, coordC, Hermitian3.add,
      Zorn.add, Vec3.add, v] <;>
    ring

theorem coordToHermitian_smul (a : ℚ) (x : Coord) :
    coordToHermitian (a • x) = Hermitian3.smul a (coordToHermitian x) := by
  apply Hermitian3.ext
  all_goals try apply Zorn.ext
  all_goals try apply Vec3.ext
  all_goals
    simp [coordToHermitian, coordV, coordS, coordC, Hermitian3.smul,
      Zorn.smul, Vec3.smul, v, smul_eq_mul]

theorem coordToHermitian_sub (x y : Coord) :
    coordToHermitian (x - y) =
      Hermitian3.sub (coordToHermitian x) (coordToHermitian y) := by
  apply Hermitian3.ext
  all_goals try apply Zorn.ext
  all_goals try apply Vec3.ext
  all_goals
    simp [coordToHermitian, coordV, coordS, coordC, Hermitian3.sub,
      Zorn.sub, Vec3.sub, v] <;>
    ring

private theorem coordV_norm (x : Coord) :
    Zorn.norm (coordV x) =
      v x 3 * v x 4 + v x 5 * v x 10 - v x 6 * v x 9 +
        v x 7 * v x 8 := by
  simp [coordV, Zorn.norm, Vec3.dot]
  ring

private theorem coordS_norm (x : Coord) :
    Zorn.norm (coordS x) =
      v x 11 * v x 15 + v x 12 * v x 16 +
        v x 13 * v x 17 + v x 14 * v x 18 := by
  simp [coordS, Zorn.norm, Vec3.dot]
  ring

private theorem coordC_norm (x : Coord) :
    Zorn.norm (coordC x) =
      v x 19 * v x 23 + v x 20 * v x 24 +
        v x 21 * v x 25 + v x 22 * v x 26 := by
  simp [coordC, Zorn.norm, Vec3.dot]
  ring

private def trialityForm (x : Coord) : ℚ :=
    v x 3 * v x 15 * v x 19 +
    v x 3 * v x 16 * v x 20 +
    v x 3 * v x 17 * v x 21 +
    v x 3 * v x 18 * v x 22 +
    v x 4 * v x 11 * v x 23 +
    v x 4 * v x 12 * v x 24 +
    v x 4 * v x 13 * v x 25 +
    v x 4 * v x 14 * v x 26 +
    v x 5 * v x 13 * v x 22 -
    v x 5 * v x 14 * v x 21 +
    v x 5 * v x 15 * v x 24 -
    v x 5 * v x 16 * v x 23 -
    v x 6 * v x 12 * v x 22 +
    v x 6 * v x 14 * v x 20 +
    v x 6 * v x 15 * v x 25 -
    v x 6 * v x 17 * v x 23 +
    v x 7 * v x 12 * v x 21 -
    v x 7 * v x 13 * v x 20 +
    v x 7 * v x 15 * v x 26 -
    v x 7 * v x 18 * v x 23 +
    v x 8 * v x 11 * v x 22 -
    v x 8 * v x 14 * v x 19 +
    v x 8 * v x 16 * v x 25 -
    v x 8 * v x 17 * v x 24 -
    v x 9 * v x 11 * v x 21 +
    v x 9 * v x 13 * v x 19 +
    v x 9 * v x 16 * v x 26 -
    v x 9 * v x 18 * v x 24 +
    v x 10 * v x 11 * v x 20 -
    v x 10 * v x 12 * v x 19 +
    v x 10 * v x 17 * v x 26 -
    v x 10 * v x 18 * v x 25

private theorem coord_triality (x : Coord) :
    Zorn.scalarTrace (Zorn.mul (Zorn.mul (coordS x) (coordC x)) (coordV x)) =
      trialityForm x := by
  simp [coordS, coordC, coordV, Zorn.scalarTrace, Zorn.mul,
    Vec3.dot, Vec3.cross, trialityForm]
  ring

/-- The C0 unit is the identity Hermitian matrix.-/
theorem coordToHermitian_one : coordToHermitian AlbertLean.one = Hermitian3.one := by
  apply Hermitian3.ext
  all_goals try apply Zorn.ext
  all_goals try apply Vec3.ext
  all_goals
    simp [coordToHermitian, coordV, coordS, coordC,
      AlbertLean.one, Hermitian3.one, Zorn.zero, v, q]

/-- The frozen 45-term cubic is the conventional Hermitian determinant.-/
theorem coordToHermitian_cubicNorm (x : Coord) :
    Hermitian3.cubicNorm (coordToHermitian x) = AlbertLean.cubicNorm x := by
  simp only [Hermitian3.cubicNorm, Hermitian3.tripleCoupling,
    coordToHermitian]
  rw [coordV_norm, coordS_norm, coordC_norm, coord_triality]
  simp [AlbertLean.cubicNorm, trialityForm, q]
  ring

end AlbertLean
