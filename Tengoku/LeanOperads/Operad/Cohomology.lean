/-
# Operad cohomology

With `d = ⁅Θ, -⁆` squaring to zero, the deformation complex is a cochain complex and its
cohomology is defined. The differential is packaged here as a genuine `LinearMap` between the
graded pieces, which is what `LinearMap.ker` and `LinearMap.range` need.

Degrees are indexed by the *source*: `dLin T m : PieceS R P m →ₗ PieceS R P (1 + m)`. Indexing
by the target would force `1 + (m - 1) = m`, reintroducing the truncated subtraction that the
whole library is arranged to avoid.
-/
import Tengoku.LeanOperads.Operad.TotalSpaceS
import Tengoku.Seed.LinearAlgebra.Quotient.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

namespace Operad

open NSOperad DirectSum

section

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-! ### Linearity of the graded bracket in its second argument -/

lemma gbracket_add_right {j k : ℕ} (α : P (j + 1)) (β β' : P (k + 1)) :
    gbracket (R := R) α (β + β') = gbracket (R := R) α β + gbracket (R := R) α β' := by
  simp only [gbracket, sstar_add_right, sstar_add_left, map_add, smul_add]
  abel

lemma gbracket_smul_right {j k : ℕ} (r : R) (α : P (j + 1)) (β : P (k + 1)) :
    gbracket (R := R) α (r • β) = r • gbracket (R := R) α β := by
  simp only [gbracket, sstar_smul_right, sstar_smul_left, map_smul, smul_sub]
  rw [smul_comm]

/-- The differential `d = ⁅Θ, -⁆` of the deformation complex, as a linear map.-/
def dLin (T : PieceS R P 1) (m : ℕ) : PieceS R P m →ₗ[R] PieceS R P (1 + m) where
  toFun x := gbracket (R := R) (P := P) (j := 1) (k := m) T x
  map_add' x y := gbracket_add_right (R := R) (P := P) (j := 1) (k := m) T x y
  map_smul' r x := gbracket_smul_right (R := R) (P := P) (j := 1) (k := m) r T x

@[simp] lemma dLin_apply (T : PieceS R P 1) (m : ℕ) (x : PieceS R P m) :
    dLin T m x = gbracket (R := R) (P := P) (j := 1) (k := m) T x := rfl

/-! ### Cocycles, coboundaries, cohomology -/

/-- The cocycles in degree `1 + m`.-/
def cocycles (T : PieceS R P 1) (m : ℕ) : Submodule R (PieceS R P (1 + m)) :=
  LinearMap.ker (dLin T (1 + m))

/-- The coboundaries in degree `1 + m`.-/
def coboundaries (T : PieceS R P 1) (m : ℕ) : Submodule R (PieceS R P (1 + m)) :=
  LinearMap.range (dLin T m)

/-- **Operad cohomology** in degree `1 + m`: cocycles modulo coboundaries.-/
def cohomology (T : PieceS R P 1) (m : ℕ) : Type v :=
  (cocycles (R := R) T m) ⧸
    ((coboundaries (R := R) T m).comap (cocycles (R := R) T m).subtype)

instance (T : PieceS R P 1) (m : ℕ) : AddCommGroup (cohomology (R := R) T m) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (T : PieceS R P 1) (m : ℕ) : Module R (cohomology (R := R) T m) :=
  inferInstanceAs (Module R (_ ⧸ _))

/-- The class of a cocycle.-/
def cohomologyMk (T : PieceS R P 1) (m : ℕ) (x : cocycles (R := R) T m) :
    cohomology (R := R) T m :=
  Submodule.Quotient.mk x

end

end Operad
