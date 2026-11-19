import Tengoku.Seed.Tactic
import Tengoku.Seed.Algebra.Field.IsField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.Certificates

/-- A three-coordinate algebra with `α³ = a + b*α`. Its arithmetic is
explicit, so finite certificates can be reduced by Lean's kernel.-/
@[ext] structure CubicAlgebra (R : Type*) (a b : R) where
  c0 : R
  c1 : R
  c2 : R
  deriving DecidableEq

namespace CubicAlgebra

variable {R : Type*} {a b : R}

def equivProd (a b : R) : CubicAlgebra R a b ≃ R × R × R where
  toFun x := (x.c0, x.c1, x.c2)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩

instance [Fintype R] : Fintype (CubicAlgebra R a b) :=
  Fintype.ofEquiv (R × R × R) (equivProd a b).symm

@[simp] theorem card [Fintype R] :
    Fintype.card (CubicAlgebra R a b) = Fintype.card R ^ 3 := by
  rw [Fintype.card_congr (equivProd a b)]
  simp [pow_succ, mul_assoc]

instance [Zero R] : Zero (CubicAlgebra R a b) := ⟨⟨0, 0, 0⟩⟩
instance [One R] [Zero R] : One (CubicAlgebra R a b) := ⟨⟨1, 0, 0⟩⟩
instance [Add R] : Add (CubicAlgebra R a b) :=
  ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2⟩⟩
instance [Neg R] : Neg (CubicAlgebra R a b) :=
  ⟨fun x => ⟨-x.c0, -x.c1, -x.c2⟩⟩
instance [Mul R] [Add R] : Mul (CubicAlgebra R a b) :=
  ⟨fun x y =>
    ⟨x.c0*y.c0 + a*(x.c1*y.c2 + x.c2*y.c1),
     x.c0*y.c1 + x.c1*y.c0 + b*(x.c1*y.c2 + x.c2*y.c1) + a*x.c2*y.c2,
     x.c0*y.c2 + x.c1*y.c1 + x.c2*y.c0 + b*x.c2*y.c2⟩⟩
instance {S : Type*} [SMul S R] : SMul S (CubicAlgebra R a b) :=
  ⟨fun n x => ⟨n • x.c0, n • x.c1, n • x.c2⟩⟩
instance [NatCast R] [Zero R] : NatCast (CubicAlgebra R a b) := ⟨fun n => ⟨n, 0, 0⟩⟩
instance [IntCast R] [Zero R] : IntCast (CubicAlgebra R a b) := ⟨fun n => ⟨n, 0, 0⟩⟩

@[simp] theorem c0_zero [Zero R] : (0 : CubicAlgebra R a b).c0 = 0 := rfl
@[simp] theorem c0_one [Zero R] [One R] : (1 : CubicAlgebra R a b).c0 = 1 := rfl
@[simp] theorem c0_add [Add R] (x y : CubicAlgebra R a b) :
    (x+y).c0 = x.c0+y.c0 := rfl
@[simp] theorem c0_neg [Neg R] (x : CubicAlgebra R a b) : (-x).c0 = -x.c0 := rfl
@[simp] theorem c0_mul [Mul R] [Add R] (x y : CubicAlgebra R a b) :
    (x*y).c0 = x.c0*y.c0 + a*(x.c1*y.c2 + x.c2*y.c1) := rfl
@[simp] theorem c0_smul {S : Type*} [SMul S R] (n : S) (x : CubicAlgebra R a b) :
    (n • x).c0 = n • x.c0 := rfl
@[simp] theorem c0_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : CubicAlgebra R a b).c0 = n := rfl
@[simp] theorem c0_intCast [IntCast R] [Zero R] (n : ℤ) :
    (n : CubicAlgebra R a b).c0 = n := rfl

@[simp] theorem c1_zero [Zero R] : (0 : CubicAlgebra R a b).c1 = 0 := rfl
@[simp] theorem c1_one [Zero R] [One R] : (1 : CubicAlgebra R a b).c1 = 0 := rfl
@[simp] theorem c1_add [Add R] (x y : CubicAlgebra R a b) :
    (x+y).c1 = x.c1+y.c1 := rfl
@[simp] theorem c1_neg [Neg R] (x : CubicAlgebra R a b) : (-x).c1 = -x.c1 := rfl
@[simp] theorem c1_mul [Mul R] [Add R] (x y : CubicAlgebra R a b) :
    (x*y).c1 = x.c0*y.c1 + x.c1*y.c0 + b*(x.c1*y.c2 + x.c2*y.c1) + a*x.c2*y.c2 := rfl
@[simp] theorem c1_smul {S : Type*} [SMul S R] (n : S) (x : CubicAlgebra R a b) :
    (n • x).c1 = n • x.c1 := rfl
@[simp] theorem c1_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : CubicAlgebra R a b).c1 = 0 := rfl
@[simp] theorem c1_intCast [IntCast R] [Zero R] (n : ℤ) :
    (n : CubicAlgebra R a b).c1 = 0 := rfl

@[simp] theorem c2_zero [Zero R] : (0 : CubicAlgebra R a b).c2 = 0 := rfl
@[simp] theorem c2_one [Zero R] [One R] : (1 : CubicAlgebra R a b).c2 = 0 := rfl
@[simp] theorem c2_add [Add R] (x y : CubicAlgebra R a b) :
    (x+y).c2 = x.c2+y.c2 := rfl
@[simp] theorem c2_neg [Neg R] (x : CubicAlgebra R a b) : (-x).c2 = -x.c2 := rfl
@[simp] theorem c2_mul [Mul R] [Add R] (x y : CubicAlgebra R a b) :
    (x*y).c2 = x.c0*y.c2 + x.c1*y.c1 + x.c2*y.c0 + b*x.c2*y.c2 := rfl
@[simp] theorem c2_smul {S : Type*} [SMul S R] (n : S) (x : CubicAlgebra R a b) :
    (n • x).c2 = n • x.c2 := rfl
@[simp] theorem c2_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : CubicAlgebra R a b).c2 = 0 := rfl
@[simp] theorem c2_intCast [IntCast R] [Zero R] (n : ℤ) :
    (n : CubicAlgebra R a b).c2 = 0 := rfl

instance [CommRing R] : CommRing (CubicAlgebra R a b) where
  nsmul := (· • ·)
  zsmul := (· • ·)
  natCast := Nat.cast
  intCast := Int.cast
  add_assoc x y z := by ext <;> simp [add_assoc]
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  add_comm x y := by ext <;> simp [add_comm]
  neg_add_cancel x := by ext <;> simp
  nsmul_zero x := by ext <;> simp
  nsmul_succ n x := by ext <;> simp <;> ring
  zsmul_zero' x := by ext <;> simp
  zsmul_succ' n x := by ext <;> simp <;> ring
  zsmul_neg' n x := by ext <;> simp [Int.negSucc_eq] <;> ring
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp
  intCast_ofNat n := by ext <;> simp
  intCast_negSucc n := by ext <;> simp
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  left_distrib x y z := by ext <;> simp <;> ring
  right_distrib x y z := by ext <;> simp <;> ring
  mul_comm x y := by ext <;> simp <;> ring

end CubicAlgebra
end MagicSquares.Certificates
