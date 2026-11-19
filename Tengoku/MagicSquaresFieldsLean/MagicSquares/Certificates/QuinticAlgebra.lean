import Tengoku.Seed.Tactic
import Tengoku.Seed.Algebra.Field.IsField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0

namespace MagicSquares.Certificates

/-- A five-coordinate algebra with `α⁵ = a + b*α`. Its arithmetic is
explicit, so finite certificates can be reduced by Lean's kernel.-/
@[ext] structure QuinticAlgebra (R : Type*) (a b : R) where
  c0 : R
  c1 : R
  c2 : R
  c3 : R
  c4 : R
  deriving DecidableEq

namespace QuinticAlgebra

variable {R : Type*} {a b : R}

def equivProd (a b : R) : QuinticAlgebra R a b ≃ R × R × R × R × R where
  toFun x := (x.c0, x.c1, x.c2, x.c3, x.c4)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩

instance [Fintype R] : Fintype (QuinticAlgebra R a b) :=
  Fintype.ofEquiv (R × R × R × R × R) (equivProd a b).symm

@[simp] theorem card [Fintype R] :
    Fintype.card (QuinticAlgebra R a b) = Fintype.card R ^ 5 := by
  rw [Fintype.card_congr (equivProd a b)]
  simp [pow_succ, mul_assoc]

instance [Zero R] : Zero (QuinticAlgebra R a b) := ⟨⟨0, 0, 0, 0, 0⟩⟩
instance [One R] [Zero R] : One (QuinticAlgebra R a b) := ⟨⟨1, 0, 0, 0, 0⟩⟩
instance [Add R] : Add (QuinticAlgebra R a b) :=
  ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2, x.c3 + y.c3, x.c4 + y.c4⟩⟩
instance [Neg R] : Neg (QuinticAlgebra R a b) :=
  ⟨fun x => ⟨-x.c0, -x.c1, -x.c2, -x.c3, -x.c4⟩⟩
instance [Mul R] [Add R] : Mul (QuinticAlgebra R a b) :=
  ⟨fun x y =>
    ⟨x.c0*y.c0 + a*(x.c1*y.c4 + x.c2*y.c3 + x.c3*y.c2 + x.c4*y.c1),
     x.c0*y.c1 + x.c1*y.c0 + a*(x.c2*y.c4 + x.c3*y.c3 + x.c4*y.c2) + b*(x.c1*y.c4 + x.c2*y.c3 + x.c3*y.c2 + x.c4*y.c1),
     x.c0*y.c2 + x.c1*y.c1 + x.c2*y.c0 + a*(x.c3*y.c4 + x.c4*y.c3) + b*(x.c2*y.c4 + x.c3*y.c3 + x.c4*y.c2),
     x.c0*y.c3 + x.c1*y.c2 + x.c2*y.c1 + x.c3*y.c0 + a*(x.c4*y.c4) + b*(x.c3*y.c4 + x.c4*y.c3),
     x.c0*y.c4 + x.c1*y.c3 + x.c2*y.c2 + x.c3*y.c1 + x.c4*y.c0 + b*(x.c4*y.c4)⟩⟩
instance {S : Type*} [SMul S R] : SMul S (QuinticAlgebra R a b) :=
  ⟨fun n x => ⟨n • x.c0, n • x.c1, n • x.c2, n • x.c3, n • x.c4⟩⟩
instance [NatCast R] [Zero R] : NatCast (QuinticAlgebra R a b) := ⟨fun n => ⟨n, 0, 0, 0, 0⟩⟩
instance [IntCast R] [Zero R] : IntCast (QuinticAlgebra R a b) := ⟨fun n => ⟨n, 0, 0, 0, 0⟩⟩

@[simp] theorem c0_zero [Zero R] : (0 : QuinticAlgebra R a b).c0 = 0 := rfl
@[simp] theorem c0_one [Zero R] [One R] : (1 : QuinticAlgebra R a b).c0 = 1 := rfl
@[simp] theorem c0_add [Add R] (x y : QuinticAlgebra R a b) :
    (x+y).c0 = x.c0+y.c0 := rfl
@[simp] theorem c0_neg [Neg R] (x : QuinticAlgebra R a b) : (-x).c0 = -x.c0 := rfl
@[simp] theorem c0_mul [Mul R] [Add R] (x y : QuinticAlgebra R a b) :
    (x*y).c0 = x.c0*y.c0 + a*(x.c1*y.c4 + x.c2*y.c3 + x.c3*y.c2 + x.c4*y.c1) := rfl
@[simp] theorem c0_smul {S : Type*} [SMul S R] (n : S) (x : QuinticAlgebra R a b) :
    (n • x).c0 = n • x.c0 := rfl
@[simp] theorem c0_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : QuinticAlgebra R a b).c0 = n := rfl
@[simp] theorem c0_intCast [IntCast R] [Zero R] (n : ℤ) :
    (n : QuinticAlgebra R a b).c0 = n := rfl

@[simp] theorem c1_zero [Zero R] : (0 : QuinticAlgebra R a b).c1 = 0 := rfl
@[simp] theorem c1_one [Zero R] [One R] : (1 : QuinticAlgebra R a b).c1 = 0 := rfl
@[simp] theorem c1_add [Add R] (x y : QuinticAlgebra R a b) :
    (x+y).c1 = x.c1+y.c1 := rfl
@[simp] theorem c1_neg [Neg R] (x : QuinticAlgebra R a b) : (-x).c1 = -x.c1 := rfl
@[simp] theorem c1_mul [Mul R] [Add R] (x y : QuinticAlgebra R a b) :
    (x*y).c1 = x.c0*y.c1 + x.c1*y.c0 + a*(x.c2*y.c4 + x.c3*y.c3 + x.c4*y.c2) + b*(x.c1*y.c4 + x.c2*y.c3 + x.c3*y.c2 + x.c4*y.c1) := rfl
@[simp] theorem c1_smul {S : Type*} [SMul S R] (n : S) (x : QuinticAlgebra R a b) :
    (n • x).c1 = n • x.c1 := rfl
@[simp] theorem c1_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : QuinticAlgebra R a b).c1 = 0 := rfl
@[simp] theorem c1_intCast [IntCast R] [Zero R] (n : ℤ) :
    (n : QuinticAlgebra R a b).c1 = 0 := rfl

@[simp] theorem c2_zero [Zero R] : (0 : QuinticAlgebra R a b).c2 = 0 := rfl
@[simp] theorem c2_one [Zero R] [One R] : (1 : QuinticAlgebra R a b).c2 = 0 := rfl
@[simp] theorem c2_add [Add R] (x y : QuinticAlgebra R a b) :
    (x+y).c2 = x.c2+y.c2 := rfl
@[simp] theorem c2_neg [Neg R] (x : QuinticAlgebra R a b) : (-x).c2 = -x.c2 := rfl
@[simp] theorem c2_mul [Mul R] [Add R] (x y : QuinticAlgebra R a b) :
    (x*y).c2 = x.c0*y.c2 + x.c1*y.c1 + x.c2*y.c0 + a*(x.c3*y.c4 + x.c4*y.c3) + b*(x.c2*y.c4 + x.c3*y.c3 + x.c4*y.c2) := rfl
@[simp] theorem c2_smul {S : Type*} [SMul S R] (n : S) (x : QuinticAlgebra R a b) :
    (n • x).c2 = n • x.c2 := rfl
@[simp] theorem c2_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : QuinticAlgebra R a b).c2 = 0 := rfl
@[simp] theorem c2_intCast [IntCast R] [Zero R] (n : ℤ) :
    (n : QuinticAlgebra R a b).c2 = 0 := rfl

@[simp] theorem c3_zero [Zero R] : (0 : QuinticAlgebra R a b).c3 = 0 := rfl
@[simp] theorem c3_one [Zero R] [One R] : (1 : QuinticAlgebra R a b).c3 = 0 := rfl
@[simp] theorem c3_add [Add R] (x y : QuinticAlgebra R a b) :
    (x+y).c3 = x.c3+y.c3 := rfl
@[simp] theorem c3_neg [Neg R] (x : QuinticAlgebra R a b) : (-x).c3 = -x.c3 := rfl
@[simp] theorem c3_mul [Mul R] [Add R] (x y : QuinticAlgebra R a b) :
    (x*y).c3 = x.c0*y.c3 + x.c1*y.c2 + x.c2*y.c1 + x.c3*y.c0 + a*(x.c4*y.c4) + b*(x.c3*y.c4 + x.c4*y.c3) := rfl
@[simp] theorem c3_smul {S : Type*} [SMul S R] (n : S) (x : QuinticAlgebra R a b) :
    (n • x).c3 = n • x.c3 := rfl
@[simp] theorem c3_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : QuinticAlgebra R a b).c3 = 0 := rfl
@[simp] theorem c3_intCast [IntCast R] [Zero R] (n : ℤ) :
    (n : QuinticAlgebra R a b).c3 = 0 := rfl

@[simp] theorem c4_zero [Zero R] : (0 : QuinticAlgebra R a b).c4 = 0 := rfl
@[simp] theorem c4_one [Zero R] [One R] : (1 : QuinticAlgebra R a b).c4 = 0 := rfl
@[simp] theorem c4_add [Add R] (x y : QuinticAlgebra R a b) :
    (x+y).c4 = x.c4+y.c4 := rfl
@[simp] theorem c4_neg [Neg R] (x : QuinticAlgebra R a b) : (-x).c4 = -x.c4 := rfl
@[simp] theorem c4_mul [Mul R] [Add R] (x y : QuinticAlgebra R a b) :
    (x*y).c4 = x.c0*y.c4 + x.c1*y.c3 + x.c2*y.c2 + x.c3*y.c1 + x.c4*y.c0 + b*(x.c4*y.c4) := rfl
@[simp] theorem c4_smul {S : Type*} [SMul S R] (n : S) (x : QuinticAlgebra R a b) :
    (n • x).c4 = n • x.c4 := rfl
@[simp] theorem c4_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : QuinticAlgebra R a b).c4 = 0 := rfl
@[simp] theorem c4_intCast [IntCast R] [Zero R] (n : ℤ) :
    (n : QuinticAlgebra R a b).c4 = 0 := rfl

instance [CommRing R] : CommRing (QuinticAlgebra R a b) where
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

end QuinticAlgebra
end MagicSquares.Certificates
