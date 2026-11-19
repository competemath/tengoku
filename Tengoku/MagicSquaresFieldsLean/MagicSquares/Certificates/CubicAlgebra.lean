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

/--
@isnad1 id=eq.0h3v.s5.786305c01278 from=translated src=- shape=ee66e77d vocab=f1d7b951
-/
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

/--
@isnad1 id=eq.0h3v.s5.4d12832ff219 from=translated src=- shape=122f25fd vocab=a8108d8f
-/
@[simp] theorem c0_zero [Zero R] : (0 : CubicAlgebra R a b).c0 = 0 := rfl
/--
@isnad1 id=eq.0h3v.s5.31af0d7d39b4 from=translated src=- shape=ece7bb16 vocab=67ed120e
-/
@[simp] theorem c0_one [Zero R] [One R] : (1 : CubicAlgebra R a b).c0 = 1 := rfl
/--
@isnad1 id=eq.0h5v.s6.4b6220012510 from=translated src=- shape=6d94a147 vocab=823c7121
-/
@[simp] theorem c0_add [Add R] (x y : CubicAlgebra R a b) :
    (x+y).c0 = x.c0+y.c0 := rfl
/--
@isnad1 id=eq.0h4v.s5.c4e8e1e5cbb4 from=translated src=- shape=345d0dc8 vocab=6b840f02
-/
@[simp] theorem c0_neg [Neg R] (x : CubicAlgebra R a b) : (-x).c0 = -x.c0 := rfl
/--
@isnad1 id=eq.0h5v.s6.44a29758f98d from=translated src=- shape=faaf2251 vocab=827d071b
-/
@[simp] theorem c0_mul [Mul R] [Add R] (x y : CubicAlgebra R a b) :
    (x*y).c0 = x.c0*y.c0 + a*(x.c1*y.c2 + x.c2*y.c1) := rfl
/--
@isnad1 id=eq.0h6v.s5.6535c6093107 from=translated src=- shape=69763d64 vocab=90a3cf4d
-/
@[simp] theorem c0_smul {S : Type*} [SMul S R] (n : S) (x : CubicAlgebra R a b) :
    (n • x).c0 = n • x.c0 := rfl
/--
@isnad1 id=eq.0h4v.s5.cf4679d3f1f6 from=translated src=- shape=170195bd vocab=3ac77596
-/
@[simp] theorem c0_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : CubicAlgebra R a b).c0 = n := rfl
/--
@isnad1 id=eq.0h4v.s5.b1aa86eb8e4a from=translated src=- shape=170195bd vocab=b9c5220c
-/
@[simp] theorem c0_intCast [IntCast R] [Zero R] (n : ℤ) :
    (n : CubicAlgebra R a b).c0 = n := rfl

/--
@isnad1 id=eq.0h3v.s5.2fbf6cd05d74 from=translated src=- shape=122f25fd vocab=bae3a47f
-/
@[simp] theorem c1_zero [Zero R] : (0 : CubicAlgebra R a b).c1 = 0 := rfl
/--
@isnad1 id=eq.0h3v.s5.0a73be9d785e from=translated src=- shape=ece7bb16 vocab=798ed9b4
-/
@[simp] theorem c1_one [Zero R] [One R] : (1 : CubicAlgebra R a b).c1 = 0 := rfl
/--
@isnad1 id=eq.0h5v.s6.9a0c38e3d0fd from=translated src=- shape=6d94a147 vocab=dd508cc1
-/
@[simp] theorem c1_add [Add R] (x y : CubicAlgebra R a b) :
    (x+y).c1 = x.c1+y.c1 := rfl
/--
@isnad1 id=eq.0h4v.s5.69f176fc013c from=translated src=- shape=345d0dc8 vocab=46e70425
-/
@[simp] theorem c1_neg [Neg R] (x : CubicAlgebra R a b) : (-x).c1 = -x.c1 := rfl
/--
@isnad1 id=eq.0h5v.s7.6b95791a6b85 from=translated src=- shape=adaea2b2 vocab=827d071b
-/
@[simp] theorem c1_mul [Mul R] [Add R] (x y : CubicAlgebra R a b) :
    (x*y).c1 = x.c0*y.c1 + x.c1*y.c0 + b*(x.c1*y.c2 + x.c2*y.c1) + a*x.c2*y.c2 := rfl
/--
@isnad1 id=eq.0h6v.s5.371aabbbe620 from=translated src=- shape=69763d64 vocab=7ffe0a0a
-/
@[simp] theorem c1_smul {S : Type*} [SMul S R] (n : S) (x : CubicAlgebra R a b) :
    (n • x).c1 = n • x.c1 := rfl
/--
@isnad1 id=eq.0h4v.s5.063431fa43d6 from=translated src=- shape=37b86746 vocab=f683ebf5
-/
@[simp] theorem c1_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : CubicAlgebra R a b).c1 = 0 := rfl
/--
@isnad1 id=eq.0h4v.s5.e14280af793b from=translated src=- shape=37b86746 vocab=269ed4c0
-/
@[simp] theorem c1_intCast [IntCast R] [Zero R] (n : ℤ) :
    (n : CubicAlgebra R a b).c1 = 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.16af61993d78 from=translated src=- shape=122f25fd vocab=1bfc6068
-/
@[simp] theorem c2_zero [Zero R] : (0 : CubicAlgebra R a b).c2 = 0 := rfl
/--
@isnad1 id=eq.0h3v.s5.a351ebdb6237 from=translated src=- shape=ece7bb16 vocab=06f23ea3
-/
@[simp] theorem c2_one [Zero R] [One R] : (1 : CubicAlgebra R a b).c2 = 0 := rfl
/--
@isnad1 id=eq.0h5v.s6.b320d5309c85 from=translated src=- shape=6d94a147 vocab=ffd86f3f
-/
@[simp] theorem c2_add [Add R] (x y : CubicAlgebra R a b) :
    (x+y).c2 = x.c2+y.c2 := rfl
/--
@isnad1 id=eq.0h4v.s5.1cdbf3827054 from=translated src=- shape=345d0dc8 vocab=72e83395
-/
@[simp] theorem c2_neg [Neg R] (x : CubicAlgebra R a b) : (-x).c2 = -x.c2 := rfl
/--
@isnad1 id=eq.0h5v.s7.b64c27ed7e91 from=translated src=- shape=c37b58c2 vocab=827d071b
-/
@[simp] theorem c2_mul [Mul R] [Add R] (x y : CubicAlgebra R a b) :
    (x*y).c2 = x.c0*y.c2 + x.c1*y.c1 + x.c2*y.c0 + b*x.c2*y.c2 := rfl
/--
@isnad1 id=eq.0h6v.s5.3558d5e68a42 from=translated src=- shape=69763d64 vocab=a30770d6
-/
@[simp] theorem c2_smul {S : Type*} [SMul S R] (n : S) (x : CubicAlgebra R a b) :
    (n • x).c2 = n • x.c2 := rfl
/--
@isnad1 id=eq.0h4v.s5.96b966fd72a8 from=translated src=- shape=37b86746 vocab=b1ce2896
-/
@[simp] theorem c2_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : CubicAlgebra R a b).c2 = 0 := rfl
/--
@isnad1 id=eq.0h4v.s5.c075c98a4abd from=translated src=- shape=37b86746 vocab=c5c6fa71
-/
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
