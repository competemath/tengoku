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

/--
@isnad1 id=eq.0h3v.s5.ea5c12af6424 from=translated src=- shape=ee66e77d vocab=2fd15371
-/
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

/--
@isnad1 id=eq.0h3v.s5.161ee3f6dca2 from=translated src=- shape=122f25fd vocab=5962975a
-/
@[simp] theorem c0_zero [Zero R] : (0 : QuinticAlgebra R a b).c0 = 0 := rfl
/--
@isnad1 id=eq.0h3v.s5.2d48788762d6 from=translated src=- shape=ece7bb16 vocab=9b15219f
-/
@[simp] theorem c0_one [Zero R] [One R] : (1 : QuinticAlgebra R a b).c0 = 1 := rfl
/--
@isnad1 id=eq.0h5v.s6.998ddfc8a2c5 from=translated src=- shape=6d94a147 vocab=996dffa8
-/
@[simp] theorem c0_add [Add R] (x y : QuinticAlgebra R a b) :
    (x+y).c0 = x.c0+y.c0 := rfl
/--
@isnad1 id=eq.0h4v.s5.b57aac6127ac from=translated src=- shape=345d0dc8 vocab=e6646c21
-/
@[simp] theorem c0_neg [Neg R] (x : QuinticAlgebra R a b) : (-x).c0 = -x.c0 := rfl
/--
@isnad1 id=eq.0h5v.s7.3ca34733cad8 from=translated src=- shape=7fb83a89 vocab=77f61a8d
-/
@[simp] theorem c0_mul [Mul R] [Add R] (x y : QuinticAlgebra R a b) :
    (x*y).c0 = x.c0*y.c0 + a*(x.c1*y.c4 + x.c2*y.c3 + x.c3*y.c2 + x.c4*y.c1) := rfl
/--
@isnad1 id=eq.0h6v.s5.c52bee67a1ec from=translated src=- shape=69763d64 vocab=7bcc8ff0
-/
@[simp] theorem c0_smul {S : Type*} [SMul S R] (n : S) (x : QuinticAlgebra R a b) :
    (n • x).c0 = n • x.c0 := rfl
/--
@isnad1 id=eq.0h4v.s5.01923649e6f1 from=translated src=- shape=170195bd vocab=65769826
-/
@[simp] theorem c0_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : QuinticAlgebra R a b).c0 = n := rfl
/--
@isnad1 id=eq.0h4v.s5.de72005cc86a from=translated src=- shape=170195bd vocab=b032db54
-/
@[simp] theorem c0_intCast [IntCast R] [Zero R] (n : ℤ) :
    (n : QuinticAlgebra R a b).c0 = n := rfl

/--
@isnad1 id=eq.0h3v.s5.7543fcfd849c from=translated src=- shape=122f25fd vocab=fcc815f3
-/
@[simp] theorem c1_zero [Zero R] : (0 : QuinticAlgebra R a b).c1 = 0 := rfl
/--
@isnad1 id=eq.0h3v.s5.ca5e9de8641c from=translated src=- shape=ece7bb16 vocab=65277440
-/
@[simp] theorem c1_one [Zero R] [One R] : (1 : QuinticAlgebra R a b).c1 = 0 := rfl
/--
@isnad1 id=eq.0h5v.s6.8f1ff96d2874 from=translated src=- shape=6d94a147 vocab=a493b96d
-/
@[simp] theorem c1_add [Add R] (x y : QuinticAlgebra R a b) :
    (x+y).c1 = x.c1+y.c1 := rfl
/--
@isnad1 id=eq.0h4v.s5.671e2c7e3289 from=translated src=- shape=345d0dc8 vocab=789d7f98
-/
@[simp] theorem c1_neg [Neg R] (x : QuinticAlgebra R a b) : (-x).c1 = -x.c1 := rfl
/--
@isnad1 id=eq.0h5v.s8.19483e9fc441 from=translated src=- shape=fa94cead vocab=77f61a8d
-/
@[simp] theorem c1_mul [Mul R] [Add R] (x y : QuinticAlgebra R a b) :
    (x*y).c1 = x.c0*y.c1 + x.c1*y.c0 + a*(x.c2*y.c4 + x.c3*y.c3 + x.c4*y.c2) + b*(x.c1*y.c4 + x.c2*y.c3 + x.c3*y.c2 + x.c4*y.c1) := rfl
/--
@isnad1 id=eq.0h6v.s5.7963adad3905 from=translated src=- shape=69763d64 vocab=6e300f2b
-/
@[simp] theorem c1_smul {S : Type*} [SMul S R] (n : S) (x : QuinticAlgebra R a b) :
    (n • x).c1 = n • x.c1 := rfl
/--
@isnad1 id=eq.0h4v.s5.6cbf05597476 from=translated src=- shape=37b86746 vocab=d8a9bb90
-/
@[simp] theorem c1_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : QuinticAlgebra R a b).c1 = 0 := rfl
/--
@isnad1 id=eq.0h4v.s5.ba56b83a3bd7 from=translated src=- shape=37b86746 vocab=d340ac7f
-/
@[simp] theorem c1_intCast [IntCast R] [Zero R] (n : ℤ) :
    (n : QuinticAlgebra R a b).c1 = 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.0c5233f2efe5 from=translated src=- shape=122f25fd vocab=d2245bc5
-/
@[simp] theorem c2_zero [Zero R] : (0 : QuinticAlgebra R a b).c2 = 0 := rfl
/--
@isnad1 id=eq.0h3v.s5.4e9afbe85bc3 from=translated src=- shape=ece7bb16 vocab=c6fc5252
-/
@[simp] theorem c2_one [Zero R] [One R] : (1 : QuinticAlgebra R a b).c2 = 0 := rfl
/--
@isnad1 id=eq.0h5v.s6.e813694a184d from=translated src=- shape=6d94a147 vocab=23790dd1
-/
@[simp] theorem c2_add [Add R] (x y : QuinticAlgebra R a b) :
    (x+y).c2 = x.c2+y.c2 := rfl
/--
@isnad1 id=eq.0h4v.s5.35115e3478ec from=translated src=- shape=345d0dc8 vocab=30c5fb2d
-/
@[simp] theorem c2_neg [Neg R] (x : QuinticAlgebra R a b) : (-x).c2 = -x.c2 := rfl
/--
@isnad1 id=eq.0h5v.s7.fb68b6992181 from=translated src=- shape=90465897 vocab=77f61a8d
-/
@[simp] theorem c2_mul [Mul R] [Add R] (x y : QuinticAlgebra R a b) :
    (x*y).c2 = x.c0*y.c2 + x.c1*y.c1 + x.c2*y.c0 + a*(x.c3*y.c4 + x.c4*y.c3) + b*(x.c2*y.c4 + x.c3*y.c3 + x.c4*y.c2) := rfl
/--
@isnad1 id=eq.0h6v.s5.d6318dad3353 from=translated src=- shape=69763d64 vocab=f29d78de
-/
@[simp] theorem c2_smul {S : Type*} [SMul S R] (n : S) (x : QuinticAlgebra R a b) :
    (n • x).c2 = n • x.c2 := rfl
/--
@isnad1 id=eq.0h4v.s5.ce43aec4c64d from=translated src=- shape=37b86746 vocab=7a0e5ec6
-/
@[simp] theorem c2_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : QuinticAlgebra R a b).c2 = 0 := rfl
/--
@isnad1 id=eq.0h4v.s5.f6fd875a0fb5 from=translated src=- shape=37b86746 vocab=e81f74ed
-/
@[simp] theorem c2_intCast [IntCast R] [Zero R] (n : ℤ) :
    (n : QuinticAlgebra R a b).c2 = 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.ef5e4f2f8beb from=translated src=- shape=122f25fd vocab=7fc5c539
-/
@[simp] theorem c3_zero [Zero R] : (0 : QuinticAlgebra R a b).c3 = 0 := rfl
/--
@isnad1 id=eq.0h3v.s5.1abf12e951ae from=translated src=- shape=ece7bb16 vocab=56e2705e
-/
@[simp] theorem c3_one [Zero R] [One R] : (1 : QuinticAlgebra R a b).c3 = 0 := rfl
/--
@isnad1 id=eq.0h5v.s6.42f926c1b4e7 from=translated src=- shape=6d94a147 vocab=738e606b
-/
@[simp] theorem c3_add [Add R] (x y : QuinticAlgebra R a b) :
    (x+y).c3 = x.c3+y.c3 := rfl
/--
@isnad1 id=eq.0h4v.s5.fad2402be72c from=translated src=- shape=345d0dc8 vocab=86bb2c27
-/
@[simp] theorem c3_neg [Neg R] (x : QuinticAlgebra R a b) : (-x).c3 = -x.c3 := rfl
/--
@isnad1 id=eq.0h5v.s7.5152e2dab05d from=translated src=- shape=f4679311 vocab=77f61a8d
-/
@[simp] theorem c3_mul [Mul R] [Add R] (x y : QuinticAlgebra R a b) :
    (x*y).c3 = x.c0*y.c3 + x.c1*y.c2 + x.c2*y.c1 + x.c3*y.c0 + a*(x.c4*y.c4) + b*(x.c3*y.c4 + x.c4*y.c3) := rfl
/--
@isnad1 id=eq.0h6v.s5.1e85f08fda24 from=translated src=- shape=69763d64 vocab=5d21f13d
-/
@[simp] theorem c3_smul {S : Type*} [SMul S R] (n : S) (x : QuinticAlgebra R a b) :
    (n • x).c3 = n • x.c3 := rfl
/--
@isnad1 id=eq.0h4v.s5.84b423ab6adb from=translated src=- shape=37b86746 vocab=75474397
-/
@[simp] theorem c3_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : QuinticAlgebra R a b).c3 = 0 := rfl
/--
@isnad1 id=eq.0h4v.s5.5c5158fbaab5 from=translated src=- shape=37b86746 vocab=338c1ab9
-/
@[simp] theorem c3_intCast [IntCast R] [Zero R] (n : ℤ) :
    (n : QuinticAlgebra R a b).c3 = 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.e3f0c127a888 from=translated src=- shape=122f25fd vocab=7dc0381f
-/
@[simp] theorem c4_zero [Zero R] : (0 : QuinticAlgebra R a b).c4 = 0 := rfl
/--
@isnad1 id=eq.0h3v.s5.4f826d625c49 from=translated src=- shape=ece7bb16 vocab=520c8e35
-/
@[simp] theorem c4_one [Zero R] [One R] : (1 : QuinticAlgebra R a b).c4 = 0 := rfl
/--
@isnad1 id=eq.0h5v.s6.a420903cdc3b from=translated src=- shape=6d94a147 vocab=135be4b5
-/
@[simp] theorem c4_add [Add R] (x y : QuinticAlgebra R a b) :
    (x+y).c4 = x.c4+y.c4 := rfl
/--
@isnad1 id=eq.0h4v.s5.c4561bec6c3d from=translated src=- shape=345d0dc8 vocab=becc6c76
-/
@[simp] theorem c4_neg [Neg R] (x : QuinticAlgebra R a b) : (-x).c4 = -x.c4 := rfl
/--
@isnad1 id=eq.0h5v.s7.18a09b496cc4 from=translated src=- shape=bb8e1c09 vocab=77f61a8d
-/
@[simp] theorem c4_mul [Mul R] [Add R] (x y : QuinticAlgebra R a b) :
    (x*y).c4 = x.c0*y.c4 + x.c1*y.c3 + x.c2*y.c2 + x.c3*y.c1 + x.c4*y.c0 + b*(x.c4*y.c4) := rfl
/--
@isnad1 id=eq.0h6v.s5.60e66f4ac231 from=translated src=- shape=69763d64 vocab=435079e5
-/
@[simp] theorem c4_smul {S : Type*} [SMul S R] (n : S) (x : QuinticAlgebra R a b) :
    (n • x).c4 = n • x.c4 := rfl
/--
@isnad1 id=eq.0h4v.s5.803ced6c2699 from=translated src=- shape=37b86746 vocab=db3dda3f
-/
@[simp] theorem c4_natCast [NatCast R] [Zero R] (n : ℕ) :
    (n : QuinticAlgebra R a b).c4 = 0 := rfl
/--
@isnad1 id=eq.0h4v.s5.e425936de2a3 from=translated src=- shape=37b86746 vocab=e0cba0c9
-/
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
