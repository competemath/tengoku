import Tengoku.Seed.Algebra.TrivSqZeroExt.Basic
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Basic
import Tengoku.Seed.RingTheory.Artinian.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A concrete algebra model for the live-path lollipop

The algebra is a triangular five-coordinate model with vertex-one corner
the dual numbers, vertex-two corner `K`, and a two-dimensional arrow corner
which is regular on the right over the dual numbers.  Its displayed
generators satisfy `x² = 0` and `a*x = u ≠ 0`.

This file does not yet assert a universal bound-path-algebra presentation or
identify the Jacobson radical and primitive idempotents.
-/

noncomputable section

open scoped RightActions

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.B1

universe u

variable (K : Type u) [Field K]

/-- The vertex-one loop corner `K[ε]/(ε²)`.-/
abbrev LoopAlgebra := TrivSqZeroExt K K

/-- The diagonal subalgebra: dual numbers at vertex one and `K` at vertex two.-/
abbrev BaseAlgebra := LoopAlgebra K × K

/-- The arrow corner, with basis `a, a*x`, identified with the regular right
module over the loop corner.-/
abbrev ArrowCorner := LoopAlgebra K

/-- Left multiplication on the arrow corner only sees vertex two.-/
def leftArrowCharacter : BaseAlgebra K →+* K :=
  RingHom.snd (LoopAlgebra K) K

instance : Module (BaseAlgebra K) (ArrowCorner K) :=
  Module.compHom (ArrowCorner K) (leftArrowCharacter K)

/-- Right multiplication on the arrow corner sees the dual-number corner at
vertex one.-/
def rightArrowCharacter : (BaseAlgebra K)ᵐᵒᵖ →+* LoopAlgebra K :=
  (RingHom.fst (LoopAlgebra K) K).fromOpposite fun _ _ => Commute.all _ _

instance : Module (BaseAlgebra K)ᵐᵒᵖ (ArrowCorner K) :=
  Module.compHom (ArrowCorner K) (rightArrowCharacter K)

/--
@isnad1 id=eq.0h3v.s8.9741b864d584 from=translated src=- shape=4052ee62 vocab=c64ffedf
-/
@[simp] theorem left_smul_fst (r : BaseAlgebra K) (m : ArrowCorner K) :
    TrivSqZeroExt.fst (r • m) = r.2 * TrivSqZeroExt.fst m := rfl

/--
@isnad1 id=eq.0h3v.s8.463a39295bbf from=translated src=- shape=4052ee62 vocab=9ba6d2e9
-/
@[simp] theorem left_smul_snd (r : BaseAlgebra K) (m : ArrowCorner K) :
    TrivSqZeroExt.snd (r • m) = r.2 * TrivSqZeroExt.snd m := rfl

/--
@isnad1 id=eq.0h3v.s8.2f76d690555a from=translated src=- shape=cdeaa298 vocab=869cf039
-/
@[simp] theorem right_smul_fst (r : (BaseAlgebra K)ᵐᵒᵖ) (m : ArrowCorner K) :
    TrivSqZeroExt.fst (r • m) =
      TrivSqZeroExt.fst r.unop.1 * TrivSqZeroExt.fst m := rfl

/--
@isnad1 id=eq.0h3v.s8.62218a615ad5 from=translated src=- shape=8d43c143 vocab=534105f3
-/
@[simp] theorem right_smul_snd (r : (BaseAlgebra K)ᵐᵒᵖ) (m : ArrowCorner K) :
    TrivSqZeroExt.snd (r • m) =
      TrivSqZeroExt.fst r.unop.1 * TrivSqZeroExt.snd m +
        TrivSqZeroExt.snd r.unop.1 * TrivSqZeroExt.fst m := rfl

instance : SMulCommClass (BaseAlgebra K) (BaseAlgebra K)ᵐᵒᵖ (ArrowCorner K) where
  smul_comm r s m := by
    ext <;> simp only [left_smul_fst, left_smul_snd, right_smul_fst,
      right_smul_snd] <;> ring

instance : IsScalarTower K (BaseAlgebra K) (ArrowCorner K) where
  smul_assoc c r m := by
    ext <;> simp only [left_smul_fst, left_smul_snd, Prod.smul_snd,
      TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, smul_eq_mul] <;> ring

instance : IsScalarTower K (BaseAlgebra K)ᵐᵒᵖ (ArrowCorner K) where
  smul_assoc c r m := by
    ext <;> simp only [right_smul_fst, right_smul_snd,
      MulOpposite.unop_smul, Prod.smul_fst, TrivSqZeroExt.fst_smul,
      TrivSqZeroExt.snd_smul, smul_eq_mul] <;> ring

/-- The five-dimensional triangular coordinate algebra.-/
abbrev B1Model := TrivSqZeroExt (BaseAlgebra K) (ArrowCorner K)

/-- Vertex idempotent at the loop vertex.-/
def e1 : B1Model K := TrivSqZeroExt.inl (1, 0)

/-- Vertex idempotent at the terminal vertex.-/
def e2 : B1Model K := TrivSqZeroExt.inl (0, 1)

/-- The square-zero loop.-/
def x : B1Model K :=
  TrivSqZeroExt.inl (TrivSqZeroExt.inr 1, 0)

/-- The arrow from vertex one to vertex two.-/
def a : B1Model K := TrivSqZeroExt.inr 1

/-- The live length-two coordinate, algebraically `a * x`.-/
def u : B1Model K :=
  TrivSqZeroExt.inr (TrivSqZeroExt.inr 1)

/--
@isnad1 id=eq.0h1v.s7.c16db2a7cdeb from=translated src=- shape=e94b03c3 vocab=0902ee4e
-/
@[simp] theorem e1_add_e2 : e1 K + e2 K = 1 := by
  ext <;> simp [e1, e2]

/--
@isnad1 id=eq.0h1v.s9.5f513def16f0 from=translated src=- shape=4156e7b5 vocab=5af85d65
-/
@[simp] theorem e1_sq : e1 K * e1 K = e1 K := by
  ext <;> simp [e1]

/--
@isnad1 id=eq.0h1v.s9.5a5b0b926810 from=translated src=- shape=4156e7b5 vocab=1a5a8bf0
-/
@[simp] theorem e2_sq : e2 K * e2 K = e2 K := by
  ext <;> simp [e2]

/--
@isnad1 id=eq.0h1v.s9.61e4c742b3d6 from=translated src=- shape=e94b03c3 vocab=4e5d8545
-/
@[simp] theorem e1_mul_e2 : e1 K * e2 K = 0 := by
  ext <;> simp [e1, e2]

/--
@isnad1 id=eq.0h1v.s9.9956e97dad44 from=translated src=- shape=e94b03c3 vocab=4e5d8545
-/
@[simp] theorem e2_mul_e1 : e2 K * e1 K = 0 := by
  ext <;> simp [e1, e2]

/--
@isnad1 id=eq.0h1v.s9.5b2336fde4db from=translated src=- shape=b2048345 vocab=b9b3282f
-/
@[simp] theorem e1_mul_x : e1 K * x K = x K := by
  ext <;> simp [e1, x]

/--
@isnad1 id=eq.0h1v.s9.75a837d46dae from=translated src=- shape=4156e7b5 vocab=b9b3282f
-/
@[simp] theorem x_mul_e1 : x K * e1 K = x K := by
  ext <;> simp [e1, x]

/--
@isnad1 id=eq.0h1v.s9.0c9b1102b0c1 from=translated src=- shape=e94b03c3 vocab=2a34368c
-/
@[simp] theorem e2_mul_x : e2 K * x K = 0 := by
  ext <;> simp [e2, x]

/--
@isnad1 id=eq.0h1v.s9.edd0d63e091a from=translated src=- shape=e94b03c3 vocab=2a34368c
-/
@[simp] theorem x_mul_e2 : x K * e2 K = 0 := by
  ext <;> simp [e2, x]

/--
@isnad1 id=eq.0h1v.s9.7ed42ab64c79 from=translated src=- shape=b9e51560 vocab=dcde87fc
-/
@[simp] theorem x_sq : x K * x K = 0 := by
  ext <;> simp [x]

/--
@isnad1 id=eq.0h1v.s9.3691aab89a35 from=translated src=- shape=b2048345 vocab=ddc23c08
-/
@[simp] theorem e2_mul_a : e2 K * a K = a K := by
  ext <;> simp [e2, a]

/--
@isnad1 id=eq.0h1v.s9.1fe521209e85 from=translated src=- shape=4156e7b5 vocab=f355a096
-/
@[simp] theorem a_mul_e1 : a K * e1 K = a K := by
  ext <;> simp [e1, a]

/--
@isnad1 id=eq.0h1v.s9.d802d3cd557c from=translated src=- shape=b2048345 vocab=5c08313c
-/
@[simp] theorem a_mul_x : a K * x K = u K := by
  ext <;> simp [a, x, u]

/--
@isnad1 id=ne.0h1v.s6.7dcb40e1092d from=translated src=- shape=bbb5e9b9 vocab=de4e1e67
-/
theorem u_ne_zero : u K ≠ 0 := by
  intro h
  have hcoord := congrArg (fun z : B1Model K => z.2.2) h
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

/--
@isnad1 id=ne.0h1v.s9.3b7ec952b287 from=translated src=- shape=e94b03c3 vocab=d75b56d5
-/
theorem a_mul_x_ne_zero : a K * x K ≠ 0 := by
  rw [a_mul_x]
  exact u_ne_zero K

/--
@isnad1 id=eq.0h1v.s9.a023fd861442 from=translated src=- shape=e94b03c3 vocab=d0cfb01d
-/
@[simp] theorem u_mul_x : u K * x K = 0 := by
  ext <;> simp [u, x]

/--
@isnad1 id=eq.0h1v.s9.865c22a55d02 from=translated src=- shape=b2048345 vocab=cd9ed8e9
-/
@[simp] theorem e2_mul_u : e2 K * u K = u K := by
  ext <;> simp [e2, u]

/--
@isnad1 id=eq.0h1v.s9.3d0e8d2fc365 from=translated src=- shape=4156e7b5 vocab=6917a459
-/
@[simp] theorem u_mul_e1 : u K * e1 K = u K := by
  ext <;> simp [e1, u]

/--
@isnad1 id=eq.0h1v.s9.35dfc5f858b2 from=translated src=- shape=e94b03c3 vocab=f355a096
-/
@[simp] theorem e1_mul_a : e1 K * a K = 0 := by
  ext <;> simp [e1, a]

/--
@isnad1 id=eq.0h1v.s9.9a9fc8e8ea55 from=translated src=- shape=e94b03c3 vocab=ddc23c08
-/
@[simp] theorem a_mul_e2 : a K * e2 K = 0 := by
  ext <;> simp [e2, a]

/--
@isnad1 id=eq.0h1v.s9.461953bea0df from=translated src=- shape=e94b03c3 vocab=6917a459
-/
@[simp] theorem e1_mul_u : e1 K * u K = 0 := by
  ext <;> simp [e1, u]

/--
@isnad1 id=eq.0h1v.s9.ed5cb94041ec from=translated src=- shape=e94b03c3 vocab=cd9ed8e9
-/
@[simp] theorem u_mul_e2 : u K * e2 K = 0 := by
  ext <;> simp [e2, u]

/--
@isnad1 id=finitedi.0h1v.s8.5ee20ab45d72 from=translated src=- shape=84bfdc15 vocab=965766e6
-/
noncomputable instance finiteDimensional :
    FiniteDimensional K (B1Model K) := by
  change Module.Finite K (((K × K) × K) × (K × K))
  infer_instance

/--
@isnad1 id=isnoethe.0h1v.s6.1b680d81de36 from=translated src=- shape=1666ae32 vocab=d5ac79e6
-/
noncomputable instance isNoetherianRing :
    IsNoetherianRing (B1Model K) :=
  IsNoetherianRing.of_finite K (B1Model K)

/--
@isnad1 id=isartini.0h1v.s6.fec78fe67893 from=translated src=- shape=1666ae32 vocab=47582f01
-/
noncomputable instance isArtinianRing :
    IsArtinianRing (B1Model K) :=
  IsArtinianRing.of_finite K (B1Model K)

/--
@isnad1 id=eq.0h1v.s8.6331d8343b13 from=translated src=- shape=a4033e76 vocab=a70763aa
-/
theorem finrank_eq_five : Module.finrank K (B1Model K) = 5 := by
  change Module.finrank K (((K × K) × K) × (K × K)) = 5
  simp

end QuotientSubmoduleEquidistribution.LollipopConcrete.B1
