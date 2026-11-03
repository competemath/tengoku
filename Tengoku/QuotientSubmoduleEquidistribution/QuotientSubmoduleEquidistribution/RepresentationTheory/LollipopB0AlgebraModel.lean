import Tengoku.Seed.Algebra.TrivSqZeroExt.Basic
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Basic
import Tengoku.Seed.RingTheory.Artinian.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A concrete square-zero model for the dead-path lollipop

This file isolates a concrete algebra model for the presentation layer
missing from the project foundation's free-quiver representation API.  Over a field `K`,
take the trivial square-zero extension of `K × K` by the bimodule with basis
`x, a` and supports

* `e₁ x = x = x e₁`,
* `e₂ a = a = a e₁`.

Thus all products of two off-diagonal generators vanish.  The coordinate
corners match the loop `1 → 1` and stem `1 → 2` of the intended lollipop.
This file proves the coordinate identities, but does not yet assert a
universal bound-path-algebra presentation, identify the Jacobson radical, or
prove primitivity of the vertex idempotents.
-/

open scoped RightActions

namespace QuotientSubmoduleEquidistribution.LollipopConcrete

variable (K : Type*) [Field K]

/-- The vertex subalgebra, with coordinate idempotents `(1, 0)` and `(0, 1)`.-/
abbrev VertexAlgebra := K × K

/-- The radical bimodule.  The two coordinates are the loop `x` and arrow `a`.-/
structure B0Radical where
  x : K
  a : K

omit [Field K] in
/--
@isnad1 id=eq.2h3v.s4.568492b6cb32 from=translated src=- shape=46590be3 vocab=6481333d
-/
@[ext] theorem B0Radical.ext {u v : B0Radical K} (hx : u.x = v.x) (ha : u.a = v.a) : u = v := by
  cases u
  cases v
  simp_all

/-- Coordinates transport the additive group structure to the radical.-/
def B0Radical.equivProd : B0Radical K ≃ K × K where
  toFun m := (m.x, m.a)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (B0Radical K) := (B0Radical.equivProd K).addCommGroup

/--
@isnad1 id=eq.0h1v.s5.aec4637bd0fa from=translated src=- shape=c6b7a0b8 vocab=98766bc4
-/
@[simp] theorem B0Radical.zero_x : (0 : B0Radical K).x = 0 := rfl

/--
@isnad1 id=eq.0h1v.s5.30bded5a73f1 from=translated src=- shape=c6b7a0b8 vocab=85dae0a3
-/
@[simp] theorem B0Radical.zero_a : (0 : B0Radical K).a = 0 := rfl

/-- The coordinate equivalence after transporting the additive group.-/
def B0Radical.addEquivProd : B0Radical K ≃+ K × K where
  __ := B0Radical.equivProd K
  map_add' _ _ := rfl

/-- The ordinary `K`-vector-space structure on the two radical coordinates.-/
instance : Module K (B0Radical K) := (B0Radical.addEquivProd K).module K

/--
@isnad1 id=eq.0h3v.s6.61fd1b91a5f3 from=translated src=- shape=0090f101 vocab=939e2255
-/
@[simp] theorem B0Radical.add_x (m n : B0Radical K) :
    (m + n).x = m.x + n.x := rfl

/--
@isnad1 id=eq.0h3v.s6.6107533ff226 from=translated src=- shape=0090f101 vocab=0a16196d
-/
@[simp] theorem B0Radical.add_a (m n : B0Radical K) :
    (m + n).a = m.a + n.a := rfl

/--
@isnad1 id=eq.0h3v.s7.9f70ea2366aa from=translated src=- shape=fcf209a7 vocab=7c999582
-/
@[simp] theorem B0Radical.smul_x (c : K) (m : B0Radical K) :
    (c • m).x = c * m.x := rfl

/--
@isnad1 id=eq.0h3v.s7.16037ed394c9 from=translated src=- shape=fcf209a7 vocab=38bb3986
-/
@[simp] theorem B0Radical.smul_a (c : K) (m : B0Radical K) :
    (c • m).a = c * m.a := rfl

/-- Left multiplication by the vertex algebra: `e₁` supports `x`, `e₂` supports `a`.-/
instance : Module (VertexAlgebra K) (B0Radical K) :=
  (B0Radical.addEquivProd K).module (VertexAlgebra K)

/-- Both radical generators end at vertex `1` on the right.-/
def rightVertexCharacter : (VertexAlgebra K)ᵐᵒᵖ →+* K :=
  (RingHom.fst K K).fromOpposite fun _ _ => Commute.all _ _

/-- The right action of the vertex algebra on each radical coordinate factors through vertex `1`.-/
instance : Module (VertexAlgebra K)ᵐᵒᵖ K := Module.compHom K (rightVertexCharacter K)

/-- Right multiplication by the vertex algebra on the radical.-/
instance : Module (VertexAlgebra K)ᵐᵒᵖ (B0Radical K) :=
  (B0Radical.addEquivProd K).module (VertexAlgebra K)ᵐᵒᵖ

/--
@isnad1 id=eq.0h3v.s7.53829226bd1a from=translated src=- shape=576081db vocab=87ab4e67
-/
@[simp] theorem B0Radical.left_smul_x (r : VertexAlgebra K) (m : B0Radical K) :
    (r • m).x = r.1 * m.x := rfl

/--
@isnad1 id=eq.0h3v.s7.6bb0af8d1218 from=translated src=- shape=576081db vocab=e2ca66c0
-/
@[simp] theorem B0Radical.left_smul_a (r : VertexAlgebra K) (m : B0Radical K) :
    (r • m).a = r.2 * m.a := rfl

/--
@isnad1 id=eq.0h3v.s7.4a2d2fa393e7 from=translated src=- shape=1a65aa61 vocab=fa597121
-/
@[simp] theorem B0Radical.right_smul_x (r : (VertexAlgebra K)ᵐᵒᵖ) (m : B0Radical K) :
    (r • m).x = r.unop.1 * m.x := rfl

/--
@isnad1 id=eq.0h3v.s7.49c941cdc20e from=translated src=- shape=1a65aa61 vocab=cbe5936e
-/
@[simp] theorem B0Radical.right_smul_a (r : (VertexAlgebra K)ᵐᵒᵖ) (m : B0Radical K) :
    (r • m).a = r.unop.1 * m.a := rfl

instance : IsScalarTower K (VertexAlgebra K) (B0Radical K) where
  smul_assoc c r m := by
    apply B0Radical.ext
    · simp
      ring
    · simp
      ring

instance : IsScalarTower K (VertexAlgebra K)ᵐᵒᵖ (B0Radical K) where
  smul_assoc c r m := by
    apply B0Radical.ext
    · simp
      ring
    · simp
      ring

instance : SMulCommClass (VertexAlgebra K) (VertexAlgebra K)ᵐᵒᵖ (B0Radical K) where
  smul_comm r s m := by
    apply B0Radical.ext
    · simp only [B0Radical.left_smul_x, B0Radical.right_smul_x]
      ac_rfl
    · simp only [B0Radical.left_smul_a, B0Radical.right_smul_a]
      ac_rfl

/-- The square-zero extension intended to model the dead-path lollipop.-/
abbrev B0Model := TrivSqZeroExt (VertexAlgebra K) (B0Radical K)

/-- The radical coordinate type is the ordinary two-dimensional vector
space.-/
def B0Radical.linearEquivProd : B0Radical K ≃ₗ[K] K × K where
  __ := B0Radical.addEquivProd K
  map_smul' _ _ := rfl

/--
@isnad1 id=finitedi.0h1v.s4.2cffca64922a from=translated src=- shape=84bfdc15 vocab=80e399be
-/
noncomputable instance B0Radical.finiteDimensional :
    FiniteDimensional K (B0Radical K) :=
  (B0Radical.linearEquivProd K).symm.finiteDimensional

/-- The concrete square-zero lollipop algebra is finite-dimensional.
@isnad1 id=finitedi.0h1v.s6.e37f534d0045 from=translated src=- shape=84bfdc15 vocab=622cf6f2
-/
noncomputable instance B0Model.finiteDimensional :
    FiniteDimensional K (B0Model K) := by
  change Module.Finite K ((K × K) × B0Radical K)
  infer_instance

/--
@isnad1 id=isnoethe.0h1v.s5.927c32a22534 from=translated src=- shape=1666ae32 vocab=e6df9540
-/
noncomputable instance B0Model.isNoetherianRing :
    IsNoetherianRing (B0Model K) :=
  IsNoetherianRing.of_finite K (B0Model K)

/--
@isnad1 id=isartini.0h1v.s5.ac39c4c98087 from=translated src=- shape=1666ae32 vocab=04136ccd
-/
noncomputable instance B0Model.isArtinianRing :
    IsArtinianRing (B0Model K) :=
  IsArtinianRing.of_finite K (B0Model K)

def e1 : B0Model K := TrivSqZeroExt.inl (1, 0)
def e2 : B0Model K := TrivSqZeroExt.inl (0, 1)
def x : B0Model K := TrivSqZeroExt.inr ⟨1, 0⟩
def a : B0Model K := TrivSqZeroExt.inr ⟨0, 1⟩

/--
@isnad1 id=eq.0h1v.s6.92c4275a2fdb from=translated src=- shape=e94b03c3 vocab=909df30b
-/
@[simp] theorem e1_add_e2 : e1 K + e2 K = 1 := by
  ext <;> simp [e1, e2]

/--
@isnad1 id=eq.0h1v.s8.53754fd1dbc9 from=translated src=- shape=4156e7b5 vocab=ba3016d9
-/
@[simp] theorem e1_sq : e1 K * e1 K = e1 K := by
  ext <;> simp [e1]

/--
@isnad1 id=eq.0h1v.s8.4f24f5760b5b from=translated src=- shape=4156e7b5 vocab=843076bd
-/
@[simp] theorem e2_sq : e2 K * e2 K = e2 K := by
  ext <;> simp [e2]

/--
@isnad1 id=eq.0h1v.s8.0bad000df3a1 from=translated src=- shape=e94b03c3 vocab=bf46cdb3
-/
@[simp] theorem e1_mul_e2 : e1 K * e2 K = 0 := by
  ext <;> simp [e1, e2]

/--
@isnad1 id=eq.0h1v.s8.a0baba722986 from=translated src=- shape=e94b03c3 vocab=bf46cdb3
-/
@[simp] theorem e2_mul_e1 : e2 K * e1 K = 0 := by
  ext <;> simp [e1, e2]

/--
@isnad1 id=eq.0h1v.s8.bfaf3b3211f3 from=translated src=- shape=b2048345 vocab=4bec4774
-/
@[simp] theorem e1_mul_x : e1 K * x K = x K := by
  ext <;> simp [e1, x]

/--
@isnad1 id=eq.0h1v.s8.b0eb4e329486 from=translated src=- shape=4156e7b5 vocab=4bec4774
-/
@[simp] theorem x_mul_e1 : x K * e1 K = x K := by
  ext <;> simp [e1, x]

/--
@isnad1 id=eq.0h1v.s8.3f5e7a71821d from=translated src=- shape=b2048345 vocab=85a2bb8c
-/
@[simp] theorem e2_mul_a : e2 K * a K = a K := by
  ext <;> simp [e2, a]

/--
@isnad1 id=eq.0h1v.s8.4b3872d53a76 from=translated src=- shape=4156e7b5 vocab=9d1d903b
-/
@[simp] theorem a_mul_e1 : a K * e1 K = a K := by
  ext <;> simp [e1, a]

/--
@isnad1 id=eq.0h1v.s8.fb0a5aa48e92 from=translated src=- shape=e94b03c3 vocab=1ee4b4d3
-/
@[simp] theorem e2_mul_x : e2 K * x K = 0 := by
  ext <;> simp [e2, x]

/--
@isnad1 id=eq.0h1v.s8.ede1f700c4ae from=translated src=- shape=e94b03c3 vocab=1ee4b4d3
-/
@[simp] theorem x_mul_e2 : x K * e2 K = 0 := by
  ext <;> simp [e2, x]

/--
@isnad1 id=eq.0h1v.s8.6872099603df from=translated src=- shape=e94b03c3 vocab=9d1d903b
-/
@[simp] theorem e1_mul_a : e1 K * a K = 0 := by
  ext <;> simp [e1, a]

/--
@isnad1 id=eq.0h1v.s8.56b663206232 from=translated src=- shape=e94b03c3 vocab=85a2bb8c
-/
@[simp] theorem a_mul_e2 : a K * e2 K = 0 := by
  ext <;> simp [e2, a]

/-- Products of any two off-diagonal coordinate generators vanish.
@isnad1 id=eq.0h3v.s8.d495007b2174 from=translated src=- shape=e8e2fbbc vocab=9a6ace54
-/
@[simp] theorem radical_mul_radical (u v : B0Radical K) :
    (TrivSqZeroExt.inr u : B0Model K) * TrivSqZeroExt.inr v = 0 := by
  exact TrivSqZeroExt.inr_mul_inr (VertexAlgebra K) u v

/--
@isnad1 id=eq.0h1v.s8.4cf6c3c648bc from=translated src=- shape=b9e51560 vocab=cf6e4e27
-/
@[simp] theorem x_sq : x K * x K = 0 := radical_mul_radical K _ _

/-- With paths read in the left-module/later-factor-first convention, the
paper path `x` followed by `a` is represented by the product `a * x`.
@isnad1 id=eq.0h1v.s8.14cd1792adcb from=translated src=- shape=e94b03c3 vocab=526a51be
-/
@[simp] theorem a_mul_x : a K * x K = 0 := radical_mul_radical K _ _

/-- The opposite order also vanishes because this model is square-zero.
@isnad1 id=eq.0h1v.s8.355303348e94 from=translated src=- shape=e94b03c3 vocab=526a51be
-/
@[simp] theorem x_mul_a : x K * a K = 0 := radical_mul_radical K _ _

end QuotientSubmoduleEquidistribution.LollipopConcrete
