/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Seed.RingTheory.TensorProduct.Maps
public import Tengoku.Seed.LinearAlgebra.Complex.Module
public import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Defs
public import Tengoku.Seed.RingTheory.Noetherian.Defs
import Tengoku.Seed.RingTheory.Finiteness.Prod
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic
import Tengoku.Seed.RingTheory.Noetherian.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The complexification `A ⊗_ℝ ℂ = A[i]` of a commutative ring

Hironaka: for a preanalytic `ℝ`-space `X = (X, 𝒪_X)`, "`(X, 𝒪_X ⊗_ℝ ℂ)` is a `ℂ`-local-ringed
space, which will be denoted by `X(ℂ)`" [Hir64, Ch. 0, §1, p. 120]. Since `ℂ = ℝ ⊕ ℝ i` is free of
rank two over `ℝ`, the tensor product `A ⊗_ℝ ℂ` of a commutative ring `A` (with an `ℝ`-structure)
is the ring `A[i] = {a + b i : a, b ∈ A}` of Gaussian pairs with `i² = -1`, and it is this ring —
which needs no `ℝ`-structure on `A` to be formed — that the complexification uses sectionwise:
`Γ(U, 𝒪_X ⊗_ℝ ℂ) = Γ(U, 𝒪_X)[i]`. The identification with Mathlib's tensor product is the
`ℝ`-algebra isomorphism `tensorEquiv : Complexified A ≃ₐ[ℝ] A ⊗[ℝ] ℂ`, `a + b i ↦ a ⊗ 1 + b ⊗ i`.

## Main definitions

In the namespace `Hironaka.AnalyticSpace.Complexified`:

* `Complexified A`: the pairs `⟨re, im⟩`, a commutative ring with
  `(a + bi)(c + di) = (ac - bd) + (ad + bc) i`; `ofReal : A →+* Complexified A` (`a ↦ a + 0 i`),
  `I` (`0 + 1 i`), `I_mul_I`, `re_add_im`; the `R`-algebra structure induced from one on `A`;
* `map (f : A →+* B) : Complexified A →+* Complexified B` (componentwise; functorial), `mapEquiv`;
* `algebraMapComplex (φ : ℝ →+* A) : ℂ →+* Complexified A`, `c ↦ φ(Re c) + φ(Im c) i`: the
  `ℂ`-structure of `X(ℂ)` from the `ℝ`-structure of `X`;
* `norm z = z.re² + z.im²` and `isUnit_iff_isUnit_norm`; the local-ring theorem
  `isLocalRing_of_exists_sub_mem`: if `A` is a local ring whose residue field is `ℝ` (every
  element is congruent to a constant `φ c` modulo `𝔪_A`), then `Complexified A` is a local ring —
  the stalks `𝒪_{X,x} ⊗_ℝ ℂ` of `X(ℂ)` are local because the residue fields of a preanalytic
  `ℝ`-space are `ℝ`; `isLocalHom_map`: a local homomorphism complexifies to a local
  homomorphism;
* `tensorEquiv`: the identification with `A ⊗[ℝ] ℂ` (the standard `ℂ = ℝ[i]`);
* `A[i]` is a finite `A`-module, hence Noetherian when `A` is.

The complexification of a space is built on this in `Hironaka/AnalyticSpace/Complexify.lean`.
-/

@[expose] public section

universe u v

namespace AnalyticSpace

/-- The complexification `A ⊗_ℝ ℂ = A[i]` of a commutative ring `A`, realised as Gaussian pairs
`a + b i` (Hironaka's `𝒪_X ⊗_ℝ ℂ` [Hir64, Ch. 0, §1, p. 120], sectionwise).-/
@[ext]
structure Complexified (A : Type u) where
  /-- The real part.-/
  re : A
  /-- The imaginary part.-/
  im : A

namespace Complexified

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

instance : Zero (Complexified A) := ⟨⟨0, 0⟩⟩
instance : One (Complexified A) := ⟨⟨1, 0⟩⟩
instance : Add (Complexified A) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg (Complexified A) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub (Complexified A) := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance : Mul (Complexified A) :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : SMul ℕ (Complexified A) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩
instance : SMul ℤ (Complexified A) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩
instance : NatCast (Complexified A) := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast (Complexified A) := ⟨fun n => ⟨n, 0⟩⟩

/--
@isnad1 id=eq.0h1v.s5.ab030affbbb4 from=translated src=- shape=c6b7a0b8 vocab=24cd843c
-/
@[simp] theorem zero_re : (0 : Complexified A).re = 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.daac864e9f0b from=translated src=- shape=c6b7a0b8 vocab=c79d0c1c
-/
@[simp] theorem zero_im : (0 : Complexified A).im = 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.7d12e7ef52a7 from=translated src=- shape=c6b7a0b8 vocab=24cd843c
-/
@[simp] theorem one_re : (1 : Complexified A).re = 1 := rfl
/--
@isnad1 id=eq.0h1v.s5.06ee1e939ec9 from=translated src=- shape=c6b7a0b8 vocab=c79d0c1c
-/
@[simp] theorem one_im : (1 : Complexified A).im = 0 := rfl
/--
@isnad1 id=eq.0h3v.s5.2c892169e8c4 from=translated src=- shape=0090f101 vocab=84c29e23
-/
@[simp] theorem add_re (z w : Complexified A) : (z + w).re = z.re + w.re := rfl
/--
@isnad1 id=eq.0h3v.s5.79ca54d07e37 from=translated src=- shape=0090f101 vocab=9d946615
-/
@[simp] theorem add_im (z w : Complexified A) : (z + w).im = z.im + w.im := rfl
/--
@isnad1 id=eq.0h2v.s5.7b60fe8e96cf from=translated src=- shape=58efbbcf vocab=c4768d2a
-/
@[simp] theorem neg_re (z : Complexified A) : (-z).re = -z.re := rfl
/--
@isnad1 id=eq.0h2v.s5.5bef83fb6f7e from=translated src=- shape=58efbbcf vocab=6ce4de6c
-/
@[simp] theorem neg_im (z : Complexified A) : (-z).im = -z.im := rfl
/--
@isnad1 id=eq.0h3v.s5.f5f94956c434 from=translated src=- shape=0090f101 vocab=2a44278e
-/
@[simp] theorem sub_re (z w : Complexified A) : (z - w).re = z.re - w.re := rfl
/--
@isnad1 id=eq.0h3v.s5.2603030157d3 from=translated src=- shape=0090f101 vocab=7a64b08a
-/
@[simp] theorem sub_im (z w : Complexified A) : (z - w).im = z.im - w.im := rfl
/--
@isnad1 id=eq.0h3v.s6.a83fa584d41f from=translated src=- shape=9d6409a6 vocab=9466cc82
-/
@[simp] theorem mul_re (z w : Complexified A) : (z * w).re = z.re * w.re - z.im * w.im := rfl
/--
@isnad1 id=eq.0h3v.s6.dbcecab36a79 from=translated src=- shape=b9761b50 vocab=9054ca30
-/
@[simp] theorem mul_im (z w : Complexified A) : (z * w).im = z.re * w.im + z.im * w.re := rfl
/--
@isnad1 id=eq.0h3v.s5.07d1c2c5fc43 from=translated src=- shape=9f363131 vocab=97c54606
-/
@[simp] theorem nsmul_re (n : ℕ) (z : Complexified A) : (n • z).re = n • z.re := rfl
/--
@isnad1 id=eq.0h3v.s5.108104575236 from=translated src=- shape=9f363131 vocab=2907f8a0
-/
@[simp] theorem nsmul_im (n : ℕ) (z : Complexified A) : (n • z).im = n • z.im := rfl
/--
@isnad1 id=eq.0h3v.s5.5a2ff460e257 from=translated src=- shape=9f363131 vocab=e2f2d47c
-/
@[simp] theorem zsmul_re (n : ℤ) (z : Complexified A) : (n • z).re = n • z.re := rfl
/--
@isnad1 id=eq.0h3v.s5.10e1be5d77ca from=translated src=- shape=9f363131 vocab=a640e6a0
-/
@[simp] theorem zsmul_im (n : ℤ) (z : Complexified A) : (n • z).im = n • z.im := rfl
/--
@isnad1 id=eq.0h2v.s4.7aaae7a34496 from=translated src=- shape=7db3a00d vocab=095ba5eb
-/
@[simp] theorem natCast_re (n : ℕ) : (n : Complexified A).re = n := rfl
/--
@isnad1 id=eq.0h2v.s5.2b8fef3882de from=translated src=- shape=7ba49ae7 vocab=75809ecd
-/
@[simp] theorem natCast_im (n : ℕ) : (n : Complexified A).im = 0 := rfl
/--
@isnad1 id=eq.0h2v.s4.6438fabc0252 from=translated src=- shape=7db3a00d vocab=92aa6991
-/
@[simp] theorem intCast_re (n : ℤ) : (n : Complexified A).re = n := rfl
/--
@isnad1 id=eq.0h2v.s5.5cc1fd7c0beb from=translated src=- shape=7ba49ae7 vocab=afd1e7d9
-/
@[simp] theorem intCast_im (n : ℤ) : (n : Complexified A).im = 0 := rfl

instance instCommRing : CommRing (Complexified A) where
  add_assoc := by intros; ext <;> simp [add_assoc]
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp [add_comm]
  nsmul := (· • ·)
  nsmul_zero := by intros; ext <;> simp
  nsmul_succ := by intros; ext <;> simp [add_mul]
  zsmul := (· • ·)
  zsmul_zero' := by intros; ext <;> simp
  zsmul_succ' := by intros; ext <;> simp [add_mul]
  zsmul_neg' := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp
  sub_eq_add_neg := by intros; ext <;> simp [sub_eq_add_neg]
  natCast_zero := by ext <;> simp
  natCast_succ := by intros; ext <;> simp
  intCast_ofNat := by intros; ext <;> simp
  intCast_negSucc := by intros; ext <;> simp [Int.cast_negSucc]
  mul_assoc := by intros; ext <;> simp <;> ring
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  zero_mul := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  mul_comm := by intros; ext <;> simp <;> ring

/--
@isnad1 id=nontrivi.0h1v.s3.9faf5af46219 from=translated src=- shape=d96e9922 vocab=b3b929e1
-/
instance instNontrivial [Nontrivial A] : Nontrivial (Complexified A) :=
  ⟨⟨0, 1, fun h => zero_ne_one (congrArg re h)⟩⟩

/-- The canonical inclusion `A → A ⊗_ℝ ℂ`, `a ↦ a ⊗ 1 = a + 0 i`.-/
def ofReal : A →+* Complexified A where
  toFun a := ⟨a, 0⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

/--
@isnad1 id=eq.0h2v.s6.c4756330e0fb from=translated src=- shape=4b9f7faf vocab=f513b116
-/
@[simp] theorem ofReal_re (a : A) : (ofReal a).re = a := rfl
/--
@isnad1 id=eq.0h2v.s6.e67cb28cdf9c from=translated src=- shape=dc77db7a vocab=f9a87a00
-/
@[simp] theorem ofReal_im (a : A) : (ofReal a).im = 0 := rfl

/-- The imaginary unit `i = 1 ⊗ i` of `A ⊗_ℝ ℂ`.-/
def I : Complexified A := ⟨0, 1⟩

/--
@isnad1 id=eq.0h1v.s4.cbaabbf5f519 from=translated src=- shape=5f1ef773 vocab=99e4183f
-/
@[simp] theorem I_re : (I : Complexified A).re = 0 := rfl
/--
@isnad1 id=eq.0h1v.s4.497ca0d4d585 from=translated src=- shape=5f1ef773 vocab=3583f0d5
-/
@[simp] theorem I_im : (I : Complexified A).im = 1 := rfl

/--
@isnad1 id=eq.0h1v.s5.56b05dd69ddb from=translated src=- shape=33cac440 vocab=241d3968
-/
theorem I_mul_I : (I : Complexified A) * I = -1 := by ext <;> simp

/-- The complexification of a ring homomorphism, componentwise.-/
def map (f : A →+* B) : Complexified A →+* Complexified B where
  toFun z := ⟨f z.re, f z.im⟩
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp

/--
@isnad1 id=eq.0h4v.s7.094cdb166279 from=translated src=- shape=7758e3e0 vocab=c9a6d665
-/
@[simp] theorem map_re (f : A →+* B) (z : Complexified A) : (map f z).re = f z.re := rfl
/--
@isnad1 id=eq.0h4v.s7.d515c5e19a7b from=translated src=- shape=7758e3e0 vocab=f4252f9a
-/
@[simp] theorem map_im (f : A →+* B) (z : Complexified A) : (map f z).im = f z.im := rfl

/--
@isnad1 id=eq.0h1v.s6.68ef9e4e1aae from=translated src=- shape=a9843297 vocab=8748ed6e
-/
@[simp]
theorem map_id : map (RingHom.id A) = RingHom.id (Complexified A) :=
  RingHom.ext fun _ => rfl

/--
@isnad1 id=eq.0h5v.s7.39338a60ca73 from=translated src=- shape=1d0a1d16 vocab=6c2eb14a
-/
theorem map_comp {C : Type*} [CommRing C] (g : B →+* C) (f : A →+* B) :
    map (g.comp f) = (map g).comp (map f) :=
  RingHom.ext fun _ => rfl

/--
@isnad1 id=eq.0h4v.s8.190462ba686c from=translated src=- shape=542b35ba vocab=1b5e767a
-/
@[simp] theorem map_ofReal (f : A →+* B) (a : A) : map f (ofReal a) = ofReal (f a) := by
  ext <;> simp

/--
@isnad1 id=eq.0h3v.s6.37a8f8a9f52a from=translated src=- shape=b393e1dd vocab=37956889
-/
@[simp] theorem map_I (f : A →+* B) : map f (I : Complexified A) = I := by ext <;> simp

/--
@isnad1 id=injectiv.1h3v.s7.e09eb4818ff3 from=translated src=- shape=1aeb3f0b vocab=6dbc5827
-/
theorem map_injective {f : A →+* B} (hf : Function.Injective f) : Function.Injective (map f) :=
  fun z w h => by
    ext
    · exact hf (congrArg re h)
    · exact hf (congrArg im h)

/--
@isnad1 id=surjecti.1h3v.s7.4c05c4b9b881 from=translated src=- shape=1aeb3f0b vocab=138dbfe0
-/
theorem map_surjective {f : A →+* B} (hf : Function.Surjective f) : Function.Surjective (map f) :=
  fun w => by
    obtain ⟨a, ha⟩ := hf w.re
    obtain ⟨b, hb⟩ := hf w.im
    exact ⟨⟨a, b⟩, by ext <;> simp [ha, hb]⟩

/--
@isnad1 id=bijectiv.1h3v.s7.a94493b5ac9e from=translated src=- shape=1aeb3f0b vocab=29435c51
-/
theorem map_bijective {f : A →+* B} (hf : Function.Bijective f) : Function.Bijective (map f) :=
  ⟨map_injective hf.1, map_surjective hf.2⟩

/-- The complexification of a ring isomorphism.-/
noncomputable def mapEquiv (e : A ≃+* B) : Complexified A ≃+* Complexified B :=
  RingEquiv.ofBijective (map e.toRingHom) (map_bijective e.bijective)

/--
@isnad1 id=eq.0h4v.s7.ec1a93db435c from=translated src=- shape=c0dea30d vocab=5a3ece95
-/
@[simp] theorem mapEquiv_apply (e : A ≃+* B) (z : Complexified A) :
    mapEquiv e z = map e.toRingHom z := rfl

/-- The `ℂ`-structure of `A ⊗_ℝ ℂ` induced by an `ℝ`-structure `φ : ℝ →+* A` of `A`:
`c ↦ φ(Re c) + φ(Im c) i`.-/
def algebraMapComplex (φ : ℝ →+* A) : ℂ →+* Complexified A where
  toFun c := ⟨φ c.re, φ c.im⟩
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp [Complex.mul_re, Complex.mul_im]
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp

/--
@isnad1 id=eq.0h3v.s6.e26a32c311f4 from=translated src=- shape=18938d98 vocab=422ef740
-/
@[simp] theorem algebraMapComplex_re (φ : ℝ →+* A) (c : ℂ) :
    (algebraMapComplex φ c).re = φ c.re := rfl
/--
@isnad1 id=eq.0h3v.s6.ba22a6d4893b from=translated src=- shape=18938d98 vocab=d2d0efa4
-/
@[simp] theorem algebraMapComplex_im (φ : ℝ →+* A) (c : ℂ) :
    (algebraMapComplex φ c).im = φ c.im := rfl

section Algebra

variable {R : Type*} [CommSemiring R] [Algebra R A]

instance instSMul : SMul R (Complexified A) := ⟨fun r z => ⟨r • z.re, r • z.im⟩⟩

/--
@isnad1 id=eq.0h4v.s6.597acd8ef9aa from=translated src=- shape=1cba1c43 vocab=cfa3fcf3
-/
@[simp] theorem smul_re (r : R) (z : Complexified A) : (r • z).re = r • z.re := rfl
/--
@isnad1 id=eq.0h4v.s6.1719748d63d5 from=translated src=- shape=1cba1c43 vocab=c2114ea3
-/
@[simp] theorem smul_im (r : R) (z : Complexified A) : (r • z).im = r • z.im := rfl

/-- The `R`-algebra structure of `A ⊗_ℝ ℂ` from one of `A` (through `ofReal`).-/
instance instAlgebra : Algebra R (Complexified A) where
  algebraMap := ofReal.comp (algebraMap R A)
  commutes' _ _ := mul_comm _ _
  smul := (· • ·)
  smul_def' r z := by ext <;> simp [Algebra.smul_def]

/--
@isnad1 id=eq.0h3v.s7.f932910c256c from=translated src=- shape=61376e1c vocab=5f510b18
-/
@[simp]
theorem algebraMap_apply (r : R) :
    algebraMap R (Complexified A) r = ofReal (algebraMap R A r) := rfl

/-- `ofReal` as an `R`-algebra homomorphism.-/
def ofRealAlgHom : A →ₐ[R] Complexified A := { ofReal with commutes' := fun _ => rfl }

/--
@isnad1 id=eq.0h3v.s7.c7732ee1b84f from=translated src=- shape=e702d4da vocab=4dcf06cd
-/
@[simp] theorem ofRealAlgHom_apply (a : A) :
    (ofRealAlgHom : A →ₐ[R] Complexified A) a = ofReal a := rfl

end Algebra

/-! ### The norm `a² + b²`, units and the local-ring theorem -/

/-- The norm `N(a + bi) = a² + b²`, multiplicative.-/
def norm (z : Complexified A) : A := z.re * z.re + z.im * z.im

/--
@isnad1 id=eq.0h3v.s5.f2a4222822ae from=translated src=- shape=0090f101 vocab=051704b8
-/
theorem norm_mul (z w : Complexified A) : norm (z * w) = norm z * norm w := by
  simp only [norm, mul_re, mul_im]; ring

/--
@isnad1 id=eq.0h1v.s5.f1384bccc4a0 from=translated src=- shape=c6b7a0b8 vocab=0697d298
-/
theorem norm_one : norm (1 : Complexified A) = 1 := by simp [norm]

/-- The conjugate `a - bi`.-/
def conj (z : Complexified A) : Complexified A := ⟨z.re, -z.im⟩

/--
@isnad1 id=eq.0h2v.s6.83b241e9dd92 from=translated src=- shape=c57a40ac vocab=93a1c928
-/
theorem mul_conj (z : Complexified A) : z * conj z = ofReal (norm z) := by
  ext
  · simp only [mul_re, conj, norm, ofReal_re, mul_neg, sub_neg_eq_add]
  · simp only [mul_im, conj, ofReal_im, mul_neg]; ring

/--
@isnad1 id=iff.0h2v.s5.e551940572c4 from=translated src=- shape=8b353daa vocab=9653db19
-/
theorem isUnit_iff_isUnit_norm (z : Complexified A) : IsUnit z ↔ IsUnit (norm z) := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : norm (u : Complexified A) * norm (↑u⁻¹ : Complexified A) = 1 := by
      rw [← norm_mul, Units.mul_inv, norm_one]
    exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
  · rintro ⟨u, hu⟩
    refine isUnit_iff_exists_inv.mpr ⟨conj z * ofReal (↑u⁻¹ : A), ?_⟩
    rw [← mul_assoc, mul_conj, ← map_mul, ← hu, Units.mul_inv, map_one]

/-- The local-ring theorem behind Hironaka's "`(X, 𝒪_X ⊗_ℝ ℂ)` is a `ℂ`-local-ringed space"
[Hir64, Ch. 0, §1, p. 120]: if `A` is a local ring with residue field `ℝ` — every element is
congruent modulo `𝔪_A` to a constant `φ c`, `φ : ℝ →+* A` — then `A ⊗_ℝ ℂ = A[i]` is a local
ring. Proof: for `z = a + bi` with `a ≡ φ α`, `b ≡ φ β`, the norm `a² + b² ≡ φ(α² + β²)`; if
`(α, β) ≠ 0` this is a unit of `A` (a constant outside `𝔪_A`), so `z` is a unit; otherwise
`a, b ∈ 𝔪_A` and `1 - z` has norm `≡ 1`, a unit.
@isnad1 id=islocalr.1h2v.s7.c2404ada8c00 from=translated src=- shape=bc114ffe vocab=140561db
-/
theorem isLocalRing_of_exists_sub_mem [IsLocalRing A] (φ : ℝ →+* A)
    (h : ∀ a : A, ∃ c : ℝ, a - φ c ∈ IsLocalRing.maximalIdeal A) :
    IsLocalRing (Complexified A) := by
  have hunit : ∀ c : ℝ, c ≠ 0 → IsUnit (φ c) := fun c hc => by
    have : φ c * φ c⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hc, map_one]
    exact isUnit_iff_exists_inv.mpr ⟨_, this⟩
  -- an element congruent to a nonzero constant is a unit
  have hcong : ∀ (a : A) (c : ℝ), c ≠ 0 → a - φ c ∈ IsLocalRing.maximalIdeal A → IsUnit a := by
    intro a c hc hm
    by_contra ha
    have hmem : a ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr ha)
    have hφ : φ c ∈ IsLocalRing.maximalIdeal A := by
      have := Ideal.sub_mem _ hmem hm
      rwa [sub_sub_cancel] at this
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hφ (hunit c hc))
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  obtain ⟨α, hα⟩ := h z.re
  obtain ⟨β, hβ⟩ := h z.im
  -- the norm is congruent to `φ(α² + β²)`
  have hnorm : ∀ (a b : A) (α β : ℝ), a - φ α ∈ IsLocalRing.maximalIdeal A →
      b - φ β ∈ IsLocalRing.maximalIdeal A →
      (a * a + b * b) - φ (α * α + β * β) ∈ IsLocalRing.maximalIdeal A := by
    intro a b α β ha hb
    have e : (a * a + b * b) - φ (α * α + β * β) =
        (a - φ α) * (a + φ α) + (b - φ β) * (b + φ β) := by
      simp only [map_add, map_mul]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ hb)
  by_cases hαβ : α * α + β * β = 0
  · -- both residues vanish: `1 - z` is a unit
    right
    have hα0 : α = 0 := by nlinarith [mul_self_nonneg α, mul_self_nonneg β]
    have hβ0 : β = 0 := by nlinarith [mul_self_nonneg α, mul_self_nonneg β]
    subst hα0; subst hβ0
    rw [isUnit_iff_isUnit_norm]
    refine hcong _ 1 one_ne_zero ?_
    have := hnorm (1 - z).re (1 - z).im 1 0 ?_ ?_
    · simpa [norm] using this
    · simp only [sub_re, one_re, map_one]
      have : (1 - z.re) - 1 = -(z.re - φ 0) := by rw [map_zero]; ring
      rw [this]; exact neg_mem hα
    · simp only [sub_im, one_im, map_zero, zero_sub]
      have : -z.im - 0 = -(z.im - φ 0) := by rw [map_zero]; ring
      rw [this]; exact neg_mem hβ
  · left
    rw [isUnit_iff_isUnit_norm]
    exact hcong _ _ hαβ (hnorm z.re z.im α β hα hβ)

/-- A local homomorphism complexifies to a local homomorphism.
@isnad1 id=islocalh.0h3v.s7.cdc3573de8cc from=translated src=- shape=80e3e4d1 vocab=366ac22d
-/
theorem isLocalHom_map (f : A →+* B) [IsLocalHom f] :
    IsLocalHom (map f) where
  map_nonunit z hz := by
    rw [isUnit_iff_isUnit_norm] at hz ⊢
    have : norm (map f z) = f (norm z) := by simp [norm]
    rw [this] at hz
    exact IsLocalHom.map_nonunit _ hz

/-! ### The identification with Mathlib's tensor product `A ⊗[ℝ] ℂ` -/

section Tensor

open TensorProduct

variable [Algebra ℝ A]

/-- The `ℂ`-structure of `A ⊗_ℝ ℂ` as an `ℝ`-algebra homomorphism `ℂ →ₐ[ℝ] A[i]`.-/
noncomputable def algebraMapComplexAlgHom : ℂ →ₐ[ℝ] Complexified A :=
  { algebraMapComplex (algebraMap ℝ A) with
    commutes' := fun r =>
      Complexified.ext (by simp) (by simp) }

/--
@isnad1 id=eq.0h2v.s7.4b3358059398 from=translated src=- shape=72ac6f0c vocab=c4c88a92
-/
@[simp] theorem algebraMapComplexAlgHom_apply (c : ℂ) :
    (algebraMapComplexAlgHom : ℂ →ₐ[ℝ] Complexified A) c =
      ⟨algebraMap ℝ A c.re, algebraMap ℝ A c.im⟩ :=
  rfl

/-- `A ⊗[ℝ] ℂ → A[i]`: `a ⊗ c ↦ a · (Re c + Im c · i)`.-/
noncomputable def ofTensor : A ⊗[ℝ] ℂ →ₐ[ℝ] Complexified A :=
  Algebra.TensorProduct.productMap ofRealAlgHom algebraMapComplexAlgHom

/--
@isnad1 id=eq.0h3v.s8.54e9a3f1a96b from=translated src=- shape=26f5d38a vocab=ab9c13cc
-/
@[simp] theorem ofTensor_tmul (a : A) (c : ℂ) :
    ofTensor (a ⊗ₜ c) = ofReal a * ⟨algebraMap ℝ A c.re, algebraMap ℝ A c.im⟩ := by
  rw [ofTensor, Algebra.TensorProduct.productMap_apply_tmul]
  rfl

/-- `A[i] → A ⊗[ℝ] ℂ`: `a + b i ↦ a ⊗ 1 + b ⊗ i`.-/
noncomputable def toTensor : Complexified A →ₐ[ℝ] A ⊗[ℝ] ℂ where
  toFun z := z.re ⊗ₜ 1 + z.im ⊗ₜ Complex.I
  map_one' := by simp [Algebra.TensorProduct.one_def]
  map_mul' z w := by
    simp only [mul_re, mul_im, sub_tmul, add_tmul, add_mul, mul_add,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Complex.I_mul_I, tmul_neg]
    abel
  map_zero' := by simp
  map_add' z w := by
    simp only [add_re, add_im, add_tmul]
    abel
  commutes' r := by
    simp [Algebra.TensorProduct.algebraMap_apply]

/--
@isnad1 id=eq.0h2v.s8.229c84c62a83 from=translated src=- shape=42b60b20 vocab=01c6ec57
-/
@[simp] theorem toTensor_apply (z : Complexified A) :
    toTensor z = z.re ⊗ₜ 1 + z.im ⊗ₜ Complex.I := rfl

end Tensor

/-! ### Noetherianity: `A[i]` is Noetherian when `A` is -/

section Noetherian

variable {A : Type u} [CommRing A]

/-- The `A`-linear map `A × A → A[i]`, `(a, b) ↦ a + b i`.-/
def ofRealPairLinear : (A × A) →ₗ[A] Complexified A where
  toFun p := ofReal p.1 + ofReal p.2 * I
  map_add' p q := by ext <;> simp [add_mul]
  map_smul' c p := by ext <;> simp [Algebra.smul_def]

end Noetherian

end Complexified

end AnalyticSpace
