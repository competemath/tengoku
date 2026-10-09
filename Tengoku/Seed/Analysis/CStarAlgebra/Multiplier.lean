/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Jon Bannon
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.CStarAlgebra.Unitization
public import Tengoku.Seed.Analysis.CStarAlgebra.Classes
public import Tengoku.Seed.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Multiplier Algebra of a C⋆-algebra

Define the multiplier algebra of a C⋆-algebra as the algebra (over `𝕜`) of double centralizers,
for which we provide the localized notation `𝓜(𝕜, A)`.  A double centralizer is a pair of
continuous linear maps `L R : A →L[𝕜] A` satisfying the intertwining condition `R x * y = x * L y`.

There is a natural embedding `A → 𝓜(𝕜, A)` which sends `a : A` to the continuous linear maps
`L R : A →L[𝕜] A` given by left and right multiplication by `a`, and we provide this map as a
coercion.

The multiplier algebra corresponds to a non-commutative Stone–Čech compactification in the sense
that when the algebra `A` is commutative, it can be identified with `C₀(X, ℂ)` for some locally
compact Hausdorff space `X`, and in that case `𝓜(𝕜, A)` can be identified with `C(β X, ℂ)`.

## Implementation notes

We make the hypotheses on `𝕜` as weak as possible so that, in particular, this construction works
for both `𝕜 = ℝ` and `𝕜 = ℂ`.

The reader familiar with C⋆-algebra theory may recognize that one
only needs `L` and `R` to be functions instead of continuous linear maps, at least when `A` is a
C⋆-algebra. Our intention is simply to eventually provide a constructor for this situation.

We pull back the `NormedAlgebra` structure (and everything contained therein) through the
ring (even algebra) homomorphism
`DoubleCentralizer.toProdMulOppositeHom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ` which
sends `a : 𝓜(𝕜, A)` to `(a.fst, MulOpposite.op a.snd)`. The star structure is provided
separately.

## References

* https://en.wikipedia.org/wiki/Multiplier_algebra

## TODO

+ Define a type synonym for `𝓜(𝕜, A)` which is equipped with the strict uniform space structure
  and show it is complete
+ Show that the image of `A` in `𝓜(𝕜, A)` is an essential ideal
+ Prove the universal property of `𝓜(𝕜, A)`
+ Construct a double centralizer from a pair of maps (not necessarily linear or continuous)
  `L : A → A`, `R : A → A` satisfying the centrality condition `∀ x y, R x * y = x * L y`.
+ Show that if `A` is unital, then `A ≃⋆ₐ[𝕜] 𝓜(𝕜, A)`.
-/

@[expose] public section


open NNReal ContinuousLinearMap MulOpposite

universe u v

/-- The type of *double centralizers*, also known as the *multiplier algebra* and denoted by
`𝓜(𝕜, A)`, of a non-unital normed algebra.

If `x : 𝓜(𝕜, A)`, then `x.fst` and `x.snd` are what is usually referred to as $L$ and $R$. -/
structure DoubleCentralizer (𝕜 : Type u) (A : Type v) [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] extends
    (A →L[𝕜] A) × (A →L[𝕜] A) where
  /-- The centrality condition that the maps linear maps intertwine one another. -/
  central : ∀ x y : A, snd x * y = x * fst y

@[inherit_doc]
scoped[MultiplierAlgebra] notation "𝓜(" 𝕜 ", " A ")" => DoubleCentralizer 𝕜 A

open MultiplierAlgebra

/--
@isnad1 id=eq.1h4v.s9.423976b433b5 from=seed src=0 shape=49c48073 vocab=d9da9942
-/
@[ext]
lemma DoubleCentralizer.ext (𝕜 : Type u) (A : Type v) [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]
    (a b : 𝓜(𝕜, A)) (h : a.toProd = b.toProd) : a = b := by
  cases a
  cases b
  simpa using h

namespace DoubleCentralizer

section NontriviallyNormed

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
variable [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]

/-!
### Algebraic structure

Because the multiplier algebra is defined as the algebra of double centralizers, there is a natural
injection `DoubleCentralizer.toProdMulOpposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ`
defined by `fun a ↦ (a.fst, MulOpposite.op a.snd)`. We use this map to pull back the ring, module
and algebra structure from `(A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ` to `𝓜(𝕜, A)`. -/

variable {𝕜 A}

/--
@isnad1 id=eq.0h2v.s11.842f97d868c2 from=seed src=0 shape=c07bb365 vocab=61b6e35b
-/
theorem range_toProd :
    Set.range toProd = { lr : (A →L[𝕜] A) × (A →L[𝕜] A) | ∀ x y, lr.2 x * y = x * lr.1 y } :=
  Set.ext fun x =>
    ⟨by
      rintro ⟨a, rfl⟩
      exact a.central, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

instance instAdd : Add 𝓜(𝕜, A) where
  add a b :=
    { toProd := a.toProd + b.toProd
      central := fun x y =>
        show (a.snd + b.snd) x * y = x * (a.fst + b.fst) y by
          simp only [add_apply, mul_add, add_mul, central] }

instance instZero : Zero 𝓜(𝕜, A) where
  zero :=
    { toProd := 0
      central := fun x y => (zero_mul y).trans (mul_zero x).symm }

instance instNeg : Neg 𝓜(𝕜, A) where
  neg a :=
    { toProd := -a.toProd
      central := fun x y =>
        show -a.snd x * y = x * -a.fst y by
          simp only [neg_mul, mul_neg, central] }

instance instSub : Sub 𝓜(𝕜, A) where
  sub a b :=
    { toProd := a.toProd - b.toProd
      central := fun x y =>
        show (a.snd - b.snd) x * y = x * (a.fst - b.fst) y by
          simp only [sub_apply, _root_.sub_mul, _root_.mul_sub, central] }

section Scalars

variable {S : Type*} [Monoid S] [DistribMulAction S A] [SMulCommClass 𝕜 S A]
  [ContinuousConstSMul S A] [IsScalarTower S A A] [SMulCommClass S A A]

instance instSMul : SMul S 𝓜(𝕜, A) where
  smul s a :=
    { toProd := s • a.toProd
      central := fun x y =>
        show (s • a.snd) x * y = x * (s • a.fst) y by
          simp only [smul_apply, mul_smul_comm, smul_mul_assoc, central] }

/--
@isnad1 id=eq.0h5v.s11.2e5db7143bc3 from=seed src=0 shape=4b65f404 vocab=4c77bb94
-/
@[simp]
theorem smul_toProd (s : S) (a : 𝓜(𝕜, A)) : (s • a).toProd = s • a.toProd :=
  rfl

/--
@isnad1 id=eq.0h5v.s10.7e5db64e3248 from=seed src=0 shape=a8ff145d vocab=e0b03f8c
-/
theorem smul_fst (s : S) (a : 𝓜(𝕜, A)) : (s • a).fst = s • a.fst :=
  rfl

/--
@isnad1 id=eq.0h5v.s10.959f3e1b0211 from=seed src=0 shape=a8ff145d vocab=744bad74
-/
theorem smul_snd (s : S) (a : 𝓜(𝕜, A)) : (s • a).snd = s • a.snd :=
  rfl

variable {T : Type*} [Monoid T] [DistribMulAction T A] [SMulCommClass 𝕜 T A]
  [ContinuousConstSMul T A] [IsScalarTower T A A] [SMulCommClass T A A]

/--
@isnad1 id=isscalar.0h4v.s10.6157e1aeeb15 from=seed src=0 shape=4ad329e1 vocab=4426c02f
-/
instance instIsScalarTower [SMul S T] [IsScalarTower S T A] : IsScalarTower S T 𝓜(𝕜, A) where
  smul_assoc _ _ a := ext (𝕜 := 𝕜) (A := A) _ _ <| smul_assoc _ _ a.toProd

/--
@isnad1 id=smulcomm.0h4v.s10.47d3ad7dabb3 from=seed src=0 shape=3f2b4d35 vocab=29611517
-/
instance instSMulCommClass [SMulCommClass S T A] : SMulCommClass S T 𝓜(𝕜, A) where
  smul_comm _ _ a := ext (𝕜 := 𝕜) (A := A) _ _ <| smul_comm _ _ a.toProd

/--
@isnad1 id=iscentra.0h3v.s10.a877e5654215 from=seed src=0 shape=ae92b748 vocab=8ef1fcae
-/
instance instIsCentralScalar {R : Type*} [Semiring R] [Module R A] [SMulCommClass 𝕜 R A]
    [ContinuousConstSMul R A] [IsScalarTower R A A] [SMulCommClass R A A] [Module Rᵐᵒᵖ A]
    [IsCentralScalar R A] : IsCentralScalar R 𝓜(𝕜, A) where
  op_smul_eq_smul _ a := ext (𝕜 := 𝕜) (A := A) _ _ <| op_smul_eq_smul _ a.toProd

end Scalars

instance instOne : One 𝓜(𝕜, A) :=
  ⟨⟨1, fun _x _y => rfl⟩⟩

instance instMul : Mul 𝓜(𝕜, A) where
  mul a b :=
    { toProd := (a.fst.comp b.fst, b.snd.comp a.snd)
      central := fun x y => show b.snd (a.snd x) * y = x * a.fst (b.fst y) by simp only [central] }

instance instNatCast : NatCast 𝓜(𝕜, A) where
  natCast n :=
    ⟨n, fun x y => by
      rw [Prod.snd_natCast, Prod.fst_natCast]
      simp only [← Nat.smul_one_eq_cast, smul_apply, one_apply_eq_self, mul_smul_comm,
        smul_mul_assoc]⟩

instance instIntCast : IntCast 𝓜(𝕜, A) where
  intCast n :=
    ⟨n, fun x y => by
      rw [Prod.snd_intCast, Prod.fst_intCast]
      simp only [← Int.smul_one_eq_cast, smul_apply, one_apply_eq_self, mul_smul_comm,
        smul_mul_assoc]⟩

instance instPow : Pow 𝓜(𝕜, A) ℕ where
  pow a n :=
    ⟨a.toProd ^ n, fun x y => by
      induction n generalizing x y with
      | zero => rfl
      | succ k hk =>
        rw [Prod.pow_snd, Prod.pow_fst] at hk ⊢
        rw [pow_succ' a.snd, mul_apply_eq_comp, a.central, hk, pow_succ a.fst, mul_apply_eq_comp]⟩

instance instInhabited : Inhabited 𝓜(𝕜, A) :=
  ⟨0⟩

/--
@isnad1 id=eq.0h4v.s10.7895eec91880 from=seed src=0 shape=d904816b vocab=21a1e30f
-/
@[simp]
theorem add_toProd (a b : 𝓜(𝕜, A)) : (a + b).toProd = a.toProd + b.toProd :=
  rfl

/--
@isnad1 id=eq.0h2v.s10.7b9a7a4ddeab from=seed src=0 shape=30cfc904 vocab=d9da9942
-/
@[simp]
theorem zero_toProd : (0 : 𝓜(𝕜, A)).toProd = 0 :=
  rfl

/--
@isnad1 id=eq.0h3v.s10.78a9bdaa4704 from=seed src=0 shape=980159f3 vocab=559ecf49
-/
@[simp]
theorem neg_toProd (a : 𝓜(𝕜, A)) : (-a).toProd = -a.toProd :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.d5895ca8440e from=seed src=0 shape=d904816b vocab=70da4bd9
-/
@[simp]
theorem sub_toProd (a b : 𝓜(𝕜, A)) : (a - b).toProd = a.toProd - b.toProd :=
  rfl

/--
@isnad1 id=eq.0h2v.s10.c8bd1348434e from=seed src=0 shape=30cfc904 vocab=d9da9942
-/
@[simp]
theorem one_toProd : (1 : 𝓜(𝕜, A)).toProd = 1 :=
  rfl

/--
@isnad1 id=eq.0h3v.s10.6a450263d666 from=seed src=0 shape=83060098 vocab=6ee62c1b
-/
@[simp]
theorem natCast_toProd (n : ℕ) : (n : 𝓜(𝕜, A)).toProd = n :=
  rfl

/--
@isnad1 id=eq.0h3v.s10.977e790a6fb0 from=seed src=0 shape=83060098 vocab=61ab6957
-/
@[simp]
theorem intCast_toProd (n : ℤ) : (n : 𝓜(𝕜, A)).toProd = n :=
  rfl

/--
@isnad1 id=eq.0h4v.s11.0d9e7fd2214b from=seed src=0 shape=11dba21b vocab=0bd11282
-/
@[simp]
theorem pow_toProd (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).toProd = a.toProd ^ n :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.6eb7db681e64 from=seed src=0 shape=08173ed0 vocab=ae0b56d3
-/
theorem add_fst (a b : 𝓜(𝕜, A)) : (a + b).fst = a.fst + b.fst :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.2d96099b4d86 from=seed src=0 shape=08173ed0 vocab=1f5146c0
-/
theorem add_snd (a b : 𝓜(𝕜, A)) : (a + b).snd = a.snd + b.snd :=
  rfl

/--
@isnad1 id=eq.0h2v.s9.1a2db76c40a9 from=seed src=0 shape=43b38e82 vocab=ca2d4e53
-/
theorem zero_fst : (0 : 𝓜(𝕜, A)).fst = 0 :=
  rfl

/--
@isnad1 id=eq.0h2v.s9.4eaa79fa16bb from=seed src=0 shape=43b38e82 vocab=77309e26
-/
theorem zero_snd : (0 : 𝓜(𝕜, A)).snd = 0 :=
  rfl

/--
@isnad1 id=eq.0h3v.s10.2ece6d80eb6e from=seed src=0 shape=be33d9fc vocab=035999c5
-/
theorem neg_fst (a : 𝓜(𝕜, A)) : (-a).fst = -a.fst :=
  rfl

/--
@isnad1 id=eq.0h3v.s10.85aa48e9de9f from=seed src=0 shape=be33d9fc vocab=d8308531
-/
theorem neg_snd (a : 𝓜(𝕜, A)) : (-a).snd = -a.snd :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.7dbbd8e1bc21 from=seed src=0 shape=08173ed0 vocab=3936929b
-/
theorem sub_fst (a b : 𝓜(𝕜, A)) : (a - b).fst = a.fst - b.fst :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.cc377f4557e7 from=seed src=0 shape=08173ed0 vocab=6455b406
-/
theorem sub_snd (a b : 𝓜(𝕜, A)) : (a - b).snd = a.snd - b.snd :=
  rfl

/--
@isnad1 id=eq.0h2v.s9.affcf204f198 from=seed src=0 shape=43b38e82 vocab=ca2d4e53
-/
theorem one_fst : (1 : 𝓜(𝕜, A)).fst = 1 :=
  rfl

/--
@isnad1 id=eq.0h2v.s9.25a511bcf4d0 from=seed src=0 shape=43b38e82 vocab=77309e26
-/
theorem one_snd : (1 : 𝓜(𝕜, A)).snd = 1 :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.d3b7948ab0a1 from=seed src=0 shape=08173ed0 vocab=7ec0f85c
-/
@[simp]
theorem mul_fst (a b : 𝓜(𝕜, A)) : (a * b).fst = a.fst * b.fst :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.acfef4a2c2bb from=seed src=0 shape=d31638f6 vocab=49cbcb86
-/
@[simp]
theorem mul_snd (a b : 𝓜(𝕜, A)) : (a * b).snd = b.snd * a.snd :=
  rfl

/--
@isnad1 id=eq.0h3v.s9.2215af7a531e from=seed src=0 shape=4e055f0b vocab=8e5f47c0
-/
theorem natCast_fst (n : ℕ) : (n : 𝓜(𝕜, A)).fst = n :=
  rfl

/--
@isnad1 id=eq.0h3v.s9.1728fb2028f4 from=seed src=0 shape=4e055f0b vocab=dd66893f
-/
theorem natCast_snd (n : ℕ) : (n : 𝓜(𝕜, A)).snd = n :=
  rfl

/--
@isnad1 id=eq.0h3v.s9.4f96e21fad6c from=seed src=0 shape=4e055f0b vocab=bed54046
-/
theorem intCast_fst (n : ℤ) : (n : 𝓜(𝕜, A)).fst = n :=
  rfl

/--
@isnad1 id=eq.0h3v.s9.16717b52063f from=seed src=0 shape=4e055f0b vocab=d1a4e67c
-/
theorem intCast_snd (n : ℤ) : (n : 𝓜(𝕜, A)).snd = n :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.7d0f935c35b4 from=seed src=0 shape=d31a09e7 vocab=e1112500
-/
theorem pow_fst (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).fst = a.fst ^ n :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.6508a84e1555 from=seed src=0 shape=d31a09e7 vocab=3025ec55
-/
theorem pow_snd (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).snd = a.snd ^ n :=
  rfl

/-- The natural injection from `DoubleCentralizer.toProd` except the second coordinate inherits
`MulOpposite.op`. The ring structure on `𝓜(𝕜, A)` is the pullback under this map. -/
def toProdMulOpposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ := fun a =>
  (a.fst, MulOpposite.op a.snd)

/--
@isnad1 id=injectiv.0h2v.s9.d62c00594f4b from=seed src=0 shape=f167d6f6 vocab=e6742e1a
-/
theorem toProdMulOpposite_injective :
    Function.Injective (toProdMulOpposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ) :=
  fun _a _b h =>
    let h' := Prod.ext_iff.mp h
    ext (𝕜 := 𝕜) (A := A) _ _ <| Prod.ext h'.1 <| MulOpposite.op_injective h'.2

/--
@isnad1 id=eq.0h2v.s11.1bd678441c54 from=seed src=0 shape=43de2521 vocab=12c2063b
-/
theorem range_toProdMulOpposite :
    Set.range toProdMulOpposite =
      { lr : (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ | ∀ x y, unop lr.2 x * y = x * lr.1 y } :=
  Set.ext fun x =>
    ⟨by
      rintro ⟨a, rfl⟩
      exact a.central, fun hx => ⟨⟨(x.1, unop x.2), hx⟩, Prod.ext rfl rfl⟩⟩

/-- The ring structure is inherited as the pullback under the injective map
`DoubleCentralizer.toProdMulOpposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ` -/
instance instRing : Ring 𝓜(𝕜, A) :=
  toProdMulOpposite_injective.ring _ rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _x _n => Prod.ext rfl <| MulOpposite.op_smul _ _)
    (fun _x _n => Prod.ext rfl <| MulOpposite.op_smul _ _)
    (fun _x _n => Prod.ext rfl <| MulOpposite.op_pow _ _) (fun _ => rfl) fun _ => rfl

/-- The canonical map `DoubleCentralizer.toProd` as an additive group homomorphism. -/
@[simps]
noncomputable def toProdHom : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A) where
  toFun := toProd
  map_zero' := rfl
  map_add' _x _y := rfl

/-- The canonical map `DoubleCentralizer.toProdMulOpposite` as a ring homomorphism. -/
@[simps]
def toProdMulOppositeHom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ where
  toFun := toProdMulOpposite
  map_zero' := rfl
  map_one' := rfl
  map_add' _x _y := rfl
  map_mul' _x _y := rfl

/-- The module structure is inherited as the pullback under the additive group monomorphism
`DoubleCentralizer.toProd : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A)` -/
noncomputable instance instModule {S : Type*} [Semiring S] [Module S A] [SMulCommClass 𝕜 S A]
    [ContinuousConstSMul S A] [IsScalarTower S A A] [SMulCommClass S A A] : Module S 𝓜(𝕜, A) :=
  Function.Injective.module S toProdHom (ext (𝕜 := 𝕜) (A := A)) fun _x _y => rfl

-- TODO: generalize to `Algebra S 𝓜(𝕜, A)` once `ContinuousLinearMap.algebra` is generalized.
instance instAlgebra : Algebra 𝕜 𝓜(𝕜, A) where
  algebraMap :=
  { toFun k :=
      { toProd := algebraMap 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A)) k
        central := fun x y => by
          simp_rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
            one_apply_eq_self, mul_smul_comm, smul_mul_assoc] }
    map_one' := ext (𝕜 := 𝕜) (A := A) _ _ <| map_one <| algebraMap 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A))
    map_mul' _ _ :=
      ext (𝕜 := 𝕜) (A := A) _ _ <|
        Prod.ext (map_mul (algebraMap 𝕜 (A →L[𝕜] A)) _ _)
          ((map_mul (algebraMap 𝕜 (A →L[𝕜] A)) _ _).trans (Algebra.commutes _ _))
    map_zero' := ext (𝕜 := 𝕜) (A := A) _ _ <| map_zero <| algebraMap 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A))
    map_add' _ _ := ext (𝕜 := 𝕜) (A := A) _ _ <|
      map_add (algebraMap 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A))) _ _ }
  commutes' _ _ := ext (𝕜 := 𝕜) (A := A) _ _ <|
    Prod.ext (Algebra.commutes _ _) (Algebra.commutes _ _).symm
  smul_def' _ _ := ext (𝕜 := 𝕜) (A := A) _ _ <|
    Prod.ext (Algebra.smul_def _ _) ((Algebra.smul_def _ _).trans <| Algebra.commutes _ _)

/--
@isnad1 id=eq.0h3v.s11.55903994e9ed from=seed src=0 shape=59955762 vocab=df01d58e
-/
@[simp]
theorem algebraMap_toProd (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).toProd = algebraMap 𝕜 _ k :=
  rfl

/--
@isnad1 id=eq.0h3v.s10.e8094da64e97 from=seed src=0 shape=a72dd5dc vocab=6d74715f
-/
theorem algebraMap_fst (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).fst = algebraMap 𝕜 _ k :=
  rfl

/--
@isnad1 id=eq.0h3v.s10.86d9a9c4f1a6 from=seed src=0 shape=a72dd5dc vocab=522bbb24
-/
theorem algebraMap_snd (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).snd = algebraMap 𝕜 _ k :=
  rfl

/-!
### Star structure
-/


section Star

variable [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A]

/-- The star operation on `a : 𝓜(𝕜, A)` is given by
`(star a).toProd = (star ∘ a.snd ∘ star, star ∘ a.fst ∘ star)`. -/
instance instStar : Star 𝓜(𝕜, A) where
  star a :=
    { fst :=
        (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp a.snd).comp
          ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A)
      snd :=
        (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp a.fst).comp
          ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A)
      central := fun x y => by
        simpa only [star_mul, star_star]
          using! (congr_arg star (a.central (star y) (star x))).symm }

/--
@isnad1 id=eq.0h4v.s10.47afd776230a from=seed src=0 shape=4806acbe vocab=6b79c357
-/
@[simp]
theorem star_fst (a : 𝓜(𝕜, A)) (b : A) : (star a).fst b = star (a.snd (star b)) :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.9afa35e1c0d2 from=seed src=0 shape=4806acbe vocab=6b79c357
-/
@[simp]
theorem star_snd (a : 𝓜(𝕜, A)) (b : A) : (star a).snd b = star (a.fst (star b)) :=
  rfl

instance instStarAddMonoid : StarAddMonoid 𝓜(𝕜, A) :=
  { DoubleCentralizer.instStar with
    star_involutive _ := by ext <;> simp
    star_add _ _ := by ext <;> simp }

instance instStarRing : StarRing 𝓜(𝕜, A) :=
  { DoubleCentralizer.instStarAddMonoid with
    star_mul _ _ := by ext <;> simp }

/--
@isnad1 id=starmodu.0h2v.s9.df205e788345 from=seed src=0 shape=f0665d0e vocab=18336094
-/
instance instStarModule : StarModule 𝕜 𝓜(𝕜, A) :=
  { DoubleCentralizer.instStarAddMonoid (𝕜 := 𝕜) (A := A) with
    star_smul _ _ := by ext <;> exact star_smul _ _ }

end Star

/-!
### Coercion from an algebra into its multiplier algebra
-/

variable (𝕜) in
/-- The natural coercion of `A` into `𝓜(𝕜, A)` given by sending `a : A` to the pair of linear
maps `Lₐ Rₐ : A →L[𝕜] A` given by left- and right-multiplication by `a`, respectively.

Warning: if `A = 𝕜`, then this is a coercion which is not definitionally equal to the
`algebraMap 𝕜 𝓜(𝕜, 𝕜)` coercion, but these are propositionally equal. See
`DoubleCentralizer.coe_eq_algebraMap` below. -/
@[coe]
protected noncomputable def coe (a : A) : 𝓜(𝕜, A) :=
  { fst := ContinuousLinearMap.mul 𝕜 A a
    snd := (ContinuousLinearMap.mul 𝕜 A).flip a
    central := fun _x _y => mul_assoc _ _ _ }

/-- The natural coercion of `A` into `𝓜(𝕜, A)` given by sending `a : A` to the pair of linear
maps `Lₐ Rₐ : A →L[𝕜] A` given by left- and right-multiplication by `a`, respectively.

Warning: if `A = 𝕜`, then this is a coercion which is not definitionally equal to the
`algebraMap 𝕜 𝓜(𝕜, 𝕜)` coercion, but these are propositionally equal. See
`DoubleCentralizer.coe_eq_algebraMap` below. -/
noncomputable instance : CoeTC A 𝓜(𝕜, A) where
  coe := DoubleCentralizer.coe 𝕜

/--
@isnad1 id=eq.0h3v.s10.6dd866df20e5 from=seed src=0 shape=c9454159 vocab=fc1e976a
-/
@[simp, norm_cast]
theorem coe_fst (a : A) : (a : 𝓜(𝕜, A)).fst = ContinuousLinearMap.mul 𝕜 A a :=
  rfl

/--
@isnad1 id=eq.0h3v.s10.91e72d11bf09 from=seed src=0 shape=b9f91b69 vocab=68aa1f6f
-/
@[simp, norm_cast]
theorem coe_snd (a : A) : (a : 𝓜(𝕜, A)).snd = (ContinuousLinearMap.mul 𝕜 A).flip a :=
  rfl

/--
@isnad1 id=eq.0h1v.s8.530138528d5c from=seed src=0 shape=f900bfdb vocab=2a342440
-/
theorem coe_eq_algebraMap : (DoubleCentralizer.coe 𝕜 : 𝕜 → 𝓜(𝕜, 𝕜)) = algebraMap 𝕜 𝓜(𝕜, 𝕜) := by
  ext x : 3
  · rfl -- `fst` is defeq
  · refine ContinuousLinearMap.ext fun y => ?_
    exact mul_comm y x  -- `snd` multiplies on the wrong side

/-- The coercion of an algebra into its multiplier algebra as a non-unital star algebra
homomorphism. -/
@[simps]
noncomputable def coeHom [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A] :
    A →⋆ₙₐ[𝕜] 𝓜(𝕜, A) where
  toFun a := a
  map_smul' _ _ := ext _ _ _ _ <| Prod.ext (map_smul _ _ _) (map_smul _ _ _)
  map_zero' := ext _ _ _ _ <| Prod.ext (map_zero _) (map_zero _)
  map_add' _ _ := ext _ _ _ _ <| Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_mul' _ _ := ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun _ => (mul_assoc _ _ _))
    (ContinuousLinearMap.ext fun _ => (mul_assoc _ _ _).symm)
  map_star' _ := ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun _ => (star_star_mul _ _).symm)
    (ContinuousLinearMap.ext fun _ => (star_mul_star _ _).symm)

/-!
### Norm structures
We define the norm structure on `𝓜(𝕜, A)` as the pullback under
`DoubleCentralizer.toProdMulOppositeHom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ`, which
provides a definitional isometric embedding. Consequently, completeness of `𝓜(𝕜, A)` is obtained
by proving that the range of this map is closed.

In addition, we prove that `𝓜(𝕜, A)` is a normed algebra, and, when `A` is a C⋆-algebra, we show
that `𝓜(𝕜, A)` is also a C⋆-algebra. Moreover, in this case, for `a : 𝓜(𝕜, A)`,
`‖a‖ = ‖a.fst‖ = ‖a.snd‖`. -/


/-- The normed group structure is inherited as the pullback under the ring monomorphism
`DoubleCentralizer.toProdMulOppositeHom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ`. -/
noncomputable instance : NormedRing 𝓜(𝕜, A) :=
  NormedRing.induced _ _ (toProdMulOppositeHom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ)
    (by simpa using! toProdMulOpposite_injective)

-- even though the definition is actually in terms of `DoubleCentralizer.toProdMulOpposite`, we
-- choose to see through that here to avoid `MulOpposite.op` appearing.
/--
@isnad1 id=eq.0h3v.s11.9c4af5ceff1b from=seed src=0 shape=15f3b73d vocab=68e207f6
-/
theorem norm_def (a : 𝓜(𝕜, A)) : ‖a‖ = ‖toProdHom a‖ :=
  rfl

/--
@isnad1 id=eq.0h3v.s11.e6399eaf8c81 from=seed src=0 shape=15f3b73d vocab=a78ef687
-/
theorem nnnorm_def (a : 𝓜(𝕜, A)) : ‖a‖₊ = ‖toProdHom a‖₊ :=
  rfl

/--
@isnad1 id=eq.0h3v.s11.c2f17145f0b8 from=seed src=0 shape=d11642e0 vocab=2f2eafe7
-/
theorem norm_def' (a : 𝓜(𝕜, A)) : ‖a‖ = ‖toProdMulOppositeHom a‖ :=
  rfl

/--
@isnad1 id=eq.0h3v.s11.f3bc6fd2b273 from=seed src=0 shape=d11642e0 vocab=7da60840
-/
theorem nnnorm_def' (a : 𝓜(𝕜, A)) : ‖a‖₊ = ‖toProdMulOppositeHom a‖₊ :=
  rfl

noncomputable instance instNormedSpace : NormedSpace 𝕜 𝓜(𝕜, A) :=
  { DoubleCentralizer.instModule with
    norm_smul_le := fun k a => (norm_smul_le k a.toProdMulOpposite :) }

noncomputable instance instNormedAlgebra : NormedAlgebra 𝕜 𝓜(𝕜, A) :=
  { DoubleCentralizer.instAlgebra, DoubleCentralizer.instNormedSpace with }

/--
@isnad1 id=isunifor.0h2v.s10.45856efce64f from=seed src=0 shape=f167d6f6 vocab=fa213bca
-/
theorem isUniformEmbedding_toProdMulOpposite :
    IsUniformEmbedding (toProdMulOpposite (𝕜 := 𝕜) (A := A)) :=
  isUniformEmbedding_comap toProdMulOpposite_injective

instance [CompleteSpace A] : CompleteSpace 𝓜(𝕜, A) := by
  rw [completeSpace_iff_isComplete_range isUniformEmbedding_toProdMulOpposite.isUniformInducing]
  apply IsClosed.isComplete
  simp only [range_toProdMulOpposite, Set.ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_eq (by fun_prop) (by fun_prop)

variable [StarRing A] [CStarRing A]

/-- For `a : 𝓜(𝕜, A)`, the norms of `a.fst` and `a.snd` coincide, and hence these
also coincide with `‖a‖` which is `max (‖a.fst‖) (‖a.snd‖)`.
@isnad1 id=eq.0h3v.s10.fbd8c70ad229 from=seed src=0 shape=749dbddf vocab=531ca59d
-/
theorem norm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fst‖ = ‖a.snd‖ := by
  -- a handy lemma for this proof
  have h0 : ∀ f : A →L[𝕜] A, ∀ C : ℝ≥0, (∀ b : A, ‖f b‖₊ ^ 2 ≤ C * ‖f b‖₊ * ‖b‖₊) → ‖f‖₊ ≤ C := by
    intro f C h
    have h1 b : C * ‖f b‖₊ * ‖b‖₊ ≤ C * ‖f‖₊ * ‖b‖₊ ^ 2 := by grw [f.le_opNNNorm b]; ring_nf; rfl
    have := NNReal.div_le_of_le_mul <| f.opNNNorm_le_bound _ <| by
      simpa only [sqrt_sq, sqrt_mul] using fun b ↦ sqrt_le_sqrt.2 <| (h b).trans (h1 b)
    convert! NNReal.rpow_le_rpow this two_pos.le
    · simp only [NNReal.rpow_two, div_pow, sq_sqrt]
      simp only [sq, mul_self_div_self]
    · simp only [NNReal.rpow_two, sq_sqrt]
  have h1 : ∀ b, ‖a.fst b‖₊ ^ 2 ≤ ‖a.snd‖₊ * ‖a.fst b‖₊ * ‖b‖₊ := by
    intro b
    calc
      ‖a.fst b‖₊ ^ 2 = ‖star (a.fst b) * a.fst b‖₊ := by
        simpa only [← sq] using CStarRing.nnnorm_star_mul_self.symm
      _ ≤ ‖a.snd (star (a.fst b))‖₊ * ‖b‖₊ := (a.central (star (a.fst b)) b ▸ nnnorm_mul_le _ _)
      _ ≤ ‖a.snd‖₊ * ‖a.fst b‖₊ * ‖b‖₊ :=
        nnnorm_star (a.fst b) ▸ mul_le_mul_left (a.snd.le_opNNNorm _) _
  have h2 : ∀ b, ‖a.snd b‖₊ ^ 2 ≤ ‖a.fst‖₊ * ‖a.snd b‖₊ * ‖b‖₊ := by
    intro b
    calc
      ‖a.snd b‖₊ ^ 2 = ‖a.snd b * star (a.snd b)‖₊ := by
        simpa only [← sq] using CStarRing.nnnorm_self_mul_star.symm
      _ ≤ ‖b‖₊ * ‖a.fst (star (a.snd b))‖₊ :=
        ((a.central b (star (a.snd b))).symm ▸ nnnorm_mul_le _ _)
      _ = ‖a.fst (star (a.snd b))‖₊ * ‖b‖₊ := mul_comm _ _
      _ ≤ ‖a.fst‖₊ * ‖a.snd b‖₊ * ‖b‖₊ :=
        nnnorm_star (a.snd b) ▸ mul_le_mul_left (a.fst.le_opNNNorm _) _
  exact le_antisymm (h0 _ _ h1) (h0 _ _ h2)

/--
@isnad1 id=eq.0h3v.s10.d9b96ee2aaaf from=seed src=0 shape=749dbddf vocab=18ae6ba4
-/
theorem nnnorm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fst‖₊ = ‖a.snd‖₊ :=
  Subtype.ext <| norm_fst_eq_snd a

/--
@isnad1 id=eq.0h3v.s9.dc2b72fc6a10 from=seed src=0 shape=89a9bba1 vocab=7518f328
-/
@[simp]
theorem norm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖ = ‖a‖ := by
  simp only [norm_def, toProdHom_apply, Prod.norm_def, norm_fst_eq_snd, max_eq_right le_rfl]

/--
@isnad1 id=eq.0h3v.s9.9d4a4c2bcc6b from=seed src=0 shape=89a9bba1 vocab=4c03950c
-/
@[simp]
theorem norm_snd (a : 𝓜(𝕜, A)) : ‖a.snd‖ = ‖a‖ := by rw [← norm_fst, norm_fst_eq_snd]

/--
@isnad1 id=eq.0h3v.s9.7c46fe227ef1 from=seed src=0 shape=89a9bba1 vocab=846475a4
-/
@[simp]
theorem nnnorm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖₊ = ‖a‖₊ :=
  Subtype.ext (norm_fst a)

/--
@isnad1 id=eq.0h3v.s9.5cc738032dce from=seed src=0 shape=89a9bba1 vocab=f625fcb9
-/
@[simp]
theorem nnnorm_snd (a : 𝓜(𝕜, A)) : ‖a.snd‖₊ = ‖a‖₊ :=
  Subtype.ext (norm_snd a)

end NontriviallyNormed

section DenselyNormed

variable {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜]
variable [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
variable [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [StarModule 𝕜 A]

/--
@isnad1 id=cstarrin.0h2v.s9.b78663fc7035 from=seed src=0 shape=a5f25b27 vocab=29a42d47
-/
instance instCStarRing : CStarRing 𝓜(𝕜, A) where
  norm_mul_self_le := fun (a : 𝓜(𝕜, A)) => le_of_eq <| Eq.symm <| congr_arg ((↑) : ℝ≥0 → ℝ) <|
    show ‖star a * a‖₊ = ‖a‖₊ * ‖a‖₊ by
    /- The essence of the argument is this: let `a = (L,R)` and recall `‖a‖ = ‖L‖`.
    `star a = (star ∘ R ∘ star, star ∘ L ∘ star)`. Then for any `x y : A`, we have
    `‖star a * a‖ = ‖(star a * a).snd‖ = ‖R (star (L (star x))) * y‖ = ‖star (L (star x)) * L y‖`
    Now, on the one hand,
    `‖star (L (star x)) * L y‖ ≤ ‖star (L (star x))‖ * ‖L y‖ = ‖L (star x)‖ * ‖L y‖ ≤ ‖L‖ ^ 2`
    whenever `‖x‖, ‖y‖ ≤ 1`, so the supremum over all such `x, y` is at most `‖L‖ ^ 2`.
    On the other hand, for any `‖z‖ ≤ 1`, we may choose `x := star z` and `y := z` to get:
    `‖star (L (star x)) * L y‖ = ‖star (L z) * (L z)‖ = ‖L z‖ ^ 2`, and taking the supremum over
    all such `z` yields that the supremum is at least `‖L‖ ^ 2`. It is the latter part of the
    argument where `DenselyNormedField 𝕜` is required (for `sSup_unitClosedBall_eq_nnnorm`). -/
      have hball : (Metric.closedBall (0 : A) 1).Nonempty :=
        Metric.nonempty_closedBall.2 zero_le_one
      have key :
        ∀ x y, ‖x‖₊ ≤ 1 → ‖y‖₊ ≤ 1 → ‖a.snd (star (a.fst (star x))) * y‖₊ ≤ ‖a‖₊ * ‖a‖₊ := by
        intro x y hx hy
        rw [a.central]
        calc
          ‖star (a.fst (star x)) * a.fst y‖₊ ≤ ‖a.fst (star x)‖₊ * ‖a.fst y‖₊ :=
            nnnorm_star (a.fst (star x)) ▸ nnnorm_mul_le _ _
          _ ≤ ‖a.fst‖₊ * 1 * (‖a.fst‖₊ * 1) :=
            (mul_le_mul' (a.fst.le_opNorm_of_le ((nnnorm_star x).trans_le hx))
              (a.fst.le_opNorm_of_le hy))
          _ ≤ ‖a‖₊ * ‖a‖₊ := by simp only [mul_one, nnnorm_fst, le_rfl]
      rw [← nnnorm_snd]
      simp only [mul_snd, ← sSup_unitClosedBall_eq_nnnorm, star_snd, mul_apply_eq_comp]
      simp only [← @opNNNorm_mul_apply 𝕜 _ A]
      simp only [← sSup_unitClosedBall_eq_nnnorm, mul_apply']
      refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (hball.image _) ?_ fun r hr => ?_
      · rintro - ⟨x, hx, rfl⟩
        refine csSup_le (hball.image _) ?_
        rintro - ⟨y, hy, rfl⟩
        exact key x y (mem_closedBall_zero_iff.1 hx) (mem_closedBall_zero_iff.1 hy)
      · simp only [Set.mem_image, exists_exists_and_eq_and]
        have hr' : NNReal.sqrt r < ‖a‖₊ := ‖a‖₊.sqrt_mul_self ▸ NNReal.sqrt_lt_sqrt.2 hr
        simp_rw [← nnnorm_fst, ← sSup_unitClosedBall_eq_nnnorm] at hr'
        obtain ⟨_, ⟨x, hx, rfl⟩, hxr⟩ := exists_lt_of_lt_csSup (hball.image _) hr'
        have hx' : ‖x‖₊ ≤ 1 := mem_closedBall_zero_iff.1 hx
        refine ⟨star x, mem_closedBall_zero_iff.2 ((nnnorm_star x).trans_le hx'), ?_⟩
        refine lt_csSup_of_lt ?_ ⟨x, hx, rfl⟩ ?_
        · refine ⟨‖a‖₊ * ‖a‖₊, ?_⟩
          rintro - ⟨y, hy, rfl⟩
          exact key (star x) y ((nnnorm_star x).trans_le hx') (mem_closedBall_zero_iff.1 hy)
        · simpa [a.central, CStarRing.nnnorm_star_mul_self, ← sq]
            using pow_lt_pow_left₀ hxr zero_le two_ne_zero

end DenselyNormed

noncomputable instance {A : Type*} [NonUnitalCStarAlgebra A] : CStarAlgebra 𝓜(ℂ, A) where

end DoubleCentralizer
