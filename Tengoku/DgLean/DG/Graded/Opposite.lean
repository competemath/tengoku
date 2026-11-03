import Tengoku.Seed.LinearAlgebra.TensorProduct.Basic
import Tengoku.Seed.LinearAlgebra.TensorProduct.Graded.External
import Tengoku.Seed.RingTheory.GradedAlgebra.Basic
import Tengoku.Seed.Tactic.SuppressCompilation
import Tengoku.DgLean.DG.Graded.Commutative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The graded opposite algebra

For a `ℤ`-graded `R`-algebra `A` with grading `𝒜 : ℤ → Submodule R A`, the graded opposite
algebra `DG.GradedOpposite 𝒜` is `A` with the same addition and `R`-action and with the signed
opposite product: for homogeneous `a ∈ 𝒜 i` and `b ∈ 𝒜 j`,
  `op a * op b = koszulSign (i * j) • op (b * a)`,
extended bilinearly to all elements. It carries the same grading (`GradedOpposite.grading 𝒜`,
whose degree-`i` piece is the image of `𝒜 i` under `op`), for which it is again a graded algebra.

## Main definitions and results

* `DG.GradedOpposite 𝒜`: the type synonym, with `Ring`, `Algebra R` and `GradedAlgebra`
  instances.
* `DG.GradedOpposite.op`, `DG.GradedOpposite.unop`: the `R`-linear equivalences with `A`.
* `DG.GradedOpposite.op_mul_op`: the product formula on homogeneous elements.
* `DG.GradedOpposite.opOpAlgEquiv`: the graded algebra isomorphism `(𝒜ᵒᵖ)ᵒᵖ ≃ₐ[R] A`, which
  preserves degrees (`DG.GradedOpposite.opOpAlgEquiv_mem_iff`).
* `DG.isGradedComm_iff_op_mul`: `𝒜` is graded commutative iff `op` is multiplicative, and
  `DG.GradedOpposite.opAlgEquiv`: for graded commutative `𝒜`, `op` as an algebra isomorphism.

## Implementation notes

`GradedOpposite 𝒜` is a type synonym of `A` rather than of `Aᵐᵒᵖ`: the identity of `A` is then
the linear equivalence `op`, the grading is (the image under `op` of) the same family of
submodules, and the sign twist lives entirely in the multiplication. (The alternative, `Aᵐᵒᵖ`
with the product twisted by the signs `(-1)^(i * (i - 1) / 2)`, hides the Koszul sign inside
`op` instead, which makes every homogeneous formula carry that twist.)

The product on general elements is defined through the decomposition into homogeneous
components, following the construction of `GradedTensorProduct` in Mathlib: on the external
direct sum `⨁ i, 𝒜 i` the signed opposite product is `mul' ∘ gradedComm`, where
`TensorProduct.gradedComm` is Mathlib's Koszul-signed braiding, and this bilinear map is
transported to `A` along `DirectSum.decomposeLinearEquiv 𝒜` (`GradedOpposite.mulHom`, a
bilinear map on `A`). The `Ring` instance on the synonym is then a single structure, so that
every algebraic instance on `GradedOpposite 𝒜` is a projection of one term; this keeps the
iterated opposite `GradedOpposite (grading 𝒜)` cheap to work with.
-/

suppress_compilation

open DirectSum TensorProduct

namespace DG

/-- Additive maps commute with the Koszul sign action.
@isnad1 id=eq.0h6v.s6.86324df49315 from=translated src=- shape=1831e539 vocab=627f76d3
-/
theorem map_koszulSign_smul {F M N : Type*} [AddCommGroup M] [AddCommGroup N] [FunLike F M N]
    [AddMonoidHomClass F M N] (f : F) (n : ℤ) (x : M) :
    f (koszulSign n • x) = koszulSign n • f x := by
  rw [Units.smul_def, map_zsmul, Units.smul_def]

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

namespace GradedOpposite

/- Instance search no longer finds the additive group structures on these types (the
`AddCommMonoid` found for `⨁ i, 𝒜 i` must be unified with an `AddCommGroup` projection);
supply them explicitly. -/
local instance : AddCommGroup ((⨁ i, 𝒜 i) ⊗[R] (⨁ i, 𝒜 i)) :=
  @TensorProduct.addCommGroup R _ (⨁ i, 𝒜 i) (⨁ i, 𝒜 i) _ _ _ _

local instance : AddCommGroup ((⨁ i, 𝒜 i) →ₗ[R] (⨁ i, 𝒜 i)) :=
  @LinearMap.addCommGroup R R (⨁ i, 𝒜 i) (⨁ i, 𝒜 i) _ _ _ _ _ _ _

/-! ### The signed opposite product on the external direct sum -/

/-- Auxiliary construction: the signed opposite product on the external direct sum
`⨁ i, 𝒜 i`, sending `lof i a ⊗ lof j b` to `koszulSign (i * j) • (lof j b * lof i a)`.-/
def mulAux : (⨁ i, 𝒜 i) →ₗ[R] (⨁ i, 𝒜 i) →ₗ[R] (⨁ i, 𝒜 i) :=
  TensorProduct.curry
    (LinearMap.mul' R (⨁ i, 𝒜 i) ∘ₗ (gradedComm R (𝒜 ·) (𝒜 ·)).toLinearMap)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h7v.s14.e8067420ef48 from=translated src=- shape=42deca0d vocab=520c4472
-/
theorem mulAux_lof_lof (i j : ℤ) (a : 𝒜 i) (b : 𝒜 j) :
    mulAux 𝒜 (lof R ℤ (𝒜 ·) i a) (lof R ℤ (𝒜 ·) j b) =
      koszulSign (i * j) • (lof R ℤ (𝒜 ·) j b * lof R ℤ (𝒜 ·) i a) := by
  rw [mulAux, curry_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, gradedComm_of_tmul_of,
    mul_comm j i, Units.smul_def, map_zsmul, LinearMap.mul'_apply]
  rfl

/--
@isnad1 id=eq.0h7v.s14.d31b54ab6a97 from=translated src=- shape=4ed003b5 vocab=d2023922
-/
theorem mulAux_of_of (i j : ℤ) (a : 𝒜 i) (b : 𝒜 j) :
    mulAux 𝒜 (of (𝒜 ·) i a) (of (𝒜 ·) j b) =
      koszulSign (i * j) • (of (𝒜 ·) j b * of (𝒜 ·) i a) :=
  mulAux_lof_lof 𝒜 i j a b

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h6v.s14.4e9062882f42 from=translated src=- shape=f9bb9cc1 vocab=4ffb685f
-/
theorem mulAux_smul_left (s : ℤ) (x y : ⨁ i, 𝒜 i) :
    mulAux 𝒜 (koszulSign s • x) y = koszulSign s • mulAux 𝒜 x y := by
  rw [Units.smul_def, map_zsmul, LinearMap.smul_apply, Units.smul_def]

/--
@isnad1 id=eq.0h6v.s14.26fff11ecf69 from=translated src=- shape=c9396d29 vocab=4ffb685f
-/
theorem mulAux_smul_right (s : ℤ) (x y : ⨁ i, 𝒜 i) :
    mulAux 𝒜 x (koszulSign s • y) = koszulSign s • mulAux 𝒜 x y := by
  rw [Units.smul_def, map_zsmul, Units.smul_def]

/--
@isnad1 id=eq.0h4v.s13.91961d46636e from=translated src=- shape=d87f260b vocab=5e0cbcdb
-/
theorem mulAux_one (x : ⨁ i, 𝒜 i) : mulAux 𝒜 x 1 = x := by
  suffices (mulAux 𝒜).flip 1 = LinearMap.id from DFunLike.congr_fun this x
  refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun a => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, LinearMap.id_coe,
    id_eq]
  rw [DirectSum.one_def, lof_eq_of, mulAux_of_of, mul_zero, koszulSign_zero, one_smul,
    ← DirectSum.one_def, one_mul]

/--
@isnad1 id=eq.0h4v.s13.26deee0b77bc from=translated src=- shape=e7cb114f vocab=5e0cbcdb
-/
theorem one_mulAux (x : ⨁ i, 𝒜 i) : mulAux 𝒜 1 x = x := by
  suffices mulAux 𝒜 1 = LinearMap.id from DFunLike.congr_fun this x
  refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun a => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  rw [DirectSum.one_def, lof_eq_of, mulAux_of_of, zero_mul, koszulSign_zero, one_smul,
    ← DirectSum.one_def, mul_one]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h6v.s15.d132c490a17d from=translated src=- shape=7331fb85 vocab=acfeacb0
-/
theorem mulAux_assoc (x y z : ⨁ i, 𝒜 i) :
    mulAux 𝒜 (mulAux 𝒜 x y) z = mulAux 𝒜 x (mulAux 𝒜 y z) := by
  let m := mulAux 𝒜
  suffices LinearMap.llcomp R _ _ _ m ∘ₗ m =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ m.flip ∘ₗ m).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext i a j b k c : 6
  simp only [m, LinearMap.coe_comp, Function.comp_apply, LinearMap.llcomp_apply,
    LinearMap.flip_apply, LinearEquiv.coe_coe, LinearMap.lflip_apply, lof_eq_of, mulAux_of_of,
    mulAux_smul_left, mulAux_smul_right, DirectSum.of_mul_of]
  simp only [← DirectSum.of_mul_of, smul_smul, ← koszulSign_add, mul_assoc]
  rw [show i * j + (j + i) * k = j * k + i * (k + j) by ring]

/-! ### The signed opposite product on `A` -/

/-- The signed opposite product, as a bilinear map on `A`: the product `mulAux` transported
along the decomposition `A ≃ₗ[R] ⨁ i, 𝒜 i`. This is the multiplication of
`GradedOpposite 𝒜`.-/
def mulHom : A →ₗ[R] A →ₗ[R] A :=
  ((mulAux 𝒜).compl₁₂ (decomposeLinearEquiv 𝒜 : A →ₗ[R] ⨁ i, 𝒜 i)
    (decomposeLinearEquiv 𝒜 : A →ₗ[R] ⨁ i, 𝒜 i)).compr₂
    ((decomposeLinearEquiv 𝒜).symm : (⨁ i, 𝒜 i) →ₗ[R] A)

/--
@isnad1 id=eq.0h5v.s13.aca768062882 from=translated src=- shape=fd518a26 vocab=85d6a47f
-/
theorem mulHom_apply (a b : A) :
    mulHom 𝒜 a b = (decompose 𝒜).symm (mulAux 𝒜 (decompose 𝒜 a) (decompose 𝒜 b)) := rfl

/--
@isnad1 id=eq.0h5v.s13.7e3b9deaca22 from=translated src=- shape=987564fc vocab=23317448
-/
theorem decompose_mulHom (a b : A) :
    decompose 𝒜 (mulHom 𝒜 a b) = mulAux 𝒜 (decompose 𝒜 a) (decompose 𝒜 b) := by
  rw [mulHom_apply, Equiv.apply_symm_apply]

/--
@isnad1 id=eq.0h4v.s9.e6c179856644 from=translated src=- shape=763cf356 vocab=30459ebd
-/
theorem mulHom_one (a : A) : mulHom 𝒜 a 1 = a := by
  rw [mulHom_apply, decompose_one, mulAux_one, Equiv.symm_apply_apply]

/--
@isnad1 id=eq.0h4v.s9.f568d24fb5ec from=translated src=- shape=b7f97b33 vocab=30459ebd
-/
theorem one_mulHom (a : A) : mulHom 𝒜 1 a = a := by
  rw [mulHom_apply, decompose_one, one_mulAux, Equiv.symm_apply_apply]

/--
@isnad1 id=eq.0h6v.s11.6b38ec002ca8 from=translated src=- shape=485ea6e4 vocab=30459ebd
-/
theorem mulHom_assoc (a b c : A) :
    mulHom 𝒜 (mulHom 𝒜 a b) c = mulHom 𝒜 a (mulHom 𝒜 b c) := by
  simp only [mulHom_apply, Equiv.apply_symm_apply]
  rw [mulAux_assoc]

/-- The signed opposite product of two homogeneous elements.
@isnad1 id=eq.2h7v.s9.51ec326cf5f0 from=translated src=- shape=ebc034dc vocab=6a2f2fe5
-/
theorem mulHom_of_mem {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) :
    mulHom 𝒜 a b = koszulSign (i * j) • (b * a) := by
  rw [mulHom_apply, decompose_of_mem 𝒜 ha, decompose_of_mem 𝒜 hb, mulAux_of_of, Units.smul_def,
    ← decomposeLinearEquiv_symm_apply, map_zsmul, decomposeLinearEquiv_symm_apply,
    decompose_symm_mul, decompose_symm_of, decompose_symm_of, Units.smul_def]

end GradedOpposite

/-- The graded opposite algebra of a `ℤ`-graded algebra: a type synonym of `A` with the product
`op a * op b = koszulSign (i * j) • op (b * a)` on homogeneous elements of degrees `i` and `j`.-/
@[nolint unusedArguments]
def GradedOpposite (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] : Type _ := A

namespace GradedOpposite

set_option backward.isDefEq.respectTransparency false in
instance instRing : Ring (GradedOpposite 𝒜) where
  __ := (inferInstance : AddCommGroupWithOne A)
  mul x y := mulHom 𝒜 x y
  mul_assoc := mulHom_assoc 𝒜
  one_mul := one_mulHom 𝒜
  mul_one := mulHom_one 𝒜
  left_distrib x y z := LinearMap.map_add (mulHom 𝒜 x) y z
  right_distrib x y z := LinearMap.map_add₂ (mulHom 𝒜) x y z
  zero_mul x := LinearMap.map_zero₂ (mulHom 𝒜) x
  mul_zero x := LinearMap.map_zero (mulHom 𝒜 x)

set_option backward.isDefEq.respectTransparency false in
/-- The `R`-algebra structure of `GradedOpposite 𝒜`. The `R`-module structure is that of `A`;
it is only available through this instance (as `Algebra.toModule`), so that there is a single
`Module R (GradedOpposite 𝒜)` instance.-/
instance instAlgebra : Algebra R (GradedOpposite 𝒜) :=
  @Algebra.ofModule R (GradedOpposite 𝒜) _ _ (inferInstanceAs (Module R A))
    (fun r x y => LinearMap.map_smul₂ (mulHom 𝒜) r x y)
    (fun r x y => LinearMap.map_smul (mulHom 𝒜 x) r y)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical `R`-linear equivalence `A ≃ₗ[R] GradedOpposite 𝒜`.-/
def op : A ≃ₗ[R] GradedOpposite 𝒜 := LinearEquiv.refl R A

set_option backward.isDefEq.respectTransparency false in
/-- The canonical `R`-linear equivalence `GradedOpposite 𝒜 ≃ₗ[R] A`.-/
def unop : GradedOpposite 𝒜 ≃ₗ[R] A := LinearEquiv.refl R A

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s8.30985c6a8818 from=translated src=- shape=1ecd1ad2 vocab=1d48ac31
-/
@[simp] theorem op_symm : (op 𝒜).symm = unop 𝒜 := rfl
/--
@isnad1 id=eq.0h3v.s8.f75bf04d845e from=translated src=- shape=19daab84 vocab=1d48ac31
-/
@[simp] theorem unop_symm : (unop 𝒜).symm = op 𝒜 := rfl
/--
@isnad1 id=eq.0h4v.s9.d3dc274f974b from=translated src=- shape=552b5e6c vocab=f522d290
-/
@[simp] theorem unop_op (a : A) : unop 𝒜 (op 𝒜 a) = a := rfl
/--
@isnad1 id=eq.0h4v.s9.4c7aa9e8fa96 from=translated src=- shape=06cc6e2e vocab=f522d290
-/
@[simp] theorem op_unop (x : GradedOpposite 𝒜) : op 𝒜 (unop 𝒜 x) = x := rfl
/--
@isnad1 id=eq.0h3v.s9.fa40b886651f from=translated src=- shape=ced98890 vocab=9e84917d
-/
@[simp] theorem op_one : op 𝒜 (1 : A) = 1 := rfl
/--
@isnad1 id=eq.0h3v.s9.73ab2682093d from=translated src=- shape=0aafdcf0 vocab=58dcd30a
-/
@[simp] theorem unop_one : unop 𝒜 (1 : GradedOpposite 𝒜) = 1 := rfl

/--
@isnad1 id=injectiv.0h3v.s8.bc3e809db7f9 from=translated src=- shape=222420b0 vocab=27bfd09c
-/
theorem unop_injective : Function.Injective (unop 𝒜) := (unop 𝒜).injective

set_option backward.isDefEq.respectTransparency false in
/-- Two linear maps out of `GradedOpposite 𝒜` agree if they agree after composing with `op`.
@isnad1 id=eq.1h6v.s9.b8c0d9a67724 from=translated src=- shape=fa095b44 vocab=9bcfb1da
-/
@[ext]
theorem hom_ext {M : Type*} [AddCommMonoid M] [Module R M] ⦃f g : GradedOpposite 𝒜 →ₗ[R] M⦄
    (h : f ∘ₗ (op 𝒜).toLinearMap = g ∘ₗ (op 𝒜).toLinearMap) : f = g :=
  h

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s10.c09538b1c4a8 from=translated src=- shape=83b640a5 vocab=88da6489
-/
theorem unop_mul' (x y : GradedOpposite 𝒜) : unop 𝒜 (x * y) = mulHom 𝒜 (unop 𝒜 x) (unop 𝒜 y) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s10.6c3924a9d987 from=translated src=- shape=322a8b8e vocab=208f61f3
-/
theorem op_mul' (a b : A) : op 𝒜 a * op 𝒜 b = op 𝒜 (mulHom 𝒜 a b) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s9.95483dc91131 from=translated src=- shape=0bdfc745 vocab=01ffadf0
-/
theorem algebraMap_def (r : R) :
    algebraMap R (GradedOpposite 𝒜) r = op 𝒜 (algebraMap R A r) := by
  change r • (1 : GradedOpposite 𝒜) = op 𝒜 (algebraMap R A r)
  rw [Algebra.algebraMap_eq_smul_one, map_smul, op_one]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s9.cd511200d116 from=translated src=- shape=cf081470 vocab=01ffadf0
-/
@[simp] theorem op_algebraMap (r : R) :
    op 𝒜 (algebraMap R A r) = algebraMap R (GradedOpposite 𝒜) r := (algebraMap_def 𝒜 r).symm

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s9.5ddd5a611745 from=translated src=- shape=603b7714 vocab=8395f415
-/
@[simp] theorem unop_algebraMap (r : R) :
    unop 𝒜 (algebraMap R (GradedOpposite 𝒜) r) = algebraMap R A r := by
  rw [algebraMap_def, unop_op]

set_option backward.isDefEq.respectTransparency false in
/-- The product of two homogeneous elements of the graded opposite algebra.
@isnad1 id=eq.2h7v.s10.edf0134a3616 from=translated src=- shape=fb944793 vocab=f41eb7da
-/
theorem op_mul_op {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) :
    op 𝒜 a * op 𝒜 b = koszulSign (i * j) • op 𝒜 (b * a) := by
  rw [op_mul', mulHom_of_mem 𝒜 ha hb, Units.smul_def, map_zsmul, Units.smul_def]

/-! ### The grading -/

set_option backward.isDefEq.respectTransparency false in
/-- The grading of the graded opposite algebra: the degree-`i` piece is the image of `𝒜 i`
under `op`.-/
def grading (i : ℤ) : Submodule R (GradedOpposite 𝒜) :=
  (𝒜 i).map (op 𝒜 : A →ₗ[R] GradedOpposite 𝒜)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=iff.0h5v.s9.0ca36d3cf955 from=translated src=- shape=47c49f79 vocab=946a06c6
-/
theorem mem_grading_iff {i : ℤ} {x : GradedOpposite 𝒜} : x ∈ grading 𝒜 i ↔ unop 𝒜 x ∈ 𝒜 i :=
  Submodule.mem_map_equiv (𝒜 i)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=iff.0h5v.s9.ed3f40871b96 from=translated src=- shape=c45c1a37 vocab=07708cbe
-/
theorem op_mem_grading_iff {i : ℤ} {a : A} : op 𝒜 a ∈ grading 𝒜 i ↔ a ∈ 𝒜 i :=
  mem_grading_iff 𝒜

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=mem.1h5v.s9.1a1f93cdc0de from=translated src=- shape=b1d5db0a vocab=07708cbe
-/
theorem op_mem_grading {i : ℤ} {a : A} (ha : a ∈ 𝒜 i) : op 𝒜 a ∈ grading 𝒜 i :=
  (op_mem_grading_iff 𝒜).mpr ha

set_option backward.isDefEq.respectTransparency false in
/-- The product of two homogeneous elements of the graded opposite algebra, in terms of
`unop`.
@isnad1 id=eq.2h7v.s10.c8fb39b79d66 from=translated src=- shape=6bfcba1c vocab=dc79b6f5
-/
theorem unop_mul {i j : ℤ} {x y : GradedOpposite 𝒜} (hx : x ∈ grading 𝒜 i)
    (hy : y ∈ grading 𝒜 j) :
    unop 𝒜 (x * y) = koszulSign (i * j) • (unop 𝒜 y * unop 𝒜 x) := by
  rw [unop_mul', mulHom_of_mem 𝒜 ((mem_grading_iff 𝒜).mp hx) ((mem_grading_iff 𝒜).mp hy)]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=gradedmo.0h3v.s8.473fa9db8ef3 from=translated src=- shape=19a043de vocab=60263e79
-/
instance instGradedMonoid : SetLike.GradedMonoid (grading 𝒜) where
  one_mem := op_mem_grading 𝒜 (SetLike.one_mem_graded 𝒜)
  mul_mem {i j} x y hx hy := by
    rw [mem_grading_iff, unop_mul 𝒜 hx hy, Units.smul_def, add_comm]
    exact zsmul_mem
      (SetLike.mul_mem_graded ((mem_grading_iff 𝒜).mp hy) ((mem_grading_iff 𝒜).mp hx)) _

set_option backward.isDefEq.respectTransparency false in
/-- The degree-`i` piece of the opposite grading is `𝒜 i`, via `op`.-/
def gradingEquiv (i : ℤ) : 𝒜 i ≃ₗ[R] grading 𝒜 i := (op 𝒜).submoduleMap (𝒜 i)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s11.1da7c14f1170 from=translated src=- shape=97b956d6 vocab=82e6b9be
-/
@[simp] theorem coe_gradingEquiv {i : ℤ} (a : 𝒜 i) :
    (gradingEquiv 𝒜 i a : GradedOpposite 𝒜) = op 𝒜 a := rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s12.a320c405b2b6 from=translated src=- shape=793bace0 vocab=22a3469b
-/
@[simp] theorem coe_gradingEquiv_symm {i : ℤ} (x : grading 𝒜 i) :
    ((gradingEquiv 𝒜 i).symm x : A) = unop 𝒜 x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The direct sum of the `gradingEquiv 𝒜 i`.-/
def toGrading : (⨁ i, 𝒜 i) →ₗ[R] ⨁ i, grading 𝒜 i :=
  DirectSum.toModule R ℤ _ fun i => lof R ℤ (grading 𝒜 ·) i ∘ₗ (gradingEquiv 𝒜 i).toLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- The direct sum of the `(gradingEquiv 𝒜 i).symm`.-/
def ofGrading : (⨁ i, grading 𝒜 i) →ₗ[R] ⨁ i, 𝒜 i :=
  DirectSum.toModule R ℤ _ fun i => lof R ℤ (𝒜 ·) i ∘ₗ (gradingEquiv 𝒜 i).symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s13.bc7b7e3a0038 from=translated src=- shape=7e895299 vocab=34e7103f
-/
@[simp] theorem toGrading_lof (i : ℤ) (a : 𝒜 i) :
    toGrading 𝒜 (lof R ℤ (𝒜 ·) i a) = lof R ℤ (grading 𝒜 ·) i (gradingEquiv 𝒜 i a) := by
  unfold toGrading; rw [DirectSum.toModule_lof]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s13.5cf8a46cf7ab from=translated src=- shape=8dd6a24c vocab=eb73c08d
-/
@[simp] theorem ofGrading_lof (i : ℤ) (x : grading 𝒜 i) :
    ofGrading 𝒜 (lof R ℤ (grading 𝒜 ·) i x) = lof R ℤ (𝒜 ·) i ((gradingEquiv 𝒜 i).symm x) := by
  unfold ofGrading; rw [DirectSum.toModule_lof]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s11.21e4b83b4e8b from=translated src=- shape=d2f897bc vocab=72de086b
-/
theorem coeLinearMap_comp_toGrading :
    coeLinearMap (grading 𝒜) ∘ₗ toGrading 𝒜 =
      (op 𝒜 : A →ₗ[R] GradedOpposite 𝒜) ∘ₗ coeLinearMap 𝒜 := by
  refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun a => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    toGrading_lof, lof_eq_of, lof_eq_of, coeLinearMap_of, coeLinearMap_of, coe_gradingEquiv,
    LinearEquiv.coe_coe]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s12.a535968f5975 from=translated src=- shape=098d97dd vocab=de370348
-/
theorem coeLinearMap_comp_ofGrading :
    coeLinearMap 𝒜 ∘ₗ ofGrading 𝒜 =
      (unop 𝒜 : GradedOpposite 𝒜 →ₗ[R] A) ∘ₗ coeLinearMap (grading 𝒜) := by
  refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    ofGrading_lof, lof_eq_of, lof_eq_of, coeLinearMap_of, coeLinearMap_of, coe_gradingEquiv_symm,
    LinearEquiv.coe_coe]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s12.1a5066ee7a5f from=translated src=- shape=31c60a4f vocab=96542487
-/
theorem toGrading_comp_ofGrading : toGrading 𝒜 ∘ₗ ofGrading 𝒜 = LinearMap.id := by
  refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, ofGrading_lof,
    toGrading_lof, LinearEquiv.apply_symm_apply, LinearMap.id_apply]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s13.6896bc639fa7 from=translated src=- shape=cc1eefec vocab=59fc1ad9
-/
theorem coeLinearMap_toGrading (y : ⨁ i, 𝒜 i) :
    coeLinearMap (grading 𝒜) (toGrading 𝒜 y) = op 𝒜 (coeLinearMap 𝒜 y) :=
  LinearMap.congr_fun (coeLinearMap_comp_toGrading 𝒜) y

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s13.03fb1eaf973f from=translated src=- shape=e0c5ba3a vocab=9eb46b03
-/
theorem unop_coeLinearMap (z : ⨁ i, grading 𝒜 i) :
    unop 𝒜 (coeLinearMap (grading 𝒜) z) = coeLinearMap 𝒜 (ofGrading 𝒜 z) :=
  (LinearMap.congr_fun (coeLinearMap_comp_ofGrading 𝒜) z).symm

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s13.e655b6da9429 from=translated src=- shape=afc57b71 vocab=4dd51d4b
-/
theorem toGrading_ofGrading (z : ⨁ i, grading 𝒜 i) : toGrading 𝒜 (ofGrading 𝒜 z) = z :=
  LinearMap.congr_fun (toGrading_comp_ofGrading 𝒜) z

/-- `DirectSum.coeLinearMap` is the inverse of the decomposition.-/
theorem _root_.DirectSum.coeLinearMap_eq_decomposeLinearEquiv_symm :
    coeLinearMap 𝒜 = ((decomposeLinearEquiv 𝒜).symm : (⨁ i, 𝒜 i) →ₗ[R] A) :=
  DirectSum.linearMap_ext _ fun i => by
    rw [decomposeLinearEquiv_symm_comp_lof]
    exact LinearMap.ext fun a => by
      rw [LinearMap.comp_apply, lof_eq_of, coeLinearMap_of, Submodule.subtype_apply]

theorem _root_.DirectSum.coeLinearMap_decompose (a : A) :
    coeLinearMap 𝒜 (decompose 𝒜 a) = a := by
  rw [DirectSum.coeLinearMap_eq_decomposeLinearEquiv_symm, LinearEquiv.coe_coe,
    decomposeLinearEquiv_symm_apply, Equiv.symm_apply_apply]

theorem _root_.DirectSum.decompose_coeLinearMap (y : ⨁ i, 𝒜 i) :
    decompose 𝒜 (coeLinearMap 𝒜 y) = y := by
  rw [DirectSum.coeLinearMap_eq_decomposeLinearEquiv_symm, LinearEquiv.coe_coe,
    decomposeLinearEquiv_symm_apply, Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
instance instDecomposition : DirectSum.Decomposition (grading 𝒜) :=
  DirectSum.Decomposition.ofLinearMap (grading 𝒜)
    (toGrading 𝒜 ∘ₗ (decomposeLinearEquiv 𝒜 : A →ₗ[R] ⨁ i, 𝒜 i) ∘ₗ
      (unop 𝒜 : GradedOpposite 𝒜 →ₗ[R] A))
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, coeLinearMap_toGrading, decomposeLinearEquiv_apply,
        DirectSum.coeLinearMap_decompose, op_unop, LinearMap.id_apply])
    (LinearMap.ext fun z => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, unop_coeLinearMap, decomposeLinearEquiv_apply,
        DirectSum.decompose_coeLinearMap, toGrading_ofGrading, LinearMap.id_apply])

set_option backward.isDefEq.respectTransparency false in
instance instGradedAlgebra : GradedAlgebra (grading 𝒜) :=
  { instGradedMonoid 𝒜, instDecomposition 𝒜 with }

set_option backward.isDefEq.respectTransparency false in
/-- The graded opposite of the graded opposite is the original algebra: the algebra isomorphism
`(𝒜ᵒᵖ)ᵒᵖ ≃ₐ[R] A` given by `unop ∘ unop`.-/
def opOpAlgEquiv : GradedOpposite (grading 𝒜) ≃ₐ[R] A :=
  AlgEquiv.ofLinearEquiv (unop (grading 𝒜) ≪≫ₗ unop 𝒜)
    (by rw [LinearEquiv.trans_apply, unop_one, unop_one])
    (map_mul_of_homogeneous (grading (grading 𝒜)) _ fun {i j} x y => by
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
        unop_mul (grading 𝒜) x.2 y.2, Units.smul_def, map_zsmul, ← Units.smul_def,
        unop_mul 𝒜 ((mem_grading_iff (grading 𝒜)).mp y.2) ((mem_grading_iff (grading 𝒜)).mp x.2),
        smul_smul, mul_comm j i, Int.units_mul_self, one_smul])

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s11.15c5e7eb6e82 from=translated src=- shape=57e57c97 vocab=f9771828
-/
@[simp] theorem opOpAlgEquiv_apply (x : GradedOpposite (grading 𝒜)) :
    opOpAlgEquiv 𝒜 x = unop 𝒜 (unop (grading 𝒜) x) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s11.8fa30b20b216 from=translated src=- shape=589da2ea vocab=61ee5d4a
-/
@[simp] theorem opOpAlgEquiv_symm_apply (a : A) :
    (opOpAlgEquiv 𝒜).symm a = op (grading 𝒜) (op 𝒜 a) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `opOpAlgEquiv` preserves degrees.
@isnad1 id=iff.0h5v.s10.cdc4d0c76be7 from=translated src=- shape=550489aa vocab=6166199e
-/
theorem opOpAlgEquiv_mem_iff {i : ℤ} {x : GradedOpposite (grading 𝒜)} :
    opOpAlgEquiv 𝒜 x ∈ 𝒜 i ↔ x ∈ grading (grading 𝒜) i :=
  ((mem_grading_iff (grading 𝒜)).trans (mem_grading_iff 𝒜)).symm

/-! ### Graded commutativity and the opposite algebra -/

set_option backward.isDefEq.respectTransparency false in
/-- `op` is multiplicative on homogeneous elements iff they commute up to the Koszul sign.
@isnad1 id=iff.2h7v.s10.628998a4211a from=translated src=- shape=be160799 vocab=f41eb7da
-/
theorem op_mul_eq_iff {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) :
    op 𝒜 (a * b) = op 𝒜 a * op 𝒜 b ↔ a * b = koszulSign (i * j) • (b * a) := by
  rw [op_mul_op 𝒜 ha hb, ← map_koszulSign_smul]
  exact (op 𝒜).injective.eq_iff

set_option backward.isDefEq.respectTransparency false in
/-- A graded algebra is graded commutative iff the identity map `op : A → GradedOpposite 𝒜` is
multiplicative.-/
theorem _root_.DG.isGradedComm_iff_op_mul :
    IsGradedComm 𝒜 ↔ ∀ a b : A, op 𝒜 (a * b) = op 𝒜 a * op 𝒜 b := by
  constructor
  · intro h
    exact map_mul_of_homogeneous 𝒜 (op 𝒜) fun a b =>
      (op_mul_eq_iff 𝒜 a.2 b.2).mpr (h.mul_comm_of_mem a.2 b.2)
  · intro h
    exact ⟨fun ha hb => (op_mul_eq_iff 𝒜 ha hb).mp (h _ _)⟩

set_option backward.isDefEq.respectTransparency false in
/-- For a graded commutative algebra, `op` is an algebra isomorphism
`A ≃ₐ[R] GradedOpposite 𝒜`.-/
def opAlgEquiv [IsGradedComm 𝒜] : A ≃ₐ[R] GradedOpposite 𝒜 :=
  AlgEquiv.ofLinearEquiv (op 𝒜) rfl ((isGradedComm_iff_op_mul 𝒜).mp inferInstance)

/--
@isnad1 id=eq.0h4v.s9.3f5c438429e9 from=translated src=- shape=5880d1ab vocab=5472c7f6
-/
@[simp] theorem opAlgEquiv_apply [IsGradedComm 𝒜] (a : A) : opAlgEquiv 𝒜 a = op 𝒜 a := rfl

end GradedOpposite

end DG
