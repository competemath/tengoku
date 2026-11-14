import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FiniteFlat_ClosureHopf

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

open scoped TensorProduct

section FlatClosureInstances

universe u v w

variable {R : Type u} [CommRing R]
variable {F : Type v} [Field F] [Algebra R F]
variable {G : Type w} [CommRing G]

attribute [local instance 1000000] SemilinearEquivClass.instSemilinearMapClass

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

section TripleInclusion

variable [Algebra R G]

noncomputable def _root_.Tengoku.FltAnthropic.tensorInclusion3 (B : Subalgebra F (F ⊗[R] G)) :
    (flatClosure B) ⊗[R] ((flatClosure B) ⊗[R] (flatClosure B)) →ₗ[R] G ⊗[R] (G ⊗[R] G) :=
  ((flatClosure B).val.toLinearMap.rTensor (G ⊗[R] G)).comp
    ((tensorInclusion B).lTensor (flatClosure B))

/--
@isnad1 id=eq.0h6v.s13.f292e084c340 from=translated src=- shape=7af374d2 vocab=fc9719bf
-/
@[simp]
lemma _root_.Tengoku.FltAnthropic.tensorInclusion3_tmul {B : Subalgebra F (F ⊗[R] G)} (x : flatClosure B)
    (w : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion3 B (x ⊗ₜ[R] w) = (x : G) ⊗ₜ[R] (tensorInclusion B w) := by
  simp [tensorInclusion3]

noncomputable def _root_.Tengoku.FltAnthropic.tensorInclusion3' (B : Subalgebra F (F ⊗[R] G)) :
    ((flatClosure B) ⊗[R] (flatClosure B)) ⊗[R] (flatClosure B) →ₗ[R] (G ⊗[R] G) ⊗[R] G :=
  ((tensorInclusion B).rTensor G).comp
    ((flatClosure B).val.toLinearMap.lTensor ((flatClosure B) ⊗[R] (flatClosure B)))

/--
@isnad1 id=eq.0h6v.s13.bd3e1471ead7 from=translated src=- shape=1ecb9ca8 vocab=d911b6d2
-/
@[simp]
lemma _root_.Tengoku.FltAnthropic.tensorInclusion3'_tmul {B : Subalgebra F (F ⊗[R] G)}
    (w : (flatClosure B) ⊗[R] (flatClosure B)) (z : flatClosure B) :
    tensorInclusion3' B (w ⊗ₜ[R] z) = (tensorInclusion B w) ⊗ₜ[R] (z : G) := by
  simp [tensorInclusion3']

/--
@isnad1 id=injectiv.0h4v.s13.e1dbff3b54bb from=translated src=- shape=0ce4debf vocab=4026986c
-/
theorem _root_.Tengoku.FltAnthropic.tensorInclusion3_injective [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) : Function.Injective (tensorInclusion3 B) := by
  haveI : Module.Free R G := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free R (flatClosure B) := flatClosure_free B
  unfold tensorInclusion3
  rw [LinearMap.coe_comp]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective).comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ (tensorInclusion_injective B))

/--
@isnad1 id=eq.0h5v.s15.bb8df7851c82 from=translated src=- shape=292dfc56 vocab=2989fab8
-/
theorem _root_.Tengoku.FltAnthropic.tensorInclusion3_assoc_apply {B : Subalgebra F (F ⊗[R] G)}
    (w : ((flatClosure B) ⊗[R] (flatClosure B)) ⊗[R] (flatClosure B)) :
    tensorInclusion3 B
        (TensorProduct.assoc R (flatClosure B) (flatClosure B) (flatClosure B) w)
      = TensorProduct.assoc R G G G (tensorInclusion3' B w) := by
  induction w with
  | zero => simp
  | tmul a z =>
      induction a with
      | zero => simp
      | tmul x y => simp
      | add a₁ a₂ h₁ h₂ =>
          simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
  | add w₁ w₂ h₁ h₂ => simp [map_add, h₁, h₂]

/--
@isnad1 id=eq.0h6v.s13.1b77257c8c25 from=translated src=- shape=93a8fc45 vocab=d28f6314
-/
theorem _root_.Tengoku.FltAnthropic.tensorInclusion_mul {B : Subalgebra F (F ⊗[R] G)}
    (z w : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion B (z * w) = tensorInclusion B z * tensorInclusion B w := by
  induction z with
  | zero => simp
  | tmul x y =>
      induction w with
      | zero => simp
      | tmul x' y' =>
          simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add b₁ b₂ h₁ h₂ => simp [mul_add, h₁, h₂]
  | add a₁ a₂ h₁ h₂ => simp [add_mul, h₁, h₂]

/--
@isnad1 id=eq.0h4v.s12.80a9dca93990 from=translated src=- shape=1adf7c24 vocab=6470d794
-/
theorem _root_.Tengoku.FltAnthropic.tensorInclusion_one {B : Subalgebra F (F ⊗[R] G)} :
    tensorInclusion B (1 : (flatClosure B) ⊗[R] (flatClosure B)) = 1 := by
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.one_def, tensorInclusion_tmul]
  simp

/--
@isnad1 id=eq.0h5v.s13.ee85d2bdc06a from=translated src=- shape=cf1b74ca vocab=ce0a8924
-/
theorem _root_.Tengoku.FltAnthropic.val_mul'_tensorInclusion {B : Subalgebra F (F ⊗[R] G)}
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    ((LinearMap.mul' R (flatClosure B) z : flatClosure B) : G)
      = LinearMap.mul' R G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.mul'_apply]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

end TripleInclusion

section CoalgebraBialgebra

variable [Bialgebra R G]

/--
@isnad1 id=eq.1h5v.s15.f8bccbb7ebff from=translated src=- shape=8606c71e vocab=ced1e821
-/
theorem _root_.Tengoku.FltAnthropic.tensorInclusion3'_rTensor_closureComul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B)
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion3' B ((closureComul hB).rTensor (flatClosure B) z)
      = (Coalgebra.comul (R := R) (A := G)).rTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

/--
@isnad1 id=eq.1h5v.s15.fe5d37bcac84 from=translated src=- shape=23896837 vocab=f20d93fb
-/
theorem _root_.Tengoku.FltAnthropic.tensorInclusion3_lTensor_closureComul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B)
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion3 B ((closureComul hB).lTensor (flatClosure B) z)
      = (Coalgebra.comul (R := R) (A := G)).lTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

/--
@isnad1 id=eq.0h5v.s14.32d4d3ae7ae4 from=translated src=- shape=68118867 vocab=025acb16
-/
theorem _root_.Tengoku.FltAnthropic.lTensor_val_rTensor_closureCounit {B : Subalgebra F (F ⊗[R] G)}
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    ((flatClosure B).val.toLinearMap.lTensor R)
        ((closureCounit B).rTensor (flatClosure B) z)
      = (Coalgebra.counit (R := R) (A := G)).rTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

/--
@isnad1 id=eq.0h5v.s14.cf681fd1bd0e from=translated src=- shape=baaf709e vocab=025acb16
-/
theorem _root_.Tengoku.FltAnthropic.rTensor_val_lTensor_closureCounit {B : Subalgebra F (F ⊗[R] G)}
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    ((flatClosure B).val.toLinearMap.rTensor R)
        ((closureCounit B).lTensor (flatClosure B) z)
      = (Coalgebra.counit (R := R) (A := G)).lTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

/--
@isnad1 id=eq.1h4v.s15.9847a51820f0 from=translated src=- shape=e7d5cf77 vocab=59351908
-/
theorem _root_.Tengoku.FltAnthropic.closureComul_coassoc [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    TensorProduct.assoc R (flatClosure B) (flatClosure B) (flatClosure B) ∘ₗ
        (closureComul hB).rTensor (flatClosure B) ∘ₗ closureComul hB
      = (closureComul hB).lTensor (flatClosure B) ∘ₗ closureComul hB := by
  apply LinearMap.ext
  intro h
  apply tensorInclusion3_injective B
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [tensorInclusion3_assoc_apply, tensorInclusion3'_rTensor_closureComul,
    tensorInclusion_closureComul, tensorInclusion3_lTensor_closureComul,
    tensorInclusion_closureComul]
  exact Coalgebra.coassoc_apply (h : G)

/--
@isnad1 id=eq.1h4v.s13.0f4b01fe6c05 from=translated src=- shape=c6a399c3 vocab=a487d49e
-/
theorem _root_.Tengoku.FltAnthropic.closureCounit_rTensor_comp_closureComul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    (closureCounit B).rTensor (flatClosure B) ∘ₗ closureComul hB
      = TensorProduct.mk R R (flatClosure B) 1 := by
  apply LinearMap.ext
  intro h
  apply Module.Flat.lTensor_preserves_injective_linearMap
    ((flatClosure B).val.toLinearMap) Subtype.val_injective
  simp only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.lTensor_tmul]
  rw [lTensor_val_rTensor_closureCounit, tensorInclusion_closureComul,
    Coalgebra.rTensor_counit_comul]
  rfl

/--
@isnad1 id=eq.1h4v.s13.ad27f806cf47 from=translated src=- shape=2528f93f vocab=db189239
-/
theorem _root_.Tengoku.FltAnthropic.closureCounit_lTensor_comp_closureComul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    (closureCounit B).lTensor (flatClosure B) ∘ₗ closureComul hB
      = (TensorProduct.mk R (flatClosure B) R).flip 1 := by
  apply LinearMap.ext
  intro h
  apply Module.Flat.rTensor_preserves_injective_linearMap
    ((flatClosure B).val.toLinearMap) Subtype.val_injective
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    LinearMap.rTensor_tmul]
  rw [rTensor_val_lTensor_closureCounit, tensorInclusion_closureComul,
    Coalgebra.lTensor_counit_comul]
  rfl

/--
@isnad1 id=eq.0h4v.s10.5668cbd9e069 from=translated src=- shape=07065616 vocab=d60f98c8
-/
theorem _root_.Tengoku.FltAnthropic.closureCounit_one (B : Subalgebra F (F ⊗[R] G)) :
    closureCounit (R := R) (F := F) B 1 = 1 := by
  simp [Bialgebra.counit_one]

/--
@isnad1 id=eq.0h6v.s11.4fbc7d38f967 from=translated src=- shape=5fd57113 vocab=032704d7
-/
theorem _root_.Tengoku.FltAnthropic.closureCounit_mul {B : Subalgebra F (F ⊗[R] G)} (x y : flatClosure B) :
    closureCounit (R := R) (F := F) B (x * y)
      = closureCounit (R := R) (F := F) B x * closureCounit (R := R) (F := F) B y := by
  simp [Bialgebra.counit_mul]

/--
@isnad1 id=eq.1h4v.s12.0c538ef19f33 from=translated src=- shape=fed910fb vocab=7b551f80
-/
theorem _root_.Tengoku.FltAnthropic.closureComul_one [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    closureComul hB 1 = 1 := by
  apply tensorInclusion_injective B
  rw [tensorInclusion_closureComul, tensorInclusion_one]
  simp [Bialgebra.comul_one]

/--
@isnad1 id=eq.1h6v.s14.902afd3a2b6f from=translated src=- shape=91a48768 vocab=a5670f7d
-/
theorem _root_.Tengoku.FltAnthropic.closureComul_mul [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (x y : flatClosure B) :
    closureComul hB (x * y) = closureComul hB x * closureComul hB y := by
  apply tensorInclusion_injective B
  rw [tensorInclusion_closureComul, tensorInclusion_mul, tensorInclusion_closureComul,
    tensorInclusion_closureComul]
  simp [Bialgebra.comul_mul]

variable (R F) in

@[reducible]
noncomputable def _root_.Tengoku.FltAnthropic.closureCoalgebra [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    Coalgebra R (flatClosure B) where
  comul := closureComul hB
  counit := closureCounit B
  coassoc := closureComul_coassoc hB
  rTensor_counit_comp_comul := closureCounit_rTensor_comp_closureComul hB
  lTensor_counit_comp_comul := closureCounit_lTensor_comp_closureComul hB

variable (R F) in

@[reducible]
noncomputable def _root_.Tengoku.FltAnthropic.closureBialgebra [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    Bialgebra R (flatClosure B) :=
  letI : Coalgebra R (flatClosure B) := closureCoalgebra R F hB
  Bialgebra.mk' R (flatClosure B)
    (closureCounit_one B)
    (fun {x y} => closureCounit_mul x y)
    (closureComul_one hB)
    (fun {x y} => closureComul_mul hB x y)

end CoalgebraBialgebra

section Hopf

variable [HopfAlgebra R G]

/--
@isnad1 id=eq.1h5v.s15.1807bea9474a from=translated src=- shape=5133a407 vocab=9b0f2c19
-/
theorem _root_.Tengoku.FltAnthropic.tensorInclusion_rTensor_closureAntipode {B : Subalgebra F (F ⊗[R] G)}
    (hB' : IsAntipodeStable R F B) (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion B ((closureAntipode hB').rTensor (flatClosure B) z)
      = (HopfAlgebra.antipode R (A := G)).rTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

/--
@isnad1 id=eq.1h5v.s15.c6ae7a20b8da from=translated src=- shape=5133a407 vocab=1dbf10db
-/
theorem _root_.Tengoku.FltAnthropic.tensorInclusion_lTensor_closureAntipode {B : Subalgebra F (F ⊗[R] G)}
    (hB' : IsAntipodeStable R F B) (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion B ((closureAntipode hB').lTensor (flatClosure B) z)
      = (HopfAlgebra.antipode R (A := G)).lTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

/--
@isnad1 id=eq.2h4v.s14.e8d7fac5b5cd from=translated src=- shape=5fa78c1c vocab=fe10d6a2
-/
theorem _root_.Tengoku.FltAnthropic.closure_mul_antipode_rTensor_comul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (hB' : IsAntipodeStable R F B) :
    LinearMap.mul' R (flatClosure B) ∘ₗ
        (closureAntipode hB').rTensor (flatClosure B) ∘ₗ closureComul hB
      = (Algebra.linearMap R (flatClosure B)) ∘ₗ closureCounit B := by
  apply LinearMap.ext
  intro h
  apply Subtype.val_injective
  simp only [LinearMap.comp_apply]
  rw [val_mul'_tensorInclusion, tensorInclusion_rTensor_closureAntipode,
    tensorInclusion_closureComul, HopfAlgebra.mul_antipode_rTensor_comul_apply]
  simp [Algebra.linearMap_apply]

/--
@isnad1 id=eq.2h4v.s14.2a3413b84096 from=translated src=- shape=5fa78c1c vocab=3644134e
-/
theorem _root_.Tengoku.FltAnthropic.closure_mul_antipode_lTensor_comul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (hB' : IsAntipodeStable R F B) :
    LinearMap.mul' R (flatClosure B) ∘ₗ
        (closureAntipode hB').lTensor (flatClosure B) ∘ₗ closureComul hB
      = (Algebra.linearMap R (flatClosure B)) ∘ₗ closureCounit B := by
  apply LinearMap.ext
  intro h
  apply Subtype.val_injective
  simp only [LinearMap.comp_apply]
  rw [val_mul'_tensorInclusion, tensorInclusion_lTensor_closureAntipode,
    tensorInclusion_closureComul, HopfAlgebra.mul_antipode_lTensor_comul_apply]
  simp [Algebra.linearMap_apply]

variable (R F) in

@[reducible]
noncomputable def _root_.Tengoku.FltAnthropic.closureHopfAlgebra [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (hB' : IsAntipodeStable R F B) :
    HopfAlgebra R (flatClosure B) :=
  letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
  { antipode := closureAntipode hB'
    mul_antipode_rTensor_comul := closure_mul_antipode_rTensor_comul hB hB'
    mul_antipode_lTensor_comul := closure_mul_antipode_lTensor_comul hB hB' }

end Hopf

section Cocomm

variable [HopfAlgebra R G]

/--
@isnad1 id=eq.0h5v.s15.fa4eb24b6848 from=translated src=- shape=e7038eb9 vocab=7b23324b
-/
theorem _root_.Tengoku.FltAnthropic.tensorInclusion_comm_apply {B : Subalgebra F (F ⊗[R] G)}
    (w : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion B (TensorProduct.comm R (flatClosure B) (flatClosure B) w)
      = TensorProduct.comm R G G (tensorInclusion B w) := by
  induction w with
  | zero => simp
  | tmul x y => simp
  | add a b ha hb => simp [ha, hb]

/--
@isnad1 id=iscocomm.1h4v.s10.282d6a2a5629 from=translated src=- shape=49b47a69 vocab=2151383d
-/
theorem _root_.Tengoku.FltAnthropic.closureIsCocomm [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    [Coalgebra.IsCocomm R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    letI : Coalgebra R (flatClosure B) := closureCoalgebra R F hB
    Coalgebra.IsCocomm R (flatClosure B) := by
  letI : Coalgebra R (flatClosure B) := closureCoalgebra R F hB
  refine ⟨LinearMap.ext fun h => tensorInclusion_injective B ?_⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorInclusion_comm_apply]
  change TensorProduct.comm R G G (tensorInclusion B (closureComul hB h))
    = tensorInclusion B (closureComul hB h)
  rw [tensorInclusion_closureComul]
  exact Coalgebra.comm_comul R (h : G)

end Cocomm

section BialgHomInclusion

variable [HopfAlgebra R G]

noncomputable def _root_.Tengoku.FltAnthropic.closureValBialgHom [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
    flatClosure B →ₐc[R] G := by
  letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
  exact
    { toFun := (flatClosure B).val
      map_add' := map_add _
      map_smul' := fun r x => (flatClosure B).val.toLinearMap.map_smul r x
      counit_comp := rfl
      map_comp_comul := LinearMap.ext fun h => tensorInclusion_closureComul hB h
      map_one' := map_one (flatClosure B).val
      map_mul' := map_mul (flatClosure B).val }

/--
@isnad1 id=eq.1h5v.s12.9a3f438dc46b from=translated src=- shape=b8b5b67e vocab=59de6979
-/
@[simp]
theorem _root_.Tengoku.FltAnthropic.closureValBialgHom_apply [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (h : flatClosure B) :
    letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
    closureValBialgHom hB h = (h : G) := rfl

/--
@isnad1 id=eq.1h4v.s11.e7d1563a9494 from=translated src=- shape=23ef5742 vocab=3064ba89
-/
theorem _root_.Tengoku.FltAnthropic.closureValBialgHom_toAlgHom [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
    ((closureValBialgHom hB : flatClosure B →ₐc[R] G) : flatClosure B →ₐ[R] G)
      = (flatClosure B).val :=
  AlgHom.ext fun _ => rfl

open WithConv in

/--
@isnad1 id=eq.1h7v.s12.eb41d5817c88 from=translated src=- shape=9b732ce9 vocab=8cfbe113
-/
theorem _root_.Tengoku.FltAnthropic.convMul_comp_closureVal [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B)
    {L : Type*} [CommRing L] [Algebra R L] (f g : WithConv (G →ₐ[R] L)) :
    letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
    toConv ((f * g).ofConv.comp (flatClosure B).val)
      = toConv (f.ofConv.comp (flatClosure B).val) * toConv (g.ofConv.comp (flatClosure B).val) := by
  letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
  have h := AlgHom.convMul_comp_bialgHom_distrib f g (closureValBialgHom hB)
  rw [closureValBialgHom_toAlgHom hB] at h
  exact congrArg toConv h

end BialgHomInclusion

end FlatClosureInstances
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
