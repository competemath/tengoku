import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FiniteFlat_SchematicClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
open scoped TensorProduct

section FlatClosureHopf

universe u v w

variable {R : Type u} [CommRing R]
variable {F : Type v} [Field F] [Algebra R F]
variable {G : Type w} [CommRing G]

attribute [local instance 1000000] SemilinearEquivClass.instSemilinearMapClass

set_option synthInstance.maxHeartbeats 400000

section ModuleLevel

variable [Algebra R G]

noncomputable def _root_.Tengoku.FltAnthropic.tensorInclusion (B : Subalgebra F (F ⊗[R] G)) :
    (flatClosure B) ⊗[R] (flatClosure B) →ₗ[R] G ⊗[R] G :=
  TensorProduct.map (flatClosure B).val.toLinearMap (flatClosure B).val.toLinearMap

/--
@isnad1 id=eq.0h6v.s11.7c11a61fa703 from=translated src=- shape=37354a6d vocab=9f5dd08b
-/
@[simp]
lemma _root_.Tengoku.FltAnthropic.tensorInclusion_tmul {B : Subalgebra F (F ⊗[R] G)} (x y : flatClosure B) :
    tensorInclusion B (x ⊗ₜ[R] y) = (x : G) ⊗ₜ[R] (y : G) := rfl

def _root_.Tengoku.FltAnthropic.closureTensorSpan (B : Subalgebra F (F ⊗[R] G)) : Submodule R (G ⊗[R] G) :=
  Submodule.span R (Set.image2 (· ⊗ₜ[R] ·) (flatClosure B : Set G) (flatClosure B : Set G))

/--
@isnad1 id=eq.0h4v.s10.efdae6f0d455 from=translated src=- shape=8a8eaeaa vocab=cd8aeb9d
-/
lemma _root_.Tengoku.FltAnthropic.range_tensorInclusion (B : Subalgebra F (F ⊗[R] G)) :
    LinearMap.range (tensorInclusion B) = closureTensorSpan B := by
  apply le_antisymm
  · rintro x hx
    obtain ⟨z, rfl⟩ := hx
    induction z with
    | zero => rw [map_zero]; exact (closureTensorSpan B).zero_mem
    | tmul a b =>
        rw [tensorInclusion_tmul]
        exact Submodule.subset_span (Set.mem_image2_of_mem a.2 b.2)
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  · rw [closureTensorSpan, Submodule.span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨(⟨a, ha⟩ : flatClosure B) ⊗ₜ[R] (⟨b, hb⟩ : flatClosure B), rfl⟩

/--
@isnad1 id=injectiv.0h4v.s11.7512b3a6801c from=translated src=- shape=a9ef2eed vocab=fcdc44cc
-/
theorem _root_.Tengoku.FltAnthropic.tensorInclusion_injective [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) : Function.Injective (tensorInclusion B) := by
  haveI : Module.Free R G := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free R (flatClosure B) := flatClosure_free B
  have hι : Function.Injective ((flatClosure B).val.toLinearMap) := Subtype.val_injective
  have hfact : tensorInclusion B
      = ((flatClosure B).val.toLinearMap.rTensor G).comp
        ((flatClosure B).val.toLinearMap.lTensor (flatClosure B)) := by
    ext x y
    rfl
  rw [hfact, LinearMap.coe_comp]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _ hι).comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ hι)

/--
@isnad1 id=mem.2h6v.s10.62a7553a0edc from=translated src=- shape=3f5e031f vocab=dd04748e
-/
theorem _root_.Tengoku.FltAnthropic.mem_closureTensorSpan_of_smul_mem [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) {x : G ⊗[R] G} {r : R} (hr : r ≠ 0)
    (hx : r • x ∈ closureTensorSpan B) : x ∈ closureTensorSpan B := by
  haveI : Module.Free R G := Module.free_of_finite_type_torsion_free'

  obtain ⟨C, hC⟩ := exists_isCompl_flatClosure (R := R) (F := F) (G := G) B
  set p : G →ₗ[R] G := (Subalgebra.toSubmodule (flatClosure B)).projection C hC with hp
  have hp_mem : ∀ g : G, p g ∈ flatClosure B := by
    intro g
    have h1 : p g ∈ Subalgebra.toSubmodule (flatClosure B) := by
      have h2 := Submodule.range_projection (p := Subalgebra.toSubmodule (flatClosure B))
        (q := C) hC
      exact h2 ▸ LinearMap.mem_range_self _ g
    simpa [Subalgebra.mem_toSubmodule] using h1
  have hp_fix : ∀ g : G, g ∈ flatClosure B → p g = g := by
    intro g hg
    rw [hp, Submodule.projection_eq_self_iff]
    simpa [Subalgebra.mem_toSubmodule] using hg

  set P : G ⊗[R] G →ₗ[R] G ⊗[R] G := TensorProduct.map p p with hP
  have hP_mem : ∀ z : G ⊗[R] G, P z ∈ closureTensorSpan B := by
    intro z
    induction z with
    | zero => rw [map_zero]; exact (closureTensorSpan B).zero_mem
    | tmul a b =>
        rw [hP, TensorProduct.map_tmul]
        exact Submodule.subset_span (Set.mem_image2_of_mem (hp_mem a) (hp_mem b))
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  have hP_fix : ∀ z, z ∈ closureTensorSpan B → P z = z := by
    intro z hz
    replace hz : z ∈ Submodule.span R
        (Set.image2 (· ⊗ₜ[R] ·) (flatClosure B : Set G) (flatClosure B : Set G)) := hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hw
        rw [hP, TensorProduct.map_tmul, hp_fix a ha, hp_fix b hb]
    | zero => rw [map_zero]
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add, h₁, h₂]
    | smul c w _ h => rw [map_smul, h]

  have h1 : P (r • x) = r • x := hP_fix _ hx
  have h2 : r • (P x - x) = 0 := by
    rw [smul_sub, ← map_smul, h1, sub_self]
  have h3 : P x = x := by
    rcases (Module.isTorsionFree_iff_smul_eq_zero.mp inferInstance) r _ h2 with h | h
    · exact absurd h hr
    · exact sub_eq_zero.mp h
  exact h3 ▸ hP_mem x

variable (R F) in

noncomputable def _root_.Tengoku.FltAnthropic.tensorToGenericFibre (x : G ⊗[R] G) : (F ⊗[R] G) ⊗[F] (F ⊗[R] G) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R F F (F ⊗[R] G) G).symm
    ((LinearMap.rTensor G
      (Algebra.TensorProduct.includeRight (R := R) (A := F) (B := G)).toLinearMap) x)

/--
@isnad1 id=eq.0h5v.s9.5b923667627e from=translated src=- shape=de2f54bc vocab=6691f88a
-/
@[simp]
lemma _root_.Tengoku.FltAnthropic.tensorToGenericFibre_tmul (g₁ g₂ : G) :
    tensorToGenericFibre R F (g₁ ⊗ₜ[R] g₂)
      = ((1 : F) ⊗ₜ[R] g₁) ⊗ₜ[F] ((1 : F) ⊗ₜ[R] g₂) := by
  simp [tensorToGenericFibre]

/--
@isnad1 id=eq.0h3v.s10.3d8b0bc46e2f from=translated src=- shape=bc8af42c vocab=594034bd
-/
lemma _root_.Tengoku.FltAnthropic.tensorToGenericFibre_zero : tensorToGenericFibre R F (0 : G ⊗[R] G) = 0 := by
  unfold tensorToGenericFibre
  rw [map_zero, map_zero]

/--
@isnad1 id=eq.0h5v.s11.2e7c7c33e438 from=translated src=- shape=eeb8bdf2 vocab=ba078410
-/
lemma _root_.Tengoku.FltAnthropic.tensorToGenericFibre_add (x y : G ⊗[R] G) :
    tensorToGenericFibre R F (x + y)
      = tensorToGenericFibre R F x + tensorToGenericFibre R F y := by
  unfold tensorToGenericFibre
  rw [map_add, map_add]

/--
@isnad1 id=eq.0h5v.s10.3e6d59085b0e from=translated src=- shape=a103df30 vocab=48d71ed9
-/
lemma _root_.Tengoku.FltAnthropic.tensorToGenericFibre_smul (r : R) (x : G ⊗[R] G) :
    tensorToGenericFibre R F (r • x) = (algebraMap R F r) • tensorToGenericFibre R F x := by
  induction x with
  | zero => rw [smul_zero, tensorToGenericFibre_zero, smul_zero]
  | tmul g₁ g₂ =>
      simp only [TensorProduct.smul_tmul', tensorToGenericFibre_tmul, one_tmul_smul]
  | add x y hx hy =>
      rw [smul_add, tensorToGenericFibre_add, tensorToGenericFibre_add, hx, hy, smul_add]

/--
@isnad1 id=injectiv.0h3v.s9.5daf352c02dc from=translated src=- shape=f2f4968a vocab=6bf4df9a
-/
theorem _root_.Tengoku.FltAnthropic.tensorToGenericFibre_injective [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G] :
    Function.Injective (tensorToGenericFibre R F (G := G)) := by
  haveI : Module.Free R G := Module.free_of_finite_type_torsion_free'

  have hφ : Function.Injective
      ((Algebra.TensorProduct.includeRight (R := R) (A := F) (B := G)).toLinearMap) := by
    intro a b hab
    have key : ∀ g : G, ((Algebra.linearMap R F).rTensor G) ((TensorProduct.lid R G).symm g)
        = (1 : F) ⊗ₜ[R] g := by
      intro g
      simp
    have h1 : Function.Injective ((Algebra.linearMap R F).rTensor G) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective R F)
    have h2 : (TensorProduct.lid R G).symm a = (TensorProduct.lid R G).symm b := by
      apply h1
      rw [key, key]
      simpa using hab
    exact (TensorProduct.lid R G).symm.injective h2

  intro x y hxy
  have h3 : Function.Injective ((Algebra.TensorProduct.includeRight
      (R := R) (A := F) (B := G)).toLinearMap.rTensor G) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hφ
  apply h3
  unfold tensorToGenericFibre at hxy
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange
    R F F (F ⊗[R] G) G).symm.injective hxy

private lemma mul_smul_tmul (c₁ c₂ : F) (m n : F ⊗[R] G) :
    (c₁ * c₂) • (m ⊗ₜ[F] n) = (c₁ • m) ⊗ₜ[F] (c₂ • n) := by
  rw [mul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul, TensorProduct.smul_tmul']

/--
@isnad1 id=ex.1h5v.s13.eeadf28e4599 from=translated src=- shape=355c967a vocab=ceb42dfd
-/
theorem _root_.Tengoku.FltAnthropic.exists_smul_eq_tensorToGenericFibre_of_mem_span [IsDomain R] [IsFractionRing R F]
    {B : Subalgebra F (F ⊗[R] G)} {y : (F ⊗[R] G) ⊗[F] (F ⊗[R] G)}
    (hy : y ∈ Submodule.span F
      (Set.image2 (· ⊗ₜ[F] ·) (B : Set (F ⊗[R] G)) (B : Set (F ⊗[R] G)))) :
    ∃ (r : R) (z : G ⊗[R] G), r ≠ 0 ∧ z ∈ closureTensorSpan B ∧
      (algebraMap R F r) • y = tensorToGenericFibre R F z := by
  induction hy using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hw
      obtain ⟨r₁, g₁, hr₁, hg₁, e₁⟩ := exists_nonzero_smul_mem_flatClosure (R := R) (F := F) hb₁
      obtain ⟨r₂, g₂, hr₂, hg₂, e₂⟩ := exists_nonzero_smul_mem_flatClosure (R := R) (F := F) hb₂
      refine ⟨r₁ * r₂, g₁ ⊗ₜ[R] g₂, mul_ne_zero hr₁ hr₂,
        Submodule.subset_span (Set.mem_image2_of_mem hg₁ hg₂), ?_⟩
      rw [tensorToGenericFibre_tmul, ← e₁, ← e₂, map_mul, mul_smul_tmul]
  | zero =>
      exact ⟨1, 0, one_ne_zero, (closureTensorSpan B).zero_mem,
        by rw [smul_zero, tensorToGenericFibre_zero]⟩
  | add y₁ y₂ _ _ ih₁ ih₂ =>
      obtain ⟨r₁, z₁, hr₁, hz₁, e₁⟩ := ih₁
      obtain ⟨r₂, z₂, hr₂, hz₂, e₂⟩ := ih₂
      refine ⟨r₁ * r₂, r₂ • z₁ + r₁ • z₂, mul_ne_zero hr₁ hr₂,
        add_mem (Submodule.smul_mem _ _ hz₁) (Submodule.smul_mem _ _ hz₂), ?_⟩
      rw [tensorToGenericFibre_add, tensorToGenericFibre_smul, tensorToGenericFibre_smul,
        ← e₁, ← e₂, map_mul]
      module
  | smul c y₁ _ ih =>
      obtain ⟨r, z, hr, hz, e⟩ := ih
      obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors R) c
      refine ⟨r * (s : R), a • z, mul_ne_zero hr (nonZeroDivisors.coe_ne_zero s),
        Submodule.smul_mem _ _ hz, ?_⟩
      rw [tensorToGenericFibre_smul, ← e, ← hs, map_mul]
      module

/--
@isnad1 id=mem.1h5v.s12.20ec402f0aa4 from=translated src=- shape=512fac70 vocab=2783368e
-/
theorem _root_.Tengoku.FltAnthropic.mem_closureTensorSpan_of_tensorToGenericFibre_mem_span [IsDomain R]
    [IsPrincipalIdealRing R] [IsNoetherianRing R] [IsFractionRing R F]
    [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} {x : G ⊗[R] G}
    (hx : tensorToGenericFibre R F x ∈ Submodule.span F
      (Set.image2 (· ⊗ₜ[F] ·) (B : Set (F ⊗[R] G)) (B : Set (F ⊗[R] G)))) :
    x ∈ closureTensorSpan B := by
  obtain ⟨r, z, hr, hz, e⟩ := exists_smul_eq_tensorToGenericFibre_of_mem_span hx
  have h1 : tensorToGenericFibre R F (r • x) = tensorToGenericFibre R F z := by
    rw [tensorToGenericFibre_smul]; exact e
  have h2 : r • x = z := tensorToGenericFibre_injective h1
  exact mem_closureTensorSpan_of_smul_mem B hr (h2 ▸ hz)

end ModuleLevel

section Bialgebra

variable [Bialgebra R G]

variable (R F) in

def _root_.Tengoku.FltAnthropic.IsComulStable (B : Subalgebra F (F ⊗[R] G)) : Prop :=
  ∀ g ∈ flatClosure B, tensorToGenericFibre R F (Coalgebra.comul (R := R) g) ∈
    Submodule.span F (Set.image2 (· ⊗ₜ[F] ·) (B : Set (F ⊗[R] G)) (B : Set (F ⊗[R] G)))

/--
@isnad1 id=mem.2h5v.s10.9799751f6973 from=translated src=- shape=31dbf7b1 vocab=3da32718
-/
theorem _root_.Tengoku.FltAnthropic.comul_mem_closureTensorSpan [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) {g : G} (hg : g ∈ flatClosure B) :
    Coalgebra.comul (R := R) g ∈ closureTensorSpan B :=
  mem_closureTensorSpan_of_tensorToGenericFibre_mem_span (hB g hg)

/--
@isnad1 id=mem.2h5v.s11.11ab1a2978ca from=translated src=- shape=6d4d6cdf vocab=164e279c
-/
theorem _root_.Tengoku.FltAnthropic.comul_mem_range_tensorInclusion [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) {g : G} (hg : g ∈ flatClosure B) :
    Coalgebra.comul (R := R) g ∈ LinearMap.range (tensorInclusion B) := by
  rw [range_tensorInclusion]
  exact comul_mem_closureTensorSpan hB hg

noncomputable def _root_.Tengoku.FltAnthropic.closureComul [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    flatClosure B →ₗ[R] (flatClosure B) ⊗[R] (flatClosure B) :=
  (LinearEquiv.ofInjective (tensorInclusion B)
      (tensorInclusion_injective B)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (tensorInclusion B))
      ((Coalgebra.comul (R := R)).comp (flatClosure B).val.toLinearMap)
      (fun h => comul_mem_range_tensorInclusion hB h.2)

/--
@isnad1 id=eq.1h5v.s13.f6812b41ff05 from=translated src=- shape=a7871098 vocab=10bc43a5
-/
@[simp]
theorem _root_.Tengoku.FltAnthropic.tensorInclusion_closureComul [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (h : flatClosure B) :
    tensorInclusion B (closureComul hB h) = Coalgebra.comul (R := R) (h : G) := by
  show tensorInclusion B ((LinearEquiv.ofInjective (tensorInclusion B)
      (tensorInclusion_injective B)).symm _) = _
  rw [LinearEquiv.ofInjective_symm_apply]
  rfl

noncomputable def _root_.Tengoku.FltAnthropic.closureCounit (B : Subalgebra F (F ⊗[R] G)) : flatClosure B →ₗ[R] R :=
  (Coalgebra.counit (R := R) (A := G)).comp (flatClosure B).val.toLinearMap

/--
@isnad1 id=eq.0h5v.s10.527932eb8eb2 from=translated src=- shape=30e5582e vocab=fd899a27
-/
@[simp]
theorem _root_.Tengoku.FltAnthropic.closureCounit_apply (B : Subalgebra F (F ⊗[R] G)) (h : flatClosure B) :
    closureCounit B h = Coalgebra.counit (R := R) (h : G) := rfl

end Bialgebra

section HopfAlgebra

variable [HopfAlgebra R G]

variable (R F) in

def _root_.Tengoku.FltAnthropic.IsAntipodeStable (B : Subalgebra F (F ⊗[R] G)) : Prop :=
  ∀ g ∈ flatClosure B, HopfAlgebra.antipode R g ∈ flatClosure B

def _root_.Tengoku.FltAnthropic.closureAntipode {B : Subalgebra F (F ⊗[R] G)} (hB : IsAntipodeStable R F B) :
    flatClosure B →ₗ[R] flatClosure B where
  toFun h := ⟨HopfAlgebra.antipode R (h : G), hB _ h.2⟩
  map_add' x y := by
    ext
    simp [map_add]
  map_smul' r x := by
    ext
    simp [map_smul]

/--
@isnad1 id=eq.1h5v.s11.7bc76dc7e431 from=translated src=- shape=104c3121 vocab=3447b73a
-/
@[simp]
theorem _root_.Tengoku.FltAnthropic.coe_closureAntipode_apply {B : Subalgebra F (F ⊗[R] G)} (hB : IsAntipodeStable R F B)
    (h : flatClosure B) :
    (closureAntipode hB h : G) = HopfAlgebra.antipode R (h : G) := rfl

end HopfAlgebra

section GenericFibre

variable [Algebra R G]

noncomputable def _root_.Tengoku.FltAnthropic.genericFibreAlgHom (B : Subalgebra F (F ⊗[R] G)) :
    F ⊗[R] (flatClosure B) →ₐ[F] F ⊗[R] G :=
  AlgHom.liftEquiv R F (flatClosure B) (F ⊗[R] G)
    ((Algebra.TensorProduct.includeRight (R := R) (A := F) (B := G)).comp (flatClosure B).val)

/--
@isnad1 id=eq.0h6v.s11.31d0f0a69e72 from=translated src=- shape=e8067d6b vocab=d8935720
-/
@[simp]
lemma _root_.Tengoku.FltAnthropic.genericFibreAlgHom_tmul (B : Subalgebra F (F ⊗[R] G)) (f : F) (h : flatClosure B) :
    genericFibreAlgHom B (f ⊗ₜ[R] h) = f ⊗ₜ[R] (h : G) := by
  simp [genericFibreAlgHom, TensorProduct.smul_tmul', smul_eq_mul]

/--
@isnad1 id=injectiv.0h4v.s10.39330755fa81 from=translated src=- shape=933eb99f vocab=b31b2da1
-/
theorem _root_.Tengoku.FltAnthropic.genericFibreAlgHom_injective [IsDomain R] [IsFractionRing R F]
    (B : Subalgebra F (F ⊗[R] G)) : Function.Injective (genericFibreAlgHom B) := by
  haveI : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  have hcoe : ⇑(genericFibreAlgHom B)
      = ⇑(LinearMap.lTensor F (flatClosure B).val.toLinearMap) := by
    funext x
    induction x with
    | zero => rw [map_zero, map_zero]
    | tmul f h => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hcoe]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

/--
@isnad1 id=eq.0h4v.s9.bb45ee869d1c from=translated src=- shape=f25a444e vocab=91301d88
-/
theorem _root_.Tengoku.FltAnthropic.range_genericFibreAlgHom [IsDomain R] [IsFractionRing R F]
    (B : Subalgebra F (F ⊗[R] G)) : (genericFibreAlgHom B).range = B := by
  have hmem : ∀ x : F ⊗[R] (flatClosure B), genericFibreAlgHom B x ∈ B := by
    intro x
    induction x with
    | zero => rw [map_zero]; exact B.zero_mem
    | tmul f h =>
        rw [genericFibreAlgHom_tmul]
        have h1 : (1 : F) ⊗ₜ[R] (h : G) ∈ B := h.2
        have h2 : f ⊗ₜ[R] (h : G) = f • ((1 : F) ⊗ₜ[R] (h : G)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [h2]
        exact B.smul_mem h1 f
    | add x y hx hy => rw [map_add]; exact B.add_mem hx hy
  apply le_antisymm
  · rintro y hy
    obtain ⟨x, rfl⟩ := ((genericFibreAlgHom B).mem_range).mp hy
    exact hmem x
  · have hspan : Subalgebra.toSubmodule B
        ≤ Subalgebra.toSubmodule (genericFibreAlgHom B).range := by
      rw [← span_image_flatClosure (R := R) (F := F) B, Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      simp only [SetLike.mem_coe, Subalgebra.mem_toSubmodule]
      refine ((genericFibreAlgHom B).mem_range).mpr
        ⟨1 ⊗ₜ[R] (⟨g, hg⟩ : flatClosure B), ?_⟩
      rw [genericFibreAlgHom_tmul]
    intro x hx
    exact hspan hx

noncomputable def _root_.Tengoku.FltAnthropic.genericFibreAlgEquiv [IsDomain R] [IsFractionRing R F]
    (B : Subalgebra F (F ⊗[R] G)) : (F ⊗[R] (flatClosure B)) ≃ₐ[F] B :=
  (AlgEquiv.ofInjective (genericFibreAlgHom B) (genericFibreAlgHom_injective B)).trans
    (Subalgebra.equivOfEq _ _ (range_genericFibreAlgHom B))

end GenericFibre

end FlatClosureHopf
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
