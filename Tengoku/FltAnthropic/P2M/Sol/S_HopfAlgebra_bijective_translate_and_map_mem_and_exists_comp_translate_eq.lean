import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq

set_option autoImplicit false

open scoped TensorProduct

universe u v w

set_option synthInstance.maxHeartbeats 800000

namespace S17Tc1

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]

noncomputable def T (g : H →ₐ[k] k) : H →ₗ[k] H :=
  (TensorProduct.lid k H).toLinearMap ∘ₗ LinearMap.rTensor H g.toLinearMap ∘ₗ Coalgebra.comul

/--
@isnad1 id=eq.0h4v.s12.556bcf147ce5 from=translated src=- shape=d9ce9ab9 vocab=5ff8c372
-/
theorem T_apply (g : H →ₐ[k] k) (h : H) :
    T g h = TensorProduct.lid k H (LinearMap.rTensor H g.toLinearMap (Coalgebra.comul (R := k) h)) := rfl

/--
@isnad1 id=eq.0h4v.s12.819a3a23c754 from=translated src=- shape=390814c3 vocab=643a2a51
-/
theorem lid_map_eq (g : H →ₐ[k] k) (z : H ⊗[k] H) :
    Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map g (AlgHom.id k H) z) =
      TensorProduct.lid k H (LinearMap.rTensor H g.toLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, AlgHom.coe_id, id_eq]
  | add a b ha hb => simp only [map_add, ha, hb]

noncomputable def Sₐ : H →ₐ[k] H :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode k) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul_antidistrib, mul_comm])

/--
@isnad1 id=eq.0h3v.s9.ff54447a554a from=translated src=- shape=31de17bd vocab=c34ffba6
-/
@[scoped simp] theorem Sₐ_apply (h : H) : Sₐ (k := k) h = HopfAlgebra.antipode k h := rfl

/--
@isnad1 id=eq.0h5v.s12.b9bc7e1bb69f from=translated src=- shape=54dd75a3 vocab=16d2789b
-/
theorem conv_apply (x y : H →ₐ[k] k) (h : H) :
    (WithConv.toConv x * WithConv.toConv y).ofConv h =
      LinearMap.mul' k k (TensorProduct.map x.toLinearMap y.toLinearMap (Coalgebra.comul (R := k) h)) := by
  rw [AlgHom.convMul_apply]
  induction (Coalgebra.comul (R := k) h) using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [Algebra.TensorProduct.lift_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
      AlgHom.toLinearMap_apply, WithConv.ofConv_toConv]
  | add a b ha hb => simp only [map_add, ha, hb]

/--
@isnad1 id=eq.0h5v.s10.6b5d64c6f8ac from=translated src=- shape=2e969700 vocab=fbd11e66
-/
theorem comp_T (x g : H →ₐ[k] k) (h : H) :
    x (T g h) = (WithConv.toConv g * WithConv.toConv x).ofConv h := by
  rw [conv_apply, T_apply]
  induction (Coalgebra.comul (R := k) h) using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, map_smul,
      TensorProduct.map_tmul, LinearMap.mul'_apply, smul_eq_mul]
  | add a b ha hb => simp only [map_add, ha, hb]

/--
@isnad1 id=eq.0h3v.s9.6277c9ae6f29 from=translated src=- shape=ec6e7127 vocab=2f938ae7
-/
theorem convMul_compS_left (x : H →ₐ[k] k) :
    WithConv.toConv (x.comp Sₐ) * WithConv.toConv x = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rw [conv_apply, AlgHom.convOne_apply]
  have key : ∀ z : H ⊗[k] H, LinearMap.mul' k k (TensorProduct.map (x.comp Sₐ).toLinearMap x.toLinearMap z) =
      x (LinearMap.mul' k H (LinearMap.rTensor H (HopfAlgebra.antipode k) z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        Sₐ_apply, LinearMap.rTensor_tmul, map_mul]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [key, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]

/--
@isnad1 id=eq.0h3v.s9.9b450a09975f from=translated src=- shape=05135f3b vocab=2f938ae7
-/
theorem convMul_compS_right (x : H →ₐ[k] k) :
    WithConv.toConv x * WithConv.toConv (x.comp Sₐ) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rw [conv_apply, AlgHom.convOne_apply]
  have key : ∀ z : H ⊗[k] H, LinearMap.mul' k k (TensorProduct.map x.toLinearMap (x.comp Sₐ).toLinearMap z) =
      x (LinearMap.mul' k H (LinearMap.lTensor H (HopfAlgebra.antipode k) z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        Sₐ_apply, LinearMap.lTensor_tmul, map_mul]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [key, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]

/--
@isnad1 id=ex.0h4v.s9.b35b7d365475 from=translated src=- shape=4471b1b0 vocab=10413d15
-/
theorem exists_comp_T_eq (x y : H →ₐ[k] k) : ∃ g : H →ₐ[k] k, ∀ h, y h = x (T g h) := by
  refine ⟨(WithConv.toConv y * WithConv.toConv (x.comp Sₐ)).ofConv, fun h => ?_⟩
  rw [comp_T, WithConv.toConv_ofConv, mul_assoc, convMul_compS_left, mul_one, WithConv.ofConv_toConv]

/--
@isnad1 id=eq.0h4v.s14.44d1fd0b3855 from=translated src=- shape=aac8563d vocab=8c0f5027
-/
theorem comul_lid_rTensor (b : H →ₐ[k] k) (z : H ⊗[k] H) :
    Coalgebra.comul (R := k) (TensorProduct.lid k H (LinearMap.rTensor H b.toLinearMap z)) =
      TensorProduct.lid k (H ⊗[k] H) (LinearMap.rTensor (H ⊗[k] H) b.toLinearMap
        (LinearMap.lTensor H (Coalgebra.comul (R := k)) z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c h =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, map_smul,
      LinearMap.lTensor_tmul]
  | add a c ha hc => simp only [map_add, ha, hc]

/--
@isnad1 id=eq.0h5v.s15.bfb3c9145111 from=translated src=- shape=d73460de vocab=3755df5c
-/
theorem threefold (a b : H →ₐ[k] k) (w : (H ⊗[k] H) ⊗[k] H) :
    TensorProduct.lid k H (LinearMap.rTensor H a.toLinearMap
      (TensorProduct.lid k (H ⊗[k] H) (LinearMap.rTensor (H ⊗[k] H) b.toLinearMap
        (TensorProduct.assoc k H H H w)))) =
    TensorProduct.lid k H (LinearMap.rTensor H
      (LinearMap.mul' k k ∘ₗ TensorProduct.map b.toLinearMap a.toLinearMap) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z c =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | tmul u v =>
      simp only [TensorProduct.assoc_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
        AlgHom.toLinearMap_apply, map_smul, LinearMap.comp_apply, TensorProduct.map_tmul,
        LinearMap.mul'_apply, smul_smul, mul_comm (b u) (a v)]
    | add z₁ z₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/--
@isnad1 id=eq.0h5v.s13.5353d8fab6eb from=translated src=- shape=05e0b355 vocab=690c0628
-/
theorem rTensor_conv (a b : H →ₐ[k] k) (w : H ⊗[k] H) :
    LinearMap.rTensor H (WithConv.toConv b * WithConv.toConv a).ofConv.toLinearMap w =
      LinearMap.rTensor H (LinearMap.mul' k k ∘ₗ TensorProduct.map b.toLinearMap a.toLinearMap)
        (LinearMap.rTensor H (Coalgebra.comul (R := k)) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c h =>
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, conv_apply, LinearMap.comp_apply]
  | add a c ha hc => simp only [map_add, ha, hc]

/--
@isnad1 id=eq.0h5v.s10.8580bb074617 from=translated src=- shape=78ae5a43 vocab=fbd11e66
-/
theorem T_T (a b : H →ₐ[k] k) (h : H) :
    T a (T b h) = T (WithConv.toConv b * WithConv.toConv a).ofConv h := by
  rw [T_apply, T_apply, T_apply, comul_lid_rTensor, ← Coalgebra.coassoc_apply, threefold, rTensor_conv]

/--
@isnad1 id=eq.0h3v.s9.b3691be8b235 from=translated src=- shape=81ae65bd vocab=93db07b1
-/
theorem T_one (h : H) : T (1 : WithConv (H →ₐ[k] k)).ofConv h = h := by
  rw [T_apply]
  have : LinearMap.rTensor H (WithConv.ofConv (1 : WithConv (H →ₐ[k] k))).toLinearMap
      (Coalgebra.comul (R := k) h) =
      LinearMap.rTensor H (Coalgebra.counit (R := k) (A := H)) (Coalgebra.comul (R := k) h) := by
    induction (Coalgebra.comul (R := k) h) using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c x =>
      simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, AlgHom.convOne_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
    | add a c ha hc => simp only [map_add, ha, hc]
  rw [this, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

/--
@isnad1 id=bijectiv.0h3v.s8.08a48427edbf from=translated src=- shape=98bb7b8c vocab=b3abe46c
-/
theorem T_bijective (g : H →ₐ[k] k) : Function.Bijective (T g) := by
  have h1 : ∀ h, T (g.comp Sₐ) (T g h) = h := fun h => by
    rw [T_T, convMul_compS_right, T_one]
  have h2 : ∀ h, T g (T (g.comp Sₐ) h) = h := fun h => by
    rw [T_T, convMul_compS_left, T_one]
  exact ⟨fun a b hab => by rw [← h1 a, ← h1 b, hab], fun b => ⟨T (g.comp Sₐ) b, h2 b⟩⟩

/--
@isnad1 id=mem.2h5v.s12.bc164009a075 from=translated src=- shape=3f69154e vocab=43dc40fc
-/
theorem T_mem (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (g : H →ₐ[k] k) (x : H) (hx : x ∈ K) : T g x ∈ K := by
  rw [T_apply]
  have hsub : ∀ z ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b},
      TensorProduct.lid k H (LinearMap.rTensor H g.toLinearMap z) ∈ K := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨a, ha, b, hb, rfl⟩ := ht
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, AlgHom.toLinearMap_apply]
      exact K.smul_mem hb _
    | zero => simp only [map_zero]; exact K.zero_mem
    | add a b _ _ ha hb => simp only [map_add]; exact K.add_mem ha hb
    | smul c a _ ha => simp only [map_smul]; exact K.smul_mem ha c
  exact hsub _ (hΔ x hx)

end S17Tc1
open scoped _root_.P2MW.S_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq.S17Tc1

open S17Tc1 in
/--
@isnad1 id=and.1h3v.s13.f655cd5214cc from=translated src=- shape=3d3da1fd vocab=9d5adaef
-/
theorem solution
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (τ : (H →ₐ[k] k) → (H →ₐ[k] H))
    (hτ : ∀ (g : H →ₐ[k] k) (h : H),
      τ g h = Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map g (AlgHom.id k H) (Coalgebra.comul h))) :
    (∀ g, Function.Bijective (τ g)) ∧
    (∀ (K : Subalgebra k H),
      (∀ x ∈ K, Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) →
      ∀ g, ∀ x ∈ K, τ g x ∈ K) ∧
    (∀ x y : H →ₐ[k] k, ∃ g : H →ₐ[k] k, y = x.comp (τ g)) := by
  have hT : ∀ g h, τ g h = T g h := fun g h => by rw [hτ, lid_map_eq, T_apply]
  have hTf : ∀ g, (τ g : H → H) = T g := fun g => funext (hT g)
  refine ⟨fun g => ?_, fun K hΔ g x hx => ?_, fun x y => ?_⟩
  · rw [hTf]; exact T_bijective g
  · rw [hT]; exact T_mem K hΔ g x hx
  · obtain ⟨g, hg⟩ := exists_comp_T_eq x y
    exact ⟨g, AlgHom.ext fun h => by rw [AlgHom.comp_apply, hT]; exact hg h⟩
