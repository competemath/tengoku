import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top

set_option autoImplicit false

open scoped TensorProduct

namespace P2mKcDescent

variable {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
variable {ι : Type} (g : ι → T) (σ : T →ₗ[S] (ι → S)) (S₀ : Subalgebra ℤ S)

abbrev spanG : Submodule S₀ T := Submodule.span S₀ (Set.range g)

/--
@isnad1 id=mem.0h6v.s8.cfdea147d404 from=translated src=- shape=a30ed3ea vocab=5ee60bde
-/
theorem g_mem_spanG (i : ι) : g i ∈ spanG g S₀ := Submodule.subset_span ⟨i, rfl⟩

/--
@isnad1 id=mem.2h7v.s9.91067f873db1 from=translated src=- shape=82bf16a6 vocab=cbbe4ce3
-/
theorem mem_spanG_of_coeff [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (t : T)
    (ht : ∀ k, σ t k ∈ S₀) : t ∈ spanG g S₀ := by
  rw [← hσ t]
  refine Submodule.sum_mem _ fun k _ => ?_
  have : σ t k • g k = (⟨σ t k, ht k⟩ : S₀) • g k := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (g_mem_spanG g S₀ k)

/--
@isnad1 id=mem.2h8v.s9.fd2675d381fb from=translated src=- shape=f0e73a6f vocab=14be2af4
-/
theorem coeff_mem_of_mem_spanG (hgc : ∀ i k, σ (g i) k ∈ S₀) {t : T} (ht : t ∈ spanG g S₀)
    (k : ι) : σ t k ∈ S₀ := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hgc i k
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, Pi.add_apply]
    exact add_mem hx hy
  | smul a x _ hx =>
    have : (a • x : T) = (a : S) • x := rfl
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_mem a.2 hx

/--
@isnad1 id=mem.2h6v.s9.76fb3e87855b from=translated src=- shape=d19cd3da vocab=cbbe4ce3
-/
theorem one_mem_spanG [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀) :
    (1 : T) ∈ spanG g S₀ :=
  mem_spanG_of_coeff g σ S₀ hσ 1 h1

/--
@isnad1 id=mem.4h8v.s10.c8fb7929283d from=translated src=- shape=704c6ee0 vocab=dceebdd5
-/
theorem mul_mem_spanG [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hm : ∀ i j k, σ (g i * g j) k ∈ S₀)
    (x y : T) (hx : x ∈ spanG g S₀) (hy : y ∈ spanG g S₀) : x * y ∈ spanG g S₀ := by
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx' =>
    obtain ⟨i, rfl⟩ := hx'
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨j, rfl⟩ := hy'
      exact mem_spanG_of_coeff g σ S₀ hσ _ (hm i j)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact add_mem hy hz
    | smul a y _ hy' =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ hy'
  | zero => simp
  | add x x' _ _ hx hx' =>
    rw [add_mul]
    exact add_mem (hx y hy) (hx' y hy)
  | smul a x _ hx =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ (hx y hy)

def model [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀)
    (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) : Subalgebra S₀ T :=
  (spanG g S₀).toSubalgebra (one_mem_spanG g σ S₀ hσ h1) (mul_mem_spanG g σ S₀ hσ hm)

/--
@isnad1 id=eq.3h6v.s11.f7b618799718 from=translated src=- shape=7e1b0182 vocab=b1e1777e
-/
theorem model_toSubmodule [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀)
    (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) :
    Subalgebra.toSubmodule (model g σ S₀ hσ h1 hm) = spanG g S₀ :=
  Submodule.toSubalgebra_toSubmodule _ _ _

def g' (i : ι) : spanG g S₀ := ⟨g i, g_mem_spanG g S₀ i⟩

noncomputable def pi0 [Fintype ι] : (ι → S₀) →ₗ[S₀] spanG g S₀ :=
  Fintype.linearCombination S₀ (g' g S₀)

/--
@isnad1 id=eq.0h6v.s12.4bcfd6f9f18d from=translated src=- shape=33bc39b4 vocab=aa55121d
-/
theorem pi0_apply [Fintype ι] (v : ι → S₀) : pi0 g S₀ v = ∑ i, v i • g' g S₀ i :=
  Fintype.linearCombination_apply _ _ _

/--
@isnad1 id=eq.0h6v.s11.0897e79493ce from=translated src=- shape=ab229c2d vocab=963773e1
-/
theorem coe_pi0 [Fintype ι] (v : ι → S₀) :
    ((pi0 g S₀ v : spanG g S₀) : T) = ∑ i, (v i : S) • g i := by
  rw [pi0_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

noncomputable def sigma0 (hgc : ∀ i k, σ (g i) k ∈ S₀) : spanG g S₀ →ₗ[S₀] (ι → S₀) where
  toFun x := fun k => ⟨σ x k, coeff_mem_of_mem_spanG g σ S₀ hgc x.2 k⟩
  map_add' x y := by
    funext k
    apply Subtype.ext
    change σ ((x : T) + y) k = σ x k + σ y k
    rw [map_add, Pi.add_apply]
  map_smul' a x := by
    funext k
    apply Subtype.ext
    change σ ((a : S) • (x : T)) k = (a : S) * σ x k
    rw [map_smul, Pi.smul_apply, smul_eq_mul]

/--
@isnad1 id=eq.1h8v.s12.787e95ff6041 from=translated src=- shape=8360c079 vocab=0ae1c827
-/
@[scoped simp] theorem coe_sigma0_apply (hgc : ∀ i k, σ (g i) k ∈ S₀) (x : spanG g S₀) (k : ι) :
    ((sigma0 g σ S₀ hgc x k : S₀) : S) = σ x k := rfl

/--
@isnad1 id=eq.2h7v.s12.0e7e4256300c from=translated src=- shape=8e297c2b vocab=9c52e718
-/
theorem pi0_sigma0 [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (hgc : ∀ i k, σ (g i) k ∈ S₀)
    (x : spanG g S₀) : pi0 g S₀ (sigma0 g σ S₀ hgc x) = x := by
  apply Subtype.ext
  rw [coe_pi0]
  simp only [coe_sigma0_apply]
  exact hσ x

/--
@isnad1 id=eq.2h6v.s12.d81a0e320f7a from=translated src=- shape=ce0387bd vocab=5bf2970f
-/
theorem pi0_comp_sigma0 [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hgc : ∀ i k, σ (g i) k ∈ S₀) :
    (pi0 g S₀).comp (sigma0 g σ S₀ hgc) = LinearMap.id :=
  LinearMap.ext fun x => pi0_sigma0 g σ S₀ hσ hgc x

/--
@isnad1 id=projecti.2h6v.s10.c44536ee1c97 from=translated src=- shape=d2037cee vocab=c789c316
-/
theorem projective_spanG [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hgc : ∀ i k, σ (g i) k ∈ S₀) : Module.Projective S₀ (spanG g S₀) :=
  Module.Projective.of_split (sigma0 g σ S₀ hgc) (pi0 g S₀) (pi0_comp_sigma0 g σ S₀ hσ hgc)

/--
@isnad1 id=finite.0h5v.s9.9d91270c5579 from=translated src=- shape=406b00db vocab=570ee8cc
-/
theorem finite_spanG [Finite ι] : Module.Finite S₀ (spanG g S₀) :=
  Module.Finite.span_of_finite S₀ (Set.finite_range g)

/--
@isnad1 id=free.1h5v.s9.279c27f504ef from=translated src=- shape=0467eae0 vocab=adf3e628
-/
theorem free_spanG (hli : LinearIndependent S g) : Module.Free S₀ (spanG g S₀) :=
  Module.Free.of_basis (Module.Basis.span (hli.restrict_scalars' S₀))

noncomputable def psi [Fintype ι] : T →ₗ[S] S ⊗[S₀] spanG g S₀ :=
  ∑ k : ι, (LinearMap.toSpanSingleton S (S ⊗[S₀] spanG g S₀) (1 ⊗ₜ g' g S₀ k)).comp
    ((LinearMap.proj k).comp σ)

/--
@isnad1 id=eq.0h7v.s12.3f80a0313c5e from=translated src=- shape=5e03bd2a vocab=6db3b131
-/
theorem psi_apply [Fintype ι] (t : T) :
    psi g σ S₀ t = ∑ k : ι, σ t k ⊗ₜ[S₀] g' g S₀ k := by
  rw [psi, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
    LinearMap.proj_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

noncomputable def theta : S ⊗[S₀] spanG g S₀ →ₗ[S] T :=
  ((spanG g S₀).subtype).liftBaseChange S

/--
@isnad1 id=eq.0h7v.s12.56ff07e2c0c3 from=translated src=- shape=254841d4 vocab=4e2a1446
-/
@[scoped simp] theorem theta_tmul (s : S) (x : spanG g S₀) :
    theta g S₀ (s ⊗ₜ x) = s • (x : T) :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/--
@isnad1 id=eq.2h7v.s12.076dd7e3af8e from=translated src=- shape=7c818631 vocab=fd471cfa
-/
theorem sum_tmul_eq_one_tmul [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hgc : ∀ i k, σ (g i) k ∈ S₀) (x : spanG g S₀) :
    ∑ k : ι, σ x k ⊗ₜ[S₀] g' g S₀ k = (1 : S) ⊗ₜ[S₀] x := by
  have hx : ∀ k, σ x k ⊗ₜ[S₀] g' g S₀ k =
      (1 : S) ⊗ₜ[S₀] ((sigma0 g σ S₀ hgc x k) • g' g S₀ k) := by
    intro k
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    change σ x k = ((sigma0 g σ S₀ hgc x k : S₀) : S) * 1
    rw [mul_one]
    rfl
  simp_rw [hx]
  rw [← TensorProduct.tmul_sum, ← pi0_apply, pi0_sigma0 g σ S₀ hσ hgc x]

/--
@isnad1 id=eq.2h6v.s13.35c282ded8a3 from=translated src=- shape=522c6206 vocab=6a010c02
-/
theorem psi_comp_theta [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hgc : ∀ i k, σ (g i) k ∈ S₀) :
    (psi g σ S₀).comp (theta g S₀) = LinearMap.id := by
  refine TensorProduct.AlgebraTensorModule.ext fun s x => ?_
  rw [LinearMap.comp_apply, LinearMap.id_apply, theta_tmul, map_smul, psi_apply,
    sum_tmul_eq_one_tmul g σ S₀ hσ hgc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/--
@isnad1 id=injectiv.2h6v.s12.418ac7d192a9 from=translated src=- shape=d44080dc vocab=a4a9f765
-/
theorem theta_injective [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hgc : ∀ i k, σ (g i) k ∈ S₀) : Function.Injective (theta g S₀) := by
  intro a b hab
  have h := LinearMap.congr_fun (psi_comp_theta g σ S₀ hσ hgc) a
  have h' := LinearMap.congr_fun (psi_comp_theta g σ S₀ hσ hgc) b
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h h'
  rw [← h, ← h', hab]

/--
@isnad1 id=surjecti.1h5v.s12.bea44758cf05 from=translated src=- shape=6dc931a3 vocab=82975c1a
-/
theorem theta_surjective (hg : Submodule.span S (Set.range g) = ⊤) :
    Function.Surjective (theta g S₀) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hg, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨1 ⊗ₜ g' g S₀ i, by rw [theta_tmul, one_smul]; rfl⟩

noncomputable def thetaEquiv [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hgc : ∀ i k, σ (g i) k ∈ S₀) (hg : Submodule.span S (Set.range g) = ⊤) :
    S ⊗[S₀] spanG g S₀ ≃ₗ[S] T :=
  LinearEquiv.ofBijective (theta g S₀) ⟨theta_injective g σ S₀ hσ hgc, theta_surjective g S₀ hg⟩

/--
@isnad1 id=isbasech.3h6v.s10.377ffb3db6ef from=translated src=- shape=3df5e24c vocab=1bd11d97
-/
theorem isBaseChange_subtype [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hgc : ∀ i k, σ (g i) k ∈ S₀) (hg : Submodule.span S (Set.range g) = ⊤) :
    IsBaseChange S ((spanG g S₀).subtype) :=
  IsBaseChange.of_equiv (thetaEquiv g σ S₀ hσ hgc hg) fun x => by
    change theta g S₀ ((1 : S) ⊗ₜ x) = x
    rw [theta_tmul, one_smul]

set_option synthInstance.maxHeartbeats 1600000 in
/--
@isnad1 id=ispushou.5h6v.s10.1d6ceebfcb92 from=translated src=- shape=926c62cc vocab=32db4bd7
-/
theorem isPushout_model [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀)
    (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) (hgc : ∀ i k, σ (g i) k ∈ S₀)
    (hg : Submodule.span S (Set.range g) = ⊤) :
    Algebra.IsPushout S₀ S (model g σ S₀ hσ h1 hm) T := by
  rw [Algebra.isPushout_iff]
  have : (IsScalarTower.toAlgHom S₀ (model g σ S₀ hσ h1 hm) T).toLinearMap =
      (spanG g S₀).subtype := by
    refine LinearMap.ext fun x => ?_
    rfl
  rw [this]
  exact isBaseChange_subtype g σ S₀ hσ hgc hg

/--
@isnad1 id=finite.3h6v.s10.56471220af35 from=translated src=- shape=8be57930 vocab=6b2a81a4
-/
theorem finite_model [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀)
    (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) : Module.Finite S₀ (model g σ S₀ hσ h1 hm) :=
  finite_spanG g S₀

/--
@isnad1 id=projecti.4h6v.s10.45794fe37ef0 from=translated src=- shape=1459012b vocab=207bd491
-/
theorem projective_model [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀)
    (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) (hgc : ∀ i k, σ (g i) k ∈ S₀) :
    Module.Projective S₀ (model g σ S₀ hσ h1 hm) :=
  projective_spanG g σ S₀ hσ hgc

/--
@isnad1 id=free.4h6v.s10.c137dc2142fb from=translated src=- shape=3ed5d69b vocab=e72a9b04
-/
theorem free_model [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀)
    (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) (hli : LinearIndependent S g) :
    Module.Free S₀ (model g σ S₀ hσ h1 hm) :=
  free_spanG g S₀ hli

/--
@isnad1 id=ex.1h4v.s12.bfecdf83a896 from=translated src=- shape=b146dc8e vocab=027a84ac
-/
theorem main [Module.Projective S T] [Finite ι]
    (hg : Submodule.span S (Set.range g) = ⊤) :
    ∃ c : Finset S, ∀ S₀ : Subalgebra ℤ S, ↑c ⊆ (S₀ : Set S) →
      ∃ T₀ : Subalgebra S₀ T, Subalgebra.toSubmodule T₀ = Submodule.span S₀ (Set.range g) ∧
        Module.Finite S₀ T₀ ∧ Module.Projective S₀ T₀ ∧
        (LinearIndependent S g → Module.Free S₀ T₀) ∧ Algebra.IsPushout S₀ S T₀ T := by
  classical
  cases nonempty_fintype ι
  have hsurj : Function.Surjective (Fintype.linearCombination S g) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hg]
  obtain ⟨σ, hσ'⟩ :=
    Module.projective_lifting_property (Fintype.linearCombination S g) LinearMap.id hsurj
  have hσ : ∀ t, ∑ i, σ t i • g i = t := fun t => by
    have := LinearMap.congr_fun hσ' t
    rwa [LinearMap.comp_apply, Fintype.linearCombination_apply, LinearMap.id_apply] at this

  let c : Finset S := ((Finset.univ.image fun k : ι => σ 1 k) ∪
    (Finset.univ.image fun p : (ι × ι) × ι => σ (g p.1.1 * g p.1.2) p.2)) ∪
    (Finset.univ.image fun p : ι × ι => σ (g p.1) p.2)
  refine ⟨c, fun S₀ hc => ?_⟩
  have h1 : ∀ k, σ 1 k ∈ S₀ := fun k => hc (by
    simp only [c, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_union, Set.mem_range]
    exact Or.inl (Or.inl ⟨k, rfl⟩))
  have hm : ∀ i j k, σ (g i * g j) k ∈ S₀ := fun i j k => hc (by
    simp only [c, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_union, Set.mem_range]
    exact Or.inl (Or.inr ⟨((i, j), k), rfl⟩))
  have hgc : ∀ i k, σ (g i) k ∈ S₀ := fun i k => hc (by
    simp only [c, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_union, Set.mem_range]
    exact Or.inr ⟨(i, k), rfl⟩)
  exact ⟨model g σ S₀ hσ h1 hm, model_toSubmodule g σ S₀ hσ h1 hm, finite_model g σ S₀ hσ h1 hm,
    projective_model g σ S₀ hσ h1 hm hgc, fun hli => free_model g σ S₀ hσ h1 hm hli,
    isPushout_model g σ S₀ hσ h1 hm hgc hg⟩

end P2mKcDescent
open scoped _root_.P2MW.S_Algebra_exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top.P2mKcDescent

/--
@isnad1 id=ex.1h4v.s12.da97d1bb800c from=translated src=- shape=5f00c459 vocab=027a84ac
-/
theorem solution
    {S T : Type} [CommRing S] [CommRing T] [Algebra S T] [Module.Projective S T]
    {ι : Type} [Finite ι] (g : ι → T) (hg : Submodule.span S (Set.range g) = ⊤) :
    ∃ c : Finset S, ∀ S₀ : Subalgebra ℤ S, ↑c ⊆ (S₀ : Set S) →
      ∃ T₀ : Subalgebra S₀ T, Subalgebra.toSubmodule T₀ = Submodule.span S₀ (Set.range g) ∧
        Module.Finite S₀ T₀ ∧ Module.Projective S₀ T₀ ∧
        (LinearIndependent S g → Module.Free S₀ T₀) ∧ Algebra.IsPushout S₀ S T₀ T :=
  P2mKcDescent.main g hg
