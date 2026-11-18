import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_IsDirectLimit_exists_linearEquiv_of_finitePresentation.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_IsDirectLimit_exists_linearEquiv_of_finitePresentation

set_option autoImplicit false

open TensorProduct

namespace S17LFP

section Helpers

variable {R : Type*} [CommRing R] {S T : Type*} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

theorem rTensor_algHom_smul (σ : S →ₐ[R] T) (Q : Type*) [AddCommGroup Q] [Module R Q]
    (b : S) (z : S ⊗[R] Q) :
    σ.toLinearMap.rTensor Q (b • z) = σ b • σ.toLinearMap.rTensor Q z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s q => simp [TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp [smul_add, hx, hy]

theorem ext_one_tmul {P N : Type*} [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N]
    {f₁ f₂ : S ⊗[R] P →ₗ[S] N} (h : ∀ p, f₁ (1 ⊗ₜ p) = f₂ (1 ⊗ₜ p)) : f₁ = f₂ := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s p
  have : s ⊗ₜ[R] p = s • ((1 : S) ⊗ₜ[R] p) := by simp [TensorProduct.smul_tmul']
  rw [this, map_smul, map_smul, h]

theorem rTensor_comp_apply_tmul (σ : S →ₐ[R] T) {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (ξ : S ⊗[R] P →ₗ[S] S ⊗[R] Q) (b : S) (p : P) :
    (σ.toLinearMap.rTensor Q ∘ₗ ξ.restrictScalars R) (b ⊗ₜ p) =
      σ b • σ.toLinearMap.rTensor Q (ξ (1 ⊗ₜ p)) := by
  have hb : b ⊗ₜ[R] p = b • ((1 : S) ⊗ₜ[R] p) := by simp [TensorProduct.smul_tmul']
  rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hb, ξ.map_smul, rTensor_algHom_smul]

theorem comp_rTensor_apply_tmul (σ : S →ₐ[R] T) {P N : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N] [Module T N] [IsScalarTower R T N]
    (ξ : T ⊗[R] P →ₗ[T] N) (b : S) (p : P) :
    (ξ.restrictScalars R ∘ₗ σ.toLinearMap.rTensor P) (b ⊗ₜ p) = σ b • ξ (1 ⊗ₜ p) := by
  have hb : σ b ⊗ₜ[R] p = σ b • ((1 : T) ⊗ₜ[R] p) := by simp [TensorProduct.smul_tmul']
  rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, hb, ξ.map_smul]

end Helpers

section Cocone

variable {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  (t : ∀ i j, i ≤ j → G i →ₗ[R] G j)
  {A : Type*} [AddCommGroup A] [Module R A] (ψ : ∀ i, G i →ₗ[R] A)

omit [Nonempty ι] in
theorem exists_ge_ge (i j : ι) : ∃ k, i ≤ k ∧ j ≤ k := directed_of (· ≤ ·) i j

theorem cocone_rTensor_surj (hψ : ∀ i j (h : i ≤ j) x, ψ j (t i j h x) = ψ i x)
    (hsurj : ∀ a, ∃ i x, ψ i x = a) (Q : Type*) [AddCommGroup Q] [Module R Q]
    (z : A ⊗[R] Q) : ∃ (i : ι) (x : G i ⊗[R] Q), (ψ i).rTensor Q x = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨Classical.arbitrary ι, 0, map_zero _⟩
  | tmul a q =>
    obtain ⟨i, x, rfl⟩ := hsurj a
    exact ⟨i, x ⊗ₜ q, by simp⟩
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨i₁, x₁, rfl⟩ := h₁
    obtain ⟨i₂, x₂, rfl⟩ := h₂
    obtain ⟨k, h₁k, h₂k⟩ := exists_ge_ge i₁ i₂
    refine ⟨k, (t i₁ k h₁k).rTensor Q x₁ + (t i₂ k h₂k).rTensor Q x₂, ?_⟩
    have e₁ : ψ k ∘ₗ t i₁ k h₁k = ψ i₁ := LinearMap.ext (hψ _ _ _)
    have e₂ : ψ k ∘ₗ t i₂ k h₂k = ψ i₂ := LinearMap.ext (hψ _ _ _)
    simp only [map_add, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, e₁, e₂]

theorem lift_bijective [DecidableEq ι] (hψ : ∀ i j (h : i ≤ j) x, ψ j (t i j h x) = ψ i x)
    (hsurj : ∀ a, ∃ i x, ψ i x = a)
    (hzero : ∀ i x, ψ i x = 0 → ∃ (j : ι) (h : i ≤ j), t i j h x = 0) :
    Function.Bijective (Module.DirectLimit.lift R ι G t ψ hψ) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    rw [Module.DirectLimit.lift_of] at hz
    obtain ⟨j, hij, hj⟩ := hzero i x hz
    rw [← Module.DirectLimit.of_f (hij := hij), hj, map_zero]
  · intro a
    obtain ⟨i, x, rfl⟩ := hsurj a
    exact ⟨Module.DirectLimit.of R ι G t i x, Module.DirectLimit.lift_of ..⟩

theorem cocone_rTensor_zero [DirectedSystem G (t · · ·)]
    (hψ : ∀ i j (h : i ≤ j) x, ψ j (t i j h x) = ψ i x)
    (hsurj : ∀ a, ∃ i x, ψ i x = a)
    (hzero : ∀ i x, ψ i x = 0 → ∃ (j : ι) (h : i ≤ j), t i j h x = 0)
    (Q : Type*) [AddCommGroup Q] [Module R Q] (i : ι) (x : G i ⊗[R] Q)
    (hx : (ψ i).rTensor Q x = 0) : ∃ (j : ι) (h : i ≤ j), (t i j h).rTensor Q x = 0 := by
  classical
  let Φ := LinearEquiv.ofBijective _ (lift_bijective t ψ hψ hsurj hzero)
  have hΦ : Φ.toLinearMap ∘ₗ Module.DirectLimit.of R ι G t i = ψ i :=
    LinearMap.ext fun y => Module.DirectLimit.lift_of (f := t) ψ hψ y
  have h1 : (Φ.rTensor Q) ((Module.DirectLimit.of R ι G t i).rTensor Q x) = 0 := by
    rw [← LinearEquiv.coe_coe, LinearEquiv.coe_rTensor, ← LinearMap.comp_apply,
      ← LinearMap.rTensor_comp, hΦ, hx]
  have h2 : (Module.DirectLimit.of R ι G t i).rTensor Q x = 0 :=
    (Φ.rTensor Q).injective (by rw [h1, map_zero])
  have h3 := congrArg (TensorProduct.directLimitLeft t Q) h2
  rw [TensorProduct.directLimitLeft_rTensor_of, map_zero] at h3
  exact Module.DirectLimit.of.zero_exact h3

theorem exists_comp_eq_of_finite [DirectedSystem G (t · · ·)]
    (hzero : ∀ i x, ψ i x = 0 → ∃ (j : ι) (h : i ≤ j), t i j h x = 0)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {i : ι} (u v : M →ₗ[R] G i) (huv : ψ i ∘ₗ u = ψ i ∘ₗ v) :
    ∃ (j : ι) (hij : i ≤ j), t i j hij ∘ₗ u = t i j hij ∘ₗ v := by
  classical
  suffices key : ∀ w : M →ₗ[R] G i, ψ i ∘ₗ w = 0 →
      ∃ (j : ι) (hij : i ≤ j), t i j hij ∘ₗ w = 0 by
    obtain ⟨j, hij, h⟩ := key (u - v) (by rw [LinearMap.comp_sub, huv, sub_self])
    exact ⟨j, hij, sub_eq_zero.mp (by rw [← LinearMap.comp_sub, h])⟩
  intro w hw
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  choose jf hjf hz using fun m : M => hzero i (w m) (by simpa using LinearMap.congr_fun hw m)
  obtain ⟨j, hj⟩ := Finset.exists_le (insert i (s.image jf))
  have hij : i ≤ j := hj i (Finset.mem_insert_self ..)
  refine ⟨j, hij, ?_⟩
  rw [← LinearMap.ker_eq_top, eq_top_iff, ← hs, Submodule.span_le]
  intro m hm
  have hjm : jf m ≤ j := hj _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jf hm))
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply]
  rw [show t i j hij (w m) = t (jf m) j hjm (t i (jf m) (hjf m) (w m)) from
    (DirectedSystem.map_map (f := (t · · ·)) (hjf m) hjm (w m)).symm, hz, map_zero]

theorem exists_factor_of_finitePresentation [DirectedSystem G (t · · ·)]
    (hψ : ∀ i j (h : i ≤ j) x, ψ j (t i j h x) = ψ i x)
    (hsurj : ∀ a, ∃ i x, ψ i x = a)
    (hzero : ∀ i x, ψ i x = 0 → ∃ (j : ι) (h : i ≤ j), t i j h x = 0)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (φ : M →ₗ[R] A) : ∃ (i : ι) (u : M →ₗ[R] G i), ψ i ∘ₗ u = φ := by
  classical
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R M
  choose i₀ x₀ hx₀ using fun k : Fin n => hsurj (φ (e.symm (K.mkQ (Pi.single k 1))))
  obtain ⟨i, hi⟩ := Finset.exists_le (Finset.univ.image i₀)
  have hik : ∀ k, i₀ k ≤ i := fun k => hi _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  let y : Fin n → G i := fun k => t (i₀ k) i (hik k) (x₀ k)
  let u₀ : (Fin n → R) →ₗ[R] G i := Fintype.linearCombination R y
  have hu₀ : ψ i ∘ₗ u₀ = φ ∘ₗ e.symm.toLinearMap ∘ₗ K.mkQ := by
    apply LinearMap.pi_ext'
    intro k
    apply LinearMap.ext_ring
    simp [u₀, y, Fintype.linearCombination_apply_single, hψ, hx₀]
  have : Module.Finite R K := Module.Finite.iff_fg.mpr hK
  obtain ⟨j, hij, hj⟩ := exists_comp_eq_of_finite t ψ hzero (u₀ ∘ₗ K.subtype) 0 (by
    rw [LinearMap.comp_zero, ← LinearMap.comp_assoc, hu₀]
    ext ⟨k, hk⟩
    simp [(Submodule.Quotient.mk_eq_zero K).mpr hk])
  have hker : K ≤ LinearMap.ker (t i j hij ∘ₗ u₀) := by
    intro k hk
    simpa using LinearMap.congr_fun hj ⟨k, hk⟩
  refine ⟨j, K.liftQ _ hker ∘ₗ e.toLinearMap, ?_⟩
  have hq : ψ j ∘ₗ K.liftQ _ hker = φ ∘ₗ e.symm.toLinearMap := by
    apply Submodule.linearMap_qext
    rw [LinearMap.comp_assoc, Submodule.liftQ_mkQ, ← LinearMap.comp_assoc,
      show ψ j ∘ₗ t i j hij = ψ i from LinearMap.ext (hψ _ _ _), hu₀]
    rfl
  rw [← LinearMap.comp_assoc, hq]
  ext m
  simp

end Cocone

section Descent

universe u v w

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {B₀ : Type u} [CommRing B₀]
  (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra B₀ (B i)]
  (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) [DirectedSystem B (fun i j h => τ i j h)]
  (Bω : Type u) [CommRing Bω] [Algebra B₀ Bω] (g : ∀ i, B i →ₐ[B₀] Bω)
  (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i)
  (hsurj : ∀ b : Bω, ∃ i x, g i x = b)
  (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0)
  (P Q : Type*) [AddCommGroup P] [Module B₀ P] [AddCommGroup Q] [Module B₀ Q]

omit [IsDirectedOrder ι] [Nonempty ι] in
theorem directedSystem_linear : DirectedSystem B (fun i j h => (τ i j h).toLinearMap) :=
  ⟨fun _ x => DirectedSystem.map_self (f := fun i j h => ⇑(τ i j h)) x,
    fun _ _ _ h₁ h₂ x => DirectedSystem.map_map (f := fun i j h => ⇑(τ i j h)) h₁ h₂ x⟩

omit [IsDirectedOrder ι] [Nonempty ι] in
theorem rTensor_self (i : ι) {M : Type*} [AddCommGroup M] [Module B₀ M] (z : B i ⊗[B₀] M) :
    (τ i i le_rfl).toLinearMap.rTensor M z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c q =>
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
    congr 1
    exact DirectedSystem.map_self (f := fun i j h => ⇑(τ i j h)) c

omit [DirectedSystem B (fun i j h => τ i j h)] [IsDirectedOrder ι] [Nonempty ι] in
include hg in
theorem glin_comp (k l : ι) (h : k ≤ l) :
    (g l).toLinearMap ∘ₗ (τ k l h).toLinearMap = (g k).toLinearMap :=
  LinearMap.ext fun x => by simpa using DFunLike.congr_fun (hg k l h) x

omit [DirectedSystem B (fun i j h => τ i j h)] [IsDirectedOrder ι] [Nonempty ι] in
include hg in
theorem glin_compat : ∀ k l (h : k ≤ l) (x : B k),
    (g l).toLinearMap ((τ k l h).toLinearMap x) = (g k).toLinearMap x :=
  fun k l h x => by simpa using DFunLike.congr_fun (hg k l h) x

omit [DirectedSystem B (fun i j h => τ i j h)] [IsDirectedOrder ι] [Nonempty ι] in
include hg in
theorem gQ_compat (Q : Type*) [AddCommGroup Q] [Module B₀ Q] : ∀ k l (h : k ≤ l) (x : B k ⊗[B₀] Q),
    (g l).toLinearMap.rTensor Q ((τ k l h).toLinearMap.rTensor Q x) = (g k).toLinearMap.rTensor Q x := by
  intro k l h x
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, glin_comp B τ Bω g hg]

include hg hsurj in
omit [DirectedSystem B (fun i j h => τ i j h)] in
theorem gQ_surj (Q : Type*) [AddCommGroup Q] [Module B₀ Q] :
    ∀ z : Bω ⊗[B₀] Q, ∃ (i : ι) (x : B i ⊗[B₀] Q), (g i).toLinearMap.rTensor Q x = z :=
  cocone_rTensor_surj (fun k l h => (τ k l h).toLinearMap) (fun k => (g k).toLinearMap)
    (glin_compat B τ Bω g hg) hsurj Q

include hg hsurj hzero in
theorem gQ_zero (Q : Type*) [AddCommGroup Q] [Module B₀ Q] :
    ∀ (i : ι) (x : B i ⊗[B₀] Q), (g i).toLinearMap.rTensor Q x = 0 →
      ∃ (j : ι) (h : i ≤ j), (τ i j h).toLinearMap.rTensor Q x = 0 :=
  have := directedSystem_linear B τ
  cocone_rTensor_zero (fun k l h => (τ k l h).toLinearMap) (fun k => (g k).toLinearMap)
    (glin_compat B τ Bω g hg) hsurj hzero Q

include hg hsurj hzero in

theorem hom_inj [Module.Finite B₀ P] (i : ι) (φ φ' : B i ⊗[B₀] P →ₗ[B i] B i ⊗[B₀] Q)
    (h : (g i).toLinearMap.rTensor Q ∘ₗ φ.restrictScalars B₀ =
      (g i).toLinearMap.rTensor Q ∘ₗ φ'.restrictScalars B₀) :
    ∃ (j : ι) (h : i ≤ j),
      (τ i j h).toLinearMap.rTensor Q ∘ₗ φ.restrictScalars B₀ =
        (τ i j h).toLinearMap.rTensor Q ∘ₗ φ'.restrictScalars B₀ := by
  have := directedSystem_linear B τ
  let u : P →ₗ[B₀] B i ⊗[B₀] Q := φ.restrictScalars B₀ ∘ₗ TensorProduct.mk B₀ (B i) P 1
  let u' : P →ₗ[B₀] B i ⊗[B₀] Q := φ'.restrictScalars B₀ ∘ₗ TensorProduct.mk B₀ (B i) P 1
  obtain ⟨j, hij, hj⟩ := exists_comp_eq_of_finite (G := fun k => B k ⊗[B₀] Q)
    (fun k l h => (τ k l h).toLinearMap.rTensor Q) (fun k => (g k).toLinearMap.rTensor Q)
    (gQ_zero B τ Bω g hg hsurj hzero Q) u u' (by simp only [u, u', ← LinearMap.comp_assoc, h])
  refine ⟨j, hij, ?_⟩
  apply TensorProduct.ext'
  intro b p
  rw [rTensor_comp_apply_tmul, rTensor_comp_apply_tmul]
  congr 1
  exact LinearMap.congr_fun hj p

include hg hsurj hzero in

theorem iso_desc [Module.FinitePresentation B₀ P] [Module.FinitePresentation B₀ Q]
    (e : Bω ⊗[B₀] P ≃ₗ[Bω] Bω ⊗[B₀] Q) :
    ∃ (i : ι) (eᵢ : B i ⊗[B₀] P ≃ₗ[B i] B i ⊗[B₀] Q),
      (e : _ →ₗ[Bω] _).restrictScalars B₀ ∘ₗ (g i).toLinearMap.rTensor P =
        (g i).toLinearMap.rTensor Q ∘ₗ (eᵢ : _ →ₗ[B i] _).restrictScalars B₀ := by
  have := directedSystem_linear B τ
  have τcomp : ∀ (a b c : ι) (hab : a ≤ b) (hbc : b ≤ c),
      (τ b c hbc).toLinearMap ∘ₗ (τ a b hab).toLinearMap = (τ a c (hab.trans hbc)).toLinearMap :=
    fun a b c hab hbc => LinearMap.ext fun x =>
      DirectedSystem.map_map (f := fun i j h => ⇑(τ i j h)) hab hbc x

  obtain ⟨i₁, u₁, hu₁⟩ := exists_factor_of_finitePresentation (G := fun k => B k ⊗[B₀] Q)
    (fun k l h => (τ k l h).toLinearMap.rTensor Q) (fun k => (g k).toLinearMap.rTensor Q)
    (gQ_compat B τ Bω g hg Q) (gQ_surj B τ Bω g hg hsurj Q) (gQ_zero B τ Bω g hg hsurj hzero Q)
    ((e : _ →ₗ[Bω] _).restrictScalars B₀ ∘ₗ TensorProduct.mk B₀ Bω P 1)
  obtain ⟨i₂, u₂, hu₂⟩ := exists_factor_of_finitePresentation (G := fun k => B k ⊗[B₀] P)
    (fun k l h => (τ k l h).toLinearMap.rTensor P) (fun k => (g k).toLinearMap.rTensor P)
    (gQ_compat B τ Bω g hg P) (gQ_surj B τ Bω g hg hsurj P) (gQ_zero B τ Bω g hg hsurj hzero P)
    ((e.symm : _ →ₗ[Bω] _).restrictScalars B₀ ∘ₗ TensorProduct.mk B₀ Bω Q 1)
  obtain ⟨i, h₁, h₂⟩ := exists_ge_ge i₁ i₂
  let u : P →ₗ[B₀] B i ⊗[B₀] Q := (τ i₁ i h₁).toLinearMap.rTensor Q ∘ₗ u₁
  let u' : Q →ₗ[B₀] B i ⊗[B₀] P := (τ i₂ i h₂).toLinearMap.rTensor P ∘ₗ u₂
  have hu : ∀ p, (g i).toLinearMap.rTensor Q (u p) = e (1 ⊗ₜ p) := fun p => by
    simp only [u, LinearMap.comp_apply, gQ_compat B τ Bω g hg Q]
    exact LinearMap.congr_fun hu₁ p
  have hu' : ∀ q, (g i).toLinearMap.rTensor P (u' q) = e.symm (1 ⊗ₜ q) := fun q => by
    simp only [u', LinearMap.comp_apply, gQ_compat B τ Bω g hg P]
    exact LinearMap.congr_fun hu₂ q

  let ψ : ∀ k, i ≤ k → (B k ⊗[B₀] P →ₗ[B k] B k ⊗[B₀] Q) := fun k hk =>
    ((τ i k hk).toLinearMap.rTensor Q ∘ₗ u).liftBaseChange (B k)
  let ψ' : ∀ k, i ≤ k → (B k ⊗[B₀] Q →ₗ[B k] B k ⊗[B₀] P) := fun k hk =>
    ((τ i k hk).toLinearMap.rTensor P ∘ₗ u').liftBaseChange (B k)

  have K1 : ∀ k (hk : i ≤ k) (z : B i ⊗[B₀] Q),
      ψ' k hk ((τ i k hk).toLinearMap.rTensor Q z) =
        (τ i k hk).toLinearMap.rTensor P (ψ' i le_rfl z) := by
    intro k hk z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c q =>
      simp only [ψ', LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        LinearMap.liftBaseChange_tmul, rTensor_algHom_smul, LinearMap.comp_apply, rTensor_self B τ i]
  have K1' : ∀ k (hk : i ≤ k) (z : B i ⊗[B₀] P),
      ψ k hk ((τ i k hk).toLinearMap.rTensor P z) =
        (τ i k hk).toLinearMap.rTensor Q (ψ i le_rfl z) := by
    intro k hk z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c q =>
      simp only [ψ, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        LinearMap.liftBaseChange_tmul, rTensor_algHom_smul, LinearMap.comp_apply, rTensor_self B τ i]

  have sq : (g i).toLinearMap.rTensor Q ∘ₗ (ψ i le_rfl).restrictScalars B₀ =
      (e : _ →ₗ[Bω] _).restrictScalars B₀ ∘ₗ (g i).toLinearMap.rTensor P := by
    apply TensorProduct.ext'
    intro b p
    rw [rTensor_comp_apply_tmul, comp_rTensor_apply_tmul]
    congr 1
    simp only [ψ, LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply, rTensor_self B τ i]
    exact hu p
  have sq' : (g i).toLinearMap.rTensor P ∘ₗ (ψ' i le_rfl).restrictScalars B₀ =
      (e.symm : _ →ₗ[Bω] _).restrictScalars B₀ ∘ₗ (g i).toLinearMap.rTensor Q := by
    apply TensorProduct.ext'
    intro b q
    rw [rTensor_comp_apply_tmul, comp_rTensor_apply_tmul]
    congr 1
    simp only [ψ', LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply, rTensor_self B τ i]
    exact hu' q

  obtain ⟨j₁, hij₁, E₁⟩ := hom_inj B τ Bω g hg hsurj hzero P P i (ψ' i le_rfl ∘ₗ ψ i le_rfl)
    LinearMap.id (by
      rw [LinearMap.restrictScalars_comp, ← LinearMap.comp_assoc, sq', LinearMap.comp_assoc, sq,
        ← LinearMap.comp_assoc]
      ext x
      simp)
  obtain ⟨j₂, hij₂, E₂⟩ := hom_inj B τ Bω g hg hsurj hzero Q Q i (ψ i le_rfl ∘ₗ ψ' i le_rfl)
    LinearMap.id (by
      rw [LinearMap.restrictScalars_comp, ← LinearMap.comp_assoc, sq, LinearMap.comp_assoc, sq',
        ← LinearMap.comp_assoc]
      ext x
      simp)
  obtain ⟨k, hk₁, hk₂⟩ := exists_ge_ge j₁ j₂
  have hik : i ≤ k := hij₁.trans hk₁

  have inv₁ : ψ' k hik ∘ₗ ψ k hik = LinearMap.id := by
    apply ext_one_tmul
    intro p
    have step : ψ k hik (1 ⊗ₜ p) = (τ i k hik).toLinearMap.rTensor Q (ψ i le_rfl (1 ⊗ₜ p)) := by
      rw [← K1', LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]
    rw [LinearMap.comp_apply, step, K1, ← τcomp i j₁ k hij₁ hk₁, LinearMap.rTensor_comp,
      LinearMap.comp_apply]
    have := LinearMap.congr_fun E₁ (1 ⊗ₜ p)
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.id_apply] at this
    rw [this]
    simp [LinearMap.rTensor_tmul]
  have inv₂ : ψ k hik ∘ₗ ψ' k hik = LinearMap.id := by
    apply ext_one_tmul
    intro q
    have step : ψ' k hik (1 ⊗ₜ q) = (τ i k hik).toLinearMap.rTensor P (ψ' i le_rfl (1 ⊗ₜ q)) := by
      rw [← K1, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]
    rw [LinearMap.comp_apply, step, K1', ← τcomp i j₂ k hij₂ hk₂, LinearMap.rTensor_comp,
      LinearMap.comp_apply]
    have := LinearMap.congr_fun E₂ (1 ⊗ₜ q)
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.id_apply] at this
    rw [this]
    simp [LinearMap.rTensor_tmul]
  refine ⟨k, LinearEquiv.ofLinearMap (ψ k hik) (ψ' k hik) inv₂ inv₁, ?_⟩

  apply TensorProduct.ext'
  intro b p
  rw [comp_rTensor_apply_tmul, rTensor_comp_apply_tmul]
  congr 1
  change e (1 ⊗ₜ p) = (g k).toLinearMap.rTensor Q (ψ k hik (1 ⊗ₜ p))
  simp only [ψ, LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply, gQ_compat B τ Bω g hg Q]
  exact (hu p).symm

end Descent

end S17LFP

universe u v w

theorem solution
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {B₀ : Type u} [CommRing B₀]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra B₀ (B i)]
    (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) [DirectedSystem B (fun i j h => τ i j h)]
    (Bω : Type u) [CommRing Bω] [Algebra B₀ Bω] (g : ∀ i, B i →ₐ[B₀] Bω)
    (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i)
    (hsurj : ∀ b : Bω, ∃ i x, g i x = b)
    (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0)
    (P Q : Type w) [AddCommGroup P] [Module B₀ P] [AddCommGroup Q] [Module B₀ Q]
    [Module.FinitePresentation B₀ P] [Module.FinitePresentation B₀ Q]
    (e : TensorProduct B₀ Bω P ≃ₗ[Bω] TensorProduct B₀ Bω Q) :
    ∃ (i : ι) (eᵢ : TensorProduct B₀ (B i) P ≃ₗ[B i] TensorProduct B₀ (B i) Q),
      (e : _ →ₗ[Bω] _).restrictScalars B₀ ∘ₗ (g i).toLinearMap.rTensor P =
        (g i).toLinearMap.rTensor Q ∘ₗ (eᵢ : _ →ₗ[B i] _).restrictScalars B₀ :=
  S17LFP.iso_desc B τ Bω g hg hsurj hzero P Q e
