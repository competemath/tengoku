/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.RingTheory.TensorProduct.Maps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Splitting tensor products along a splitting of the base

Let `R → A → B` be ring maps and `O` an `R`-algebra. Suppose `O ⊗[R] A ≅ ∏ᵥ Pᵥ` and
`O ⊗[R] B ≅ ∏_w Q_w` compatibly, where every `w` lies over some `v = π w` and `Pᵥ → Q_w` is given.
Then `Pᵥ ⊗[A] B ≅ ∏_{π w = v} Q_w` for every `v`
(`ComplexAnalytic.TensorTower.bijective_liftAt`). This is how the stalks of a finite étale cover
of `V^an` are computed from those of its composite with a finite map `V^an → ℂ`.

We also record that such a statement is unchanged when the base ring `R` and the ring `O` are
replaced by isomorphic rings (`ComplexAnalytic.TensorTower.bijective_transferLift`).
-/
open TensorProduct

universe u

namespace ComplexAnalytic.TensorTower

section Tower

variable {R A B O : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing O] [Algebra R A]
  [Algebra A B] [Algebra R B] [IsScalarTower R A B] [Algebra R O]
  {ι J : Type*} (P : ι → Type*) [∀ v, CommRing (P v)]
  (αP : ∀ v, O →+* P v) (βP : ∀ v, A →+* P v)
  (hαβ : ∀ v r, αP v (algebraMap R O r) = βP v (algebraMap R A r))
  (π : J → ι) (Q : J → Type*) [∀ w, CommRing (Q w)]
  (γ : ∀ v (w : {w // π w = v}), P v →+* Q w.1) (δ : ∀ w, B →+* Q w)
  (hγδ : ∀ w a, δ w (algebraMap A B a) = γ (π w) ⟨w, rfl⟩ (βP (π w) a))

/-- The map `O ⊗[R] A → ∏ᵥ Pᵥ`. -/
noncomputable def lift₁ : O ⊗[R] A →+* ∀ v, P v :=
  letI : Algebra O (∀ v, P v) := (RingHom.pi αP).toAlgebra
  letI : Algebra R (∀ v, P v) := ((RingHom.pi αP).comp (algebraMap R O)).toAlgebra
  haveI : IsScalarTower R O (∀ v, P v) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  (Algebra.TensorProduct.lift (Algebra.ofId O _)
    { toRingHom := RingHom.pi βP
      commutes' := fun r ↦ funext fun v ↦ (hαβ v r).symm }
    fun _ _ ↦ Commute.all _ _).toRingHom

include hαβ hγδ in
lemma comp_γ_comp_αP (w : J) (r : R) :
    (γ (π w) ⟨w, rfl⟩).comp (αP (π w)) (algebraMap R O r) = δ w (algebraMap R B r) := by
  rw [IsScalarTower.algebraMap_apply R A B, hγδ, RingHom.comp_apply, hαβ]

/-- The map `O ⊗[R] B → ∏_w Q_w`. -/
noncomputable def lift₂ : O ⊗[R] B →+* ∀ w, Q w :=
  letI : Algebra O (∀ w, Q w) := (RingHom.pi fun w ↦ (γ (π w) ⟨w, rfl⟩).comp (αP (π w))).toAlgebra
  letI : Algebra R (∀ w, Q w) := ((RingHom.pi fun w ↦
    (γ (π w) ⟨w, rfl⟩).comp (αP (π w))).comp (algebraMap R O)).toAlgebra
  haveI : IsScalarTower R O (∀ w, Q w) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  (Algebra.TensorProduct.lift (Algebra.ofId O _)
    { toRingHom := RingHom.pi δ
      commutes' := fun r ↦ funext fun w ↦ (comp_γ_comp_αP P αP βP hαβ π Q γ δ hγδ w r).symm }
    fun _ _ ↦ Commute.all _ _).toRingHom

/-- The map `Pᵥ ⊗[A] B → ∏_{w ↦ v} Q_w`. -/
noncomputable def liftAt (v : ι) :
    letI := (βP v).toAlgebra
    P v ⊗[A] B →+* ∀ w : {w // π w = v}, Q w.1 :=
  letI := (βP v).toAlgebra
  letI : Algebra (P v) (∀ w : {w // π w = v}, Q w.1) := (RingHom.pi (γ v)).toAlgebra
  letI : Algebra A (∀ w : {w // π w = v}, Q w.1) := ((RingHom.pi (γ v)).comp (βP v)).toAlgebra
  haveI : IsScalarTower A (P v) (∀ w : {w // π w = v}, Q w.1) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  (Algebra.TensorProduct.lift (Algebra.ofId (P v) _)
    { toRingHom := RingHom.pi fun w ↦ δ w.1
      commutes' := fun a ↦ funext fun w ↦ by
        obtain ⟨w, rfl⟩ := w
        exact hγδ w a }
    fun _ _ ↦ Commute.all _ _).toRingHom

lemma lift₁_tmul (s : O) (a : A) (v : ι) : lift₁ P αP βP hαβ (s ⊗ₜ a) v = αP v s * βP v a :=
  rfl

lemma lift₂_tmul (s : O) (b : B) (w : J) :
    lift₂ P αP βP hαβ π Q γ δ hγδ (s ⊗ₜ b) w = γ (π w) ⟨w, rfl⟩ (αP (π w) s) * δ w b :=
  rfl

lemma liftAt_tmul (v : ι) (p : P v) (b : B) (w : {w // π w = v}) :
    letI := (βP v).toAlgebra
    liftAt P βP π Q γ δ hγδ v (p ⊗ₜ b) w = γ v w p * δ w.1 b :=
  rfl

/-- **Splitting a finite algebra along a splitting of the base.** If `O ⊗[R] A ≅ ∏ᵥ Pᵥ` and
`O ⊗[R] B ≅ ∏_w Q_w` compatibly, with `w` lying over `π w`, then `Pᵥ ⊗[A] B ≅ ∏_{π w = v} Q_w` for
every `v`. -/
theorem bijective_liftAt (h₁ : Function.Bijective (lift₁ P αP βP hαβ))
    (h₂ : Function.Bijective (lift₂ P αP βP hαβ π Q γ δ hγδ)) (v : ι) :
    letI := (βP v).toAlgebra
    Function.Bijective (liftAt P βP π Q γ δ hγδ v) := by
  classical
  letI := (βP v).toAlgebra
  letI : Algebra R (P v ⊗[A] B) := ((algebraMap A (P v ⊗[A] B)).comp (algebraMap R A)).toAlgebra
  let f : O →ₐ[R] P v ⊗[A] B :=
    { toRingHom := Algebra.TensorProduct.includeLeftRingHom.comp (αP v)
      commutes' := fun r ↦ by
        change αP v (algebraMap R O r) ⊗ₜ[A] (1 : B) = algebraMap A (P v ⊗[A] B) _
        rw [hαβ, Algebra.TensorProduct.algebraMap_apply]
        rfl }
  let g : B →ₐ[R] P v ⊗[A] B :=
    { toRingHom := Algebra.TensorProduct.includeRight.toRingHom
      commutes' := fun r ↦ by
        change (1 : P v) ⊗ₜ[A] algebraMap R B r = algebraMap A (P v ⊗[A] B) _
        rw [IsScalarTower.algebraMap_apply R A B, Algebra.TensorProduct.algebraMap_apply,
          ← Algebra.TensorProduct.tmul_one_eq_one_tmul] }
  let Ψ : O ⊗[R] B →+* P v ⊗[A] B :=
    (Algebra.TensorProduct.lift f g fun _ _ ↦ Commute.all _ _).toRingHom
  let ιAB : O ⊗[R] A →+* O ⊗[R] B :=
    (Algebra.TensorProduct.map (AlgHom.id R O) (IsScalarTower.toAlgHom R A B)).toRingHom
  have K1 : ∀ y (w : {w // π w = v}),
      liftAt P βP π Q γ δ hγδ v (Ψ y) w = lift₂ P αP βP hαβ π Q γ δ hγδ y w.1 := by
    intro y w
    obtain ⟨w, rfl⟩ := w
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]
    | tmul s b =>
      have e : Ψ (s ⊗ₜ b) = (αP _ s ⊗ₜ[A] (1 : B)) * ((1 : P _) ⊗ₜ b) := rfl
      rw [e, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, liftAt_tmul, lift₂_tmul]
    | add y y' hy hy' => simp only [map_add, Pi.add_apply, hy, hy']
  have K3 : ∀ e, Ψ (ιAB e) = lift₁ P αP βP hαβ e v ⊗ₜ (1 : B) := by
    intro e
    induction e using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply, TensorProduct.zero_tmul]
    | tmul s a =>
      change (αP v s ⊗ₜ[A] (1 : B)) * ((1 : P v) ⊗ₜ algebraMap A B a) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, lift₁_tmul,
        Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
      rfl
    | add e e' he he' => simp only [map_add, Pi.add_apply, he, he', TensorProduct.add_tmul]
  have K4 : ∀ e w, lift₂ P αP βP hαβ π Q γ δ hγδ (ιAB e) w =
      γ (π w) ⟨w, rfl⟩ (lift₁ P αP βP hαβ e (π w)) := by
    intro e w
    induction e using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]
    | tmul s a =>
      change γ (π w) ⟨w, rfl⟩ (αP (π w) s) * δ w (algebraMap A B a) = _
      rw [hγδ, lift₁_tmul, map_mul]
    | add e e' he he' => simp only [map_add, Pi.add_apply, he, he']
  have e2 : ∀ b : B, Ψ ((1 : O) ⊗ₜ b) = (1 : P v) ⊗ₜ b := fun b ↦ by
    change (αP v 1 ⊗ₜ[A] (1 : B)) * ((1 : P v) ⊗ₜ b) = _
    rw [map_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ ?_, fun t ↦ ?_⟩
  · have hΨ : Function.Surjective Ψ := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul p b =>
        obtain ⟨e, he⟩ := h₁.2 (Pi.single v p)
        refine ⟨ιAB e * ((1 : O) ⊗ₜ b), ?_⟩
        rw [map_mul, K3, he, Pi.single_eq_same, e2, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
      | add x y hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, map_add _ _ _⟩
    obtain ⟨y, rfl⟩ := hΨ z
    obtain ⟨e, he⟩ := h₁.2 (Pi.single v 1)
    have hy' : lift₂ P αP βP hαβ π Q γ δ hγδ (ιAB e * y) = 0 := by
      funext w
      rw [map_mul, Pi.mul_apply, K4, he]
      by_cases hw : π w = v
      · have := K1 y ⟨w, hw⟩
        rw [hz] at this
        rw [← this, Pi.zero_apply, mul_zero]
        rfl
      · rw [Pi.single_eq_of_ne hw, map_zero, zero_mul]
        rfl
    have h0 : ιAB e * y = 0 := h₂.1 (hy'.trans (map_zero _).symm)
    calc Ψ y = Ψ (ιAB e) * Ψ y := by
          rw [K3, he, Pi.single_eq_same, ← Algebra.TensorProduct.one_def, one_mul]
      _ = 0 := by rw [← map_mul, h0, map_zero]
  · let T : ∀ w, Q w := fun w ↦ if h : π w = v then t ⟨w, h⟩ else 0
    obtain ⟨y, hy⟩ := h₂.2 T
    refine ⟨Ψ y, funext fun w ↦ ?_⟩
    rw [K1, hy]
    simp only [T, dite_eq_left w.2]

end Tower

section Transfer

variable {R R₀ T O S Pt : Type*} [CommRing R] [CommRing R₀] [CommRing T] [CommRing O]
  [CommRing S] [CommRing Pt] [Algebra R₀ T] [Algebra R O] [Algebra R₀ S] [Algebra R S]
  (θ : R ≃+* R₀) (σ : T ≃+* O) (hσ : ∀ r, σ (algebraMap R₀ T (θ r)) = algebraMap R O r)
  (hS : ∀ r, algebraMap R₀ S (θ r) = algebraMap R S r)
  (α : O →+* Pt) (β : S →+* Pt) (hαβ : ∀ r, α (algebraMap R O r) = β (algebraMap R S r))

include hσ hS hαβ in
lemma hαβ₀ (r₀ : R₀) : α (σ (algebraMap R₀ T r₀)) = β (algebraMap R₀ S r₀) := by
  obtain ⟨r, rfl⟩ := θ.surjective r₀
  rw [hσ, hS]
  exact hαβ r

/-- The map `O ⊗[R] S → Pt`, `o ⊗ s ↦ α o * β s`. -/
noncomputable def transferLift : O ⊗[R] S →+* Pt :=
  letI : Algebra O Pt := α.toAlgebra
  letI : Algebra R Pt := (α.comp (algebraMap R O)).toAlgebra
  haveI : IsScalarTower R O Pt := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  (Algebra.TensorProduct.lift (Algebra.ofId O Pt)
    { toRingHom := β
      commutes' := fun r ↦ (hαβ r).symm }
    fun _ _ ↦ Commute.all _ _).toRingHom

/-- The map `T ⊗[R₀] S → Pt`, `t ⊗ s ↦ α (σ t) * β s`. -/
noncomputable def transferLift₀ : T ⊗[R₀] S →+* Pt :=
  letI : Algebra T Pt := (α.comp σ.toRingHom).toAlgebra
  letI : Algebra R₀ Pt := ((α.comp σ.toRingHom).comp (algebraMap R₀ T)).toAlgebra
  haveI : IsScalarTower R₀ T Pt := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  (Algebra.TensorProduct.lift (Algebra.ofId T Pt)
    { toRingHom := β
      commutes' := fun r ↦ (hαβ₀ θ σ hσ hS α β hαβ r).symm }
    fun _ _ ↦ Commute.all _ _).toRingHom

/-- **Changing the base ring and the local ring along isomorphisms.** -/
theorem bijective_transferLift (h : Function.Bijective (transferLift₀ θ σ hσ hS α β hαβ)) :
    Function.Bijective (transferLift α β hαβ) := by
  letI : Algebra R (T ⊗[R₀] S) := ((algebraMap R₀ (T ⊗[R₀] S)).comp θ.toRingHom).toAlgebra
  letI : Algebra R₀ (O ⊗[R] S) := ((algebraMap R (O ⊗[R] S)).comp θ.symm.toRingHom).toAlgebra
  let E : O ⊗[R] S →+* T ⊗[R₀] S :=
    (Algebra.TensorProduct.lift
      { toRingHom := Algebra.TensorProduct.includeLeftRingHom.comp σ.symm.toRingHom
        commutes' := fun r ↦ by
          change σ.symm (algebraMap R O r) ⊗ₜ[R₀] (1 : S) = algebraMap R₀ _ (θ r)
          rw [← hσ, RingEquiv.symm_apply_apply, Algebra.TensorProduct.algebraMap_apply] }
      { toRingHom := Algebra.TensorProduct.includeRight.toRingHom
        commutes' := fun r ↦ by
          change (1 : T) ⊗ₜ[R₀] algebraMap R S r = algebraMap R₀ _ (θ r)
          rw [← hS, Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.tmul_one_eq_one_tmul] }
      fun _ _ ↦ Commute.all _ _).toRingHom
  let E' : T ⊗[R₀] S →+* O ⊗[R] S :=
    (Algebra.TensorProduct.lift
      { toRingHom := Algebra.TensorProduct.includeLeftRingHom.comp σ.toRingHom
        commutes' := fun r₀ ↦ by
          obtain ⟨r, rfl⟩ := θ.surjective r₀
          change σ (algebraMap R₀ T (θ r)) ⊗ₜ[R] (1 : S) = algebraMap R _ (θ.symm (θ r))
          rw [hσ, RingEquiv.symm_apply_apply, Algebra.TensorProduct.algebraMap_apply] }
      { toRingHom := Algebra.TensorProduct.includeRight.toRingHom
        commutes' := fun r₀ ↦ by
          obtain ⟨r, rfl⟩ := θ.surjective r₀
          change (1 : O) ⊗ₜ[R] algebraMap R₀ S (θ r) = algebraMap R _ (θ.symm (θ r))
          rw [hS, RingEquiv.symm_apply_apply, Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.tmul_one_eq_one_tmul] }
      fun _ _ ↦ Commute.all _ _).toRingHom
  have hE : ∀ x, transferLift₀ θ σ hσ hS α β hαβ (E x) = transferLift α β hαβ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o s =>
      have e : E (o ⊗ₜ s) = σ.symm o ⊗ₜ s := by
        change (σ.symm o ⊗ₜ[R₀] (1 : S)) * ((1 : T) ⊗ₜ[R₀] s) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e]
      change α (σ (σ.symm o)) * β s = α o * β s
      rw [RingEquiv.apply_symm_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hE'E : ∀ x, E' (E x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o s =>
      have e : E (o ⊗ₜ s) = σ.symm o ⊗ₜ s := by
        change (σ.symm o ⊗ₜ[R₀] (1 : S)) * ((1 : T) ⊗ₜ[R₀] s) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e]
      change (σ (σ.symm o) ⊗ₜ[R] (1 : S)) * ((1 : O) ⊗ₜ[R] s) = o ⊗ₜ s
      rw [RingEquiv.apply_symm_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hEE' : ∀ x, E (E' x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul t s =>
      have e : E' (t ⊗ₜ s) = σ t ⊗ₜ s := by
        change (σ t ⊗ₜ[R] (1 : S)) * ((1 : O) ⊗ₜ[R] s) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e]
      change (σ.symm (σ t) ⊗ₜ[R₀] (1 : S)) * ((1 : T) ⊗ₜ[R₀] s) = t ⊗ₜ s
      rw [RingEquiv.symm_apply_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨fun x y hxy ↦ ?_, fun p ↦ ?_⟩
  · rw [← hE, ← hE] at hxy
    rw [← hE'E x, ← hE'E y, h.1 hxy]
  · obtain ⟨z, rfl⟩ := h.2 p
    exact ⟨E' z, by rw [← hE, hEE']⟩

end Transfer

end ComplexAnalytic.TensorTower
