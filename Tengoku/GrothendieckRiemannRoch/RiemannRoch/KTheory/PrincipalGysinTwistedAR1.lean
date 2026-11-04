/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.KTheory.PrincipalGysin
import Tengoku.Seed.CategoryTheory.Monoidal.Braided.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Gysin restriction to an effective Cartier divisor on Grothendieck groups (route AR1, leaf G6)

Generalisation of `ExactGrothendieck.PrincipalGysin` from a central endomorphism `τ : 𝟭 ⟶ 𝟭`
(principal divisor `t = 0`) to a natural transformation `σ : T ⟶ 𝟭` for an exact endofunctor `T`
(geometrically `T = L⁻¹ ⊗ -` and `σ` the section `L⁻¹ → O` cutting out an effective Cartier
divisor `D`; the Koszul sequence `0 → L⁻¹ → O → O_D → 0` gives `E ⊗ O_D = coker σ_E`,
`Tor₁(E, O_D) = ker σ_E`).

* `cartierGysin σ : G(P) →+ G(P ∩ {σ = 0})`, `[E] ↦ [coker σ_E] - [ker σ_E]`, well defined by the
  snake lemma applied to `T S → S`;
* `cartierGysin_classOf_of_mono`: on `σ`-regular objects it is `[E/σE]`;
* `cartierGysin_pushDivisor`: `D^! D_* [F] = [F] - [T F]` (self-intersection formula; for trivial
  `L` this recovers `j^! j_* = 0`);
* `pushDivisor_cartierGysin`: `D_* D^! [E] = [E] - [T E]`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open ExactGrothendieck.PrincipalGysin (KerCokerClosed classOf_eq_ker_add_ker classOf_eq_ker_add_of_epi classOf_eq_of_iso six_term)

universe u v

namespace ExactGrothendieck

namespace CartierGysinAR1

variable {C : Type u} [Category.{v} C] [Abelian C]

section Defs

variable (T : C ⥤ C) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T] [T.PreservesMonomorphisms]
variable (σ : T ⟶ 𝟭 C)

/-- The component of `σ` at `A`.-/
def ap (A : C) : T.obj A ⟶ A := σ.app A

/--
@isnad1 id=eq.0h6v.s7.f981f3546244 from=translated src=- shape=e2ff2352 vocab=9e5f7e0f
-/
theorem naturality' {A B : C} (f : A ⟶ B) : T.map f ≫ ap T σ B = ap T σ A ≫ f := by
  simpa [ap] using σ.naturality f

/-- Objects killed by `σ` (sheaves supported scheme-theoretically on the divisor).-/
def Killed (P : C → Prop) (E : C) : Prop := P E ∧ ap T σ E = 0

/-- `σ` is compatible with the twist: `σ_{T E} = T σ_E` (true for `T = L⁻¹ ⊗ -`, since the
tensor product of line-bundle maps is symmetric).-/
def Central : Prop :=
  ∀ E : C, ap T σ (T.obj E) = T.map (ap T σ E)

end Defs

section Gysin

variable {T : C ⥤ C} [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T] [T.PreservesMonomorphisms]
variable {σ : T ⟶ 𝟭 C} {P : C → Prop}

/--
@isnad1 id=eq.1h6v.s7.3db62009e704 from=translated src=- shape=df8f8e52 vocab=d545b4d8
-/
theorem app_eq_zero_of_mono {A B : C} (f : A ⟶ B) [Mono f] (hB : ap T σ B = 0) :
    ap T σ A = 0 := by
  rw [← cancel_mono f, ← naturality' T σ f, hB, comp_zero, zero_comp]

/--
@isnad1 id=eq.1h6v.s7.e946dbf32dbf from=translated src=- shape=3196a7a5 vocab=0357aab3
-/
theorem app_eq_zero_of_epi {A B : C} (f : A ⟶ B) [Epi f] (hA : ap T σ A = 0) :
    ap T σ B = 0 := by
  haveI : Epi (T.map f) := inferInstance
  rw [← cancel_epi (T.map f), naturality' T σ f, hA, zero_comp, comp_zero]

/--
@isnad1 id=kercoker.1h4v.s6.8dbaf34ea023 from=translated src=- shape=136be84e vocab=da76f94c
-/
theorem killedClosed (hP : KerCokerClosed P) : KerCokerClosed (Killed T σ P) where
  zero := ⟨hP.zero, (isZero_zero C).eq_of_tgt _ _⟩
  kernel f hA hB := ⟨hP.kernel f hA.1 hB.1, app_eq_zero_of_mono (kernel.ι f) hA.2⟩
  cokernel f hA hB := ⟨hP.cokernel f hA.1 hB.1, app_eq_zero_of_epi (cokernel.π f) hB.2⟩

/--
@isnad1 id=eq.1h4v.s8.99a03f1d373d from=translated src=- shape=af078890 vocab=6d74fc8e
-/
theorem app_kernel_eq_zero (hc : Central T σ) (E : C) :
    ap T σ (kernel (ap T σ E)) = 0 := by
  rw [← cancel_mono (kernel.ι (ap T σ E)), ← naturality' T σ (kernel.ι (ap T σ E)), hc,
    ← Functor.map_comp, kernel.condition, Functor.map_zero, zero_comp]

/--
@isnad1 id=eq.0h4v.s8.12b648db01a9 from=translated src=- shape=f5b072fe vocab=284c7b25
-/
theorem app_cokernel_eq_zero (E : C) : ap T σ (cokernel (ap T σ E)) = 0 := by
  rw [← cancel_epi (T.map (cokernel.π (ap T σ E))), naturality' T σ, cokernel.condition,
    comp_zero]

variable (hc : Central T σ) (hP : KerCokerClosed P) (hT : ∀ E, P E → P (T.obj E))
include hc hP hT

/--
@isnad1 id=killed.2h7v.s7.604d2e7d6371 from=translated src=- shape=7a9dcbab vocab=3b1574a8
-/
theorem killed_kernel {E : C} (hE : P E) : Killed T σ P (kernel (ap T σ E)) :=
  ⟨hP.kernel _ (hT E hE) hE, app_kernel_eq_zero hc E⟩

/--
@isnad1 id=killed.2h7v.s7.245ae9779047 from=translated src=- shape=7a9dcbab vocab=818c5cf3
-/
theorem killed_cokernel {E : C} (hE : P E) : Killed T σ P (cokernel (ap T σ E)) :=
  ⟨hP.cokernel _ (hT E hE) hE, app_cokernel_eq_zero E⟩

/-- The value of the Cartier Gysin map on one object: `[coker σ_E] - [ker σ_E]`, i.e.
`[E ⊗ O_D] - [Tor₁(E, O_D)]`.-/
def gysinObj (E : {E : C // P E}) : SubcategoryGroup C (Killed T σ P) :=
  subcategoryClassOf C (Killed T σ P) (cokernel (ap T σ E.1)) (killed_cokernel hc hP hT E.2) -
    subcategoryClassOf C (Killed T σ P) (kernel (ap T σ E.1)) (killed_kernel hc hP hT E.2)

omit hc hP hT in
/-- The snake input attached to `σ` acting on a short exact sequence: the top row is `T S`.-/
def snakeInput (S : ShortComplex C) (hS : S.ShortExact) : ShortComplex.SnakeInput C :=
  haveI := hS.mono_f
  haveI := hS.epi_g
  {
  L₀ := ShortComplex.mk (kernel.map (ap T σ S.X₁) (ap T σ S.X₂) (T.map S.f) S.f
      (naturality' T σ S.f).symm)
    (kernel.map (ap T σ S.X₂) (ap T σ S.X₃) (T.map S.g) S.g (naturality' T σ S.g).symm)
    (by
      have h : T.map S.f ≫ T.map S.g = 0 := by rw [← T.map_comp, S.zero, T.map_zero]
      apply (cancel_mono (kernel.ι _)).1; simp [kernel.map, h])
  L₁ := S.map T
  L₂ := S
  L₃ := ShortComplex.mk (cokernel.map (ap T σ S.X₁) (ap T σ S.X₂) (T.map S.f) S.f (naturality' T σ S.f).symm)
    (cokernel.map (ap T σ S.X₂) (ap T σ S.X₃) (T.map S.g) S.g (naturality' T σ S.g).symm)
    (by apply (cancel_epi (cokernel.π _)).1; simp [cokernel.map])
  v₀₁ := { τ₁ := kernel.ι _, τ₂ := kernel.ι _, τ₃ := kernel.ι _
           comm₁₂ := (kernel.lift_ι _ _ _).symm, comm₂₃ := (kernel.lift_ι _ _ _).symm }
  v₁₂ := { τ₁ := ap T σ S.X₁, τ₂ := ap T σ S.X₂, τ₃ := ap T σ S.X₃
           comm₁₂ := (naturality' T σ S.f).symm, comm₂₃ := (naturality' T σ S.g).symm }
  v₂₃ := { τ₁ := cokernel.π _, τ₂ := cokernel.π _, τ₃ := cokernel.π _
           comm₁₂ := (cokernel.π_desc _ _ _), comm₂₃ := (cokernel.π_desc _ _ _) }
  w₀₂ := by ext <;> exact kernel.condition _
  w₁₃ := by ext <;> exact cokernel.condition _
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ <;>
      apply (KernelFork.isLimitMapConeEquiv _ _).2 <;> exact kernelIsKernel _
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ <;>
      apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2 <;> exact cokernelIsCokernel _
  L₁_exact := (hS.map T).exact
  epi_L₁_g := (hS.map T).epi_g
  L₂_exact := hS.exact
  mono_L₂_f := hS.mono_f }

/--
@isnad1 id=eq.3h8v.s8.293e5c2efc25 from=translated src=- shape=bb7bd05e vocab=65a37ea2
-/
theorem gysinObj_additive (A B D : {E : C // P E}) (h : shortExactIn C P A B D) :
    gysinObj hc hP hT B = gysinObj hc hP hT A + gysinObj hc hP hT D := by
  obtain ⟨f, g, zero, hS⟩ := h
  let S := ShortComplex.mk f g zero
  haveI := hS.mono_f
  haveI := hS.epi_g
  let I := snakeInput (T := T) (σ := σ) S hS
  have hQ := killedClosed (T := T) (σ := σ) hP
  haveI : Mono I.L₀.f := by
    have w : I.L₀.f ≫ kernel.ι (ap T σ S.X₂) = kernel.ι (ap T σ S.X₁) ≫ T.map S.f :=
      kernel.lift_ι _ _ _
    haveI hm : Mono (T.map S.f) := (hS.map T).mono_f
    haveI : Mono (I.L₀.f ≫ kernel.ι (ap T σ S.X₂)) := by
      rw [w]; exact @mono_comp _ _ _ _ _ (kernel.ι _) _ (T.map S.f) hm
    exact mono_of_mono _ (kernel.ι (ap T σ S.X₂))
  haveI : Epi I.L₃.g := by
    have w : cokernel.π (ap T σ S.X₂) ≫ I.L₃.g = S.g ≫ cokernel.π (ap T σ S.X₃) :=
      cokernel.π_desc _ _ _
    haveI : Epi (cokernel.π (ap T σ S.X₂) ≫ I.L₃.g) := by
      rw [w]; exact @epi_comp _ _ _ _ _ S.g hS.epi_g (cokernel.π _) _
    exact epi_of_epi (cokernel.π (ap T σ S.X₂)) _
  have key : subcategoryClassOf C (Killed T σ P) (kernel (ap T σ A.1))
        (killed_kernel hc hP hT A.2) -
      subcategoryClassOf C (Killed T σ P) (kernel (ap T σ B.1)) (killed_kernel hc hP hT B.2) +
      subcategoryClassOf C (Killed T σ P) (kernel (ap T σ D.1)) (killed_kernel hc hP hT D.2) -
      subcategoryClassOf C (Killed T σ P) (cokernel (ap T σ A.1)) (killed_cokernel hc hP hT A.2) +
      subcategoryClassOf C (Killed T σ P) (cokernel (ap T σ B.1)) (killed_cokernel hc hP hT B.2) -
      subcategoryClassOf C (Killed T σ P) (cokernel (ap T σ D.1))
        (killed_cokernel hc hP hT D.2) = 0 :=
    six_term hQ I.L₀.f I.L₀.g I.δ I.L₃.f I.L₃.g I.L₀.zero I.L₀_g_δ I.δ_L₃_f
    I.L₃.zero I.L₀_exact I.L₁'_exact I.L₂'_exact I.L₃_exact
    (killed_kernel hc hP hT A.2) (killed_kernel hc hP hT B.2) (killed_kernel hc hP hT D.2)
    (killed_cokernel hc hP hT A.2) (killed_cokernel hc hP hT B.2) (killed_cokernel hc hP hT D.2)
  simp only [gysinObj]
  rw [← sub_eq_zero, ← key]
  abel

/-- **Gysin restriction to an effective Cartier divisor** `D^! : G(P) → G(P ∩ {σ = 0})`,
`[E] ↦ [coker σ_E] - [ker σ_E]`. Well defined by the snake lemma.-/
def cartierGysin : SubcategoryGroup C P →+ SubcategoryGroup C (Killed T σ P) :=
  lift (gysinObj hc hP hT) (gysinObj_additive hc hP hT)

/--
@isnad1 id=eq.2h7v.s9.e3c2ba318620 from=translated src=- shape=b2259ddc vocab=82b19f58
-/
@[simp]
theorem cartierGysin_classOf (E : C) (hE : P E) :
    cartierGysin hc hP hT (subcategoryClassOf C P E hE) =
      subcategoryClassOf C (Killed T σ P) (cokernel (ap T σ E)) (killed_cokernel hc hP hT hE) -
        subcategoryClassOf C (Killed T σ P) (kernel (ap T σ E)) (killed_kernel hc hP hT hE) :=
  lift_classOf _ _ _

/-- If `σ_E` is injective (`σ` a non-zero-divisor on `E`), the Gysin class is the naive
restriction `[E/σE] = [E ⊗ O_D]`.
@isnad1 id=eq.2h7v.s9.87e807f53a98 from=translated src=- shape=aa50e7c6 vocab=21f6c402
-/
theorem cartierGysin_classOf_of_mono (E : C) (hE : P E) [Mono (ap T σ E)] :
    cartierGysin hc hP hT (subcategoryClassOf C P E hE) =
      subcategoryClassOf C (Killed T σ P) (cokernel (ap T σ E)) (killed_cokernel hc hP hT hE) := by
  rw [cartierGysin_classOf, subcategoryClassOf_isZero C _ _ (isZero_kernel_of_mono _), sub_zero]

omit hc hP hT in
/-- Pushforward from the divisor: the inclusion of `σ`-killed objects.-/
def pushDivisor : SubcategoryGroup C (Killed T σ P) →+ SubcategoryGroup C P :=
  map (fun E => ⟨E.1, E.2.1⟩) fun _ _ _ ⟨f, g, zero, h⟩ => ⟨f, g, zero, h⟩

omit hc hP hT in
/--
@isnad1 id=eq.1h5v.s9.03d46db0379a from=translated src=- shape=f3102765 vocab=b619aa87
-/
@[simp]
theorem pushDivisor_classOf (E : C) (hE : Killed T σ P E) :
    pushDivisor (T := T) (σ := σ) (subcategoryClassOf C (Killed T σ P) E hE) =
      subcategoryClassOf C P E hE.1 := by
  simp [pushDivisor, subcategoryClassOf, map]

/-- **Self-intersection formula** `D^! D_* [F] = [F] - [T F]` for `F` supported on `D`
(`T F = L⁻¹ ⊗ F`; for trivial `L` this is `j^! j_* = 0`).
@isnad1 id=eq.3h6v.s10.743fa3ddffd0 from=translated src=- shape=329bd71d vocab=451120c4
-/
theorem cartierGysin_pushDivisor (F : C) (hF : Killed T σ P F) :
    cartierGysin hc hP hT (pushDivisor (T := T) (σ := σ)
        (subcategoryClassOf C (Killed T σ P) F hF)) =
      subcategoryClassOf C (Killed T σ P) F hF -
        subcategoryClassOf C (Killed T σ P) (T.obj F)
          ⟨hT F hF.1, (hc F).trans (by rw [hF.2, T.map_zero])⟩ := by
  have hQ := killedClosed (T := T) (σ := σ) hP
  have hTF : Killed T σ P (T.obj F) := ⟨hT F hF.1, (hc F).trans (by rw [hF.2, T.map_zero])⟩
  rw [pushDivisor_classOf, cartierGysin_classOf]
  have e₁ : cokernel (ap T σ F) ≅ F :=
    cokernelIsoOfEq hF.2 ≪≫ (asIso (cokernel.π (0 : T.obj F ⟶ F))).symm
  have e₂ : kernel (ap T σ F) ≅ T.obj F :=
    kernelIsoOfEq hF.2 ≪≫ asIso (kernel.ι (0 : T.obj F ⟶ F))
  rw [classOf_eq_of_iso hQ e₁ (killed_cokernel hc hP hT hF.1) hF,
    classOf_eq_of_iso hQ e₂ (killed_kernel hc hP hT hF.1) hTF]

/-- `D_* D^! [E] = [E] - [T E]` in `G(P)` (four-term sequence `0 → ker σ_E → T E → E → coker σ_E → 0`;
the class of `O_D` is `1 - [L⁻¹]`).
@isnad1 id=eq.2h7v.s10.f55c81098617 from=translated src=- shape=7274bab7 vocab=4a7619a5
-/
theorem pushDivisor_cartierGysin (E : C) (hE : P E) :
    pushDivisor (T := T) (σ := σ) (cartierGysin hc hP hT (subcategoryClassOf C P E hE)) =
      subcategoryClassOf C P E hE - subcategoryClassOf C P (T.obj E) (hT E hE) := by
  rw [cartierGysin_classOf, map_sub, pushDivisor_classOf, pushDivisor_classOf]
  have hQ : P (cokernel (ap T σ E)) := hP.cokernel _ (hT E hE) hE
  have r₁ := classOf_eq_ker_add_ker hP _ (ShortComplex.exact_cokernel (ap T σ E)) (hT E hE) hE hQ
  have r₂ := classOf_eq_ker_add_of_epi hP (cokernel.π (ap T σ E)) hE hQ
  dsimp only at r₁
  rw [r₁, r₂]
  abel

end Gysin

section Monoidal

open MonoidalCategory

variable [MonoidalCategory C] [BraidedCategory C] (Λ : C) (s : Λ ⟶ 𝟙_ C)

/-- The Koszul map `σ_E = s ⊗ E : Λ ⊗ E → 𝟙 ⊗ E ≅ E` (for `Λ = L⁻¹`, `s` the section of the
divisor); a natural transformation `Λ ⊗ - ⟶ 𝟭`.-/
def koszulσ : tensorLeft Λ ⟶ 𝟭 C where
  app E := (s ▷ E) ≫ (λ_ E).hom
  naturality {A B} f := by
    change Λ ◁ f ≫ (s ▷ B ≫ (λ_ B).hom) = (s ▷ A ≫ (λ_ A).hom) ≫ f
    rw [← Category.assoc, whisker_exchange, Category.assoc, Category.assoc, leftUnitor_naturality]

/--
@isnad1 id=eq.0h4v.s7.5e23a29c53ba from=translated src=- shape=d572cce2 vocab=eb9b1027
-/
theorem koszulσ_app (E : C) : (koszulσ Λ s).app E = (s ▷ E) ≫ (λ_ E).hom := rfl

/-- If the braiding of `Λ` with itself is the identity (true for invertible sheaves), the Koszul
map is central: `σ_{Λ ⊗ E} = Λ ⊗ σ_E`.
@isnad1 id=central.1h3v.s6.bc41a2420865 from=translated src=- shape=60401b03 vocab=12915a82
-/
theorem koszulσ_central (hβ : (β_ Λ Λ).hom = 𝟙 _) :
    Central (tensorLeft Λ) (koszulσ Λ s) := by
  intro E
  have h1 : (s ▷ Λ) ≫ (λ_ Λ).hom = (Λ ◁ s) ≫ (ρ_ Λ).hom := by
    have hn := BraidedCategory.braiding_naturality_left s Λ
    simp only [hβ, Category.id_comp] at hn
    have hn' : (s ▷ Λ) ≫ (λ_ Λ).hom ≫ (ρ_ Λ).inv = Λ ◁ s := by simpa using hn
    calc (s ▷ Λ) ≫ (λ_ Λ).hom = ((s ▷ Λ) ≫ (λ_ Λ).hom ≫ (ρ_ Λ).inv) ≫ (ρ_ Λ).hom := by simp
      _ = _ := by rw [hn']
  change (s ▷ (Λ ⊗ E)) ≫ (λ_ (Λ ⊗ E)).hom = Λ ◁ ((s ▷ E) ≫ (λ_ E).hom)
  have e : s ▷ (Λ ⊗ E) = (α_ Λ Λ E).inv ≫ (s ▷ Λ) ▷ E ≫ (α_ (𝟙_ C) Λ E).hom := by
    rw [Iso.eq_inv_comp]; exact (associator_naturality_left s Λ E).symm
  have lt : (λ_ (Λ ⊗ E)).hom = (α_ (𝟙_ C) Λ E).inv ≫ (λ_ Λ).hom ▷ E := by simp
  rw [e, lt]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight, h1, comp_whiskerRight, ← triangle, ← Category.assoc ((Λ ◁ s) ▷ E),
    associator_naturality_middle, Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp]

/-- **Cartier Gysin map of a divisor `(Λ = L⁻¹, s)`** in a braided monoidal abelian category
in which `Λ ⊗ -` is exact and `β_{Λ,Λ} = id`: `G(P) → G(P ∩ {s = 0})`.-/
def monoidalCartierGysin [PreservesFiniteLimits (tensorLeft Λ)]
    [PreservesFiniteColimits (tensorLeft Λ)] [(tensorLeft Λ).PreservesMonomorphisms]
    [(tensorLeft Λ).Additive] (hβ : (β_ Λ Λ).hom = 𝟙 _) {P : C → Prop}
    (hP : KerCokerClosed P) (hT : ∀ E, P E → P (Λ ⊗ E)) :
    SubcategoryGroup C P →+ SubcategoryGroup C (Killed (tensorLeft Λ) (koszulσ Λ s) P) :=
  cartierGysin (koszulσ_central Λ s hβ) hP hT

end Monoidal

end CartierGysinAR1

end ExactGrothendieck
