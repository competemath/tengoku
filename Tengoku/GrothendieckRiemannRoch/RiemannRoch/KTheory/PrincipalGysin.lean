/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.Algebra.Homology.ShortComplex.SnakeLemma
import Tengoku.Seed.CategoryTheory.Abelian.Exact
import Tengoku.Seed.Algebra.Category.ModuleCat.Abelian
import Tengoku.Seed.RingTheory.Flat.TorsionFree
import Tengoku.Seed.Algebra.Polynomial.Basic
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.KTheory.ExactCategory

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Gysin restriction to a principal divisor on Grothendieck groups

For an abelian category `C`, a class `P` of objects closed under kernels and cokernels, and a
central endomorphism `τ : 𝟭 C ⟶ 𝟭 C` (geometrically: multiplication by `t - c` for a family
`ρ : M → 𝔸¹`, the fibre `M_c = {t = c}` being a principal Cartier divisor), we construct

  `gysin : G(P) → G(P ∩ {τ = 0})`, `[E] ↦ [coker τ_E] - [ker τ_E]`

(`= [E ⊗ O_{M_c}] - [Tor₁(E, O_{M_c})]`), well defined by the snake lemma, and prove
* `gysin_classOf_of_mono`: on `τ`-regular objects (e.g. flat over the base line,
  `mono_ap_smulNatTrans_of_flat`) it is the naive restriction `[E/τE]`;
* `gysin_comp_pushDivisor`: `j^! j_* = 0` (the normal bundle of a principal divisor is trivial) —
  the input making Fulton's specialization map well defined (`KSpecialization.Data`);
* `pushDivisor_comp_gysin`: `j_* j^! = 0` (`[O_{M_c}] = 0` in the principal case).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

namespace ExactGrothendieck

namespace PrincipalGysin

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A full class of objects containing `0` and closed under kernels and cokernels of morphisms
between its members (coherent sheaves inside all `O_X`-modules on a noetherian scheme; note that
closure under arbitrary subobjects would be false there).-/
structure KerCokerClosed (P : C → Prop) : Prop where
  /-- contains the zero object-/
  zero : P 0
  /-- closed under kernels-/
  kernel : ∀ {A B : C} (f : A ⟶ B), P A → P B → P (kernel f)
  /-- closed under cokernels-/
  cokernel : ∀ {A B : C} (f : A ⟶ B), P A → P B → P (cokernel f)

variable {P : C → Prop}

section Telescoping

variable (hP : KerCokerClosed P)
include hP

/-- For an exact `A --f--> B --g--> D` in the class, `[A] = [ker f] + [ker g]`.
@isnad1 id=eq.2h6v.s8.261c4e11fd39 from=translated src=- shape=02b1fc9a vocab=8eba065b
-/
theorem classOf_eq_ker_add_ker (T : ShortComplex C) (hT : T.Exact) (hA : P T.X₁)
    (hB : P T.X₂) (hD : P T.X₃) :
    subcategoryClassOf C P T.X₁ hA =
      subcategoryClassOf C P (kernel T.f) (hP.kernel T.f hA hB) +
        subcategoryClassOf C P (kernel T.g) (hP.kernel T.g hB hD) := by
  haveI : Epi (kernel.lift T.g T.f T.zero) := hT.epi_kernelLift
  let S : ShortComplex C :=
    ShortComplex.mk (kernel.ι T.f) (kernel.lift T.g T.f T.zero)
      (by ext; simp)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _
        (isKernelOfComp (kernel.ι T.g) T.f (kernelIsKernel T.f) S.zero (kernel.lift_ι _ _ _)) }
  exact subcategoryClassOf_middle C P _ _ _ S.zero hS

/-- For an epimorphism `g : B ⟶ D`, `[B] = [ker g] + [D]`.
@isnad1 id=eq.1h7v.s7.cb912d6a659f from=translated src=- shape=b09dc4ea vocab=6a61551e
-/
theorem classOf_eq_ker_add_of_epi {B D : C} (g : B ⟶ D) [Epi g] (hB : P B) (hD : P D) :
    subcategoryClassOf C P B hB =
      subcategoryClassOf C P (kernel g) (hP.kernel g hB hD) +
        subcategoryClassOf C P D hD := by
  let S : ShortComplex C := ShortComplex.mk (kernel.ι g) g (by simp)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel g }
  exact subcategoryClassOf_middle C P _ _ _ S.zero hS

/--
@isnad1 id=eq.1h7v.s6.c55de48b70e7 from=translated src=- shape=ba7cf13b vocab=aed9aba9
-/
theorem classOf_eq_of_iso {A B : C} (e : A ≅ B) (hA : P A) (hB : P B) :
    subcategoryClassOf C P A hA = subcategoryClassOf C P B hB :=
  subcategoryClassOf_iso C P hA hB hP.zero (isZero_zero C) e

/-- Alternating sum over a six-term exact sequence `0 → X₀ → ⋯ → X₅ → 0` vanishes.
@isnad1 id=eq.9h19v.s10.f53691ec0e5d from=translated src=- shape=7b1f19e0 vocab=2ab0af90
-/
theorem six_term {X₀ X₁ X₂ X₃ X₄ X₅ : C} (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (f₃ : X₃ ⟶ X₄) (f₄ : X₄ ⟶ X₅) [Mono f₀] [Epi f₄]
    (w₁ : f₀ ≫ f₁ = 0) (w₂ : f₁ ≫ f₂ = 0) (w₃ : f₂ ≫ f₃ = 0) (w₄ : f₃ ≫ f₄ = 0)
    (e₁ : (ShortComplex.mk f₀ f₁ w₁).Exact) (e₂ : (ShortComplex.mk f₁ f₂ w₂).Exact)
    (e₃ : (ShortComplex.mk f₂ f₃ w₃).Exact) (e₄ : (ShortComplex.mk f₃ f₄ w₄).Exact)
    (h₀ : P X₀) (h₁ : P X₁) (h₂ : P X₂) (h₃ : P X₃) (h₄ : P X₄) (h₅ : P X₅) :
    subcategoryClassOf C P X₀ h₀ - subcategoryClassOf C P X₁ h₁ +
      subcategoryClassOf C P X₂ h₂ - subcategoryClassOf C P X₃ h₃ +
      subcategoryClassOf C P X₄ h₄ - subcategoryClassOf C P X₅ h₅ = 0 := by
  have r₁ := classOf_eq_ker_add_ker hP _ e₁ h₀ h₁ h₂
  have r₂ := classOf_eq_ker_add_ker hP _ e₂ h₁ h₂ h₃
  have r₃ := classOf_eq_ker_add_ker hP _ e₃ h₂ h₃ h₄
  have r₄ := classOf_eq_ker_add_ker hP _ e₄ h₃ h₄ h₅
  have r₅ := classOf_eq_ker_add_of_epi hP f₄ h₄ h₅
  have z : subcategoryClassOf C P (kernel f₀) (hP.kernel f₀ h₀ h₁) = 0 :=
    subcategoryClassOf_isZero C P _ (isZero_kernel_of_mono f₀)
  dsimp only at r₁ r₂ r₃ r₄
  rw [r₁, r₂, r₃, r₄, r₅, z]
  abel

end Telescoping

section Gysin

variable (τ : 𝟭 C ⟶ 𝟭 C)

/-- The component of `τ` at `A`, typed as an endomorphism of `A`.-/
def ap (A : C) : A ⟶ A := τ.app A

omit [Abelian C] in
/--
@isnad1 id=eq.0h5v.s6.820e2cd3488b from=translated src=- shape=ca2d1dc5 vocab=b8554313
-/
theorem naturality' {A B : C} (f : A ⟶ B) : ap τ A ≫ f = f ≫ ap τ B := by
  simpa [ap] using (τ.naturality f).symm

/-- Objects killed by `τ` (for `τ = t`, sheaves on `M` supported scheme-theoretically on the
fibre `t = 0`).-/
def Killed (P : C → Prop) (τ : 𝟭 C ⟶ 𝟭 C) (E : C) : Prop := P E ∧ ap τ E = 0

/--
@isnad1 id=eq.1h5v.s7.46b95789a070 from=translated src=- shape=3a6cf8d1 vocab=174f1163
-/
theorem app_eq_zero_of_mono {A B : C} (f : A ⟶ B) [Mono f] (hB : ap τ B = 0) :
    ap τ A = 0 := by
  rw [← cancel_mono f, naturality' τ f, hB, comp_zero, zero_comp]

/--
@isnad1 id=eq.1h5v.s7.13696cff2103 from=translated src=- shape=7a204ef5 vocab=03ad5e6f
-/
theorem app_eq_zero_of_epi {A B : C} (f : A ⟶ B) [Epi f] (hA : ap τ A = 0) :
    ap τ B = 0 := by
  rw [← cancel_epi f, ← naturality' τ f, hA, comp_zero, zero_comp]

/--
@isnad1 id=kercoker.1h3v.s5.1416d7085ba1 from=translated src=- shape=bb385c78 vocab=8d8feaf2
-/
theorem KerCokerClosed.killed (hP : KerCokerClosed P) : KerCokerClosed (Killed P τ) where
  zero := ⟨hP.zero, (isZero_zero C).eq_of_src _ _⟩
  kernel f hA hB := ⟨hP.kernel f hA.1 hB.1, app_eq_zero_of_mono τ (kernel.ι f) hA.2⟩
  cokernel f hA hB := ⟨hP.cokernel f hA.1 hB.1, app_eq_zero_of_epi τ (cokernel.π f) hB.2⟩

/--
@isnad1 id=eq.0h3v.s7.fead19f4b0d9 from=translated src=- shape=9d2b8ede vocab=b9ed9a5b
-/
theorem app_kernel_eq_zero (E : C) : ap τ (kernel (ap τ E)) = 0 := by
  rw [← cancel_mono (kernel.ι (ap τ E)), naturality' τ, kernel.condition, zero_comp]

/--
@isnad1 id=eq.0h3v.s7.87f895299843 from=translated src=- shape=9d2b8ede vocab=d40d732d
-/
theorem app_cokernel_eq_zero (E : C) : ap τ (cokernel (ap τ E)) = 0 := by
  rw [← cancel_epi (cokernel.π (ap τ E)), ← naturality' τ, cokernel.condition, comp_zero]

variable (hP : KerCokerClosed P)
include hP

/--
@isnad1 id=killed.1h5v.s6.d8bd45a46d3e from=translated src=- shape=87ee9ab1 vocab=28efcd17
-/
theorem killed_kernel {E : C} (hE : P E) : Killed P τ (kernel (ap τ E)) :=
  ⟨hP.kernel _ hE hE, app_kernel_eq_zero τ E⟩

/--
@isnad1 id=killed.1h5v.s6.69d23fcc93db from=translated src=- shape=87ee9ab1 vocab=2d9684e4
-/
theorem killed_cokernel {E : C} (hE : P E) : Killed P τ (cokernel (ap τ E)) :=
  ⟨hP.cokernel _ hE hE, app_cokernel_eq_zero τ E⟩

/-- The value of the Gysin map on one object: `[coker τ_E] - [ker τ_E]`, i.e.
`[E ⊗ O_{M₀}] - [Tor₁(E, O_{M₀})]`.-/
def gysinObj (E : {E : C // P E}) : SubcategoryGroup C (Killed P τ) :=
  subcategoryClassOf C (Killed P τ) (cokernel (ap τ E.1)) (killed_cokernel τ hP E.2) -
    subcategoryClassOf C (Killed P τ) (kernel (ap τ E.1)) (killed_kernel τ hP E.2)

/-- The snake input attached to `τ` acting on a short exact sequence.-/
@[simps]
def snakeInput (S : ShortComplex C) (hS : S.ShortExact) : ShortComplex.SnakeInput C where
  L₀ := ShortComplex.mk (kernel.map (ap τ S.X₁) (ap τ S.X₂) S.f S.f (naturality' τ S.f))
    (kernel.map (ap τ S.X₂) (ap τ S.X₃) S.g S.g (naturality' τ S.g))
    (by apply (cancel_mono (kernel.ι _)).1; simp [kernel.map, S.zero])
  L₁ := S
  L₂ := S
  L₃ := ShortComplex.mk (cokernel.map (ap τ S.X₁) (ap τ S.X₂) S.f S.f (naturality' τ S.f))
    (cokernel.map (ap τ S.X₂) (ap τ S.X₃) S.g S.g (naturality' τ S.g))
    (by apply (cancel_epi (cokernel.π _)).1; simp [cokernel.map])
  v₀₁ := { τ₁ := kernel.ι _, τ₂ := kernel.ι _, τ₃ := kernel.ι _ }
  v₁₂ := { τ₁ := ap τ S.X₁, τ₂ := ap τ S.X₂, τ₃ := ap τ S.X₃
           comm₁₂ := naturality' τ S.f, comm₂₃ := naturality' τ S.g }
  v₂₃ := { τ₁ := cokernel.π _, τ₂ := cokernel.π _, τ₃ := cokernel.π _ }
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ <;>
      apply (KernelFork.isLimitMapConeEquiv _ _).2 <;> exact kernelIsKernel _
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ <;>
      apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2 <;> exact cokernelIsCokernel _
  L₁_exact := hS.exact
  epi_L₁_g := hS.epi_g
  L₂_exact := hS.exact
  mono_L₂_f := hS.mono_f

/--
@isnad1 id=eq.2h6v.s8.c1051b47ac3e from=translated src=- shape=a0799865 vocab=fea3dbc0
-/
theorem gysinObj_additive (A B D : {E : C // P E}) (h : shortExactIn C P A B D) :
    gysinObj τ hP B = gysinObj τ hP A + gysinObj τ hP D := by
  obtain ⟨f, g, zero, hS⟩ := h
  let S := ShortComplex.mk f g zero
  let I := snakeInput τ S hS
  have hQ := hP.killed τ
  haveI : Mono I.L₀.f := by
    have w : I.L₀.f ≫ kernel.ι (ap τ S.X₂) = kernel.ι (ap τ S.X₁) ≫ S.f := kernel.lift_ι _ _ _
    haveI : Mono (I.L₀.f ≫ kernel.ι (ap τ S.X₂)) := by
      rw [w]; exact @mono_comp _ _ _ _ _ (kernel.ι _) _ S.f hS.mono_f
    exact mono_of_mono _ (kernel.ι (ap τ S.X₂))
  haveI : Epi I.L₃.g := by
    have w : cokernel.π (ap τ S.X₂) ≫ I.L₃.g = S.g ≫ cokernel.π (ap τ S.X₃) :=
      cokernel.π_desc _ _ _
    haveI : Epi (cokernel.π (ap τ S.X₂) ≫ I.L₃.g) := by
      rw [w]; exact @epi_comp _ _ _ _ _ S.g hS.epi_g (cokernel.π _) _
    exact epi_of_epi (cokernel.π (ap τ S.X₂)) _
  have key : subcategoryClassOf C (Killed P τ) (kernel (ap τ A.1)) (killed_kernel τ hP A.2) -
      subcategoryClassOf C (Killed P τ) (kernel (ap τ B.1)) (killed_kernel τ hP B.2) +
      subcategoryClassOf C (Killed P τ) (kernel (ap τ D.1)) (killed_kernel τ hP D.2) -
      subcategoryClassOf C (Killed P τ) (cokernel (ap τ A.1)) (killed_cokernel τ hP A.2) +
      subcategoryClassOf C (Killed P τ) (cokernel (ap τ B.1)) (killed_cokernel τ hP B.2) -
      subcategoryClassOf C (Killed P τ) (cokernel (ap τ D.1)) (killed_cokernel τ hP D.2) = 0 :=
    six_term hQ I.L₀.f I.L₀.g I.δ I.L₃.f I.L₃.g I.L₀.zero I.L₀_g_δ I.δ_L₃_f
    I.L₃.zero I.L₀_exact I.L₁'_exact I.L₂'_exact I.L₃_exact
    (killed_kernel τ hP A.2) (killed_kernel τ hP B.2) (killed_kernel τ hP D.2)
    (killed_cokernel τ hP A.2) (killed_cokernel τ hP B.2) (killed_cokernel τ hP D.2)
  simp only [gysinObj]
  rw [← sub_eq_zero, ← key]
  abel

/-- **Gysin restriction to a principal divisor** `j^! : G(P) → G(P ∩ {τ = 0})`,
`[E] ↦ [coker τ_E] - [ker τ_E]`. Well defined by the snake lemma.-/
def gysin : SubcategoryGroup C P →+ SubcategoryGroup C (Killed P τ) :=
  lift (gysinObj τ hP) (gysinObj_additive τ hP)

/--
@isnad1 id=eq.1h5v.s9.8890aae28933 from=translated src=- shape=7afc051b vocab=f8150d36
-/
@[simp]
theorem gysin_classOf (E : C) (hE : P E) :
    gysin τ hP (subcategoryClassOf C P E hE) =
      subcategoryClassOf C (Killed P τ) (cokernel (ap τ E)) (killed_cokernel τ hP hE) -
        subcategoryClassOf C (Killed P τ) (kernel (ap τ E)) (killed_kernel τ hP hE) :=
  lift_classOf _ _ _

/-- If `τ` is injective on `E` (`t` a non-zero-divisor, e.g. `E` flat over the base line), the
Gysin class is the naive restriction `[E/τE]`.
@isnad1 id=eq.1h5v.s9.c524388f3bc7 from=translated src=- shape=ec64413d vocab=4c869d4d
-/
theorem gysin_classOf_of_mono (E : C) (hE : P E) [Mono (ap τ E)] :
    gysin τ hP (subcategoryClassOf C P E hE) =
      subcategoryClassOf C (Killed P τ) (cokernel (ap τ E)) (killed_cokernel τ hP hE) := by
  rw [gysin_classOf, subcategoryClassOf_isZero C _ _ (isZero_kernel_of_mono _), sub_zero]

omit hP in
/-- Pushforward from the divisor: the inclusion of `τ`-killed objects.-/
def pushDivisor : SubcategoryGroup C (Killed P τ) →+ SubcategoryGroup C P :=
  map (fun E => ⟨E.1, E.2.1⟩) fun _ _ _ ⟨f, g, zero, h⟩ => ⟨f, g, zero, h⟩

omit hP in
/--
@isnad1 id=eq.1h4v.s9.48fe36bda723 from=translated src=- shape=0fd41ce1 vocab=45f39594
-/
@[simp]
theorem pushDivisor_classOf (E : C) (hE : Killed P τ E) :
    pushDivisor τ (subcategoryClassOf C (Killed P τ) E hE) = subcategoryClassOf C P E hE.1 := by
  simp [pushDivisor, subcategoryClassOf, map]

/-- `j^! j_* = 0`: the normal bundle of a principal divisor is trivial. This is exactly what makes
the Fulton specialization map well defined.
@isnad1 id=eq.1h3v.s10.448adba7c1bc from=translated src=- shape=0e92a84d vocab=8fa1fa8f
-/
theorem gysin_comp_pushDivisor : (gysin τ hP).comp (pushDivisor τ) = 0 := by
  refine hom_ext _ _ fun E => ?_
  obtain ⟨E, hE⟩ := E
  change gysin τ hP (pushDivisor τ (subcategoryClassOf C (Killed P τ) E hE)) = 0
  rw [pushDivisor_classOf, gysin_classOf, sub_eq_zero]
  have hQ := hP.killed τ
  have e₁ : cokernel (ap τ E) ≅ E :=
    cokernelIsoOfEq hE.2 ≪≫ (asIso (cokernel.π (0 : E ⟶ E))).symm
  have e₂ : kernel (ap τ E) ≅ E := kernelIsoOfEq hE.2 ≪≫ asIso (kernel.ι (0 : E ⟶ E))
  rw [classOf_eq_of_iso hQ e₁ _ hE, classOf_eq_of_iso hQ e₂ _ hE]

/-- `j_* j^! = 0`: `[coker τ_E] = [ker τ_E]` in `G(P)` (four-term sequence
`0 → ker → E → E → coker → 0`), i.e. `[O_{M₀}] = 0` for a principal divisor.
@isnad1 id=eq.1h3v.s10.8d8b5de9482d from=translated src=- shape=7503d272 vocab=8fa1fa8f
-/
theorem pushDivisor_comp_gysin : (pushDivisor τ).comp (gysin τ hP) = 0 := by
  refine hom_ext _ _ fun E => ?_
  obtain ⟨E, hE⟩ := E
  change pushDivisor τ (gysin τ hP (subcategoryClassOf C P E hE)) = 0
  rw [gysin_classOf, map_sub, pushDivisor_classOf, pushDivisor_classOf, sub_eq_zero]
  have hQ : P (cokernel (ap τ E)) := hP.cokernel _ hE hE
  have r₁ := classOf_eq_ker_add_ker hP _ (ShortComplex.exact_cokernel (ap τ E)) hE hE hQ
  have r₂ := classOf_eq_ker_add_of_epi hP (cokernel.π (ap τ E)) hE hQ
  dsimp only at r₁
  rw [r₁] at r₂
  exact add_left_cancel (r₂.symm.trans (add_comm _ _))

end Gysin

section ModuleCat

variable (R : Type u) [CommRing R]

/-- Multiplication by `r : R`, a central endomorphism of the identity of `ModuleCat R`
(affine model of `t ∈ Γ(M, O_M)` acting on `O_M`-modules).-/
def smulNatTrans (r : R) : 𝟭 (ModuleCat.{v} R) ⟶ 𝟭 (ModuleCat.{v} R) where
  app M := ModuleCat.ofHom (r • LinearMap.id)
  naturality M N f := by
    ext x
    change r • f.hom x = f.hom (r • x)
    exact (map_smul f.hom r x).symm

/--
@isnad1 id=iff.0h3v.s7.c2cd3b14c74a from=translated src=- shape=a993c03b vocab=2596a6ed
-/
theorem mono_ap_smulNatTrans_iff (r : R) (M : ModuleCat.{v} R) :
    Mono (ap (smulNatTrans R r) M) ↔ IsSMulRegular M r := by
  rw [ModuleCat.mono_iff_injective]
  rfl

/-- **Tor-independence of fibres of a flat family over `𝔸¹_k`**: on a `k[t]`-flat module, `t - c`
acts injectively, so `j_c^![E] = [E/(t-c)E]` (`gysin_classOf_of_mono`).
@isnad1 id=mono.0h3v.s8.24ee74157e89 from=translated src=- shape=bf181cf2 vocab=fb8d819f
-/
theorem mono_ap_smulNatTrans_of_flat (k : Type u) [Field k] (c : k)
    (M : ModuleCat.{v} (Polynomial k)) [Module.Flat (Polynomial k) M] :
    Mono (ap (smulNatTrans (Polynomial k) (Polynomial.X - Polynomial.C c)) M) := by
  rw [mono_ap_smulNatTrans_iff]
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (Polynomial.X_sub_C_ne_zero c))

end ModuleCat

end PrincipalGysin

end ExactGrothendieck
