/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Homology.ShortComplex.SnakeLemma

/-!
# Long exact sequence for the kernel and cokernel of a composition

If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms in an
abelian category, we construct a long exact sequence:
`0 ⟶ ker f ⟶ ker (f ≫ g) ⟶ ker g ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0`.

This is obtained by applying the snake lemma to the following morphism of
exact sequences, where the rows are the obvious split exact sequences
```
0 ⟶ X ⟶ X ⊞ Y ⟶ Y ⟶ 0
    |f    |φ    |g
    v     v     v
0 ⟶ Y ⟶ Y ⊞ Z ⟶ Z ⟶ 0
```
and `φ` is given by the following matrix:
```
(f  -𝟙 Y)
(0     g)
```

Indeed the snake lemma gives an exact sequence involving the kernels and cokernels
of the vertical maps: in order to get the expected long exact sequence, it suffices
to obtain isomorphisms `ker φ ≅ ker (f ≫ g)` and `coker φ ≅ coker (f ≫ g)`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits Category Preadditive

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

namespace kernelCokernelCompSequence

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
this is the morphism `kernel (f ≫ g) ⟶ X ⊞ Y` which
"sends `x` to `(x, f(x))`". -/
noncomputable def ι : kernel (f ≫ g) ⟶ X ⊞ Y :=
  biprod.lift (kernel.ι (f ≫ g)) (kernel.ι (f ≫ g) ≫ f)

/--
@isnad1 id=eq.0h6v.s7.ecd41ef9dab1 from=seed src=0 shape=701aa8fa vocab=213a521c
-/
@[reassoc (attr := simp)]
lemma ι_fst : ι f g ≫ biprod.fst = kernel.ι (f ≫ g) := by simp [ι]

/--
@isnad1 id=eq.0h6v.s7.b2802904909d from=seed src=0 shape=27705de6 vocab=8c5e5761
-/
@[reassoc (attr := simp)]
lemma ι_snd : ι f g ≫ biprod.snd = kernel.ι (f ≫ g) ≫ f := by simp [ι]

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
this is the morphism `X ⊞ Y ⟶ Y ⊞ Z` given by the matrix
```
(f  -𝟙 Y)
(0     g)
```
-/
noncomputable def φ : X ⊞ Y ⟶ Y ⊞ Z :=
  biprod.desc (f ≫ biprod.inl) (biprod.lift (-𝟙 Y) g)

/--
@isnad1 id=eq.0h6v.s7.226ddedc9093 from=seed src=0 shape=f4866a9c vocab=b0818e0f
-/
@[reassoc (attr := simp)]
lemma inl_φ : biprod.inl ≫ φ f g = f ≫ biprod.inl := by simp [φ]

/--
@isnad1 id=eq.0h6v.s7.da3fe11a61e7 from=seed src=0 shape=ae66db17 vocab=ed40f1d3
-/
@[reassoc (attr := simp)]
lemma inr_φ_fst : biprod.inr ≫ φ f g ≫ biprod.fst = - 𝟙 Y := by simp [φ]

/--
@isnad1 id=eq.0h6v.s7.65014d68676e from=seed src=0 shape=8985f88d vocab=4f8b8f2b
-/
@[reassoc (attr := simp)]
lemma φ_snd : φ f g ≫ biprod.snd = biprod.snd ≫ g := by
  dsimp [φ]
  aesop

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
this is the morphism `Y ⊞ Z ⟶ cokernel (f ≫ g)` which
"sends `(y, z)` to `[g(y)] + [z]`". -/
noncomputable def π : Y ⊞ Z ⟶ cokernel (f ≫ g) :=
  biprod.desc (g ≫ cokernel.π (f ≫ g)) (cokernel.π (f ≫ g))

/--
@isnad1 id=eq.0h6v.s7.3cdb8128ff52 from=seed src=0 shape=5818b685 vocab=11ebb806
-/
@[reassoc (attr := simp)]
lemma inl_π : biprod.inl ≫ π f g = g ≫ cokernel.π (f ≫ g) := by simp [π]

/--
@isnad1 id=eq.0h6v.s7.4f68646ee665 from=seed src=0 shape=40443420 vocab=757a8bd8
-/
@[reassoc (attr := simp)]
lemma inr_π : biprod.inr ≫ π f g = cokernel.π (f ≫ g) := by simp [π]

/--
@isnad1 id=eq.0h6v.s8.c17e576b28d1 from=seed src=0 shape=e3416346 vocab=199ecf36
-/
@[reassoc (attr := simp)]
lemma ι_φ : ι f g ≫ φ f g = 0 := by
  dsimp [ι, φ]
  aesop

/--
@isnad1 id=eq.0h6v.s8.ae435db56293 from=seed src=0 shape=53d38abe vocab=53df01b5
-/
@[reassoc (attr := simp)]
lemma φ_π : φ f g ≫ π f g = 0 := by
  dsimp [φ, π]
  ext
  · rw [biprod.inl_desc_assoc, assoc, biprod.inl_desc, comp_zero,
      ← assoc, cokernel.condition]
  · simp

instance : Mono (ι f g) := mono_of_mono_fac (ι_fst f g)

instance : Epi (π f g) := epi_of_epi_fac (inr_π f g)

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
then the kernel of `φ f g : X ⊞ Y ⟶ Y ⊞ Z` identifies
to `kernel (f ≫ g)`. -/
noncomputable def isLimit : IsLimit (KernelFork.ofι _ (ι_φ f g)) :=
  KernelFork.IsLimit.ofι' _ _ (fun {A} k hk ↦ by
    refine ⟨kernel.lift _ (k ≫ biprod.fst) ?_, ?_⟩
    all_goals
      obtain ⟨k₁, k₂, rfl⟩ := biprod.decomp_hom_to k
      simp only [biprod.ext_to_iff, add_comp, assoc, inl_φ, BinaryBicone.inl_fst,
        comp_id, inr_φ_fst, comp_neg, zero_comp, BinaryBicone.inl_snd, comp_zero, φ_snd,
        BinaryBicone.inr_snd_assoc, zero_add, add_neg_eq_zero] at hk
      obtain ⟨rfl, hk⟩ := hk
      aesop)

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
then the cokernel of `φ f g : X ⊞ Y ⟶ Y ⊞ Z` identifies
to `cokernel (f ≫ g)`. -/
noncomputable def isColimit : IsColimit (CokernelCofork.ofπ _ (φ_π f g)) :=
  CokernelCofork.IsColimit.ofπ' _ _ (fun {A} k hk ↦ by
    refine ⟨cokernel.desc _ (biprod.inr ≫ k) ?_, ?_⟩
    all_goals
      obtain ⟨k₁, k₂, rfl⟩ := biprod.decomp_hom_from k
      simp only [comp_add, φ_snd_assoc, biprod.ext_from_iff, inl_φ_assoc,
        BinaryBicone.inl_fst_assoc, BinaryBicone.inl_snd_assoc, zero_comp, add_zero, comp_zero,
        inr_φ_fst_assoc, neg_comp, id_comp, BinaryBicone.inr_snd_assoc, neg_add_eq_zero] at hk
      obtain ⟨hk, rfl⟩ := hk
      aesop)

/-- The "snake input" which gives the exact sequence
`0 ⟶ ker f ⟶ ker (f ≫ g) ⟶ ker g ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0`,
see `kernelCokernelCompSequence_exact`. -/
@[simps]
noncomputable def snakeInput : ShortComplex.SnakeInput C where
  L₀ :=
    { f := kernel.map f (f ≫ g) (𝟙 _) g (by simp)
      g := kernel.map (f ≫ g) g f (𝟙 _) (by simp)
      zero := by aesop }
  L₁ := ShortComplex.mk (biprod.inl : X ⟶ _) (biprod.snd : _ ⟶ Y) (by simp)
  L₂ := ShortComplex.mk (biprod.inl : Y ⟶ _) (biprod.snd : _ ⟶ Z) (by simp)
  L₃ :=
    { f := cokernel.map f (f ≫ g) (𝟙 _) g (by simp)
      g := cokernel.map (f ≫ g) g f (𝟙 _) (by simp)
      zero := by aesop }
  v₀₁ :=
    { τ₁ := kernel.ι f
      τ₂ := ι f g
      τ₃ := kernel.ι g }
  v₁₂ :=
    { τ₁ := f
      τ₂ := φ f g
      τ₃ := g }
  v₂₃ :=
    { τ₁ := cokernel.π f
      τ₂ := π f g
      τ₃ := cokernel.π g }
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ <;>
      apply (KernelFork.isLimitMapConeEquiv _ _).2
    · exact kernelIsKernel _
    · exact isLimit f g
    · exact kernelIsKernel _
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ <;>
      apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2
    · exact cokernelIsCokernel _
    · exact isColimit f g
    · exact cokernelIsCokernel _
  epi_L₁_g := by dsimp; infer_instance
  mono_L₂_f := by dsimp; infer_instance
  L₁_exact := (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).exact
  L₂_exact := (ShortComplex.Splitting.ofHasBinaryBiproduct Y Z).exact

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms, this
is the connecting homomorphism `kernel g ⟶ cokernel f`. -/
noncomputable def δ : kernel g ⟶ cokernel f := (snakeInput f g).δ

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.0h6v.s8.2ca3b68d411e from=seed src=0 shape=0c129895 vocab=d56ff12d
-/
lemma δ_fac : δ f g = - kernel.ι g ≫ cokernel.π f := by
  simpa using! (snakeInput f g).δ_eq (𝟙 _) (kernel.ι g ≫ biprod.inr) (-kernel.ι g)
    (by simp) (by aesop)

end kernelCokernelCompSequence

open kernelCokernelCompSequence

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms in an
abelian category, this is the long exact sequence
`0 ⟶ ker f ⟶ ker (f ≫ g) ⟶ ker g ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0`. -/
noncomputable abbrev kernelCokernelCompSequence : ComposableArrows C 5 :=
  .mk₅ (kernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (kernel.map (f ≫ g) g f (𝟙 _) (by simp))
    (δ f g)
    (cokernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (cokernel.map (f ≫ g) g f (𝟙 _) (by simp))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance : Mono ((kernelCokernelCompSequence f g).map' 0 1) := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : Epi ((kernelCokernelCompSequence f g).map' 4 5) := by
  dsimp [ComposableArrows.Precomp.map]
  infer_instance

/--
@isnad1 id=exact.0h6v.s5.58f4f54b5301 from=seed src=0 shape=132f6127 vocab=7ee22448
-/
lemma kernelCokernelCompSequence_exact :
    (kernelCokernelCompSequence f g).Exact :=
  (snakeInput f g).snake_lemma

end CategoryTheory
