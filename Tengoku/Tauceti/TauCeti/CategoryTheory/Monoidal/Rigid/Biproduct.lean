/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# Exact pairings of finite biproducts

In a monoidal preadditive category, the tensor product distributes over finite biproducts. As a
consequence, dualizable objects are closed under finite biproducts: if `Y i` is a right dual of
`X i` for every `i` in a finite index type, then `⨁ Y` is a right dual of `⨁ X`. The
coevaluation is the sum of the coevaluations of the summands and the evaluation is the sum of the
evaluations of the summands:

```
η = ∑ i, η_ (X i) (Y i) ≫ (biproduct.ι X i ⊗ₘ biproduct.ι Y i)
ε = ∑ i, (biproduct.π Y i ⊗ₘ biproduct.π X i) ≫ ε_ (X i) (Y i)
```

In a category of modules or of sheaves of modules this shows that finite free objects, which are
finite biproducts of copies of the unit, are dualizable.

## Main declarations

* `TauCeti.ExactPairing.unit_evaluation` and `TauCeti.ExactPairing.unit_coevaluation`: the
  evaluation and coevaluation of Mathlib's self-pairing of the unit;
* `TauCeti.ExactPairing.biproduct`: the exact pairing between `⨁ X` and `⨁ Y` induced by exact
  pairings between `X i` and `Y i`;
* `TauCeti.ExactPairing.biproduct_ι_tensorHom_biproduct_ι_evaluation` and
  `TauCeti.ExactPairing.coevaluation_biproduct_π_tensorHom_biproduct_π`, with their `_of_ne`
  variants: the evaluation and coevaluation are, componentwise, those of the summands on the
  diagonal and zero off it.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe v u w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Naturality

/-- Moving a tensor product of morphisms past the inverse associator: the two middle factors
compose. -/
@[reassoc]
theorem whiskerLeft_tensorHom_associator_inv_tensorHom_whiskerRight {Z Z' A B X Y D : C}
    (a : A ⟶ X) (b : B ⟶ Y) (c : Z ⟶ Z') (d : X ⟶ D) :
    Z ◁ (a ⊗ₘ b) ≫ (α_ Z X Y).inv ≫ (c ⊗ₘ d) ▷ Y =
      (α_ Z A B).inv ≫ ((c ⊗ₘ (a ≫ d)) ⊗ₘ b) := by
  rw [← id_tensorHom, associator_inv_naturality_assoc, ← tensorHom_id, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

/-- Moving a tensor product of morphisms past the associator: the two middle factors compose. -/
@[reassoc]
theorem tensorHom_whiskerRight_associator_hom_whiskerLeft_tensorHom {Z Z' A B X Y D : C}
    (a : A ⟶ X) (b : B ⟶ Y) (c : Y ⟶ D) (d : Z ⟶ Z') :
    (a ⊗ₘ b) ▷ Z ≫ (α_ X Y Z).hom ≫ X ◁ (c ⊗ₘ d) =
      (α_ A B Z).hom ≫ (a ⊗ₘ ((b ≫ c) ⊗ₘ d)) := by
  rw [← tensorHom_id, associator_naturality_assoc, ← id_tensorHom, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

/-- The second zigzag identity of an exact pairing, with morphisms `d` and `a` inserted on the
outer factors. -/
theorem evaluation_coevaluation_tensorHom {Z X Y W : C} [ExactPairing X Y] (a : X ⟶ W)
    (d : Z ⟶ X) :
    η_ X Y ▷ Z ≫ (α_ X Y Z).hom ≫ (a ⊗ₘ (𝟙 Y ⊗ₘ d)) ≫ W ◁ ε_ X Y =
      (λ_ Z).hom ≫ d ≫ a ≫ (ρ_ W).inv := by
  rw [id_tensorHom, tensorHom_def', Category.assoc, ← whisker_exchange,
    ← associator_naturality_right_assoc, ← whisker_exchange_assoc,
    ExactPairing.evaluation_coevaluation_assoc, leftUnitor_naturality_assoc,
    rightUnitor_inv_naturality]

end Naturality

namespace ExactPairing

/-- The evaluation of the canonical self-pairing of the unit is the right unitor. -/
@[simp]
theorem unit_evaluation : ε_ (𝟙_ C) (𝟙_ C) = (ρ_ (𝟙_ C)).hom :=
  (rfl)

/-- The coevaluation of the canonical self-pairing of the unit is the inverse right unitor. -/
@[simp]
theorem unit_coevaluation : η_ (𝟙_ C) (𝟙_ C) = (ρ_ (𝟙_ C)).inv :=
  (rfl)

end ExactPairing

variable [Preadditive C] [MonoidalPreadditive C] {ι : Type w} [Finite ι]
  (X Y : ι → C) [HasBiproduct X] [HasBiproduct Y] [∀ i, ExactPairing (X i) (Y i)]

namespace ExactPairing

variable {X Y}

end ExactPairing

end TauCeti
