/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku.Imoshortlist.IMOSLLean4.Generalization.IMO2012A5.A5Defs
public import Tengoku

/-!
# IMO 2012 A5 (Good maps and ring homomorphisms)

We prove some results relating good maps and ring homomorphisms.
Namely, good maps behave well with respect to composing with ring homomorphisms.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization

variable [NonAssocSemiring R] [NonAssocSemiring S] {f : R → S}

/--
@isnad1 id=good.1h5v.s6.82a8a318ee5e from=translated src=- shape=dbdab72b vocab=a57b5f67
-/
theorem good_comp_hom (h : good f) [NonAssocSemiring R₀]
    (φ : R₀ →+* R) : good (f ∘ φ) := λ x y ↦ by
  simp only [Function.comp_apply]
  rw [φ.map_add, φ.map_mul, φ.map_one, h, φ.map_add]

/--
@isnad1 id=good.1h5v.s6.e21f002c777b from=translated src=- shape=add57f43 vocab=a57b5f67
-/
theorem good_hom_comp (h : good f) [NonAssocSemiring S₀]
    (φ : S →+* S₀) : good (φ ∘ f) := λ x y ↦ by
  simp only [Function.comp_apply]
  rw [h, φ.map_add, φ.map_mul]

/--
@isnad1 id=nontrivi.1h5v.s6.0dc3941da595 from=translated src=- shape=dbdab72b vocab=cde090c3
-/
theorem NontrivialGood.comp_hom (hf : NontrivialGood f) [NonAssocSemiring R₀]
    (φ : R₀ →+* R) : NontrivialGood (f ∘ φ) :=
  ⟨good_comp_hom hf.is_good φ, hf.map_zero_add_one ▸ congrArg (λ x ↦ f x + 1) φ.map_zero⟩

/--
@isnad1 id=nontrivi.1h5v.s6.92bad002af99 from=translated src=- shape=add57f43 vocab=cde090c3
-/
theorem NontrivialGood.hom_comp (hf : NontrivialGood f) [NonAssocSemiring S₀]
    (φ : S →+* S₀) : NontrivialGood (φ ∘ f) :=
  ⟨good_hom_comp hf.is_good φ,
  by rw [← φ.map_one, ← φ.map_zero, ← hf.map_zero_add_one, φ.map_add]; rfl⟩
