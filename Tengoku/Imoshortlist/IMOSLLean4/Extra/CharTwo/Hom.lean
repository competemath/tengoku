/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku.Imoshortlist.IMOSLLean4.Extra.CharTwo.Defs
public import Tengoku

/-!
# Characteristic two monoids and homomorphisms

We prove some results relating characteristic two monoids and homomorphism.
-/

@[expose] public section

namespace IMOSL
namespace Extra
namespace CharTwo

variable [AddMonoid R] [CharTwo R] [AddMonoid R']

/--
@isnad1 id=chartwo.1h3v.s6.3b0bb9712ea9 from=translated src=- shape=9e442ef7 vocab=eaca8c75
-/
theorem pullback_of_inj (φ : R' →+ R) (h : Function.Injective φ) : CharTwo R' :=
  ⟨λ x ↦ h <| by rw [φ.map_add, φ.map_zero, CharTwo.add_self_eq_zero]⟩

/--
@isnad1 id=chartwo.1h3v.s6.f92805a4eb5e from=translated src=- shape=49792410 vocab=7a1c3e65
-/
theorem forward_of_surj (φ : R →+ R') (h : Function.Surjective φ) : CharTwo R' :=
  ⟨λ x ↦ (h x).elim λ c h0 ↦ by rw [← h0, ← φ.map_add, add_self_eq_zero, φ.map_zero]⟩
