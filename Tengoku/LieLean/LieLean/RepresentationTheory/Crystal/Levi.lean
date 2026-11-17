/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.RepresentationTheory.Crystal.Folding

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Morphisms from crystals of a Levi datum

Let `D` be a Cartan datum indexed by `ι`, `D'` one indexed by `κ`, and `e : κ → ι` a map of
colours (typically the inclusion of a subset `J ⊆ ι`, `D'` a Cartan datum of the principal
submatrix `A_J`). A map `Φ : B' → B` from a `D'`-crystal to a `D`-crystal is a *Levi morphism*
(`Crystal.IsLeviHom`) if it sends `ẽₖ, f̃ₖ` to `ẽ_{e k}, f̃_{e k}` and
`⟨wt Φ b, α_{e k}^∨⟩ = ⟨wt b, αₖ^∨⟩`. Thus `Φ` is a strict morphism from `B'` to the restriction
of `B` to the colours `e(κ)`, where weights are compared only through the coroots of those
colours. These maps are used to define normal crystals relative to the path model
(`Crystal.IsNormal`).

## Main results

* `Crystal.IsLeviHom.ε_apply`, `Crystal.IsLeviHom.φ_apply`: between seminormal crystals a Levi
  morphism preserves `εₖ` and `φₖ`.
* `Crystal.IsLeviHom.map_reflection`: it intertwines Kashiwara's reflections,
  `Φ ∘ Sₖ = S_{e k} ∘ Φ`.
* `Crystal.IsLeviHom.tensor`: the tensor product of Levi morphisms between seminormal crystals is
  a Levi morphism.
* `Crystal.IsLeviHom.comp_strictHom`, `Crystal.IsLeviHom.strictHom_comp`, `Crystal.IsLeviHom.inl`,
  `Crystal.IsLeviHom.inr`: compatibility with strict morphisms and disjoint unions.
-/
namespace Tengoku.LieLean end Tengoku.LieLean open Tengoku.LieLean
namespace Tengoku.LieLean.Crystal

variable {ι κ X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {D : CartanDatum ι X}
  {D' : CartanDatum κ Y} {B B' B'' B₁ B₂ B₁' B₂' : Type*}

/-- A *Levi morphism* along a map of colours `e : κ → ι`: a map `Φ : B' → B` from a crystal over
`D'` to a crystal over `D` such that `Φ (ẽₖ b) = ẽ_{e k} Φ(b)`, `Φ (f̃ₖ b) = f̃_{e k} Φ(b)` (both
sides possibly `0`) and `⟨wt Φ(b), α_{e k}^∨⟩ = ⟨wt b, αₖ^∨⟩`.-/
structure IsLeviHom (C' : Crystal D' B') (C : Crystal D B) (e : κ → ι) (Φ : B' → B) : Prop where
  map_e : ∀ k b, (C'.e k b).map Φ = C.e (e k) (Φ b)
  map_f : ∀ k b, (C'.f k b).map Φ = C.f (e k) (Φ b)
  coroot_wt : ∀ k b, D.coroot (e k) (C.wt (Φ b)) = D'.coroot k (C'.wt b)

namespace IsLeviHom

variable {C' : Crystal D' B'} {C : Crystal D B} {e : κ → ι} {Φ : B' → B}

/--
@isnad1 id=eq.1h15v.s6.2d3184247ccf from=translated src=- shape=8562d64c vocab=d1b978cc
-/
lemma map_eIter (h : IsLeviHom C' C e Φ) (k : κ) (n : ℕ) (b : B') :
    (C'.eIter k n b).map Φ = C.eIter (e k) n (Φ b) := by
  rw [eIter_eq_iterOpt, eIter_eq_iterOpt]
  exact iterOpt_map (h.map_e k) n b

/--
@isnad1 id=eq.1h15v.s6.125478aa5214 from=translated src=- shape=8562d64c vocab=16735da8
-/
lemma map_fIter (h : IsLeviHom C' C e Φ) (k : κ) (n : ℕ) (b : B') :
    (C'.fIter k n b).map Φ = C.fIter (e k) n (Φ b) := by
  rw [fIter_eq_iterOpt, fIter_eq_iterOpt]
  exact iterOpt_map (h.map_f k) n b

/-- A Levi morphism between seminormal crystals intertwines Kashiwara's reflections:
`Φ (Sₖ b) = S_{e k} Φ(b)`.
@isnad1 id=eq.3h14v.s6.6c0952aab42e from=translated src=- shape=cdd84f01 vocab=949c1231
-/
theorem map_reflection (h : IsLeviHom C' C e Φ) (hC' : C'.IsSeminormal) (hC : C.IsSeminormal)
    (k : κ) (b : B') : Φ (C'.reflection k b) = C.reflection (e k) (Φ b) :=
  hC'.map_reflection_of_eq hC (h.map_e k) (h.map_f k) (h.coroot_wt k) b

/-- Precomposition with a strict morphism.
@isnad1 id=isleviho.1h15v.s7.3c9c5a36dfe3 from=translated src=- shape=d16a51fb vocab=b24071cc
-/
theorem comp_strictHom (h : IsLeviHom C' C e Φ) {C'' : Crystal D' B''} (ψ : StrictHom C'' C') :
    IsLeviHom C'' C e (Φ ∘ ψ) where
  map_e k b := by rw [Function.comp_apply, ← h.map_e, ψ.e_apply, Option.map_map]
  map_f k b := by rw [Function.comp_apply, ← h.map_f, ψ.f_apply, Option.map_map]
  coroot_wt k b := by rw [Function.comp_apply, h.coroot_wt, ψ.wt_apply]

/-- Postcomposition with a strict morphism.
@isnad1 id=isleviho.1h15v.s7.b8d46c88a88c from=translated src=- shape=da1ec488 vocab=b24071cc
-/
theorem strictHom_comp (h : IsLeviHom C' C e Φ) {C₂ : Crystal D B₂} (ψ : StrictHom C C₂) :
    IsLeviHom C' C₂ e (ψ ∘ Φ) where
  map_e k b := by rw [Function.comp_apply, ψ.e_apply, ← h.map_e, Option.map_map]
  map_f k b := by rw [Function.comp_apply, ψ.f_apply, ← h.map_f, Option.map_map]
  coroot_wt k b := by rw [Function.comp_apply, ψ.wt_apply, h.coroot_wt]

/-- Composition with the first inclusion into a disjoint union.
@isnad1 id=isleviho.1h14v.s6.c34e30a62001 from=translated src=- shape=b67f15f8 vocab=fbe94c46
-/
theorem inl (h : IsLeviHom C' C e Φ) (C₂ : Crystal D B₂) :
    IsLeviHom C' (C.sum C₂) e (Sum.inl ∘ Φ) where
  map_e k b := by
    change _ = (C.e (e k) (Φ b)).map Sum.inl
    rw [← h.map_e, Option.map_map]
  map_f k b := by
    change _ = (C.f (e k) (Φ b)).map Sum.inl
    rw [← h.map_f, Option.map_map]
  coroot_wt k b := h.coroot_wt k b

/-- Composition with the second inclusion into a disjoint union.
@isnad1 id=isleviho.1h14v.s6.08524c29fbfe from=translated src=- shape=c8102f3e vocab=d2ecb25e
-/
theorem inr (h : IsLeviHom C' C e Φ) (C₁ : Crystal D B₁) :
    IsLeviHom C' (C₁.sum C) e (Sum.inr ∘ Φ) where
  map_e k b := by
    change _ = (C.e (e k) (Φ b)).map Sum.inr
    rw [← h.map_e, Option.map_map]
  map_f k b := by
    change _ = (C.f (e k) (Φ b)).map Sum.inr
    rw [← h.map_f, Option.map_map]
  coroot_wt k b := h.coroot_wt k b

end IsLeviHom

end Tengoku.LieLean.Crystal
-- Tengoku: root names of this library moved to Tengoku.LieLean so they do not collide with other libraries (generated)
