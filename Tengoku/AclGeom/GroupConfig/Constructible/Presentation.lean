/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.GroupConfig.Constructible.Closure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Constructible group and action presentations

Blueprint `sources/group_configuration/09-constructibility.tex`.

The literal predicates of supplemental `def:constructible-group`, with actual
surjections and constructible equality and operation relations. The group predicate persists
under extension of the coefficient field.

**Status:** the source definitions and coefficient-field extension are formalized. Actual
producers are proved in `GroupPresentation`, `SpacePresentation` and `CanonicalPresentation`.
-/

namespace GroupConfig

open Set

universe u v w x

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- `def:constructible-group`: an actual surjection from a constructible
parameter domain, with constructible equality, multiplication and inverse
relations. Named consumer: the actual pair-domain presentation.-/
structure ConstructibleGroupPresentation (L : IntermediateField k K)
    {P : Type w} [Finite P] {G : Type x} [Group G]
    (D : Set (P → K)) (ρ : D → G) : Prop where
  /-- The actual group parameter domain is constructible.-/
  domain : IsConstructibleOver (↥L) D
  /-- Every element of the actual group has a parameter.-/
  surjective : Function.Surjective ρ
  /-- Equality of actual group images is constructible.-/
  kernel : IsConstructibleOver (↥L) {d : (P ⊕ P) → K |
    ∃ (hL : d ∘ Sum.inl ∈ D) (hR : d ∘ Sum.inr ∈ D),
      ρ ⟨d ∘ Sum.inl, hL⟩ = ρ ⟨d ∘ Sum.inr, hR⟩}
  /-- The actual multiplication relation on three parameters is constructible.-/
  multiplication : IsConstructibleOver (↥L) {d : ((P ⊕ P) ⊕ P) → K |
    ∃ (hL : (d ∘ Sum.inl) ∘ Sum.inl ∈ D)
      (hR : (d ∘ Sum.inl) ∘ Sum.inr ∈ D) (hT : d ∘ Sum.inr ∈ D),
      ρ ⟨(d ∘ Sum.inl) ∘ Sum.inl, hL⟩ * ρ ⟨(d ∘ Sum.inl) ∘ Sum.inr, hR⟩ =
        ρ ⟨d ∘ Sum.inr, hT⟩}
  /-- The actual inverse relation on two parameters is constructible.-/
  inverse : IsConstructibleOver (↥L) {d : (P ⊕ P) → K |
    ∃ (hL : d ∘ Sum.inl ∈ D) (hR : d ∘ Sum.inr ∈ D),
      (ρ ⟨d ∘ Sum.inl, hL⟩)⁻¹ = ρ ⟨d ∘ Sum.inr, hR⟩}

/-- `def:constructible-group`, the constructible `G`-set clause: an actual
surjection onto a group action with constructible equality and action
relations. Named consumer: the Hrushovski–Weil homogeneous-space presentation.-/
structure ConstructibleGSetPresentation (L : IntermediateField k K)
    {P Q G X : Type*} [Finite P] [Finite Q] [Group G] [MulAction G X]
    (D : Set (P → K)) (ρ : D → G) (Dₓ : Set (Q → K)) (ρₓ : Dₓ → X) : Prop where
  /-- The acting group has this constructible presentation.-/
  group : ConstructibleGroupPresentation L D ρ
  /-- The actual space parameter domain is constructible.-/
  domain : IsConstructibleOver (↥L) Dₓ
  /-- Every point of the actual space has a parameter.-/
  surjective : Function.Surjective ρₓ
  /-- Equality of actual space images is constructible.-/
  kernel : IsConstructibleOver (↥L) {d : (Q ⊕ Q) → K |
    ∃ (hL : d ∘ Sum.inl ∈ Dₓ) (hR : d ∘ Sum.inr ∈ Dₓ),
      ρₓ ⟨d ∘ Sum.inl, hL⟩ = ρₓ ⟨d ∘ Sum.inr, hR⟩}
  /-- The actual group action relation on parameters is constructible.-/
  action : IsConstructibleOver (↥L) {d : ((P ⊕ Q) ⊕ Q) → K |
    ∃ (hG : (d ∘ Sum.inl) ∘ Sum.inl ∈ D)
      (hX : (d ∘ Sum.inl) ∘ Sum.inr ∈ Dₓ) (hT : d ∘ Sum.inr ∈ Dₓ),
      ρ ⟨(d ∘ Sum.inl) ∘ Sum.inl, hG⟩ • ρₓ ⟨(d ∘ Sum.inl) ∘ Sum.inr, hX⟩ =
        ρₓ ⟨d ∘ Sum.inr, hT⟩}

end GroupConfig
