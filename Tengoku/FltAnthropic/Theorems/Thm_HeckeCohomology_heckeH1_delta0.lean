import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_TransferHecke
import Tengoku.Seed.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeCohomology_heckeH1_delta0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeCohomology_heckeH1_delta0.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open CategoryTheory groupCohomology in

/--
@isnad1 id=eq.6h10v.s16.7071477d8e8c from=translated src=- shape=5dfd44f1 vocab=eca73b07
-/
theorem HeckeCohomology.heckeH1_delta0 {k Γ : Type} [CommRing k] [Group Γ]
    (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) [S₂.FiniteIndex]
    {X : ShortComplex (Rep k Γ)} (hX : X.ShortExact)
    (φ₁ : X.X₁ →ₗ[k] X.X₁) (hφ₁ : IsTwist S₁ S₂ c X.X₁ φ₁)
    (φ₂ : X.X₂ →ₗ[k] X.X₂) (hφ₂ : IsTwist S₁ S₂ c X.X₂ φ₂)
    (φ₃ : X.X₃ →ₗ[k] X.X₃) (hφ₃ : IsTwist S₁ S₂ c X.X₃ φ₃)
    (hf : ∀ a : X.X₁, X.f.hom (φ₁ a) = φ₂ (X.f.hom a))
    (hg : ∀ b : X.X₂, X.g.hom (φ₂ b) = φ₃ (X.g.hom b))
    (z : X.X₃.ρ.invariants) :
    heckeH1 S₁ S₂ c X.X₁ φ₁ hφ₁ (δ hX 0 1 rfl ((H0Iso X.X₃).inv z)) =
      δ hX 0 1 rfl ((H0Iso X.X₃).inv (heckeInv S₁ S₂ c X.X₃ φ₃ hφ₃ z)) := by exact @_root_.P2MW.S_HeckeCohomology_heckeH1_delta0.solution k Γ _ _ S₁ S₂ c _ X hX φ₁ hφ₁ φ₂ hφ₂ φ₃ hφ₃ hf hg z
