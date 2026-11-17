import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_TransferHecke
import Tengoku.Seed.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeCohomology_heckeH1_natural

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeCohomology_heckeH1_natural.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open groupCohomology in

/--
@isnad1 id=eq.3h11v.s11.00c78deca609 from=translated src=- shape=b57b2558 vocab=33abbb4a
-/
theorem HeckeCohomology.heckeH1_natural {k Γ : Type} [CommRing k] [Group Γ]
    (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) {A B : Rep k Γ} [S₂.FiniteIndex] (f : A ⟶ B)
    (φA : A →ₗ[k] A) (hφA : IsTwist S₁ S₂ c A φA)
    (φB : B →ₗ[k] B) (hφB : IsTwist S₁ S₂ c B φB)
    (hcomm : ∀ a : A, f.hom (φA a) = φB (f.hom a)) (x : H1 A) :
    heckeH1 S₁ S₂ c B φB hφB (map (MonoidHom.id Γ) f 1 x) =
      map (MonoidHom.id Γ) f 1 (heckeH1 S₁ S₂ c A φA hφA x) := by exact @_root_.P2MW.S_HeckeCohomology_heckeH1_natural.solution k Γ _ _ S₁ S₂ c A B _ f φA hφA φB hφB hcomm x
