import Tengoku.Seed.Algebra.Field.Subfield.Basic
import Tengoku.Seed.Algebra.Group.Units.Hom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MonoidHom_exists_subfield_units_coe_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MonoidHom_exists_subfield_units_coe_eq

set_option autoImplicit false

/--
@isnad1 id=ex.1h4v.s13.ce427ca655dd from=translated src=- shape=06f11306 vocab=0b216f99
-/
theorem solution
    {G : Type*} [Group G] {L : Type*} [Field L] (K : Subfield L)
    (F : G →* G →* Lˣ) (hF : ∀ α β : G, ((F α β : Lˣ) : L) ∈ K) :
    ∃ F' : G →* G →* (↥K)ˣ, ∀ α β : G, (((F' α β : (↥K)ˣ) : ↥K) : L) = F α β := by

  have hinv : ∀ α β : G, ((F α β : Lˣ) : L)⁻¹ ∈ K := fun α β => K.inv_mem (hF α β)
  let u : G → G → (↥K)ˣ := fun α β =>
    ⟨⟨(F α β : L), hF α β⟩, ⟨((F α β : Lˣ) : L)⁻¹, hinv α β⟩,
      Subtype.ext (by simp), Subtype.ext (by simp)⟩
  have hu : ∀ α β, (((u α β : (↥K)ˣ) : ↥K) : L) = F α β := fun _ _ => rfl
  refine ⟨{ toFun := fun α => { toFun := u α, map_one' := ?_, map_mul' := ?_ }, map_one' := ?_, map_mul' := ?_ }, hu⟩
  · ext; simp [u]
  · intro β₁ β₂; ext; simp [u, Units.val_mul]
  · ext β; simp [u]
  · intro α₁ α₂; ext β; simp [u, Units.val_mul]
