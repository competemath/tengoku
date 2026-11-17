import Tengoku.Seed.GroupTheory.OrderOfElement
import Tengoku.Seed.Data.Set.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff

set_option autoImplicit false

/--
@isnad1 id=iff.0h3v.s7.6bafd5ebb8a1 from=translated src=- shape=3a072dcc vocab=129b8cff
-/
theorem solution {G : Type*} [Group G] [Finite G] (σ τ : G) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard ≠ 0
      ↔ ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) τ := by
  constructor
  · intro hne
    obtain ⟨g, k, hk, hgk⟩ := Set.nonempty_of_ncard_ne_zero hne
    exact ⟨k, hk, isConj_iff.mpr ⟨g, hgk⟩⟩
  · rintro ⟨k, hk, hconj⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    exact Set.ncard_ne_zero_of_mem (a := g) ⟨k, hk, hg⟩ (Set.toFinite _)
