import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_span_le_pow_of_forall_isIdempotentElem_of_subset.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_span_le_pow_of_forall_isIdempotentElem_of_subset

set_option autoImplicit false
universe u

/--
@isnad1 id=le.2h4v.s7.37c9ba07f901 from=translated src=- shape=8a8bfb9f vocab=e7de4002
-/
theorem solution
    {R : Type u} [CommRing R] (S : Set R) (hS : ∀ e ∈ S, IsIdempotentElem e)
    (𝔭 : Ideal R) (hS𝔭 : S ⊆ 𝔭) (n : ℕ) : Ideal.span S ≤ 𝔭 ^ n := by
  rcases n with _ | n
  · rw [pow_zero, Ideal.one_eq_top]; exact le_top
  · rw [Ideal.span_le]
    intro e he
    have h := Ideal.pow_mem_pow (hS𝔭 he) (n + 1)
    rwa [(hS e he).pow_succ_eq] at h
