import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Data.ZMod.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# The finite cyclic dimension chain

The spaces are a genuinely dependent family and may initially have different
dimensions, including dimension zero. No equal-size identification is assumed.
-/

namespace FugledeAudit

open Module

/--
@isnad1 id=eq.1h6v.s9.47bbc417ff1b from=translated src=- shape=e0d0f5e4 vocab=b4c099ef
-/
theorem permutation_dimensions_equal_of_injective
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    {𝕜 : Type*} [DivisionRing 𝕜] (V : ι → Type*)
    [∀ j, AddCommGroup (V j)] [∀ j, Module 𝕜 (V j)]
    [∀ j, FiniteDimensional 𝕜 (V j)]
    (S : ∀ j, V (σ j) →ₗ[𝕜] V j) (hS : ∀ j, Function.Injective (S j)) :
    ∀ j, finrank 𝕜 (V (σ j)) = finrank 𝕜 (V j) := by
  have hle : ∀ j, finrank 𝕜 (V (σ j)) ≤ finrank 𝕜 (V j) :=
    fun j => LinearMap.finrank_le_finrank_of_injective (hS j)
  have hsum : ∑ j, finrank 𝕜 (V (σ j)) = ∑ j, finrank 𝕜 (V j) :=
    Equiv.sum_comp σ (fun j => finrank 𝕜 (V j))
  have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hsum
  exact fun j => heq j (Finset.mem_univ j)

/--
@isnad1 id=bijectiv.1h6v.s9.2a07d3231eaf from=translated src=- shape=89b4598f vocab=fe5d5230
-/
theorem permutation_blocks_bijective_of_injective
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    {𝕜 : Type*} [DivisionRing 𝕜] (V : ι → Type*)
    [∀ j, AddCommGroup (V j)] [∀ j, Module 𝕜 (V j)]
    [∀ j, FiniteDimensional 𝕜 (V j)]
    (S : ∀ j, V (σ j) →ₗ[𝕜] V j) (hS : ∀ j, Function.Injective (S j)) :
    ∀ j, Function.Bijective (S j) := by
  intro j
  exact ⟨hS j, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (permutation_dimensions_equal_of_injective σ V S hS j)).mp (hS j)⟩

/--
@isnad1 id=eq.1h4v.s6.61c070849d93 from=translated src=- shape=3ec1c4e3 vocab=e51a689f
-/
theorem zmod_function_constant_of_successor_eq
    (q : ℕ) [NeZero q] {α : Type*} (d : ZMod q → α)
    (hd : ∀ j, d (j + 1) = d j) : ∀ j, d j = d 0 := by
  have hnat : ∀ n : ℕ, d (n : ZMod q) = d 0 := by
    intro n
    induction n with
    | zero => simp only [Nat.cast_zero]
    | succ n ih => simpa only [Nat.cast_succ, hd] using ih
  intro j
  simpa only [ZMod.natCast_zmod_val] using hnat j.val

/--
@isnad1 id=eq.1h5v.s10.a919433aa746 from=translated src=- shape=0c961eb5 vocab=d7b29b9a
-/
theorem cyclic_common_dimension_of_injective
    (q : ℕ) [NeZero q]
    {𝕜 : Type*} [DivisionRing 𝕜] (V : ZMod q → Type*)
    [∀ j, AddCommGroup (V j)] [∀ j, Module 𝕜 (V j)]
    [∀ j, FiniteDimensional 𝕜 (V j)]
    (S : ∀ j, V (j + 1) →ₗ[𝕜] V j) (hS : ∀ j, Function.Injective (S j)) :
    ∀ j, finrank 𝕜 (V j) = finrank 𝕜 (V 0) := by
  apply zmod_function_constant_of_successor_eq q
  exact permutation_dimensions_equal_of_injective (Equiv.addRight (1 : ZMod q)) V S hS

end FugledeAudit
