import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsGaloisGroup_exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsGaloisGroup_exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=and.1h4v.s10.55e830c126b4 from=translated src=- shape=3cec0e2d vocab=18f7dfa6
-/
theorem IsGaloisGroup.exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard
    (O A B : Type) [CommRing O] [IsNoetherianRing O] [CommRing A] [CommRing B]
    [Algebra O A] [Algebra O B] [Algebra A B] [IsScalarTower O A B] [Algebra.FiniteType O B]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G O B]
    [IsGaloisGroup G A B] [FaithfulSMul A B]
    (hG : IsUnit ((Nat.card G : ℕ) : O)) :
    (∃ r : B →ₗ[A] A, ∀ a : A, r (algebraMap A B a) = a) ∧
    (∀ 𝔞 : Ideal O,
      (∀ a : A, algebraMap A B a ∈ 𝔞.map (algebraMap O B) → a ∈ 𝔞.map (algebraMap O A)) ∧
      (∀ b : B, (∀ g : G, g • b - b ∈ 𝔞.map (algebraMap O B)) →
        ∃ a : A, algebraMap A B a - b ∈ 𝔞.map (algebraMap O B))) ∧
    Module.Finite A B ∧ Algebra.FiniteType O A ∧
    (Module.Flat O B → Module.Flat O A) := by exact @_root_.P2MW.S_IsGaloisGroup_exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard.solution O A B _ _ _ _ _ _ _ _ _ G _ _ _ _ _ _ hG
