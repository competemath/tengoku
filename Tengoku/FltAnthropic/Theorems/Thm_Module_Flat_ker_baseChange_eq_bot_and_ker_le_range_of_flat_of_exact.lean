import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open TensorProduct

/--
@isnad1 id=and.4h5v.s12.498b2ba961ac from=translated src=- shape=60c82785 vocab=2c9c629d
-/
theorem Module.Flat.ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact
    {R : Type u} [CommRing R] (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
    [∀ i, Module.Flat R (C i)] (d : ∀ i, C i →ₗ[R] C (i + 1))
    (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (h0 : LinearMap.ker (d 0) = ⊥) (hex : ∀ i, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i))
    (A : Type u) [CommRing A] [Algebra R A] :
    LinearMap.ker ((d 0).baseChange A) = ⊥ ∧
      ∀ i, LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A) := by exact @_root_.P2MW.S_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact.solution R _ C _ _ _ d hdd n hbd h0 hex A _ _
