import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Representation_exists_ne_zero_forall_apply_eq_self_or_eq_char_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Representation_exists_ne_zero_forall_apply_eq_self_or_eq_char_smul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.1h5v.s11.2254760d68f5 from=translated src=- shape=908545a8 vocab=5546d8d4
-/
theorem Representation.exists_ne_zero_forall_apply_eq_self_or_eq_char_smul
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [Finite V] [Nontrivial V]
    (ρ : Representation k G V) (χ : G →* kˣ)
    (h : ∀ (g : G) (v : V), ρ g (ρ g v - (χ g : k) • v) = ρ g v - (χ g : k) • v) :
    ∃ v : V, v ≠ 0 ∧ ((∀ g : G, ρ g v = v) ∨ (∀ g : G, ρ g v = (χ g : k) • v)) := by exact @_root_.P2MW.S_Representation_exists_ne_zero_forall_apply_eq_self_or_eq_char_smul.solution k G V _ _ _ _ _ _ ρ χ h
