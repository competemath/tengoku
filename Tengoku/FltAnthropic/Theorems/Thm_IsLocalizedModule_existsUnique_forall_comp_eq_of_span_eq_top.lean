import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalizedModule_existsUnique_forall_comp_eq_of_span_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalizedModule_existsUnique_forall_comp_eq_of_span_eq_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

theorem IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top
    {B : Type u} [CommRing B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (M : Fin k → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)]
    (M₂ : Fin k → Fin k → Type u) [∀ i j, AddCommGroup (M₂ i j)] [∀ i j, Module B (M₂ i j)]
    (ρl : ∀ i j, M i →ₗ[B] M₂ i j) (ρr : ∀ i j, M j →ₗ[B] M₂ i j)
    (hρr : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr i j))
    (N : Type u) [AddCommGroup N] [Module B N] (π : ∀ i, N →ₗ[B] M i)
    (hπ : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (π i))
    (hπc : ∀ i j, ρl i j ∘ₗ π i = ρr i j ∘ₗ π j)
    (T : Type u) [AddCommGroup T] [Module B T] (g : ∀ i, T →ₗ[B] M i)
    (hg : ∀ i j, ρl i j ∘ₗ g i = ρr i j ∘ₗ g j) :
    ∃! G : T →ₗ[B] N, ∀ i, π i ∘ₗ G = g i := by exact @_root_.P2MW.S_IsLocalizedModule_existsUnique_forall_comp_eq_of_span_eq_top.solution B _ k f hf M _ _ M₂ _ _ ρl ρr hρr N _ _ π hπ hπc T _ _ g hg
