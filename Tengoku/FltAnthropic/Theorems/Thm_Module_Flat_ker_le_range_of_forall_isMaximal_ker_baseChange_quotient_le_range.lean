import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open TensorProduct

/--
@isnad1 id=le.4h5v.s13.e66cc018f8cd from=translated src=- shape=e2f9d5e0 vocab=58180a17
-/
theorem Module.Flat.ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (hfib : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal] (i : ℕ),
      LinearMap.ker ((d (i + 1)).baseChange (R ⧸ 𝔪)) ≤ LinearMap.range ((d i).baseChange (R ⧸ 𝔪))) :
    ∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i) := by exact @_root_.P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.solution R _ _ C _ _ _ d hdd n hbd hfin hfib
