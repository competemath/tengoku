import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_RingTheory_AffineDilatation
import Tengoku.FltAnthropic.P2M.Sol.S_AffineDilatation_nonempty_algEquiv_tensorProduct_of_flat_of_map_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AffineDilatation_nonempty_algEquiv_tensorProduct_of_flat_of_map_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open TensorProduct

universe u

theorem AffineDilatation.nonempty_algEquiv_tensorProduct_of_flat_of_map_eq
    {P : Type u} [CommRing P] (I : Ideal P) (a : P) (ha : a ∈ I)
    {C : Type u} [CommRing C] [Algebra P C] [Module.Flat P C]
    (J : Ideal C) (b : C) (hJ : I.map (algebraMap P C) = J) (hb : algebraMap P C a = b) :
    ∃ e : C ⊗[P] AffineDilatation.Ring I a ≃ₐ[C] AffineDilatation.Ring J b,
      ∀ (g : P) (hg : g ∈ I),
        e (1 ⊗ₜ AffineDilatation.divElem I a g hg) =
          AffineDilatation.divElem J b (algebraMap P C g) (hJ ▸ Ideal.mem_map_of_mem (algebraMap P C) hg) := by exact @_root_.P2MW.S_AffineDilatation_nonempty_algEquiv_tensorProduct_of_flat_of_map_eq.solution P _ I a ha C _ _ _ J b hJ hb
