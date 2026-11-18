import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Multiset_esymm_map_sub_esymm_map_mem_pow_succ

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Multiset_esymm_map_sub_esymm_map_mem_pow_succ.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=mem.2h7v.s8.8193a5aebe6e from=translated src=- shape=39b952a8 vocab=ee6ace69
-/
theorem Multiset.esymm_map_sub_esymm_map_mem_pow_succ
    (A : Type) [CommRing A] (I : Ideal A) (ι : Type) (s : Finset ι) (y z : ι → A)
    (hz : ∀ i ∈ s, z i ∈ I) (hyz : ∀ i ∈ s, y i - z i ∈ I ^ 2) (k : ℕ) :
    (s.val.map y).esymm k - (s.val.map z).esymm k ∈ I ^ (k + 1) := by exact @_root_.P2MW.S_Multiset_esymm_map_sub_esymm_map_mem_pow_succ.solution A _ I ι s y z hz hyz k
