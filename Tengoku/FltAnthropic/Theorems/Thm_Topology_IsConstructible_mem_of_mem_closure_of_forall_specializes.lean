import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Topology

universe u

/--
@isnad1 id=mem.3h3v.s5.f9f58168bf25 from=translated src=- shape=387f4c10 vocab=6d785e0a
-/
theorem Topology.IsConstructible.mem_of_mem_closure_of_forall_specializes
    {X : Type u} [TopologicalSpace X] {s : Set X} (hs : Topology.IsConstructible s)
    {x : X} (hx : x ∈ closure s) (hgen : ∀ y ∈ s, x ⤳ y) : x ∈ s := by exact @_root_.P2MW.S_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes.solution X _ s hs x hx hgen
