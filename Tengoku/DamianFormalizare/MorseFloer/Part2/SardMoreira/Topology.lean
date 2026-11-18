import Tengoku.Seed.Topology.NhdsWithin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.DamianFormalizare end Tengoku.DamianFormalizare open Tengoku.DamianFormalizare
open Filter
open scoped Topology

/--
@isnad1 id=iff.1h4v.s5.7856e5b233f4 from=translated src=- shape=8fd5e85d vocab=f4497fe8
-/
theorem _root_.Tengoku.DamianFormalizare.eventually_nhdsWithin_nhds {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    {p : X → Prop} {x : X} :
    (∀ᶠ y in 𝓝[U] x, ∀ᶠ z in 𝓝 y, p z) ↔ ∀ᶠ y in 𝓝[U] x, p y := by
  conv_rhs => rw [← eventually_eventually_nhdsWithin]
  refine eventually_congr <| eventually_mem_nhdsWithin.mono fun y hy ↦ ?_
  rw [hU.nhdsWithin_eq hy]
-- Tengoku: root names of this library moved to Tengoku.DamianFormalizare so they do not collide with other libraries (generated)
