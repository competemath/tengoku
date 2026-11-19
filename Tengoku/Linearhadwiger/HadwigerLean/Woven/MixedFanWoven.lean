import Tengoku.Linearhadwiger.HadwigerLean.Woven.HubMatching

import Tengoku.Linearhadwiger.HadwigerLean.Woven.MixedFanTrim

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proxy woven solution from the mixed fan

This combines the paired-source mixed Menger linkage with the linked hub
and an arbitrary rooted clique model in the residual graph.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {a j : ℕ}
  {Z U H : Finset V}
  {P : IndexedPairs (Fin a × Fin 2) V}

/-- Proxy root vertices indexed by the root roles.-/
def hubProxyRoots (proxy : HubProxyRole a j ≃ Z) : Fin a → V :=
  fun i => (proxy (Sum.inl i)).1

/-- Proxy terminal pairs indexed by the terminal roles.-/
def hubProxyPairs (proxy : HubProxyRole a j ≃ Z) :
    IndexedPairs (Fin j) V where
  start := fun k => (proxy (Sum.inr (k,0))).1
  finish := fun k => (proxy (Sum.inr (k,1))).1

end Woven
end HadwigerLean
