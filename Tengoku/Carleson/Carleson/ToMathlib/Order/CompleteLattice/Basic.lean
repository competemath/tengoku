module

public import Tengoku.Carleson.Carleson.ToMathlib.Order.ConditionallyCompleteLattice.Basic

public section

-- Upstreaming status: ready but maybe unnecessary

--currently unused
/--
@isnad1 id=eq.2h5v.s6.a1b677cef5d4 from=translated src=- shape=9886736f vocab=fa336fd0
-/
theorem iSup_eq_iSup {α : Type*} {ι ι' : Sort*} [CompleteLattice α] {f : ι → α} {g : ι' → α}
  (h₀ : ∀ i, ∃ j, f i ≤ g j) (h₁ : ∀ j, ∃ i, g j ≤ f i) :
    ⨆ i, f i = ⨆ j, g j := le_antisymm (iSup_mono' h₀) (iSup_mono' h₁)
