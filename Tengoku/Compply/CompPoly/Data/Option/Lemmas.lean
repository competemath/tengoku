/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa
-/
module

public import Tengoku.Seed.Data.Option.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Auxiliary lemmas for `Option`
-/

@[expose] public section

namespace Option

/-- `Option.filter` leaves its argument alone exactly when the predicate holds of the contained
value. The `Option` analogue of `List.filter_eq_self` and `Array.filter_eq_self`.
@isnad1 id=iff.0h3v.s5.26b5f69ade52 from=translated src=- shape=facc5688 vocab=4e483964
-/
theorem filter_eq_self {α : Type*} {o : Option α} {p : α → Bool} :
    o.filter p = o ↔ ∀ a ∈ o, p a := by
  cases o <;> simp

end Option
