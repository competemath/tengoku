import Tengoku.Seed.Algebra.FreeMonoid.Basic
import Tengoku.Seed.Algebra.MonoidAlgebra.Basic
import Tengoku.Seed.Data.List.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact residual-word consumption

`consumePrefix p w` returns the unique suffix after consuming a prescribed
initial word p, or fails if no such suffix exists.  This explicit recursion
will describe the deterministic internal part of the suffix-trie automaton.
-/

namespace CriticalGK2.Automaton

def consumePrefix : List Bool → List Bool → Option (List Bool)
  | [], w => some w
  | _ :: _, [] => none
  | a :: p, b :: w => if a = b then consumePrefix p w else none

/--
@isnad1 id=eq.0h1v.s3.ab74416bcbcc from=translated src=- shape=c7592c35 vocab=0bd37907
-/
@[simp]
theorem consumePrefix_nil (w : List Bool) : consumePrefix [] w = some w := rfl

/-- Successful word consumption is equivalent to word concatenation.
@isnad1 id=iff.0h3v.s5.ebb26dae3887 from=translated src=- shape=41a1b28c vocab=ad1fdb47
-/
theorem consumePrefix_eq_some_iff (p w t : List Bool) :
    consumePrefix p w = some t ↔ w = p ++ t := by
  induction p generalizing w with
  | nil => simp [consumePrefix]
  | cons a p ih =>
    cases w with
    | nil => simp [consumePrefix]
    | cons b w =>
      cases a <;> cases b <;> simp [consumePrefix, ih]

/--
@isnad1 id=eq.0h2v.s4.24139b537dc6 from=translated src=- shape=340ca5c4 vocab=ad1fdb47
-/
@[simp]
theorem consumePrefix_append (p t : List Bool) :
    consumePrefix p (p ++ t) = some t :=
  (consumePrefix_eq_some_iff p (p ++ t) t).mpr rfl

/--
@isnad1 id=le.1h3v.s4.8f4e9cf2f361 from=translated src=- shape=b4ec3a51 vocab=c4c7ea34
-/
theorem length_le_of_consumePrefix_eq_some (p w t : List Bool)
    (h : consumePrefix p w = some t) : t.length ≤ w.length := by
  have hw := (consumePrefix_eq_some_iff p w t).mp h
  rw [hw, List.length_append]
  omega

/--
@isnad1 id=not.1h2v.s5.4240de4a6f4f from=translated src=- shape=f15a381d vocab=43a1507d
-/
theorem consumePrefix_none_no_append (p w : List Bool)
    (h : consumePrefix p w = none) : ¬ ∃ t, w = p ++ t := by
  rintro ⟨t, ht⟩
  have hs := (consumePrefix_eq_some_iff p w t).mpr ht
  rw [h] at hs
  contradiction

end CriticalGK2.Automaton
