import Tengoku.Seed.Data.List.OfFn
import Tengoku.Seed.Data.Fin.Tuple.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ordered finite insertion under List.ofFn

Converting a finite tuple insertion to a list preserves the exact prefix,
inserted element, and suffix order. No commutativity assumption is involved.
-/

noncomputable section
set_option autoImplicit false
namespace List

/-- Finite insertion has exactly the same ordered list as inserting between
the corresponding prefix and suffix.
@isnad1 id=eq.0h5v.s6.c268cdf42da3 from=translated src=- shape=06241896 vocab=c3452659
-/
theorem ofFn_insertNth_eq_take_cons_drop {α : Type*} {m : ℕ}
    (v : Fin m → α) (i : Fin (m + 1)) (a : α) :
    List.ofFn (Fin.insertNth i a v) =
      (List.ofFn v).take i ++ a :: (List.ofFn v).drop i := by
  induction m with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [← Fin.cons_self_tail v, Fin.insertNth_succ_cons,
        List.ofFn_cons, List.ofFn_cons, ih]
      simp

end List
