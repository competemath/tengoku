module

public import Tengoku

public section

namespace ZMod
variable {M : Type*} {q : ℕ}

-- FIXME: The LHS has type `Fin (q + 1)`. See
/--
@isnad1 id=eq.1h2v.s5.433effde3c6e from=translated src=- shape=5af00b7a vocab=858cad74
-/
@[simp↓] lemma val_mk (n : ℕ) (hn) : val (n := q + 1) (⟨n, hn⟩ : ZMod (q + 1)) = n := rfl

-- FIXME: The LHS has type `Fin (q + 1)`. See
/--
@isnad1 id=eq.1h2v.s7.1d74067f79a1 from=translated src=- shape=4c386033 vocab=4820fd51
-/
@[simp] lemma mk_eq_natCast (n : ℕ) (hn) : ⟨n, hn⟩ = (n : ZMod (q + 1)) :=
  (Fin.natCast_eq_mk _).symm

end ZMod
