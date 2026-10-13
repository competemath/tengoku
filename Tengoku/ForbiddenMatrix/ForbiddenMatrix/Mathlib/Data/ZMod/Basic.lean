module

public import Tengoku

public section

/--
@isnad1 id=eq.0h2v.s7.0436391c4c39 from=translated src=- shape=085ea553 vocab=2f80e219
-/
@[simp, norm_cast] lemma Fin.natCast_val_eq_zmodFinEquiv {n : ℕ} [NeZero n] (a : Fin n) :
    a = ZMod.finEquiv n a := by
  obtain _ | n := n
  · obtain ⟨_, ⟨⟩⟩ := a
  · change (⟨_, _⟩ : ZMod (n + 1)) = ⟨_, _⟩
    congr
    simp
    lia
