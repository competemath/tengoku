module
public import Tengoku

namespace WithBot

variable {α β} {f : α → β} (a b : WithBot α)

/--
@isnad1 id=eq.1h5v.s6.b6cacb831ca7 from=translated src=- shape=9453931c vocab=a4a4cbfe
-/
@[to_dual]
public theorem map_add' [Add α] [Add β] (hf : ∀ x y, f (x + y) = f x + f y) :
    (a + b).map f = a.map f + b.map f := by
  induction a
  · exact (bot_add _).symm
  · induction b
    · exact (add_bot _).symm
    · rw [map_coe, map_coe, ← coe_add, ← coe_add, ← hf]
      rfl

/--
@isnad1 id=iff.1h5v.s6.5d9acff11c26 from=translated src=- shape=690bca31 vocab=f2548894
-/
@[to_dual]
public lemma map_lt_iff [LT α] [LT β] (f : α → β) (mono_iff : ∀ {a b}, f a < f b ↔ a < b) :
    a.map f < b.map f ↔ a < b := by cases a <;> cases b <;> simp [mono_iff]

end WithBot
