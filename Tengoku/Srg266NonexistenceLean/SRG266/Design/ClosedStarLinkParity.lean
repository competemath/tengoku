/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.Data.Fin.Basic
import Tengoku.Seed.Tactic.Tauto

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.QuasiSymmetric

theorem twoColor_link_parity (x y z : Fin 2) :
    (x = y ↔ (x = z ↔ y = z)) := by omega

theorem three_link_parities_force_face (A B C D : Prop)
    (h₁ : A ↔ (B ↔ C)) (h₂ : A ↔ (B ↔ D)) (h₃ : A ↔ (C ↔ D)) :
    A := by tauto

theorem triple_of_four_point_link_parity
    {P : Type*} (H : P → P → P → Prop)
    (swap : ∀ p q r, H p q r ↔ H q p r)
    (rotate : ∀ p q r, H p q r ↔ H q r p)
    (a b c d : P)
    (ha : H a b c ↔ (H a b d ↔ H a c d))
    (hb : H b a c ↔ (H b a d ↔ H b c d))
    (hc : H c a b ↔ (H c a d ↔ H c b d)) :
    H a b c := by
  rw [swap b a c, swap b a d] at hb
  rw [rotate c a b, swap c a d, swap c b d] at hc
  exact three_link_parities_force_face _ _ _ _ ha hb hc

end SRG266.QuasiSymmetric
