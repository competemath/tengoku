/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.Data.Int.Basic
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

def ShortFrameLabel (a c : ℤ) : Prop :=
  ((a = 3 ∨ a = 9) ∧ c = 0) ∨ ((a = 1 ∨ a = 11) ∧ (c = -1 ∨ c = 1))

def orientedALabel (ε a : ℤ) : ℤ := if ε = 1 then a else 12-a

theorem shortFrameLabel_compatible_B {a b c d : ℤ}
    (ha : ShortFrameLabel a c) (hb : b = 1 ∨ b = 11) (hd : d = -1 ∨ d = 1)
    (hdiv : 12 ∣ 21-a*b+16*c*d) :
    (orientedALabel (if b = 1 then 1 else -1) a = 9 ∧ c = 0) ∨
      (orientedALabel (if b = 1 then 1 else -1) a = 1 ∧ c = d) := by
  rcases ha with ⟨ha, rfl⟩ | ⟨ha, hc⟩
  · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      rcases hd with rfl | rfl <;> norm_num at hdiv <;> norm_num [orientedALabel]
  · rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;>
      rcases hb with rfl | rfl <;> rcases hd with rfl | rfl <;>
      norm_num at hdiv <;> norm_num [orientedALabel]

theorem shortFrameLabel_compatible_A {a b : ℤ}
    (ha : a = 3 ∨ a = 9) (hb : b = 3 ∨ b = 9) (hdiv : 12 ∣ 21-a*b) :
    a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num at hdiv <;> rfl

theorem shortFrameLabel_global_orientation {ι : Type*} (anchor : ι) (a c : ι → ℤ)
    (hlabel : ∀ i, ShortFrameLabel (a i) (c i))
    (hpair : ∀ i j, 12 ∣ 21-a i*a j+16*c i*c j) :
    ∃ ε δ : ℤ, (ε = -1 ∨ ε = 1) ∧ (δ = -1 ∨ δ = 1) ∧
      ∀ i, (orientedALabel ε (a i) = 9 ∧ c i = 0) ∨
        (orientedALabel ε (a i) = 1 ∧ c i = δ) := by
  classical
  by_cases hB : ∃ i, c i ≠ 0
  · obtain ⟨j, hj⟩ := hB
    have hBj : (a j = 1 ∨ a j = 11) ∧ (c j = -1 ∨ c j = 1) :=
      (hlabel j).resolve_left (fun h => hj h.2)
    refine ⟨if a j = 1 then 1 else -1, c j, ?_, hBj.2, ?_⟩
    · split_ifs <;> simp
    · intro i
      exact shortFrameLabel_compatible_B (hlabel i) hBj.1 hBj.2 (hpair i j)
  · have hc (i) : c i = 0 := by
      by_contra hi
      exact hB ⟨i, hi⟩
    have ha (i) : a i = 3 ∨ a i = 9 := by
      rcases hlabel i with h | ⟨_, h⟩
      · exact h.1
      · rw [hc i] at h
        omega
    have heq (i) : a i = a anchor := by
      apply shortFrameLabel_compatible_A (ha i) (ha anchor)
      simpa only [hc, mul_zero, add_zero] using hpair i anchor
    refine ⟨if a anchor = 9 then 1 else -1, 1, ?_, Or.inr rfl, ?_⟩
    · split_ifs <;> simp
    · intro i
      refine Or.inl ⟨?_, hc i⟩
      rw [heq i]
      rcases ha anchor with h | h <;> simp [h, orientedALabel]

end SRG266.Lattice
