/-
Copyright (c) 2025 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Tengoku

/-!
Misere combinatorial games.
-/

namespace MisereGames

public section

/-- Either the Left or Right player. -/
@[aesop safe cases]
inductive Player where
  /-- The Left player. -/
  | left  : Player
  /-- The Right player. -/
  | right : Player
deriving DecidableEq, Inhabited

instance : Fintype Player :=
  Fintype.ofList [Player.left, Player.right] (by
    intro player
    cases player <;> simp)

namespace Player

/-- Specify a function `Player → α` from its two outputs. -/
@[simp]
abbrev cases {α : Sort*} (l r : α) : Player → α
  | .left => l
  | .right => r

/--
@isnad1 id=eq.0h6v.s5.4e9c20b49e10 from=translated src=- shape=f2e23aaf vocab=16c3ace3
-/
lemma apply_cases {α β : Sort*} (f : α → β) (l r : α) (p : Player) :
    f (cases l r p) = cases (f l) (f r) p := by
  cases p <;> rfl

/--
@isnad1 id=iff.0h5v.s5.ffd11e7282d3 from=translated src=- shape=fcc8073c vocab=16c3ace3
-/
@[simp]
theorem cases_inj {α : Sort*} {l₁ r₁ l₂ r₂ : α} :
    cases l₁ r₁ = cases l₂ r₂ ↔ l₁ = l₂ ∧ r₁ = r₂ :=
  ⟨fun h ↦ ⟨congr($h left), congr($h right)⟩, fun ⟨hl, hr⟩ ↦ hl ▸ hr ▸ rfl⟩

/--
@isnad1 id=eq.1h4v.s4.29887d1d6527 from=translated src=- shape=45363872 vocab=b0ebc1c1
-/
theorem const_of_left_eq_right {α : Sort*} {f : Player → α} (hf : f left = f right) :
    ∀ p q, f p = f q
  | left, left | right, right => rfl
  | left, right => hf
  | right, left => hf.symm

/--
@isnad1 id=iff.1h3v.s4.3ae4573138e2 from=translated src=- shape=87b8f4aa vocab=b0ebc1c1
-/
theorem const_of_left_eq_right' {f : Player → Prop} (hf : f left ↔ f right) (p q) : f p ↔ f q :=
  (const_of_left_eq_right hf.eq ..).to_iff

@[simp low]
protected lemma «forall» {p : Player → Prop} :
    (∀ x, p x) ↔ p left ∧ p right :=
  ⟨fun h ↦ ⟨h left, h right⟩, fun ⟨hl, hr⟩ ↦ fun | left => hl | right => hr⟩

@[simp low]
protected lemma «exists» {p : Player → Prop} :
    (∃ x, p x) ↔ p left ∨ p right :=
  ⟨fun | ⟨left, h⟩ => .inl h | ⟨right, h⟩ => .inr h, fun | .inl h | .inr h => ⟨_, h⟩⟩

instance : Neg Player where
  neg := cases right left

/--
@isnad1 id=eq.0h0v.s2.d1c74a0ab5d6 from=translated src=- shape=28fc0566 vocab=e371676b
-/
@[simp] lemma neg_left : -left = right := rfl
/--
@isnad1 id=eq.0h0v.s2.e7449757f02a from=translated src=- shape=28fc0566 vocab=e371676b
-/
@[simp] lemma neg_right : -right = left := rfl

instance : InvolutiveNeg Player where
  neg_neg := by
    intro player
    cases player <;> rfl

/--
@isnad1 id=iff.0h2v.s4.165847fbed01 from=translated src=- shape=c9de3dee vocab=e834e268
-/
@[simp]
theorem ne_iff_eq_neg {a b : Player} : (a ≠ b ↔ a = -b) := by
  cases a <;> cases b <;> simp

/--
@isnad1 id=false.2h2v.s4.b80183e45ebe from=translated src=- shape=fc7194d9 vocab=e834e268
-/
protected theorem absurd {p q : Player} (h1 : p = q) (h2 : p = -q) : False := by
  subst h1
  cases p <;> simp at h2

instance : LE Player where
  le lhs rhs := (lhs = .right) ∨ (lhs = .left ∧ rhs = .left)

instance : DecidableLE Player := by
  simp only [DecidableLE, DecidableRel, LE.le]
  infer_instance

/--
@isnad1 id=eq.1h1v.s3.e1929eea2d57 from=translated src=- shape=0faf4c8c vocab=559d7555
-/
theorem le_right_eq (p : Player) (h1 : p ≤ .right) : p = .right := by
  simp only [LE.le, reduceCtorEq, and_false, or_false] at h1
  exact h1

/--
@isnad1 id=iff.0h1v.s3.90a93aba6e0e from=translated src=- shape=828d6e43 vocab=559d7555
-/
@[simp]
theorem le_right_iff (p : Player) : p ≤ .right ↔ p = .right :=
  ⟨le_right_eq p, by
    intro h
    subst p
    exact Or.inl rfl⟩

/--
@isnad1 id=eq.1h1v.s3.6fb8e957cb03 from=translated src=- shape=ac17ed56 vocab=e3645a91
-/
theorem le_left_eq (p : Player) (h1 : .left ≤ p) : p = .left := by
  simp only [LE.le, reduceCtorEq, true_and, false_or] at h1
  exact h1

/--
@isnad1 id=iff.0h1v.s3.6519789a299c from=translated src=- shape=00314e92 vocab=e3645a91
-/
@[simp]
theorem left_le_iff (p : Player) : .left ≤ p ↔ p = .left :=
  ⟨le_left_eq p, by
    intro h
    subst p
    exact Or.inr ⟨rfl, rfl⟩⟩

/--
@isnad1 id=le.0h1v.s2.aeaeac4916de from=translated src=- shape=63e234e9 vocab=559d7555
-/
@[simp]
theorem right_le (p : Player) : .right ≤ p := by
  simp only [LE.le, reduceCtorEq, or_false, false_and]

/--
@isnad1 id=le.0h1v.s2.0bd479f82d5e from=translated src=- shape=fb20e06d vocab=e3645a91
-/
@[simp]
theorem le_left (p : Player) : p ≤ .left := by
  cases p <;> simp only [LE.le, reduceCtorEq, and_self, or_false, or_true, and_true]

/--
@isnad1 id=false.1h0v.s2.71c57fb81e94 from=translated src=- shape=58dd77c6 vocab=1c1a5c12
-/
theorem left_le_right (h1 : Player.left ≤ Player.right) : False := by
  simp only [LE.le, reduceCtorEq, and_false, or_self] at h1

/--
@isnad1 id=not.0h0v.s2.7f164ccb6f14 from=translated src=- shape=6516253f vocab=1c1a5c12
-/
theorem not_left_le_right : ¬ Player.left ≤ Player.right :=
  left_le_right

end Player

end

end MisereGames
