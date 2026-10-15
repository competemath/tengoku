/-
Copyright (c) 2024 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/
module

public import Tengoku

/-!
# Extra lemmas about context-free grammars

Additions to `Mathlib.Computability.ContextFreeGrammar` from the authors'
in-review Mathlib branch (`alex-loitzl-cnf`) that are not yet available in the
Mathlib release pinned here: the step-counting derivation relation
`ContextFreeGrammar.DerivesIn` with its induction principles and splitting
lemmas, plus a few facts about `ContextFreeGrammar.Produces`.
-/

@[expose] public section

universe uT

variable {T : Type uT}

namespace ContextFreeGrammar

variable {g : ContextFreeGrammar T}

/--
@isnad1 id=produces.1h3v.s6.fd2de1320ea6 from=translated src=- shape=7e689eac vocab=dbe371c7
-/
lemma Produces.input_output {r : ContextFreeRule T g.NT} (hrg : r ∈ g.rules) :
    g.Produces [.nonterminal r.input] r.output := ⟨r, hrg, ContextFreeRule.Rewrites.input_output⟩

/--
@isnad1 id=mem.1h4v.s6.e8f692674e7b from=translated src=- shape=aa611ab7 vocab=e0b159a9
-/
lemma Produces.rule {n : g.NT} {u : List (Symbol T g.NT)}
    (hnu : g.Produces [Symbol.nonterminal n] u) :
    ⟨n, u⟩ ∈ g.rules := by
  obtain ⟨_, _, hr⟩ := hnu
  cases hr
  · rwa [List.append_nil]
  · contradiction

/--
@isnad1 id=var.1h7v.s6.8c732c98c78e from=translated src=- shape=437f863b vocab=074192de
-/
theorem Derives.head_induction_on {v : List (Symbol T g.NT)} {P : ∀ u, g.Derives u v → Prop}
    {u : List (Symbol T g.NT)} (huv : g.Derives u v)
    (refl : P v (Derives.refl v))
    (head : ∀ {u w} (huw : g.Produces u w) (hwv : g.Derives w v),
      P w hwv → P u (hwv.head huw)) :
    P u huv := Relation.ReflTransGen.head_induction_on huv refl head

end ContextFreeGrammar

/-! Alternative definition of `ContextFreeGrammar.Derives` which allows to use well-founded
induction on derivations, by explicitely counting the number of steps of the transformation -/
section derivesIn

namespace ContextFreeGrammar

/-- Given a context-free grammar `g`, strings `u` and `v`, and number `n`
`g.DerivesIn u v n` means that `g` can transform `u` to `v` in `n` rewriting steps. -/
inductive DerivesIn (g : ContextFreeGrammar T) :
    List (Symbol T g.NT) → List (Symbol T g.NT) → ℕ → Prop
  /-- 0 steps entail no transformation -/
  | refl (w : List (Symbol T g.NT)) : g.DerivesIn w w 0
  /-- n + 1 steps, if transforms `u` to `v` in n steps, and `v` to `w` in 1 step  -/
  | tail (u v w : List (Symbol T g.NT)) (n : ℕ) :
    g.DerivesIn u v n → g.Produces v w → g.DerivesIn u w n.succ

/--
@isnad1 id=iff.0h4v.s5.db655abcb60e from=translated src=- shape=cac795a5 vocab=cd4ff675
-/
lemma derives_iff_derivesIn (g : ContextFreeGrammar T) (v w : List (Symbol T g.NT)) :
    g.Derives v w ↔ ∃ n : ℕ, g.DerivesIn v w n := by
  constructor
  · intro hgvw
    induction hgvw with
    | refl =>
      use 0
      left
    | tail _ last ih =>
      obtain ⟨n, ihn⟩ := ih
      exact ⟨n.succ, .tail _ _ _ _ ihn last⟩
  · intro ⟨n, hgvwn⟩
    induction hgvwn with
    | refl => rfl
    | tail _ _ _ _ last ih => exact ih.trans_produces last

/--
@isnad1 id=iff.0h3v.s5.284873df3321 from=translated src=- shape=e65b7ee4 vocab=e24fe764
-/
lemma mem_language_iff_derivesIn (g : ContextFreeGrammar T) (w : List T) :
    w ∈ g.language ↔
      ∃ n, g.DerivesIn [Symbol.nonterminal g.initial] (w.map Symbol.terminal) n := by
  rw [mem_language_iff, derives_iff_derivesIn]

variable {g : ContextFreeGrammar T}

/--
@isnad1 id=derivesi.0h3v.s4.5ca3a4bc9659 from=translated src=- shape=13db0486 vocab=7ff560dd
-/
lemma DerivesIn.zero_steps (w : List (Symbol T g.NT)) : g.DerivesIn w w 0 := by left

/--
@isnad1 id=derivesi.1h4v.s5.bbbf1e24a904 from=translated src=- shape=69ddac46 vocab=087e2d32
-/
lemma Produces.single_step {v w : List (Symbol T g.NT)} (hvw : g.Produces v w) :
    g.DerivesIn v w 1 := .tail _ _ _ _ (.refl v) hvw

variable {n : ℕ}

/--
@isnad1 id=derivesi.2h6v.s5.5de7357d400c from=translated src=- shape=eec93e65 vocab=c95f4f8a
-/
lemma DerivesIn.trans_produces {u v w : List (Symbol T g.NT)}
    (huv : g.DerivesIn u v n) (hvw : g.Produces v w) :
    g.DerivesIn u w n.succ := DerivesIn.tail u v w n huv hvw

/--
@isnad1 id=derivesi.2h7v.s5.ff571150e0b1 from=translated src=- shape=b9ff49af vocab=b0bcb136
-/
@[trans]
lemma DerivesIn.trans {u v w : List (Symbol T g.NT)} {m : ℕ}
    (huv : g.DerivesIn u v n) (hvw : g.DerivesIn v w m) :
    g.DerivesIn u w (n + m) := by
  induction hvw with
  | refl => exact huv
  | tail _ _ _ _ last ih => exact trans_produces ih last

/--
@isnad1 id=derivesi.2h6v.s5.2577bfc9877e from=translated src=- shape=281a9b31 vocab=c95f4f8a
-/
lemma Produces.trans_derivesIn {u v w : List (Symbol T g.NT)}
    (huv : g.Produces u v) (hvw : g.DerivesIn v w n) :
    g.DerivesIn u w n.succ := n.succ_eq_one_add ▸ huv.single_step.trans hvw

/--
@isnad1 id=ex.1h5v.s5.8e0935f6c342 from=translated src=- shape=fc54c83c vocab=c95f4f8a
-/
lemma DerivesIn.tail_of_succ {u w : List (Symbol T g.NT)} (huw : g.DerivesIn u w n.succ) :
    ∃ v : List (Symbol T g.NT), g.DerivesIn u v n ∧ g.Produces v w := by
  cases huw with
  | tail v w n huv hvw =>
    use v

/--
@isnad1 id=ex.1h5v.s5.a1343c3a5ae1 from=translated src=- shape=3b09ba89 vocab=c95f4f8a
-/
lemma DerivesIn.head_of_succ {u w : List (Symbol T g.NT)} (huw : g.DerivesIn u w n.succ) :
    ∃ v : List (Symbol T g.NT), g.Produces u v ∧ g.DerivesIn v w n := by
  induction n generalizing w with
  | zero =>
    cases huw with
    | tail v w n huv hvw =>
      cases huv with
      | refl => exact ⟨w, hvw, zero_steps w⟩
  | succ m ih =>
    cases huw with
    | tail v w n huv hvw =>
      obtain ⟨x, hux, hxv⟩ := ih huv
      exact ⟨x, hux, hxv.trans_produces hvw⟩

/-- Add extra prefix to context-free deriving (number of steps unchanged).
@isnad1 id=derivesi.1h6v.s6.cb4e4694041d from=translated src=- shape=e54743c9 vocab=d654da64
-/
lemma DerivesIn.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.DerivesIn v w n) (p : List (Symbol T g.NT)) :
    g.DerivesIn (p ++ v) (p ++ w) n := by
  induction hvw with
  | refl => left
  | tail _ _ _ _ last ih => exact ih.trans_produces <| last.append_left p

/-- Add extra postfix to context-free deriving (number of steps unchanged).
@isnad1 id=derivesi.1h6v.s6.5a80cc9299d3 from=translated src=- shape=ac3566ed vocab=d654da64
-/
lemma DerivesIn.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.DerivesIn v w n) (p : List (Symbol T g.NT)) :
    g.DerivesIn (v ++ p) (w ++ p) n := by
  induction hvw with
  | refl => left
  | tail _ _ _ _ last ih => exact ih.trans_produces <| last.append_right p

/--
@isnad1 id=ex.1h6v.s7.af9545dade52 from=translated src=- shape=ce34ebd0 vocab=a2a11eb4
-/
lemma DerivesIn.append_split {p q w : List (Symbol T g.NT)} {n : ℕ}
    (hpqw : g.DerivesIn (p ++ q) w n) :
    ∃ x y m₁ m₂,
      w = x ++ y ∧ g.DerivesIn p x m₁ ∧ g.DerivesIn q y m₂ ∧ n = m₁ + m₂ := by
  cases n with
  | zero =>
    cases hpqw
    exact ⟨p, q, 0, 0, rfl, DerivesIn.refl p, DerivesIn.refl q, rfl⟩
  | succ n =>
    obtain ⟨v, hp, hd⟩ := hpqw.head_of_succ
    obtain ⟨r, hrg, hr⟩ := hp
    obtain ⟨p', q', heq, hv⟩ := hr.exists_parts
    rw [List.append_assoc, List.singleton_append] at heq
    have append_eq_append_cons {p q x y : List (Symbol T g.NT)} {v : Symbol T g.NT}
        (hpqxvy : p ++ q = x ++ v :: y) :
        (∃ w, y = w ++ q ∧ p = x ++ v :: w) ∨ (∃ w, x = p ++ w ∧ q = w ++ v :: y) := by
      rw [List.append_eq_append_iff] at hpqxvy
      cases hpqxvy with
      | inl hxq =>
        simp_all
      | inr hpy =>
        obtain ⟨a, rfl, hq⟩ := hpy
        cases a with
        | nil =>
          simp_all
        | cons d l =>
          simp_all
    rcases append_eq_append_cons heq with ⟨a, hq', hp⟩ | ⟨a, hp', hq⟩
    · rw [hv, hq', ← List.append_assoc] at hd
      obtain ⟨x, y, m₁, m₂, hw, hd₁, hd₂, hn⟩ := hd.append_split
      refine ⟨x, y, m₁ + 1, m₂, hw, ?_, hd₂, by omega⟩
      refine Produces.trans_derivesIn ⟨r, hrg, ?_⟩ hd₁
      rw [hp, ← List.singleton_append, ← List.append_assoc]
      apply r.rewrites_of_exists_parts
    · rw [hv, hp', List.append_assoc, List.append_assoc] at hd
      obtain ⟨x, y, m₁, m₂, hw, hd₁, hd₂, hn⟩ := hd.append_split
      refine ⟨x, y, m₁, m₂ + 1, hw, hd₁, ?_, by omega⟩
      apply Produces.trans_derivesIn
      · refine ⟨r, hrg, ?_⟩
        rw [hq, ← List.singleton_append, ← List.append_assoc]
        apply r.rewrites_of_exists_parts
      · rwa [List.append_assoc]

/--
@isnad1 id=ex.1h7v.s8.c4c3f053037a from=translated src=- shape=ab195eb7 vocab=a2a11eb4
-/
lemma DerivesIn.three_split {p q r w : List (Symbol T g.NT)} {n : ℕ}
    (hg : g.DerivesIn (p ++ q ++ r) w n) :
  ∃ x y z m₁ m₂ m₃, w = x ++ y ++ z ∧ g.DerivesIn p x m₁ ∧ g.DerivesIn q y m₂
    ∧ g.DerivesIn r z m₃ ∧ n = m₁ + m₂ + m₃ := by
  obtain ⟨x', z, m₁', m₃, hw₂, hd₁', hd₃, hn₂⟩ := hg.append_split
  obtain ⟨x, y, m₁, m₂, hw₁, hd₁, hd₂, hn₁⟩ := hd₁'.append_split
  exact ⟨x, y, z, m₁, m₂, m₃, hw₁ ▸ hw₂, hd₁, hd₂, hd₃, hn₁ ▸ hn₂⟩

/--
@isnad1 id=var.1h8v.s6.79e56a6ce187 from=translated src=- shape=8735b07e vocab=b930e82d
-/
@[elab_as_elim]
lemma DerivesIn.head_induction_on {b : List (Symbol T g.NT)}
    {P : ∀ n : ℕ, ∀ a : List (Symbol T g.NT), g.DerivesIn a b n → Prop}
    (refl : P 0 b (DerivesIn.zero_steps b))
    (head : ∀ {n a c} (hac : g.Produces a c) (hcb : g.DerivesIn c b n),
      P n c hcb → P n.succ a (hac.trans_derivesIn hcb))
    {a : List (Symbol T g.NT)} (hab : g.DerivesIn a b n) :
    P n a hab := by
  induction hab with
  | refl => exact refl
  | tail _ _ _ _ last ih =>
    apply ih
    · exact head last _ refl
    · intro _ _ _ produc deriv
      exact head produc (deriv.tail _ _ _ _ last)

end ContextFreeGrammar

end derivesIn
