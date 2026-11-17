import Tengoku.StringDiagramsLean.StringDiagrams.Examples.TemperleyLieb.Representation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dyck sequences and crossingless matchings

Combinatorics for J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
proof of Theorem A.2.

A crossingless (non-crossing) perfect matching of `N` points on a line is encoded by its
*Dyck sequence*: writing `+1` under the left end and `-1` under the right end of every arc
gives a sequence `(s_1, …, s_N)` with all partial sums `≥ 0` and total sum `0`, and the
matching is recovered uniquely (the right end of the arc starting at `k` is the first position
after `k` where the partial sum returns to its value before `k`). We write a Dyck sequence as
a word over `Fin 2`, the letter `0` standing for `+1` (the basis vector `v₁` of Lemma A.1) and
the letter `1` for `-1` (the basis vector `v₋₁`); `IsDyck w` is the Dyck condition, with
partial sums `bal`.

## Tracking arcs through cups and caps

For a crossingless matching `w` of the points on the top boundary of a diagram,

* adding a cup at position `i` inserts an arc between the new points `i`, `i + 1`: the new
  sequence is `ins i 0 1 w` (inserting an adjacent pair `+1, -1` does not change the other
  arcs);
* adding a cap at position `i` joins the points `i` and `i + 1` (`capT i w`): if they form an
  arc (`w_i w_{i+1} = +1 -1`) a closed loop is removed (`loopT i w`); otherwise the two arcs
  ending at `i` and `i + 1` are merged into one arc joining their other ends. In the sequence,
  the letters at `i`, `i + 1` are deleted, and, when both are left ends (resp. both right
  ends), the right end `closer w (i + 1)` of the inner arc becomes a left end (resp. the left
  end `opener w i` of the inner arc becomes a right end).

`capT` commutes with the insertion of an arc away from the cap (`capT_ins_right`,
`capT_ins_left`), and is computed explicitly near the first adjacent pair of a Dyck sequence
(`capT_rep_self`, `capT_rep_succ`, `capT_rep_pred`). The *first adjacent pair* `firstPair w`
is the position of the first factor `+1 -1`; a non-empty Dyck sequence has the form
`+1^{p+1} -1 ⋯` with `p = firstPair w` (`dyck_decomp`).

## The dominance order

`dle t w` (`t ≤ w`) means `bal (t.take k) ≤ bal (w.take k)` for all `k`; it is antisymmetric on
words of the same length (`dle_antisymm`) and compatible with inserting `ins p a b` against
`ins p 0 1` for `(a, b) ∈ {(0, 1), (1, 0)}` (`dle_ins`). This is the partial order of the proof
of Theorem A.2.
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open TemperleyLieb.Rep (ins del length_ins length_del getD_ins_lt getD_ins_self getD_ins_succ
  getD_ins_ge getD_del_lt getD_del_ge del_ins del_succ_ins del_ins_succ ins_ins del_del
  del_ins_far del_ins_far')

/-! ## Partial sums -/

/-- The value `+1` of the letter `0` and `-1` of the letter `1`.-/
def step (a : Fin 2) : ℤ := if a = 0 then 1 else -1

/--
@isnad1 id=eq.0h0v.s4.a368f3056156 from=translated src=- shape=012516b9 vocab=469a212e
-/
@[simp] theorem step_zero : step 0 = 1 := rfl
/--
@isnad1 id=eq.0h0v.s4.26e8b488e8d6 from=translated src=- shape=f05c4898 vocab=a771fb6f
-/
@[simp] theorem step_one : step 1 = -1 := rfl

/--
@isnad1 id=le.0h1v.s4.a2ad723c776a from=translated src=- shape=9a4b31c0 vocab=200fa49d
-/
theorem step_le_one (a : Fin 2) : step a ≤ 1 := by fin_cases a <;> simp

/-- The sum of the values of the letters of a word.-/
def bal : List (Fin 2) → ℤ
  | [] => 0
  | a :: w => step a + bal w

/--
@isnad1 id=eq.0h0v.s3.5517491de637 from=translated src=- shape=e5f64c51 vocab=47865d32
-/
@[simp] theorem bal_nil : bal [] = 0 := rfl
/--
@isnad1 id=eq.0h2v.s5.ce80e13f6ec5 from=translated src=- shape=37ec8678 vocab=b39f6382
-/
@[simp] theorem bal_cons (a : Fin 2) (w : List (Fin 2)) : bal (a :: w) = step a + bal w := rfl

/--
@isnad1 id=eq.0h2v.s6.31276e70eb8f from=translated src=- shape=155616fe vocab=5bb4e387
-/
@[simp] theorem bal_append (u v : List (Fin 2)) : bal (u ++ v) = bal u + bal v := by
  induction u with
  | nil => simp
  | cons a u ih => simp [ih, add_assoc]

/--
@isnad1 id=eq.0h1v.s5.dbb6da7eae68 from=translated src=- shape=ae6b078e vocab=ae9b548b
-/
@[simp] theorem bal_replicate_zero (n : ℕ) : bal (List.replicate n 0) = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]; ring

/--
@isnad1 id=eq.1h2v.s6.f903640bcf54 from=translated src=- shape=e09a08b3 vocab=8a23ef6b
-/
theorem bal_take_succ {k : ℕ} {w : List (Fin 2)} (h : k < w.length) :
    bal (w.take (k + 1)) = bal (w.take k) + step (w.getD k 0) := by
  induction k generalizing w with
  | zero => cases w with
    | nil => simp at h
    | cons a w => simp
  | succ k ih => cases w with
    | nil => simp at h
    | cons a w =>
      simp only [List.take_succ_cons, bal_cons, List.getD_cons_succ]
      rw [ih (by simp at h; omega)]; ring

/-- Partial sums of a word with an inserted pair of letters.
@isnad1 id=eq.1h5v.s7.1fc8d478849c from=translated src=- shape=fefd2622 vocab=78725494
-/
theorem bal_take_ins (i k : ℕ) (a b : Fin 2) {x : List (Fin 2)} (hi : i ≤ x.length) :
    bal ((ins i a b x).take k) =
      if k ≤ i then bal (x.take k) else if k = i + 1 then bal (x.take i) + step a
      else bal (x.take (k - 2)) + step a + step b := by
  induction i generalizing k x with
  | zero =>
    rcases k with _ | _ | k
    · simp
    · simp [ins]
    · simp [ins]; ring
  | succ i ih => cases x with
    | nil => simp at hi
    | cons c x =>
      rcases k with _ | k
      · simp
      · simp only [ins, List.take_succ_cons, bal_cons]
        rw [ih k (by simp at hi; omega)]
        by_cases h1 : k ≤ i
        · simp [h1, show k + 1 ≤ i + 1 by omega]
        · by_cases h2 : k = i + 1
          · subst h2; simp; ring
          · simp only [h1, h2, ite_false, show ¬(k + 1 ≤ i + 1) by omega,
              show ¬(k + 1 = i + 1 + 1) by omega]
            obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
            simp only [show k + 2 + 1 - 2 = k + 1 by omega, show k + 2 - 2 = k by omega,
              List.take_succ_cons, bal_cons]
            ring

/--
@isnad1 id=eq.1h4v.s6.11528483f5a8 from=translated src=- shape=f64bb357 vocab=a3cf2b67
-/
theorem bal_ins (i : ℕ) (a b : Fin 2) {x : List (Fin 2)} (hi : i ≤ x.length) :
    bal (ins i a b x) = bal x + step a + step b := by
  have := bal_take_ins i (x.length + 2) a b hi
  rw [List.take_of_length_le (by simp)] at this
  rw [this, ite_eq_right (by omega), ite_eq_right (by omega),
    show x.length + 2 - 2 = x.length by omega,
    List.take_length]

/-! ## Dyck sequences -/

/-- The Dyck condition: all partial sums are `≥ 0` and the total sum is `0`.-/
def IsDyck (w : List (Fin 2)) : Prop := (∀ k, 0 ≤ bal (w.take k)) ∧ bal w = 0

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=iff.0h1v.s6.562ab740aec8 from=translated src=- shape=1e445abb vocab=f0f902ae
-/
theorem isDyck_iff (w : List (Fin 2)) :
    IsDyck w ↔ (∀ k ∈ Finset.range (w.length + 1), 0 ≤ bal (w.take k)) ∧ bal w = 0 := by
  refine ⟨fun h => ⟨fun k _ => h.1 k, h.2⟩, fun h => ⟨fun k => ?_, h.2⟩⟩
  rcases le_or_gt k w.length with hk | hk
  · exact h.1 k (Finset.mem_range.mpr (by omega))
  · rw [List.take_of_length_le hk.le, h.2]

instance (w : List (Fin 2)) : Decidable (IsDyck w) := decidable_of_iff _ (isDyck_iff w).symm

/--
@isnad1 id=isdyck.0h0v.s3.831b8df54bc7 from=translated src=- shape=f4d8664b vocab=39cedb28
-/
theorem isDyck_nil : IsDyck [] := ⟨fun k => by simp, rfl⟩

/-- Inserting an adjacent pair `+1, -1` preserves the Dyck condition.
@isnad1 id=isdyck.2h2v.s5.80b58b844e35 from=translated src=- shape=248bd327 vocab=e9467b14
-/
theorem IsDyck.ins_pair {w : List (Fin 2)} (hw : IsDyck w) {i : ℕ} (hi : i ≤ w.length) :
    IsDyck (ins i 0 1 w) := by
  refine ⟨fun k => ?_, by rw [bal_ins _ _ _ hi, hw.2]; simp⟩
  rw [bal_take_ins i k 0 1 hi]
  split_ifs
  · exact hw.1 k
  · have := hw.1 i; simp; omega
  · have := hw.1 (k - 2); simp; omega

/-- The word `ins p a b x` with `a b` read off at `p`.
@isnad1 id=eq.1h2v.s6.c5456862e7e0 from=translated src=- shape=20c82da8 vocab=c6dee16a
-/
theorem ins_getD_del {p : ℕ} {w : List (Fin 2)} (h : p + 2 ≤ w.length) :
    ins p (w.getD p 0) (w.getD (p + 1) 0) (del p w) = w := by
  induction p generalizing w with
  | zero =>
    obtain ⟨x, y, w, rfl⟩ : ∃ x y w', w = x :: y :: w' := by
      rcases w with _ | ⟨x, _ | ⟨y, w'⟩⟩
      · simp at h
      · simp at h
      · exact ⟨x, y, w', rfl⟩
    simp [ins, del]
  | succ p ih => cases w with
    | nil => simp at h
    | cons x w =>
      simp only [List.getD_cons_succ, del, ins]
      rw [ih (by simp at h; omega)]

/-- Deleting an adjacent pair `+1, -1` preserves the Dyck condition.
@isnad1 id=isdyck.4h2v.s7.f417f149e80f from=translated src=- shape=59ea0ed5 vocab=ac3a6b44
-/
theorem IsDyck.del_pair {w : List (Fin 2)} (hw : IsDyck w) {p : ℕ} (hp : p + 2 ≤ w.length)
    (h0 : w.getD p 0 = 0) (h1 : w.getD (p + 1) 0 = 1) : IsDyck (del p w) := by
  have e := ins_getD_del hp
  rw [h0, h1] at e
  have hl : p ≤ (del p w).length := by have := length_del hp; omega
  refine ⟨fun k => ?_, ?_⟩
  · have := hw.1 (if k ≤ p then k else k + 2)
    rw [← e, bal_take_ins p _ 0 1 hl] at this
    split_ifs at this with h₁ h₂ h₃
    · exact this
    · omega
    · omega
    · simpa using this
  · have := hw.2
    rw [← e, bal_ins _ _ _ hl] at this
    simpa using this

/--
@isnad1 id=eq.0h1v.s6.90bd1baa21ab from=translated src=- shape=65e1fb79 vocab=cd576379
-/
theorem length_eq_bal (w : List (Fin 2)) : (w.length : ℤ) = bal w + 2 * (w.count 1) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    · simp [ih]; ring
    · simp [ih]; ring

/--
@isnad1 id=even.1h1v.s4.d65ccca9e45d from=translated src=- shape=520b9233 vocab=06e8e233
-/
theorem IsDyck.length_even {w : List (Fin 2)} (hw : IsDyck w) : Even w.length := by
  have := length_eq_bal w
  rw [hw.2, zero_add] at this
  exact ⟨w.count 1, by omega⟩

/-! ## The first adjacent pair -/

/-- The position of the first factor `0 1` (i.e. `+1 -1`) of a word.-/
def firstPair : List (Fin 2) → ℕ
  | a :: b :: w => if a = 0 ∧ b = 1 then 0 else firstPair (b :: w) + 1
  | _ => 0

/--
@isnad1 id=eq.0h2v.s6.a715ffbdbd69 from=translated src=- shape=14f2fdb9 vocab=5f1a5d48
-/
theorem firstPair_rep (j : ℕ) (r : List (Fin 2)) :
    firstPair (List.replicate j 0 ++ 0 :: 1 :: r) = j := by
  induction j with
  | zero => simp [firstPair]
  | succ j ih =>
    rw [List.replicate_succ, List.cons_append]
    cases j with
    | zero => simp [firstPair]
    | succ j =>
      rw [List.replicate_succ, List.cons_append] at ih ⊢
      simp only [firstPair] at ih ⊢
      simp [ih]

/--
@isnad1 id=ex.2h1v.s7.81caa480c22a from=translated src=- shape=344e2fec vocab=40fd9af0
-/
theorem decomp_of_head {w : List (Fin 2)} (h0 : w.head? = some 0) (h1 : (1 : Fin 2) ∈ w) :
    ∃ r, w = List.replicate (firstPair w) 0 ++ 0 :: 1 :: r := by
  induction w with
  | nil => simp at h0
  | cons a w ih =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    cases w with
    | nil => simp at h1
    | cons b w =>
      obtain rfl | rfl : b = 0 ∨ b = 1 := by fin_cases b <;> simp
      · have ⟨r, hr⟩ := ih rfl (by simpa using h1)
        refine ⟨r, ?_⟩
        simp only [firstPair]
        rw [ite_eq_right (by decide), List.replicate_succ, List.cons_append, ← hr]
      · exact ⟨w, by simp [firstPair]⟩

/-- A non-empty Dyck sequence is `+1^{p+1} -1 ⋯` with `p = firstPair w`.
@isnad1 id=ex.2h1v.s7.45ca754e3cf1 from=translated src=- shape=2a2794f2 vocab=be1883ad
-/
theorem dyck_decomp {w : List (Fin 2)} (hw : IsDyck w) (hne : w ≠ []) :
    ∃ r, w = List.replicate (firstPair w) 0 ++ 0 :: 1 :: r := by
  obtain ⟨a, w', rfl⟩ := List.exists_cons_of_ne_nil hne
  have ha : a = 0 := by
    have := hw.1 1
    fin_cases a
    · rfl
    · simp at this
  subst ha
  refine decomp_of_head rfl ?_
  by_contra h
  have : ∀ w : List (Fin 2), (1 : Fin 2) ∉ w → bal w = w.length := by
    intro w hw'
    induction w with
    | nil => simp
    | cons b w ih =>
      have hb : b = 0 := by
        fin_cases b
        · rfl
        · simp at hw'
      subst hb
      simp only [List.mem_cons, not_or] at hw'
      simp [ih hw'.2]; ring
  have := this _ h
  rw [hw.2] at this
  simp at this
  omega

/-! ## List lemmas for `ins`, `take`, `drop`, `set`, `reverse` -/

/--
@isnad1 id=eq.0h5v.s7.c5b0fd19f5a6 from=translated src=- shape=e59e1b85 vocab=805230d2
-/
theorem ins_rep (j : ℕ) (c a b : Fin 2) (r : List (Fin 2)) :
    ins j a b (List.replicate j c ++ r) = List.replicate j c ++ a :: b :: r := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, ins, ih]

/--
@isnad1 id=eq.0h5v.s7.dfc37b714667 from=translated src=- shape=37122c2d vocab=14242c50
-/
theorem del_rep (j : ℕ) (c a b : Fin 2) (r : List (Fin 2)) :
    del j (List.replicate j c ++ a :: b :: r) = List.replicate j c ++ r := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, del, ih]

/--
@isnad1 id=eq.1h4v.s6.64e25b48045f from=translated src=- shape=5e9cea94 vocab=f766481f
-/
theorem getD_rep_lt {j i : ℕ} (h : i < j) (c : Fin 2) (r : List (Fin 2)) :
    (List.replicate j c ++ r).getD i 0 = c := by
  induction j generalizing i with
  | zero => omega
  | succ j ih => cases i with
    | zero => simp [List.replicate_succ]
    | succ i => simp only [List.replicate_succ, List.cons_append, List.getD_cons_succ]
                exact ih (by omega)

/--
@isnad1 id=eq.0h4v.s7.6f6078cac96a from=translated src=- shape=72e39f65 vocab=c1db6b86
-/
theorem getD_rep_add (j k : ℕ) (c : Fin 2) (r : List (Fin 2)) :
    (List.replicate j c ++ r).getD (j + k) 0 = r.getD k 0 := by
  induction j with
  | zero => simp
  | succ j ih => simp only [List.replicate_succ, List.cons_append,
      show j + 1 + k = (j + k) + 1 by omega, List.getD_cons_succ, ih]

/--
@isnad1 id=eq.0h5v.s7.ae76df8585f6 from=translated src=- shape=c70c03bc vocab=2d825694
-/
theorem set_rep (j : ℕ) (c a b : Fin 2) (r : List (Fin 2)) :
    (List.replicate j c ++ a :: r).set j b = List.replicate j c ++ b :: r := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, ih]

/--
@isnad1 id=eq.0h3v.s6.d198787a0974 from=translated src=- shape=74cbd819 vocab=e057c28f
-/
theorem drop_rep (j : ℕ) (c : Fin 2) (r : List (Fin 2)) :
    (List.replicate j c ++ r).drop j = r := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, ih]

/--
@isnad1 id=eq.0h3v.s6.c7abe3350919 from=translated src=- shape=11ad5937 vocab=0684a35f
-/
theorem take_rep (j : ℕ) (c : Fin 2) (r : List (Fin 2)) :
    (List.replicate j c ++ r).take j = List.replicate j c := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, ih]

/--
@isnad1 id=eq.2h5v.s6.9e3800feb6af from=translated src=- shape=4b33ae52 vocab=3d07e9d9
-/
theorem drop_ins_le {k p : ℕ} (a b : Fin 2) {w : List (Fin 2)} (hk : k ≤ p) (hp : p ≤ w.length) :
    (ins p a b w).drop k = ins (p - k) a b (w.drop k) := by
  induction k generalizing p w with
  | zero => rfl
  | succ k ih => cases w with
    | nil => simp at hp; omega
    | cons x w =>
      obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      simp only [ins, List.drop_succ_cons, show p + 1 - (k + 1) = p - k by omega]
      exact ih (by omega) (by simp at hp; omega)

/--
@isnad1 id=eq.2h5v.s6.680e881b65bf from=translated src=- shape=b953952d vocab=bcaddd06
-/
theorem drop_ins_ge {k p : ℕ} (a b : Fin 2) {w : List (Fin 2)} (hk : p ≤ k) (hp : p ≤ w.length) :
    (ins p a b w).drop (k + 2) = w.drop k := by
  induction p generalizing k w with
  | zero => simp [ins]
  | succ p ih => cases w with
    | nil => simp at hp
    | cons x w =>
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [ins, show k + 1 + 2 = (k + 2) + 1 by omega, List.drop_succ_cons]
      exact ih (by omega) (by simp at hp; omega)

/--
@isnad1 id=eq.2h5v.s6.79efa67a0c9c from=translated src=- shape=a2490996 vocab=4a0b43d7
-/
theorem take_ins_le {k p : ℕ} (a b : Fin 2) {w : List (Fin 2)} (hk : k ≤ p) (hp : p ≤ w.length) :
    (ins p a b w).take k = w.take k := by
  induction k generalizing p w with
  | zero => rfl
  | succ k ih => cases w with
    | nil => simp at hp; omega
    | cons x w =>
      obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      simp only [ins, List.take_succ_cons]
      rw [ih (by omega) (by simp at hp; omega)]

/--
@isnad1 id=eq.2h5v.s6.84fc29c7c64b from=translated src=- shape=1d5ca7f7 vocab=a05ab99c
-/
theorem take_ins_ge {k p : ℕ} (a b : Fin 2) {w : List (Fin 2)} (hk : p ≤ k) (hp : p ≤ w.length) :
    (ins p a b w).take (k + 2) = ins p a b (w.take k) := by
  induction p generalizing k w with
  | zero => simp [ins]
  | succ p ih => cases w with
    | nil => simp at hp
    | cons x w =>
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [ins, show k + 1 + 2 = (k + 2) + 1 by omega, List.take_succ_cons]
      rw [ih (by omega) (by simp at hp; omega)]

/--
@isnad1 id=eq.1h4v.s6.0aa7cbe4cde2 from=translated src=- shape=d221905e vocab=9d00c81f
-/
theorem ins_eq_append {p : ℕ} (a b : Fin 2) {w : List (Fin 2)} (hp : p ≤ w.length) :
    ins p a b w = w.take p ++ a :: b :: w.drop p := by
  induction p generalizing w with
  | zero => rfl
  | succ p ih => cases w with
    | nil => simp at hp
    | cons x w => simp only [ins, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
                  rw [ih (by simp at hp; omega)]

/--
@isnad1 id=eq.1h4v.s6.c8eada2deebd from=translated src=- shape=f0617b2f vocab=fac0445c
-/
theorem reverse_ins {p : ℕ} (a b : Fin 2) {w : List (Fin 2)} (hp : p ≤ w.length) :
    (ins p a b w).reverse = ins (w.length - p) b a w.reverse := by
  rw [ins_eq_append _ _ hp, ins_eq_append _ _ (by simp)]
  simp only [List.reverse_append, List.reverse_cons, List.append_assoc,
    List.cons_append]
  rw [List.reverse_take, List.reverse_drop]
  simp

/--
@isnad1 id=eq.0h5v.s6.7196a4acd5d6 from=translated src=- shape=219b334c vocab=1b6addfa
-/
theorem map_ins (f : Fin 2 → Fin 2) (p : ℕ) (a b : Fin 2) (w : List (Fin 2)) :
    (ins p a b w).map f = ins p (f a) (f b) (w.map f) := by
  induction p generalizing w with
  | zero => rfl
  | succ p ih => cases w with
    | nil => rfl
    | cons x w => simp [ins, ih]

/--
@isnad1 id=eq.2h6v.s6.02c4ccc15260 from=translated src=- shape=1b6238b7 vocab=19440068
-/
theorem set_ins_lt {y p : ℕ} (a b c : Fin 2) {w : List (Fin 2)} (hy : y < p) (hp : p ≤ w.length) :
    (ins p a b w).set y c = ins p a b (w.set y c) := by
  induction p generalizing y w with
  | zero => omega
  | succ p ih => cases w with
    | nil => simp at hp
    | cons x w => cases y with
      | zero => simp [ins]
      | succ y => simp only [ins, List.set_cons_succ]
                  rw [ih (by omega) (by simp at hp; omega)]

/--
@isnad1 id=eq.2h6v.s6.196752b8747a from=translated src=- shape=642720ad vocab=2216a0a1
-/
theorem set_ins_ge {y p : ℕ} (a b c : Fin 2) {w : List (Fin 2)} (hy : p ≤ y) (hp : p ≤ w.length) :
    (ins p a b w).set (y + 2) c = ins p a b (w.set y c) := by
  induction p generalizing y w with
  | zero => simp [ins]
  | succ p ih => cases w with
    | nil => simp at hp
    | cons x w =>
      obtain ⟨y, rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
      simp only [ins, show y + 1 + 2 = (y + 2) + 1 by omega, List.set_cons_succ]
      rw [ih (by omega) (by simp at hp; omega)]

/--
@isnad1 id=eq.0h3v.s5.6b9af957291c from=translated src=- shape=a411de27 vocab=14319f4e
-/
theorem length_set' (w : List (Fin 2)) (y : ℕ) (c : Fin 2) : (w.set y c).length = w.length :=
  List.length_set

/-! ## Arcs: partners of left and right ends -/

/-- Scanning a word from depth `d`, the index at which the depth first drops below `0`
(the length of the word if it never does).-/
def fwd : ℕ → List (Fin 2) → ℕ
  | _, [] => 0
  | d, a :: w => if a = 0 then fwd (d + 1) w + 1 else
      match d with
      | 0 => 0
      | d + 1 => fwd d w + 1

/--
@isnad1 id=eq.0h2v.s6.5a07e830f4cb from=translated src=- shape=7cd14d36 vocab=5c4ed75a
-/
theorem fwd_cons_zero (d : ℕ) (w : List (Fin 2)) : fwd d (0 :: w) = fwd (d + 1) w + 1 := by
  simp [fwd]

/--
@isnad1 id=eq.0h1v.s5.07204fe7b616 from=translated src=- shape=33ed1ece vocab=6a5cd85b
-/
theorem fwd_cons_one_zero (w : List (Fin 2)) : fwd 0 (1 :: w) = 0 := by simp [fwd]

/--
@isnad1 id=eq.0h2v.s6.d3c48bd9861c from=translated src=- shape=066f470e vocab=5c4ed75a
-/
theorem fwd_cons_one_succ (d : ℕ) (w : List (Fin 2)) : fwd (d + 1) (1 :: w) = fwd d w + 1 := by
  simp [fwd]

/-- Inserting a balanced pair `+1 -1` shifts the result of the scan past the insertion.
@isnad1 id=eq.1h3v.s6.bb23e68e8208 from=translated src=- shape=b0920c49 vocab=4958d237
-/
theorem fwd_ins (d : ℕ) {k : ℕ} {v : List (Fin 2)} (hk : k ≤ v.length) :
    fwd d (ins k 0 1 v) = if fwd d v < k then fwd d v else fwd d v + 2 := by
  induction v generalizing d k with
  | nil =>
    obtain rfl : k = 0 := by simpa using hk
    simp [ins, fwd_cons_zero, fwd]
  | cons x v ih =>
    rcases k with _ | k
    · simp [ins, fwd_cons_zero, fwd_cons_one_succ]
    · simp only [ins]
      fin_cases x
      · simp only [Fin.zero_eta, fwd_cons_zero]
        rw [ih (d + 1) (by simp at hk; omega)]
        split_ifs <;> omega
      · rcases d with _ | d
        · simp [fwd_cons_one_zero]
        · simp only [Fin.mk_one, fwd_cons_one_succ]
          rw [ih d (by simp at hk; omega)]
          split_ifs <;> omega

/--
@isnad1 id=le.0h2v.s4.a2ab1b824f1e from=translated src=- shape=2ca6dfa9 vocab=133fad25
-/
theorem fwd_le_length (d : ℕ) (v : List (Fin 2)) : fwd d v ≤ v.length := by
  induction v generalizing d with
  | nil => simp [fwd]
  | cons x v ih =>
    fin_cases x
    · simp only [Fin.zero_eta, fwd_cons_zero, List.length_cons]; have := ih (d + 1); omega
    · rcases d with _ | d
      · simp [fwd_cons_one_zero]
      · simp only [Fin.mk_one, fwd_cons_one_succ, List.length_cons]; have := ih d; omega

/-- If the total sum is below `-d`, the scan from depth `d` stops inside the word.
@isnad1 id=lt.1h2v.s5.91b7a27b35a9 from=translated src=- shape=6de5583f vocab=bb07a282
-/
theorem fwd_lt_length {d : ℕ} {v : List (Fin 2)} (h : bal v < -(d : ℤ)) : fwd d v < v.length := by
  induction v generalizing d with
  | nil => simp at h; omega
  | cons x v ih =>
    fin_cases x
    · simp only [Fin.zero_eta, fwd_cons_zero, List.length_cons]
      have := ih (d := d + 1) (by simp at h; push_cast; omega); omega
    · rcases d with _ | d
      · simp [fwd_cons_one_zero]
      · simp only [Fin.mk_one, fwd_cons_one_succ, List.length_cons]
        have := ih (d := d) (by simp at h; omega); omega

/-- The right end of the arc whose left end is at `x`.-/
def closer (w : List (Fin 2)) (x : ℕ) : ℕ := x + 1 + fwd 0 (w.drop (x + 1))

/-- The prefix of length `y`, read backwards with `+1` and `-1` exchanged.-/
def bwdList (w : List (Fin 2)) (y : ℕ) : List (Fin 2) := ((w.take y).reverse).map (· + 1)

/-- The left end of the arc whose right end is at `y`.-/
def opener (w : List (Fin 2)) (y : ℕ) : ℕ := y - 1 - fwd 0 (bwdList w y)

/-- The effect of a cap at position `i` on the Dyck sequence of the top boundary.-/
def capT (i : ℕ) (w : List (Fin 2)) : List (Fin 2) :=
  if w.getD i 0 = 0 ∧ w.getD (i + 1) 0 = 0 then (del i w).set (closer w (i + 1) - 2) 0
  else if w.getD i 0 = 1 ∧ w.getD (i + 1) 0 = 1 then (del i w).set (opener w i) 1
  else del i w

/-- A cap at position `i` closes a loop exactly when the points `i`, `i + 1` form an arc.-/
def loopT (i : ℕ) (w : List (Fin 2)) : Bool := w.getD i 0 = 0 ∧ w.getD (i + 1) 0 = 1

/--
@isnad1 id=eq.1h2v.s6.dc2b03028a93 from=translated src=- shape=d987dc62 vocab=c95fd647
-/
theorem length_capT {i : ℕ} {w : List (Fin 2)} (h : i + 2 ≤ w.length) :
    (capT i w).length + 2 = w.length := by
  have := length_del h
  unfold capT
  split_ifs <;> simp [List.length_set, this]

/-! ## `capT` and insertions away from the cap -/

/--
@isnad1 id=eq.2h5v.s6.bee8a2584fb5 from=translated src=- shape=6c6f9490 vocab=80b7062a
-/
theorem getD_ins_lt' {p q : ℕ} (a b : Fin 2) {w : List (Fin 2)} (hq : q < p) (hp : p ≤ w.length) :
    (ins p a b w).getD q 0 = w.getD q 0 := getD_ins_lt a b hq hp

/-- The left end of the arc ending at a right end `y` of a Dyck sequence is found.
@isnad1 id=lt.3h2v.s6.20385e4fffb7 from=translated src=- shape=3411f509 vocab=3f77adf6
-/
theorem fwd_bwdList_lt {w : List (Fin 2)} (hw : IsDyck w) {y : ℕ} (hy : y < w.length)
    (h1 : w.getD y 0 = 1) : fwd 0 (bwdList w y) < y := by
  have hb := hw.1 (y + 1)
  rw [bal_take_succ hy, h1, step_one] at hb
  have hl : (bwdList w y).length = y := by simp [bwdList]; omega
  have key : ∀ v : List (Fin 2), bal (v.reverse.map (· + 1)) = -bal v := by
    intro v
    induction v with
    | nil => simp
    | cons a v ih =>
      simp only [List.reverse_cons, List.map_append, bal_append, ih, List.map_cons,
        List.map_nil, bal_cons, bal_nil, add_zero]
      fin_cases a <;> simp [step]
  have := fwd_lt_length (d := 0) (v := bwdList w y) (by
    rw [bwdList, key]; push_cast; omega)
  omega

/-- A cap at `i` and an arc inserted at `p ≥ i + 2` commute.
@isnad1 id=and.3h3v.s7.b89e746c4445 from=translated src=- shape=e7e69576 vocab=abdb06f0
-/
theorem capT_ins_right {i p : ℕ} {w : List (Fin 2)} (hw : IsDyck w) (hip : i + 2 ≤ p)
    (hp : p ≤ w.length) :
    capT i (ins p 0 1 w) = ins (p - 2) 0 1 (capT i w) ∧ loopT i (ins p 0 1 w) = loopT i w := by
  have g0 : (ins p 0 1 w).getD i 0 = w.getD i 0 := getD_ins_lt _ _ (by omega) hp
  have g1 : (ins p 0 1 w).getD (i + 1) 0 = w.getD (i + 1) 0 := getD_ins_lt _ _ (by omega) hp
  have hd : del i (ins p 0 1 w) = ins (p - 2) 0 1 (del i w) := by
    have := del_ins_far' (p := i) (k := p - 2 - i) 0 1 (w := w) (by omega)
    rwa [show i + 2 + (p - 2 - i) = p by omega, show i + (p - 2 - i) = p - 2 by omega] at this
  have hdl : p - 2 ≤ (del i w).length := by have := length_del (p := i) (w := w) (by omega); omega
  refine ⟨?_, by unfold loopT; rw [g0, g1]⟩
  unfold capT
  rw [g0, g1, hd]
  split_ifs with h₁ h₂
  · -- two left ends: the right end of the inner arc moves
    have hc : closer (ins p 0 1 w) (i + 1) =
        if closer w (i + 1) < p then closer w (i + 1) else closer w (i + 1) + 2 := by
      unfold closer
      rw [drop_ins_le _ _ (show i + 1 + 1 ≤ p by omega) hp,
        fwd_ins 0 (by simp; omega)]
      split_ifs <;> omega
    have hc2 : i + 2 ≤ closer w (i + 1) := by unfold closer; omega
    rw [hc]
    split_ifs with h₃
    · rw [set_ins_lt _ _ _ (by omega) hdl]
    · rw [show closer w (i + 1) + 2 - 2 = (closer w (i + 1) - 2) + 2 by omega,
        set_ins_ge _ _ _ (by omega) hdl]
  · -- two right ends: the left end of the inner arc moves (it lies to the left of `i`)
    have ho : opener (ins p 0 1 w) i = opener w i := by
      unfold opener bwdList
      rw [take_ins_le _ _ (by omega) hp]
    have hf := fwd_bwdList_lt hw (y := i) (by omega) h₂.1
    rw [ho, set_ins_lt _ _ _ (by unfold opener; omega) hdl]
  · rfl

/-- A cap at `i` and an arc inserted at `p ≤ i - 2` commute (for a Dyck sequence `w`).
@isnad1 id=and.3h3v.s7.bd94917e92a7 from=translated src=- shape=57924357 vocab=d19c7360
-/
theorem capT_ins_left {i p : ℕ} {w : List (Fin 2)} (hw : IsDyck w) (hpi : p ≤ i)
    (hi : i + 2 ≤ w.length) :
    capT (i + 2) (ins p 0 1 w) = ins p 0 1 (capT i w) ∧
      loopT (i + 2) (ins p 0 1 w) = loopT i w := by
  have hp : p ≤ w.length := by omega
  have g0 : (ins p 0 1 w).getD (i + 2) 0 = w.getD i 0 := getD_ins_ge _ _ hpi hp
  have g1 : (ins p 0 1 w).getD (i + 2 + 1) 0 = w.getD (i + 1) 0 := by
    rw [show i + 2 + 1 = (i + 1) + 2 by omega]; exact getD_ins_ge _ _ (by omega) hp
  have hd : del (i + 2) (ins p 0 1 w) = ins p 0 1 (del i w) := by
    have := del_ins_far (p := p) (k := i - p) 0 1 (w := w) (by omega)
    rwa [show p + 2 + (i - p) = i + 2 by omega, show p + (i - p) = i by omega] at this
  have hdl : p ≤ (del i w).length := by have := length_del (p := i) (w := w) hi; omega
  refine ⟨?_, by unfold loopT; rw [g0, g1]⟩
  unfold capT
  rw [g0, g1, hd]
  split_ifs with h₁ h₂
  · have hc : closer (ins p 0 1 w) (i + 2 + 1) = closer w (i + 1) + 2 := by
      unfold closer
      rw [show i + 2 + 1 + 1 = (i + 1 + 1) + 2 by omega, drop_ins_ge _ _ (by omega) hp]
      simp only [show i + 1 + 1 = i + 2 from rfl]
      omega
    rw [hc, show closer w (i + 1) + 2 - 2 = (closer w (i + 1) - 2) + 2 by unfold closer; omega,
      set_ins_ge _ _ _ (by unfold closer; omega) hdl]
  · have hf := fwd_bwdList_lt hw (y := i) (by omega) h₂.1
    have hb : bwdList (ins p 0 1 w) (i + 2) = ins (i - p) 0 1 (bwdList w i) := by
      unfold bwdList
      rw [take_ins_ge _ _ hpi hp, reverse_ins _ _ (by simp; omega), map_ins]
      simp only [List.length_take, show min i w.length = i by omega]
      rfl
    have ho : opener (ins p 0 1 w) (i + 2) =
        if fwd 0 (bwdList w i) < i - p then opener w i + 2 else opener w i := by
      unfold opener
      rw [hb, fwd_ins 0 (by simp [bwdList]; omega)]
      split_ifs <;> omega
    rw [ho]
    split_ifs with h₃
    · rw [set_ins_ge _ _ _ (by unfold opener; omega) hdl]
    · rw [set_ins_lt _ _ _ (by unfold opener; omega) hdl]
  · rfl

/-! ## `capT` near the first adjacent pair -/

/-- The cap on the first adjacent pair `+1 -1` closes a loop.
@isnad1 id=and.0h2v.s8.66905097bd27 from=translated src=- shape=ec9768f3 vocab=cf5819b4
-/
theorem capT_rep_self (p : ℕ) (r : List (Fin 2)) :
    capT p (List.replicate p 0 ++ 0 :: 1 :: r) = List.replicate p 0 ++ r ∧
      loopT p (List.replicate p 0 ++ 0 :: 1 :: r) = true := by
  have g0 := getD_rep_add p 0 0 (0 :: 1 :: r)
  have g1 := getD_rep_add p 1 0 (0 :: 1 :: r)
  simp only [add_zero, List.getD_cons_zero, List.getD_cons_succ] at g0 g1
  refine ⟨?_, by unfold loopT; rw [g0, g1]; simp⟩
  simp [capT, del_rep]

/-- The cap to the right of the first adjacent pair: a zigzag.
@isnad1 id=and.0h3v.s8.7e414c05efd5 from=translated src=- shape=8032e928 vocab=511d38df
-/
theorem capT_rep_succ (p : ℕ) (c : Fin 2) (r : List (Fin 2)) :
    capT (p + 1) (List.replicate p 0 ++ 0 :: 1 :: c :: r) = List.replicate p 0 ++ c :: r ∧
      loopT (p + 1) (List.replicate p 0 ++ 0 :: 1 :: c :: r) = false := by
  have e : List.replicate p 0 ++ 0 :: 1 :: c :: r = List.replicate (p + 1) 0 ++ 1 :: c :: r := by
    simp [List.replicate_succ']
  have g0 := getD_rep_add (p + 1) 0 0 (1 :: c :: r)
  have g1 := getD_rep_add (p + 1) 1 0 (1 :: c :: r)
  simp only [add_zero, List.getD_cons_zero, List.getD_cons_succ] at g0 g1
  rw [e]
  refine ⟨?_, by unfold loopT; rw [g0, g1]; simp⟩
  unfold capT
  rw [g0, g1, del_rep]
  obtain rfl | rfl : c = 0 ∨ c = 1 := by fin_cases c <;> simp
  · simp [List.replicate_succ']
  · rw [ite_eq_right (by decide), ite_eq_left (by decide)]
    have ho : opener (List.replicate (p + 1) 0 ++ 1 :: 1 :: r) (p + 1) = p := by
      unfold opener bwdList
      rw [take_rep]
      simp only [List.reverse_replicate, List.map_replicate, zero_add]
      simp [List.replicate_succ, fwd_cons_one_zero]
    rw [ho, List.replicate_succ', List.append_assoc, List.singleton_append, set_rep]

/-- The cap to the left of the first adjacent pair: a zigzag.
@isnad1 id=and.0h2v.s8.55532e827c39 from=translated src=- shape=1b0e3746 vocab=511d38df
-/
theorem capT_rep_pred (p : ℕ) (r : List (Fin 2)) :
    capT p (List.replicate (p + 1) 0 ++ 0 :: 1 :: r) = List.replicate (p + 1) 0 ++ r ∧
      loopT p (List.replicate (p + 1) 0 ++ 0 :: 1 :: r) = false := by
  have e : List.replicate (p + 1) 0 ++ 0 :: 1 :: r = List.replicate p 0 ++ 0 :: 0 :: 1 :: r := by
    simp [List.replicate_succ']
  have g0 := getD_rep_add p 0 0 (0 :: 0 :: 1 :: r)
  have g1 := getD_rep_add p 1 0 (0 :: 0 :: 1 :: r)
  simp only [add_zero, List.getD_cons_zero, List.getD_cons_succ] at g0 g1
  rw [e]
  refine ⟨?_, by unfold loopT; rw [g0, g1]; simp⟩
  unfold capT
  rw [g0, g1, del_rep]
  simp only [and_self, ite_true]
  have hc : closer (List.replicate p 0 ++ 0 :: 0 :: 1 :: r) (p + 1) = p + 2 := by
    unfold closer
    rw [show p + 1 + 1 = p + 2 by omega, show List.replicate p (0 : Fin 2) ++ 0 :: 0 :: 1 :: r =
      List.replicate (p + 2) 0 ++ 1 :: r by simp [List.replicate_succ'], drop_rep]
    simp [fwd_cons_one_zero]
  rw [hc, show p + 2 - 2 = p by omega, set_rep, List.replicate_succ', List.append_assoc,
    List.singleton_append]

/-! ## The dominance order -/

/-- The dominance order on words: all partial sums of `t` are at most those of `w`.-/
def dle (t w : List (Fin 2)) : Prop := ∀ k, bal (t.take k) ≤ bal (w.take k)

/--
@isnad1 id=dle.0h1v.s3.bfa9fd2ed8a9 from=translated src=- shape=f9d70a60 vocab=058217fc
-/
theorem dle_refl (w : List (Fin 2)) : dle w w := fun _ => le_rfl

/--
@isnad1 id=dle.4h5v.s6.07bed9b9a0a6 from=translated src=- shape=f851b390 vocab=6b99ba31
-/
theorem dle_ins {t w : List (Fin 2)} (h : dle t w) {p : ℕ} (ht : p ≤ t.length)
    (hw : p ≤ w.length) {a b : Fin 2} (hab : step a + step b = 0) :
    dle (ins p a b t) (ins p 0 1 w) := by
  intro k
  rw [bal_take_ins p k a b ht, bal_take_ins p k 0 1 hw]
  have := step_le_one a
  split_ifs
  · exact h k
  · have := h p; simp; omega
  · have := h (k - 2); simp; omega

/--
@isnad1 id=eq.3h2v.s5.bde67e275c15 from=translated src=- shape=61fd45e0 vocab=0cea05b9
-/
theorem dle_antisymm {t w : List (Fin 2)} (h₁ : dle t w) (h₂ : dle w t)
    (hl : t.length = w.length) : t = w := by
  apply List.ext_getElem hl
  intro k hk hk'
  have e : ∀ j, bal (t.take j) = bal (w.take j) := fun j => le_antisymm (h₁ j) (h₂ j)
  have := e (k + 1)
  rw [bal_take_succ hk, bal_take_succ hk', e k] at this
  have hs : step (t.getD k 0) = step (w.getD k 0) := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some] at hs
  revert hs
  generalize t[k] = a
  generalize w[k] = b
  fin_cases a <;> fin_cases b <;> simp [step]

end StringDiagrams.OddTemperleyLieb

end
