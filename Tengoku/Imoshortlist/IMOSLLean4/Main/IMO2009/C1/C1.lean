/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku

/-!
# IMO 2009 C1

Fix non-negative integers $M$ and $n$.
Two players, $A$ and $B$, play the following game on the board.
The board consists of $M$ cards in a row, one side labelled $0$ and another side labelled $1$.

Initially, all cards are labelled $1$.
Then $A$ and $B$ take turns performing a move of the following form.
Choose an index $i ∈ ℕ$ such that $i + n < M$ and the $(i + n)^{\text{th}}$ card shows $1$.
Then flip the $j^{\text{th}}$ card for any $i ≤ j ≤ i + n$.
The last player who can make a legal move wins.

Assume that $A$ and $B$ uses the best strategy.
1. Show that the game always ends.
2. Determine the outcome of the game.
-/

@[expose] public section

namespace IMOSL
namespace IMO2009C1

open Relation Finset

/-! ### Extra lemmas -/

/--
@isnad1 id=iff.0h3v.s4.420b783c2450 from=translated src=- shape=c99e4eb7 vocab=e3b0c442
-/
theorem and_and_or_not_iff (P Q R : Prop) : (P ∧ Q) ∧ (R ∨ ¬Q) ↔ (P ∧ R) ∧ Q := by
  rw [and_assoc, and_or_left, and_not_self_iff, and_assoc, and_comm (b := Q)]
  exact and_congr Iff.rfl (or_iff_left id)

/--
@isnad1 id=eq.0h2v.s6.c27fe27618a0 from=translated src=- shape=5e21d0d8 vocab=d1ab83f7
-/
theorem Iic_filter_dvd_card (k n : ℕ) :
    ((Icc k (k + n)).filter λ i : ℕ ↦ n + 1 ∣ i + 1).card = 1 := by
  let h := (k + (n + 1)).card_multiples (n + 1)
  rwa [range_eq_Ico, ← Ico_union_Ico_eq_Ico k.zero_le le_self_add, filter_union,
    card_union_of_disjoint (disjoint_filter_filter (Ico_disjoint_Ico_consecutive 0 k _)),
    ← range_eq_Ico, Nat.card_multiples, k.add_div_right n.succ_pos,
    Nat.succ_eq_add_one, add_right_inj] at h

section symmDiff

variable [DecidableEq α] (A B : Finset α)

/--
@isnad1 id=disjoint.0h3v.s5.02c035858811 from=translated src=- shape=3dba4853 vocab=b1813512
-/
theorem disjoint_symmDiff_inter : Disjoint (symmDiff A B) (A ∩ B) :=
  disjoint_symmDiff_inf A B

/--
@isnad1 id=eq.0h3v.s5.05a9742c4489 from=translated src=- shape=34b6ad2a vocab=170f4e63
-/
theorem symmDiff_union_inter_eq_union : symmDiff A B ∪ A ∩ B = A ∪ B :=
  symmDiff_sup_inf A B

/--
@isnad1 id=eq.0h3v.s6.f19ac0f1961a from=translated src=- shape=2f57ece7 vocab=8a1430a2
-/
theorem symmDiff_card_add_two_mul_inter_card :
    (symmDiff A B).card + 2 * (A ∩ B).card = A.card + B.card := by
  rw [two_mul, ← add_assoc, ← card_union_of_disjoint (disjoint_symmDiff_inter A B),
    symmDiff_union_inter_eq_union, card_union_add_card_inter]

/--
@isnad1 id=eq.0h3v.s6.4ecb2b4d9744 from=translated src=- shape=94eda873 vocab=2aaf3678
-/
theorem symmDiff_card_mod_two : (symmDiff A B).card % 2 = (A.card + B.card) % 2 := by
  rw [← symmDiff_card_add_two_mul_inter_card, Nat.add_mul_mod_self_left]

/--
@isnad1 id=iff.1h4v.s6.f49c03da7422 from=translated src=- shape=2e7496bf vocab=2689ad13
-/
theorem mem_symmDiff_iff_mem_left {B : Finset α} (h : a ∉ B) :
    a ∈ symmDiff A B ↔ a ∈ A :=
  mem_union.trans <| (or_iff_left (notMem_sdiff_of_notMem_left h)).trans <|
    mem_sdiff.trans <| and_iff_left h

/--
@isnad1 id=eq.0h4v.s6.fecdb054fbd2 from=translated src=- shape=b6266753 vocab=eeef2975
-/
theorem filter_symmDiff (p : α → Prop) [DecidablePred p] :
    (symmDiff A B).filter p = symmDiff (A.filter p) (B.filter p) :=
  Finset.ext λ x ↦ by rw [mem_filter, mem_symmDiff, mem_symmDiff,
    mem_filter, mem_filter, not_and_or, not_and_or,
    and_and_or_not_iff, and_and_or_not_iff, ← or_and_right]

end symmDiff

/-! ### Setup -/

structure GameState (n : ℕ) where
  board : Finset ℕ
  numMoves : ℕ

namespace GameState

/-- The initial state of the game -/
def init (M n : ℕ) : GameState n where
  board := range M
  numMoves := 0

/-- The valid moves -/
inductive ValidMove (X : GameState n) : GameState n → Prop
  | flip (i : ℕ) (h : i + n ∈ X.board) :
      ValidMove X ⟨symmDiff X.board (Icc i (i + n)), X.numMoves.succ⟩

/-- Can a state reach another state via a sequence of valid moves? -/
def IsReachable : GameState n → GameState n → Prop := ReflTransGen ValidMove

/-- Does the game end in the current state? -/
def Ends (X : GameState n) := ∀ Y : GameState n, ¬X.ValidMove Y

/-- If the first player wins, return `True`, else return `False`. -/
def P1Wins {X : GameState n} (_ : X.Ends) : Prop := X.numMoves % 2 = 1

/--
@isnad1 id=ex.1h3v.s6.c1b18aaea437 from=translated src=- shape=3ec9690b vocab=7552650a
-/
theorem ValidMove_board {X Y : GameState n} (h : X.ValidMove Y) :
    ∃ i : ℕ, i + n ∈ X.board ∧ Y.board = symmDiff X.board (Icc i (i + n)) :=
  ValidMove.recOn h λ i h0 ↦ ⟨i, h0, rfl⟩

/--
@isnad1 id=eq.1h3v.s5.6ddbea5efb8a from=translated src=- shape=a1f9ba46 vocab=9ac86b98
-/
theorem ValidMove_numMoves {X Y : GameState n} (h : X.ValidMove Y) :
    Y.numMoves = X.numMoves + 1 :=
  ValidMove.recOn h λ _ _ ↦ rfl

/--
@isnad1 id=eq.0h2v.s3.d3f499dc87d9 from=translated src=- shape=8910b6c4 vocab=12e7b685
-/
theorem board_init (M n : ℕ) : (init M n).board = range M := rfl

/--
@isnad1 id=eq.0h2v.s4.38ab0fede9d7 from=translated src=- shape=b34664ed vocab=f427f045
-/
theorem numMoves_init (M n : ℕ) : (init M n).numMoves = 0 := rfl

/--
@isnad1 id=iff.0h2v.s4.9c3629bca35b from=translated src=- shape=b1761d1f vocab=c44f3555
-/
theorem Ends_iff {X : GameState n} : X.Ends ↔ X.board ⊆ range n :=
  ⟨λ h i h0 ↦ by
    rw [mem_range, ← not_le]
    refine λ h1 ↦ h _ (ValidMove.flip (i - n) ?_)
    rwa [Nat.sub_add_cancel h1],
  λ h Y h0 ↦ ValidMove.recOn h0 λ i h1 ↦ (mem_range.mp (h h1)).not_ge le_add_self⟩

/-! ### Game termination -/

/--
@isnad1 id=lt.1h3v.s6.c4fa1b1e5396 from=translated src=- shape=734873e9 vocab=97f55f86
-/
theorem ValidMove_Colex {X Y : GameState n} (h : X.ValidMove Y) :
    toColex Y.board < toColex X.board := by
  rcases h with ⟨i, h⟩
  refine Colex.toColex_lt_toColex.mpr ⟨?_, λ j h0 h1 ↦ ?_⟩
  · rw [Ne, symmDiff_eq_left]
    exact ne_empty_of_mem (left_mem_Icc.mpr le_self_add)
  · refine ⟨i + n, h, λ h2 ↦ ?_, ?_⟩
    · rw [mem_symmDiff, mem_Icc] at h2
      exact h2.elim (λ h2 ↦ h2.2 ⟨le_self_add, (i + n).le_refl⟩) (λ h2 ↦ h2.2 h)
    · rw [mem_symmDiff, or_iff_right (λ h2 ↦ h1 h2.1), mem_Icc] at h0
      exact h0.1.2

/--
@isnad1 id=lt.1h3v.s6.b6a9df1a8ff6 from=translated src=- shape=7ae20d6d vocab=313c87b9
-/
theorem ValidMove_sum_two_pow {X Y : GameState n} (h : X.ValidMove Y) :
    Y.board.sum (2 ^ ·) < X.board.sum (2 ^ ·) :=
  (geomSum_lt_geomSum_iff_toColex_lt_toColex (Nat.le_refl 2)).mpr (ValidMove_Colex h)

/--
@isnad1 id=le.1h3v.s6.9606d716d67a from=translated src=- shape=d42d0916 vocab=a3e82cdd
-/
theorem isReachable_sum_two_pow_add_numMoves {X Y : GameState n} (h : X.IsReachable Y) :
    Y.board.sum (λ i ↦ 2 ^ i) + Y.numMoves ≤ X.board.sum (λ i ↦ 2 ^ i) + X.numMoves := by
  refine ReflTransGen.head_induction_on h (le_refl _) λ h0 _ h1 ↦ h1.trans ?_
  ---- One move case
  rw [ValidMove_numMoves h0, ← add_assoc, Nat.succ_le_iff]
  exact Nat.add_lt_add_right (ValidMove_sum_two_pow h0) _

/-- The number of moves made is always at most `2^M - 1`.
@isnad1 id=lt.1h3v.s5.dc88f384da5c from=translated src=- shape=f3ff7a05 vocab=05d2ba57
-/
theorem moves_lt_two_pow (h : (init M n).IsReachable X) : X.numMoves < 2 ^ M :=
  (le_of_add_le_right (isReachable_sum_two_pow_add_numMoves h)).trans_lt <|
    (geomSum_lt_geomSum_iff_toColex_lt_toColex (Nat.le_refl 2)).mpr
      (Colex.toColex_lt_singleton.mpr λ _ ↦ mem_range.mp)

/-! ### Winner of the game -/

/-- The set of central cards with `1` face-up -/
def centralCards (X : GameState n) : Finset ℕ :=
  X.board.filter λ i : ℕ ↦ n + 1 ∣ i + 1

/--
@isnad1 id=eq.1h3v.s5.a3418d6766c3 from=translated src=- shape=5c232c06 vocab=50a71e4d
-/
theorem ValidMove_central_card_mod_two {X Y : GameState n} (h : X.ValidMove Y) :
    Y.centralCards.card % 2 = (X.centralCards.card + 1) % 2 :=
  ValidMove.recOn h λ i _ ↦ by
    rw [centralCards, filter_symmDiff, ← centralCards,
      symmDiff_card_mod_two, Iic_filter_dvd_card]

/--
@isnad1 id=eq.1h3v.s6.22c54ed69541 from=translated src=- shape=59732c2a vocab=40db0a4f
-/
theorem isReachable_central_card_add_numMoves_mod_two
    {X Y : GameState n} (h : X.IsReachable Y) :
    (Y.centralCards.card + Y.numMoves) % 2
      = (X.centralCards.card + X.numMoves) % 2 := by
  refine ReflTransGen.head_induction_on h rfl λ h0 _ h1 ↦ ?_
  ---- One move case
  rw [h1, ValidMove_numMoves h0, Nat.add_mod, ValidMove_central_card_mod_two h0,
    ← Nat.add_mod, add_add_add_comm, Nat.add_mod_right]

/--
@isnad1 id=eq.0h2v.s4.3ba69b5903ae from=translated src=- shape=574a19d6 vocab=a0e719b6
-/
theorem filter_central_init_card (M n : ℕ) : (init M n).centralCards.card = M / n.succ :=
  M.card_multiples n.succ

/--
@isnad1 id=eq.1h2v.s4.d5063de9445a from=translated src=- shape=48a42d13 vocab=903bce5a
-/
theorem filter_central_ends {X : GameState n} (h : X.Ends) : X.centralCards = ∅ := by
  refine filter_eq_empty_iff.mpr λ i h0 ↦ Nat.not_dvd_of_pos_of_lt i.succ_pos ?_
  rw [Nat.succ_lt_succ_iff, ← mem_range]; exact Ends_iff.mp h h0

/-- The number of moves made has the same parity as `⌊M/(n + 1)⌋` when the game ends.
@isnad1 id=eq.2h3v.s5.cf48b7094749 from=translated src=- shape=8f4fab4c vocab=9df29eca
-/
theorem numMoves_mod_two_eq_div_of_ends (h : (init M n).IsReachable X) (h0 : X.Ends) :
    X.numMoves % 2 = M / n.succ % 2 := by
  have h1 := isReachable_central_card_add_numMoves_mod_two h
  rwa [filter_central_init_card, numMoves_init, Nat.add_zero,
    filter_central_ends h0, card_empty, Nat.zero_add] at h1

/-- The first player wins iff `⌊M/(n + 1)⌋` is odd
@isnad1 id=iff.2h3v.s5.96c96c04c18d from=translated src=- shape=f7e53a52 vocab=9c900f6c
-/
theorem P1Wins_iff (h : (init M n).IsReachable X) (h0 : X.Ends) :
    P1Wins h0 ↔ (M / n.succ) % 2 = 1 :=
  iff_of_eq (congrArg₂ _ (numMoves_mod_two_eq_div_of_ends h h0) rfl)

end GameState

/-! ### Final solution -/

/-- Final solution, part 1: Game termination
@isnad1 id=lt.1h3v.s5.dc88f384da5c from=translated src=- shape=f3ff7a05 vocab=05d2ba57
-/
alias final_solution_part1 := GameState.moves_lt_two_pow

/-- Final solution, part 2: Determining the winner
@isnad1 id=iff.2h3v.s5.96c96c04c18d from=translated src=- shape=f7e53a52 vocab=9c900f6c
-/
alias final_solution_part2 := GameState.P1Wins_iff
