/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/
module

public import Tengoku

/-! # A General Theory for Determined Two-player Games

Nothing here is specific about PDL, but we give a general
definition of games and show that one of the two players
must have a winning strategy: `gamedet` at the end.

-/

@[expose] public section

namespace Lean4GlCoalgebras

/-! ## Games -/

/-- Two players, `A` and `B`. -/
inductive Player : Type
| A : Player
| B : Player
deriving DecidableEq

open Player

/--
@isnad1 id=iff.0h1v.s3.c96fcc18833e from=translated src=- shape=64d1a3cf vocab=79721767
-/
theorem Player.ne_A_iff_eq_B {p} : p ≠ A ↔ p = B := by cases p <;> simp

/--
@isnad1 id=iff.0h1v.s3.f14e62d9280f from=translated src=- shape=64d1a3cf vocab=79721767
-/
theorem Player.ne_B_iff_eq_A {p} : p ≠ B ↔ p = A := by cases p <;> simp

/--
@isnad1 id=iff.0h1v.s3.408296783914 from=translated src=- shape=f8683d95 vocab=79721767
-/
theorem Player.not_eq_iff_eq_other {p} : (¬ p = A) ↔ p = B := by cases p <;> simp

/--
@isnad1 id=iff.0h1v.s3.a478939cbaee from=translated src=- shape=f8683d95 vocab=79721767
-/
theorem Player.not_eq_B_iff_eq_A {p} : (¬ p = B) ↔ p = A := by cases p <;> simp

theorem Player.eq_A_or_eq_B {p} : p = A ∨ p = B := by cases p <;> simp

/-- Auxiliary declaration used in the GL coalgebra development. -/
def other : Player → Player
| A => B
| B => A

/--
@isnad1 id=eq.0h0v.s2.740f8ced39df from=translated src=- shape=4b736592 vocab=6884036a
-/
@[simp]
theorem other_A_eq_B : other A = B := by simp [other]

/--
@isnad1 id=eq.0h0v.s2.41cbf99866c5 from=translated src=- shape=4b736592 vocab=6884036a
-/
@[simp]
theorem other_B_eq_A : other B = A := by simp [other]

/--
@isnad1 id=iff.0h2v.s3.03aba2efbaba from=translated src=- shape=0aa68ff2 vocab=34f3bfef
-/
@[simp]
theorem Player.not_eq_i_eq_other {p i} : (¬ p = i) ↔ p = other i := by cases p <;> cases i <;> simp

/--
@isnad1 id=iff.0h2v.s3.43ed6beb3e57 from=translated src=- shape=eb1feff0 vocab=34f3bfef
-/
theorem Player.not_eq_other_eq_i {p i} : (¬ p = other i) ↔ p = i := by cases p <;> cases i <;> simp

/--
@isnad1 id=not.0h1v.s3.f0d0c9b6be2f from=translated src=- shape=b963f59e vocab=34f3bfef
-/
@[simp]
theorem Player.not_i_eq_other {i} : ¬ i = other i := by cases i <;> simp

/--
@isnad1 id=not.0h1v.s3.3702ca2c1ddc from=translated src=- shape=2c351717 vocab=34f3bfef
-/
@[simp]
theorem Player.not_other_i_eq_i {i} : ¬ other i = i := by cases i <;> simp

/--
@isnad1 id=eq.0h1v.s3.ac2dc223b15b from=translated src=- shape=47dcad53 vocab=34f3bfef
-/
@[simp]
theorem other_other {i} : other (other i) = i := by cases i <;> simp [other]

/-- Two-player game with
- perfect information
- sequential moves (i.e. only one player moves at each position)
- finitely many moves at each step (aka finitely branching)
- a well-founded relation to ensure that the game ends.
-/
class Game where
  /-- Positions in the game. -/
  Pos : Type
  /-- Whose turn is it? -/
  turn : Pos → Player
  /-- What are the available moves? -/
  moves : Pos → Finset Pos
  /-- A wellfounded relation on positions. -/
  wf : WellFoundedRelation Pos
  /-- Every move goes a step down in the relation. -/
  move_rel : ∀ (p next : Pos), next ∈ moves p → wf.rel next p

/-- This seems a bit hacky, but makes `termination_by (p : g.Pos)` work in `winner` and elsewhere.
If the instance causes trouble, change to `termination_by g.wf.2.wrap p` via `WellFounded.wrap`. -/
instance {g : Game} : WellFoundedRelation Game.Pos := g.wf

/-- Allow notation `p.moves` for `g.moves p`. -/
abbrev Game.Pos.moves {g : Game} : g.Pos → Finset g.Pos := Game.moves

/-- If the bound bound is zero then there are no more moves.
@isnad1 id=eq.1h2v.s4.c2d70fae9610 from=translated src=- shape=01313599 vocab=9e088dba
-/
lemma Game.no_moves_of_no_rel {g : Game} {p : g.Pos}
    (no_rel : ∀ q, ¬ g.wf.rel q p) : g.moves p = ∅ := by
  suffices ¬ (g.moves p).Nonempty by simp_all
  by_contra hyp
  rcases Finset.Nonempty.exists_mem hyp with ⟨q, q_in⟩
  have := g.move_rel _ q q_in
  simp_all

instance {g : Game} : LT g.Pos := ⟨fun p q => g.wf.rel q p⟩

/-! ## Strategies -/

/-- A strategy in `g` for `i`, whenever it is `i`'s turn, chooses a move, if there are any. -/
def Strategy (g : Game) (i : Player) : Type :=
  ∀ p : g.Pos, g.turn p = i → p.moves.Nonempty → p.moves

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def chooseMove {g : Game} {p : g.Pos} : p.moves.Nonempty → p.moves :=
  Classical.choice ∘ Set.Nonempty.to_subtype

/-- There is always some strategy.
@isnad1 id=nonempty.0h2v.s3.9bc00d431478 from=translated src=- shape=c57da3d9 vocab=af29d640
-/
instance Strategy.instNonempty {g i} : Nonempty (Strategy g i) := ⟨fun _ _ => chooseMove⟩

/-- Winner of a game, if the given strategies are used.
A player loses iff it is their turn and there are no moves.
A player wins if the opponent loses. -/
def winner {i} {g : Game} (sI : Strategy g i) (sJ : Strategy g (other i)) (p : g.Pos) : Player :=
  if h1 : (g.moves p).Nonempty
    then if h2 : g.turn p = i --
      then winner sI sJ (sI p h2 h1)
      else winner sI sJ (sJ p (by cases i <;> simp_all) h1)
    else other (g.turn p) -- no more moves, the other player wins
termination_by
  p
decreasing_by
  all_goals
    apply g.move_rel; simp

/-- A strategy is winning at `p` if it wins against all strategies of the other player. -/
def winning {g : Game} {i : Player} (sI : Strategy g i) (p : g.Pos) : Prop :=
  ∀ sJ : Strategy g (other i), winner sI sJ p = i

/-! ## Good positions -/

/-- Auxiliary declaration used in the GL coalgebra development. -/
def good {g : Game} (i : Player) (p : g.Pos) : Prop :=
    (g.turn p = i       ∧ ∃ (q : g.Pos) (_ : q ∈ p.moves), good i q)
  ∨ (g.turn p = other i ∧ ∀ (q : g.Pos) (_ : q ∈ p.moves), good i q)
termination_by p
decreasing_by all_goals apply g.move_rel _ _; assumption

/--
@isnad1 id=nonempty.2h3v.s4.26af28adb9a4 from=translated src=- shape=16793c1d vocab=247d15c9
-/
theorem good_is_surviving {i} {g : Game} {p : g.Pos} :
    good i p → g.turn p = i → p.moves.Nonempty := by
  intro W turn
  unfold good at W
  apply (Or.resolve_right · (not_and_of_not_left _ <| not_eq_other_eq_i.mpr turn)) at W
  match W with | ⟨_, ⟨q, ⟨h, _⟩⟩⟩ => exact ⟨q,h⟩

/--
@isnad1 id=or.0h2v.s4.b48bf640ba2a from=translated src=- shape=6f1d9249 vocab=af642ca0
-/
theorem good_or_other {g : Game} (p : g.Pos) : good (g.turn p) p ∨ good (other (g.turn p)) p := by
  apply WellFounded.induction g.wf.2 p
  intro r IH
  by_cases ∃ q ∈ r.moves, good (g.turn r) q
  case pos E =>
    apply Or.inl
    unfold good
    simp_all
  case neg A =>
    apply Or.inr
    unfold good
    refine Or.inr (And.intro other_other.symm ?_)
    intro q h
    specialize IH q (g.move_rel _ _ h)
    by_cases g.turn r = g.turn q <;> simp_all

/--
@isnad1 id=or.0h2v.s3.3c2f4c900735 from=translated src=- shape=8b010770 vocab=5cee64be
-/
theorem good_A_or_B {g : Game} (p : g.Pos) : good A p ∨ good B p := by
  have det := good_or_other p
  cases i : g.turn p <;> cases det <;> simp_all

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def goodStrat (i : Player) : Strategy g i := fun p turn nempty =>
  have := Classical.dec
  if W : good i p
    then by
      unfold good at W
      have E := And.right <| W.resolve_right (not_and_of_not_left _ <| not_eq_other_eq_i.mpr turn)
      exact ⟨E.choose, E.choose_spec.choose⟩
    else chooseMove nempty

/-! ## Cones -/

/-- The cone of all positions reachable from `p` assuming that `i` plays `sI`. -/
inductive inMyCone {i} {g : Game} (sI : Strategy g i) (p : g.Pos) : g.Pos → Prop
| nil : inMyCone sI p p
| myStep {q} : inMyCone sI p q → (has_moves : q.moves.Nonempty) → (h : g.turn q = i)
                → inMyCone sI p (sI q h has_moves)
| oStep {q r} : inMyCone sI p q → g.turn q = other i → r ∈ g.moves q → inMyCone sI p r

/--
@isnad1 id=inmycone.2h6v.s5.ba92248240a5 from=translated src=- shape=9f962870 vocab=389ec76b
-/
theorem inMyCone_trans {g i} {p q r : g.Pos} {s : Strategy g i} :
    inMyCone s p q → inMyCone s q r → inMyCone s p r :=
  fun a b => by induction b with
  | nil => assumption
  | myStep _ _ _ ih => exact .myStep ih ..
  | oStep a turn h ih => exact .oStep ih turn h

/-- The cone of the `goodStrat` stays inside `good` positions.
@isnad1 id=good.2h4v.s4.718d3194d857 from=translated src=- shape=1c6cb45f vocab=37058ae0
-/
theorem good_cone {i} {g : Game} {p r : g.Pos} (W : good i p) (h : inMyCone (goodStrat i) p r) :
    good i r := by
  induction h with
  | nil => exact W
  | oStep _ turn h ih =>
    unfold good at ih
    exact (ih.resolve_left (not_and_of_not_left _ <| not_eq_i_eq_other.mpr turn)).right _ h
  | @myStep q a nempty turn ih =>
    unfold goodStrat
    by_cases hq : good i q
    · simp only [hq, ↓reduceDIte]
      unfold good at hq
      have E := And.right <| hq.resolve_right (not_and_of_not_left _ <| not_eq_other_eq_i.mpr turn)
      exact E.choose_spec.choose_spec
    · simp_all

/-! ## Zermelo's Theorem -/

/--
@isnad1 id=winning.1h4v.s5.9e6b99d2f1bc from=translated src=- shape=7c596c13 vocab=f032b753
-/
theorem surviving_is_winning {g i p} {sI : Strategy g i}
    (surv : ∀ q, inMyCone sI p q → g.turn q = i → q.moves.Nonempty)
    : winning sI p :=
  fun sJ => by
    unfold winner
    split
    case isFalse empty =>
      by_contra turn
      apply (not_eq_other_eq_i.mp ∘ Ne.symm) at turn
      exact empty (surv _ .nil turn.symm)
    split
    · exact surviving_is_winning (surv · ∘ inMyCone_trans (.myStep .nil _ _)) _
    next _ turn =>
      exact surviving_is_winning
        (surv · ∘ inMyCone_trans (.oStep .nil (not_eq_i_eq_other.mp turn) <| Subtype.mem _)) _
termination_by p
decreasing_by all_goals apply g.move_rel; exact Subtype.mem _

/--
@isnad1 id=winning.1h3v.s4.e1627ecbac95 from=translated src=- shape=20f05e29 vocab=35afdd9a
-/
theorem good_strat_winning {g : Game} {i} {p : g.Pos} (W : good i p) : winning (goodStrat i) p :=
  surviving_is_winning fun _ => good_is_surviving ∘ (good_cone W)

/--
[Zermelo's Theorem](https://en.wikipedia.org/wiki/Zermelo%27s_theorem_(game_theory)):
In every `Game` position one of the two players has a winning strategy.
@isnad1 id=or.0h2v.s5.69981ecce4e2 from=translated src=- shape=d6cd514b vocab=0e24ece7
-/
theorem gamedet (g : Game) (p : g.Pos) :
    (∃ s : Strategy g A, winning s p) ∨ (∃ s : Strategy g B, winning s p) := Or.imp
    (⟨goodStrat A, good_strat_winning ·⟩)
    (⟨goodStrat B, good_strat_winning ·⟩)
    <| good_A_or_B p

/-! ## Additional Helper Theorems -/

/--
@isnad1 id=nonempty.2h4v.s4.2451b1254acb from=translated src=- shape=91eb5a54 vocab=5b6ef97e
-/
lemma winning_has_moves {i g} {sI : Strategy g i} {p : g.Pos}
    (h : g.turn p = i) (sI_wins_p : winning sI p) :
    (g.moves p).Nonempty := by
  specialize sI_wins_p (Classical.choice Strategy.instNonempty)
  unfold winner at sI_wins_p
  by_contra hyp
  simp_all

/--
@isnad1 id=winning.2h4v.s5.b3f87f1687d6 from=translated src=- shape=95e4ffa6 vocab=4efba45f
-/
lemma winning_of_winning_move {i g} {sI : Strategy g i} {p : g.Pos}
    (h : g.turn p = i) (sI_wins_p : winning sI p) :
    winning sI (sI p h (winning_has_moves h sI_wins_p)).val := by
  intro sJ
  have := winning_has_moves h sI_wins_p
  specialize sI_wins_p sJ
  unfold winner at sI_wins_p
  simp_all

/--
@isnad1 id=refltran.1h5v.s4.38c8e9b1d5fe from=translated src=- shape=d1d03a36 vocab=0dcdea58
-/
lemma game_wf_rel_of_cone {i g} {p r : g.Pos} (sI : Strategy g i) (r_in : inMyCone sI p r) :
    Relation.ReflTransGen g.wf.rel r p := by
  induction r_in
  · exact Relation.ReflTransGen.refl
  case myStep q q_in q_has_moves turn IH =>
    apply Relation.ReflTransGen.head _ IH
    apply g.move_rel
    simp
  case oStep IH =>
    apply Relation.ReflTransGen.head _ IH
    apply g.move_rel
    assumption

/--
@isnad1 id=not.1h5v.s5.781fba34c69a from=translated src=- shape=47f2c8c4 vocab=dceb6626
-/
lemma not_in_cone_of_move {i g} {p q : g.Pos} (q_in : q ∈ g.moves p) (sI : Strategy g i) :
    ¬ @inMyCone _ g sI q p := by
  intro hyp
  have claim : Relation.TransGen g.wf.rel p p := by
    have m_to_p := g.move_rel _ q q_in
    have := game_wf_rel_of_cone _ hyp
    rw [Relation.reflTransGen_iff_eq_or_transGen] at this
    cases this
    · subst_eqs
      absurd m_to_p
      exact WellFoundedRelation.asymmetric m_to_p
    · apply Relation.TransGen.trans _ (Relation.TransGen.single m_to_p)
      aesop
  absurd claim
  exact Std.Irrefl.irrefl p

/--
@isnad1 id=eq.1h6v.s6.32f82a1fed13 from=translated src=- shape=ee027ca9 vocab=8620ac33
-/
lemma same_winner_of_same_in_cone {i g} {sI : Strategy g i} {sJ sJ' : Strategy g (other i)}
    {p : g.Pos}
    (same_cone : ∀ r, inMyCone sJ p r → sJ r = sJ' r)
    : winner sI sJ p = winner sI sJ' p := by
  by_cases p_has_moves : (Game.moves p).Nonempty
  · by_cases turn : Game.turn p = i
    · conv_lhs => unfold winner; rw [dite_eq_left p_has_moves, dite_eq_left turn]
      conv_rhs => unfold winner; rw [dite_eq_left p_has_moves, dite_eq_left turn]
      apply same_winner_of_same_in_cone
      intro r r_in
      apply same_cone r
      apply @inMyCone_trans g (other i) p (sI p turn p_has_moves) r sJ ?_ r_in
      apply @inMyCone.oStep (other i) g sJ _ p _ inMyCone.nil (by simp_all) (by simp)
    · have other_turn : Game.turn p = other i := Player.not_eq_i_eq_other.mp turn
      conv_lhs => unfold winner; rw [dite_eq_left p_has_moves, dite_eq_right turn]
      conv_rhs => unfold winner; rw [dite_eq_left p_has_moves, dite_eq_right turn]
      have := @same_winner_of_same_in_cone _ g sI sJ sJ' (sJ' p other_turn p_has_moves).val ?_
      · convert this using 2
        rw [same_cone p inMyCone.nil]
      · intro r r_in
        apply same_cone r
        apply @inMyCone_trans g (other i) p (sJ' p other_turn p_has_moves) r sJ ?_ r_in
        have : (sJ p other_turn p_has_moves) = (sJ' p other_turn p_has_moves) := by
          rw [same_cone p .nil]
        rw [← this]
        apply @inMyCone.myStep _ g sJ _ p inMyCone.nil
  · conv_lhs => unfold winner; rw [dite_eq_right p_has_moves]
    conv_rhs => unfold winner; rw [dite_eq_right p_has_moves]
termination_by p
decreasing_by all_goals apply g.move_rel; exact Subtype.mem _

/-- Helper for `gameP_general`.
@isnad1 id=winning.2h5v.s6.3626e239470e from=translated src=- shape=bfb5fff1 vocab=30e88565
-/
theorem winning_of_whatever_other_move {i g} {sI : Strategy g i}
    {p : g.Pos} (h : g.turn p = other i) (sI_wins_p : winning sI p) (m : g.moves p)
    : winning sI m.val := by
  have : DecidableEq g.Pos := by exact Classical.typeDecidableEq Game.Pos
  unfold winning
  intro sJ
  let sJ_m : Strategy g (other i) := fun npos npos_Bui_turn nonE =>
    -- At `p` we use the given `m`, otherwise d othe same as `sJ`.
    if same_p : npos = p then same_p ▸ m else  sJ _ npos_Bui_turn nonE
  specialize sI_wins_p sJ_m
  unfold winner at sI_wins_p
  have : (Game.moves p).Nonempty := ⟨m.1,m.2⟩
  have : ¬ Game.turn p = i := by aesop
  have sI_wins_p := by simpa [sJ_m, *] using sI_wins_p
  convert sI_wins_p using 1 -- because rw [← sI_wins_p] does not work
  apply same_winner_of_same_in_cone
  -- Remains to show that sJ and sJ_m will agree on all remaining moves.
  -- In those lemmas we also use use the well-founded order, not used so far.
  intro r r_in
  have : r ≠ p := by
    intro hyp
    subst hyp
    absurd r_in
    exact not_in_cone_of_move m.2 sJ
  aesop

/--
@isnad1 id=winning.2h5v.s5.d3a89fab6317 from=translated src=- shape=e66e3ef7 vocab=c4415211
-/
lemma winning_of_in_cone_winning {g : Game} {i : Player} {p q : g.Pos} {sI : Strategy g i}
    (in_cone : inMyCone sI p q) (h : winning sI p) : winning sI q := by
  induction in_cone
  case nil => exact h
  case myStep q q_in_cone has_moves my_turn ih =>
    apply winning_of_winning_move
    exact ih
  case oStep q q' q_in_cone o_turn in_moves ih =>
    exact @winning_of_whatever_other_move i g sI q o_turn ih ⟨q', in_moves⟩
end Lean4GlCoalgebras
