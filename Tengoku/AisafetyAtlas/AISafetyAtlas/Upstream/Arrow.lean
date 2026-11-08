module

public import Tengoku.Seed.Data.Fintype.EquivFin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vendored Arrow proof

This is CC Liang's Lean 4 proof of Arrow's impossibility theorem from
https://github.com/ChihChengLiang/arrow at commit
`758398779decc66d2830a70b02597b0f22030181`, licensed Apache-2.0.
The original `Arrow/Arrow.lean` SHA-256 is
`ed006bc3ddc4249dfbff213e2f9f32b59a71721827060a25a46f8e5980ab7ab0`.

The proof body is unchanged. The atlas adds the modern `module` marker, public
declaration visibility, and this namespace. It converts the upstream `Profile`
and `SWF` definitions to reducible abbreviations so the adapted interfaces
elaborate across Lean 4.32's public-module boundary. It also adds four
`Iff.rfl` elimination lemmas required across that boundary:
`Preorder'.lt_iff`, `unanimity_iff`, `iia_iff`, and
`nonDictatorship_iff`. These lemmas expose existing definitions; they do not
change the Arrow proof.
-/

namespace AISafetyAtlas.Upstream.Arrow

noncomputable section
open Classical

/-! ## Preorder'

A total preorder over candidates `α`, representing an individual's preference ranking.
-/
variable {α : Type}

-- ANCHOR: Preorder
/-- A total preorder: reflexive, transitive, and total.-/
public structure Preorder' (α : Type) where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ a b c, le a b → le b c → le a c
  total : ∀ a b, le a b ∨ le b a
-- ANCHOR_END: Preorder

-- ANCHOR: StrictPref
/-- Strict preference: `a` is strictly preferred to `b` iff `a ≤ b` but not `b ≤ a`.-/
@[simp]
public def Preorder'.lt (p : Preorder' α) (a b : α) : Prop :=
  p.le a b ∧ ¬p.le b a
-- ANCHOR_END: StrictPref

/-- Public elimination rule for strict preference. Atlas addition.-/
public theorem Preorder'.lt_iff (p : Preorder' α) (a b : α) :
    p.lt a b ↔ p.le a b ∧ ¬p.le b a :=
  Iff.rfl

-- ANCHOR: Notation
-- Notation: `a ≻[p] b` means voter with preference `p` strictly prefers `a` over `b`
scoped notation a " ≻[" p  "] " b => Preorder'.lt p b a
scoped notation a " ≽[" p  "] " b => Preorder'.le p b a
scoped notation a " ≻[" p  "] " b "≻ " c => (a ≻[p] b) ∧ b ≻[p] c
scoped notation a " ≽[" p  "] " b "≻ " c => (a ≽[p] b) ∧ b ≻[p] c
-- ANCHOR_END: Notation

public lemma Preorder'.lt_asymm {p : Preorder' α} {a b : α} :
    p.lt a b → ¬ p.lt b a := by intro ⟨_, hnba⟩ ⟨hba, _⟩; exact hnba hba

public lemma Preorder'.lt_trans {p : Preorder' α} {a b c : α}
    (h1 : p.lt a b) (h2 : p.lt b c) : p.lt a c := by
    constructor
    . exact p.trans _ _ _ h1.1 h2.1
    . intro h; exact h1.2 (p.trans _ _ _ h2.1 h)

public lemma Preorder'.lt_of_lt_of_le {p : Preorder' α} {a b c : α}
    (hab : p.lt a b) (hbc : p.le b c) : p.lt a c := by
    simp [Preorder'.lt] at hab ⊢; constructor
    . exact p.trans _ _ _ hab.1 hbc
    . intro h; exact absurd (p.trans _ _ _ hbc h) hab.2

/-- The three possible outcomes when comparing two elements under a total preorder.-/
public inductive Cmp (p : Preorder' α) (a b : α) : Type
  | Indiff (h₁ : p.le a b) (h₂ : p.le b a) : Cmp p a b
  | LT     (h  : p.le a b) (hn : ¬p.le b a) : Cmp p a b
  | GT     (hn : ¬p.le a b) (h  : p.le b a)  : Cmp p a b

public noncomputable def Preorder'.cmp (p : Preorder' α) (a b : α) : Cmp p a b :=
  if hab : p.le a b then
    if hba : p.le b a then Cmp.Indiff hab hba
    else Cmp.LT hab hba
  else Cmp.GT hab (p.total a b |>.resolve_left hab)

/-! ## Social Welfare Function

Core definitions for Arrow's theorem: profiles, SWFs, and the three key properties.
-/
variable {N : ℕ}

-- ANCHOR: Profile
/-- A preference profile assigns each voter `i ∈ Fin N` their preference ordering.-/
public abbrev Profile (α : Type) (N : ℕ) := Fin N → Preorder' α
-- ANCHOR_END: Profile

-- ANCHOR: SWF
/-- A Social Welfare Function aggregates individual preferences into a social ordering.-/
public abbrev SWF (α : Type) (N : ℕ) := Profile α N → Preorder' α
-- ANCHOR_END: SWF

-- ANCHOR: Dictates
/-- Voter `k` is a dictator for the pair `(a, b)` if whenever `k` prefers `a` over `b`,
    society also prefers `a` over `b`.-/
public def Dictates (R : SWF α N) (k : Fin N) (a b : α): Prop :=
  ∀ (p: Profile α N ), (a ≻[p k] b) → a ≻[R p] b
-- ANCHOR_END: Dictates

-- ANCHOR: AgreeOn
/-- Two profiles agree on `(a, b)` if every voter ranks `a` vs `b` the same way in both.-/
@[simp]
public def AgreeOn (p q : Profile α N) (a b : α) : Prop :=
  ∀ i, ((a ≽[p i] b) ↔ a ≽[q i] b) ∧ ((b ≽[p i] a) ↔ b ≽[q i] a)
-- ANCHOR_END: AgreeOn

-- ANCHOR: Unanimity
/-- **Unanimity** (Pareto): If all voters prefer `a` over `b`, so does society.-/
public def Unanimity (R : SWF α N) : Prop :=
  ∀ (p: Profile α N) (a b: α), (∀ i: Fin N, a ≻[p i] b) → a ≻[R p] b
-- ANCHOR_END: Unanimity

-- ANCHOR: IIA
/-- **Independence of Irrelevant Alternatives**: The social ranking of `a` vs `b`
    depends only on individual rankings of `a` vs `b`.-/
public def IIA (R : SWF α N) : Prop :=
  ∀ (p q: Profile α N) (a b: α),
    AgreeOn p q a b → ((a ≽[R p] b) ↔ a ≽[R q] b) ∧ ((b ≽[R p] a) ↔ b ≽[R q] a)
-- ANCHOR_END: IIA

-- ANCHOR: NonDictatorship
/-- **Non-Dictatorship**: No single voter dictates the outcome for all pairs.-/
public def NonDictatorship (R : SWF α N): Prop :=
  ¬ (∃ i: Fin N, ∀ (a b: α), (a ≠ b) → Dictates R i a b)
-- ANCHOR_END: NonDictatorship

/-! ## Preference Construction

We construct concrete preference orderings to build test profiles for the proof.
Given three alternatives, `prefer a₀ a₁ a₂ tie` ranks them with optional ties.
-/

-- ANCHOR: Tie
/-- Where ties occur in a 3-element preference ranking-/
public inductive Tie | Not | Top | Bot
-- ANCHOR_END: Tie

@[simp]
public def prefer_ifs (x y a₀ _a₁ a₂ : α) (tie : Tie): Prop :=
  match tie with
  | .Not =>
    if x = a₂ then True              -- a₂ is bottom
    else if y = a₀ then True         -- a₀ is top
    else if x = a₀ then y = a₀       -- only a₀ ≤ a₀
    else if y = a₂ then x = a₂       -- only a₂ ≥ a₂
    else True
  | .Top =>
    if y = a₂ then x = a₂           -- only a₂ ≥ a₂ (a₂ is bottom)
    else if x = a₂ then True        -- a₂ ≤ everything else
    else True                        -- a₀ ~ a₁: both directions
  | .Bot =>
    if x = a₀ then y = a₀           -- only a₀ ≤ a₀ (a₀ is top)
    else if y = a₀ then True        -- everything else ≤ a₀
    else True                        -- a₁ ~ a₂: both directions

-- ANCHOR: prefer
/-- Construct a preference ordering with optional ties:
    - `Tie.Not`: a₀ > a₁ > a₂ (strict ranking)
    - `Tie.Top`: a₀ ~ a₁ > a₂ (top two tied)
    - `Tie.Bot`: a₀ > a₁ ~ a₂ (bottom two tied)-/
public def prefer (a₀ _a₁ a₂ : α) (tie : Tie) (h02 : a₀ ≠ a₂) : Preorder' α where
-- ANCHOR_END: prefer
  le x y := prefer_ifs x y a₀ _a₁ a₂ tie
  refl _ := by cases tie <;> simp
  trans _ _ _ _ _ := by unfold prefer_ifs at *; split <;> split_ifs <;> simp_all
  total a b := by unfold prefer_ifs at *; split <;> by_cases a = a₂ <;> by_cases b = a₀ <;> simp_all

/-! ## Pivotal Voter

The key construction: we find the "pivotal voter" who flips society's preference.
Starting from a profile where everyone prefers `b ≻ a`, we flip voters one by one
to prefer `a ≻ b`. By unanimity, society eventually flips too. The first voter
whose flip changes society's preference is the pivotal voter.
-/
variable [NeZero N] {R : SWF α N}

-- ANCHOR: canonicalSwap
/-- A family of profiles indexed by `k ∈ Fin (N+1)`:
    voters `0..k-1` prefer `b ≻ a`, voters `k..N-1` prefer `a ≻ b`.-/
@[simp]
public def canonicalSwap (a b : α) (hab : a ≠ b) : Fin (N+1) → Profile α N :=
  fun k: Fin (N+1) =>
    fun i: Fin N => if i < k.val
      -- `prefer` takes 3 items, we duplicate middle as a workaround
      then prefer b b a .Not hab.symm  -- b on top
      else prefer a b b .Not hab            -- a on top
-- ANCHOR_END: canonicalSwap

-- ANCHOR: flipping
/-- `flipping R a b hab k` holds iff society prefers `b ≻ a` when voters `0..k` prefer `b ≻ a`.-/
public def flipping (R : SWF α N) (a b : α) (hab : a ≠ b) :=
  fun k: Fin N => ¬ a ≻[R (canonicalSwap a b hab k.succ)] b
-- ANCHOR_END: flipping

/-- By unanimity, a flip must occur: when all voters prefer `b ≻ a`, so does society.-/
public lemma flip_exists (R : SWF α N) (a b : α) (hab : a ≠ b) (hu : Unanimity R):
    ∃ k, flipping R a b hab k := by
  use (0:Fin N).rev
  unfold flipping canonicalSwap
  simp [Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne N))]
  intros
  exact (show b ≻[R (fun _ => prefer b b a .Not hab.symm)] a from
          hu _ _ _ (fun _ => by simp [prefer, hab, hab.symm])).1

-- ANCHOR: pivoter
/-- The pivotal voter for `(a, b)`: the minimum `k` where society flips from `a ≻ b` to `b ≻ a`.-/
public noncomputable def pivoter (a b : α) (hab : a ≠ b) (hu : Unanimity R) : Fin N :=
  Fin.find (flipping R a b hab) (flip_exists R a b hab hu)
-- ANCHOR_END: pivoter

-- ANCHOR: no_flip

omit [NeZero N] in
/-- Public elimination rule for the upstream unanimity definition. Atlas addition.-/
public theorem unanimity_iff (R : SWF α N) :
    Unanimity R ↔
      ∀ profile a b,
        (∀ voter, Preorder'.lt (profile voter) b a) →
        Preorder'.lt (R profile) b a :=
  Iff.rfl

omit [NeZero N] in
/-- Public elimination rule for the upstream IIA definition. Atlas addition.-/
public theorem iia_iff (R : SWF α N) :
    IIA R ↔
      ∀ profile₁ profile₂ a b,
        (∀ voter,
          ((profile₁ voter).le b a ↔ (profile₂ voter).le b a) ∧
          ((profile₁ voter).le a b ↔ (profile₂ voter).le a b)) →
        (((R profile₁).le b a ↔ (R profile₂).le b a) ∧
          ((R profile₁).le a b ↔ (R profile₂).le a b)) :=
  Iff.rfl

omit [NeZero N] in
/-- Public elimination rule for non-dictatorship. Atlas addition.-/
public theorem nonDictatorship_iff (R : SWF α N) :
    NonDictatorship R ↔
      ¬ ∃ dictator : Fin N, ∀ a b,
        a ≠ b → ∀ profile,
          Preorder'.lt (profile dictator) b a →
          Preorder'.lt (R profile) b a :=
  Iff.rfl

end

end AISafetyAtlas.Upstream.Arrow
-- Tengoku: 4 notation(s) of this module made scoped so they do not change other libraries (generated)
