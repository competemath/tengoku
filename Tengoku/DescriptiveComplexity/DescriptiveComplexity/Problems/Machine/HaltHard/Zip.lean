/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Tengoku.DescriptiveComplexity.DescriptiveComplexity.Problems.Machine.HaltHard.Table

/-!
# The simulating machine on a zipper tape

The simulation of `Turing.ToPartrec.step` by
`DescriptiveComplexity.HaltHard.simStep` is proved against a concrete
sequential semantics first: a configuration is a *zipper*
(`DescriptiveComplexity.HaltHard.LCfg`) – the state, the letters left of the
head (nearest first), the letter under the head, and the letters right of the
head (nearest first) – and one step (`DescriptiveComplexity.HaltHard.lstep`)
applies the table and moves, materializing a blank when the head leaves the
recorded region. This keeps every walk argument a plain list induction; the
sibling `Bridge` file identifies runs of `lstep` with derivations of the
rewriting system `DescriptiveComplexity.HaltPcp.MRule` of the drawn machine,
so nothing here mentions words or rules.

Beside the step and its reachability
(`DescriptiveComplexity.HaltHard.Reach`, and the step-counted
`DescriptiveComplexity.HaltHard.stepsTo` the deterministic backward reading
needs), the file provides the two **walk combinators**: a state that passes a
set of letters unchanged in one direction crosses any run of them
(`DescriptiveComplexity.HaltHard.reach_walkR`/`reach_walkL`). Every phase of
the simulation is a chain of these.
-/

namespace DescriptiveComplexity

namespace HaltHard

open Turing.ToPartrec

variable {c : Code}

/-- A configuration of the simulating machine, as a zipper: the letters left
of the head are listed nearest-first, the letters right of the head
nearest-first. Cells outside the recorded region are blank; a move beyond it
materializes the blank. -/
structure LCfg (c : Code) where
  /-- The current state. -/
  q : SimQ c
  /-- The letters left of the head, nearest first. -/
  L : List (SimSym c)
  /-- The letter under the head. -/
  s : SimSym c
  /-- The letters right of the head, nearest first. -/
  R : List (SimSym c)

/-- One step of the machine on the zipper tape: apply the table, write, move;
a move beyond the recorded region reads a fresh blank. -/
def lstep (x : LCfg c) : Option (LCfg c) :=
  (simStep x.q x.s).map fun a =>
    if a.2.2 then
      match x.R with
      | [] => ⟨a.2.1, a.1 :: x.L, .bk, []⟩
      | t :: R' => ⟨a.2.1, a.1 :: x.L, t, R'⟩
    else
      match x.L with
      | [] => ⟨a.2.1, [], .bk, a.1 :: x.R⟩
      | t :: L' => ⟨a.2.1, L', t, a.1 :: x.R⟩

/-- Reachability in any number of machine steps. -/
def Reach : LCfg c → LCfg c → Prop :=
  Relation.ReflTransGen fun x y => lstep x = some y

/-- Reaching one configuration from another in exactly `n` steps. -/
def stepsTo : ℕ → LCfg c → LCfg c → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ d, lstep x = some d ∧ stepsTo n d y

/-! ### The four single steps -/

section Steps

variable {q q' : SimQ c} {σ σ' : SimSym c}

/-- A right move with a recorded cell to enter.
@isnad1 id=eq.1h8v.s6.0aae4834c633 from=translated src=- shape=f9d6b28d vocab=bce04deb
-/
theorem lstep_right (h : simStep q σ = some (σ', q', true)) (L : List (SimSym c))
    (t : SimSym c) (R : List (SimSym c)) :
    lstep ⟨q, L, σ, t :: R⟩ = some ⟨q', σ' :: L, t, R⟩ := by
  simp [lstep, h]

/-- A right move off the recorded region: the entered cell is blank.
@isnad1 id=eq.1h6v.s6.a7d4c47a6ea5 from=translated src=- shape=fc19f7fc vocab=c6dcbdea
-/
theorem lstep_right_end (h : simStep q σ = some (σ', q', true)) (L : List (SimSym c)) :
    lstep ⟨q, L, σ, []⟩ = some ⟨q', σ' :: L, .bk, []⟩ := by
  simp [lstep, h]

/-- A left move with a recorded cell to enter.
@isnad1 id=eq.1h8v.s6.876f63e98a40 from=translated src=- shape=d34441be vocab=67057c0c
-/
theorem lstep_left (h : simStep q σ = some (σ', q', false)) (t : SimSym c)
    (L R : List (SimSym c)) :
    lstep ⟨q, t :: L, σ, R⟩ = some ⟨q', L, t, σ' :: R⟩ := by
  simp [lstep, h]

/-- A left move off the recorded region: the entered cell is blank.
@isnad1 id=eq.1h6v.s6.983348fed64d from=translated src=- shape=991a5976 vocab=31bc747e
-/
theorem lstep_left_end (h : simStep q σ = some (σ', q', false)) (R : List (SimSym c)) :
    lstep ⟨q, [], σ, R⟩ = some ⟨q', [], .bk, σ' :: R⟩ := by
  simp [lstep, h]

/-- A right move into a run of blanks – recorded or materialized, the
entered cell is blank either way.
@isnad1 id=eq.1h7v.s6.e4ce9ba719e7 from=translated src=- shape=48bd3f9e vocab=c21dd372
-/
theorem lstep_right_pad (h : simStep q σ = some (σ', q', true)) (L : List (SimSym c))
    (t : ℕ) :
    lstep ⟨q, L, σ, List.replicate t .bk⟩ =
      some ⟨q', σ' :: L, .bk, List.replicate (t - 1) .bk⟩ := by
  rcases t with - | t
  · exact lstep_right_end h L
  · exact lstep_right (h := h) L .bk (List.replicate t .bk)

/-- A left move into a run of blanks – recorded or materialized, the entered
cell is blank either way.
@isnad1 id=eq.1h7v.s6.ba5cebad9e36 from=translated src=- shape=d1d59211 vocab=e8cb98f6
-/
theorem lstep_left_pad (h : simStep q σ = some (σ', q', false)) (g : ℕ)
    (R : List (SimSym c)) :
    lstep ⟨q, List.replicate g .bk, σ, R⟩ =
      some ⟨q', List.replicate (g - 1) .bk, .bk, σ' :: R⟩ := by
  rcases g with - | g
  · exact lstep_left_end h R
  · exact lstep_left (h := h) .bk (List.replicate g .bk) R

end Steps

/-! ### Reachability -/

namespace Reach

/--
@isnad1 id=reach.0h2v.s3.d7421ecee8f0 from=translated src=- shape=f3577ae2 vocab=6beee1bb
-/
theorem refl (x : LCfg c) : Reach x x := Relation.ReflTransGen.refl

/--
@isnad1 id=reach.1h3v.s4.890e34c5c33b from=translated src=- shape=da954ed3 vocab=efbbe18f
-/
theorem single {x y : LCfg c} (h : lstep x = some y) : Reach x y :=
  Relation.ReflTransGen.single h

/--
@isnad1 id=reach.2h4v.s5.5b0d5593888f from=translated src=- shape=7bca89ef vocab=efbbe18f
-/
theorem head {x y z : LCfg c} (h : lstep x = some y) (hr : Reach y z) : Reach x z :=
  Relation.ReflTransGen.head h hr

/--
@isnad1 id=reach.2h4v.s4.3d91b4b32f00 from=translated src=- shape=de5dbc67 vocab=6beee1bb
-/
theorem trans {x y z : LCfg c} (h : Reach x y) (h' : Reach y z) : Reach x z :=
  Relation.ReflTransGen.trans h h'

end Reach

/-! ### Counted steps, and determinism -/

/-- A counted run, extended by one step at its end.
@isnad1 id=stepsto.2h5v.s5.2e9223c14b76 from=translated src=- shape=c8005018 vocab=f10d7293
-/
theorem stepsTo.trans_step : ∀ {n : ℕ} {x y z : LCfg c},
    stepsTo n x y → lstep y = some z → stepsTo (n + 1) x z := by
  intro n
  induction n with
  | zero => intro x y z hxy hyz; exact ⟨z, by rw [show x = y from hxy]; exact hyz, rfl⟩
  | succ n ih =>
    rintro x y z ⟨d, hstep, hrest⟩ hyz
    exact ⟨d, hstep, ih hrest hyz⟩

/-- Counted runs compose.
@isnad1 id=stepsto.2h6v.s5.456b91ff188d from=translated src=- shape=6828037c vocab=af00174a
-/
theorem stepsTo.trans : ∀ {n m : ℕ} {x y z : LCfg c},
    stepsTo n x y → stepsTo m y z → stepsTo (n + m) x z := by
  intro n
  induction n with
  | zero =>
    intro m x y z hxy hyz
    rw [show x = y from hxy, Nat.zero_add]
    exact hyz
  | succ n ih =>
    rintro m x y z ⟨d, hstep, hrest⟩ hyz
    rw [Nat.succ_add]
    exact ⟨d, hstep, ih hrest hyz⟩

/-- Reachability is a counted run of some length.
@isnad1 id=iff.0h3v.s4.043de15be64e from=translated src=- shape=23b633fb vocab=96f7967a
-/
theorem reach_iff_stepsTo {x y : LCfg c} : Reach x y ↔ ∃ n, stepsTo n x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hstep ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, hn.trans_step hstep⟩
  · rintro ⟨n, hn⟩
    induction n generalizing x with
    | zero => exact (show x = y from hn) ▸ Reach.refl x
    | succ n ih =>
      obtain ⟨d, hstep, hrest⟩ := hn
      exact Reach.head hstep (ih hrest)

/-- **The machine is deterministic**: a counted run to anywhere follows the
run to a terminal configuration, step for step.
@isnad1 id=stepsto.3h6v.s5.9a5b51da5130 from=translated src=- shape=ad427da2 vocab=c0bc0bf9
-/
theorem stepsTo_det : ∀ {m n : ℕ} {x y z : LCfg c},
    stepsTo m x y → stepsTo n x z → m ≤ n → stepsTo (n - m) y z := by
  intro m
  induction m with
  | zero =>
    intro n x y z hxy hxz _
    rw [Nat.sub_zero, ← show x = y from hxy]
    exact hxz
  | succ m ih =>
    rintro n x y z ⟨d, hstep, hrest⟩ hxz hmn
    rcases n with - | n
    · omega
    obtain ⟨d', hstep', hrest'⟩ := hxz
    rw [hstep] at hstep'
    obtain rfl : d = d' := Option.some_injective _ hstep'
    rw [Nat.succ_sub_succ]
    exact ih hrest hrest' (by omega)

/-- A run cannot leave a terminal configuration, so it is at least as long as
any run from the same start.
@isnad1 id=le.3h6v.s5.4c450a9ff65a from=translated src=- shape=2f275e65 vocab=879a238b
-/
theorem le_of_stepsTo_terminal : ∀ {n m : ℕ} {x y z : LCfg c},
    stepsTo n x y → lstep y = none → stepsTo m x z → m ≤ n := by
  intro n m x y z hxy hy hxz
  by_contra hcon
  have h := stepsTo_det hxy hxz (by omega)
  rcases hd : m - n with - | d
  · omega
  · rw [hd] at h
    obtain ⟨e, hstep, -⟩ := h
    rw [hy] at hstep
    exact absurd hstep (by simp)

/-! ### The walk combinators

A state that passes a set of letters unchanged in one direction crosses any
run of them. The head starts *on* the first letter of the run and ends on the
first letter beyond it; the crossed letters pile up behind the head in
reverse. -/

section Walk

variable {q : SimQ c} {P : SimSym c → Prop} {f : SimSym c → SimSym c}

/-- **Walking right** over a run of passed letters, rewriting each by `f` –
the transducing form: erasure sweeps take `f := fun _ => .bk`, unpriming
takes the unpriming map.
@isnad1 id=reach.1h11v.s7.2f19831b52bd from=translated src=- shape=013c4b82 vocab=9f18a9bd
-/
theorem reach_walkR_map (hq : ∀ σ, P σ → simStep q σ = some (f σ, q, true)) :
    ∀ (w : List (SimSym c)), (∀ σ ∈ w, P σ) → ∀ {s : SimSym c}, P s →
      ∀ (L : List (SimSym c)) (t : SimSym c) (R : List (SimSym c)),
      Reach ⟨q, L, s, w ++ t :: R⟩ ⟨q, (w.map f).reverse ++ f s :: L, t, R⟩ := by
  intro w
  induction w with
  | nil =>
    intro _ s hs L t R
    exact Reach.single (lstep_right (hq s hs) L t R)
  | cons a w ih =>
    intro hw s hs L t R
    refine Reach.head (lstep_right (hq s hs) L a (w ++ t :: R)) ?_
    have h := ih (fun σ hσ => hw σ (by simp [hσ])) (hw a (by simp)) (f s :: L) t R
    simpa using h

/-- **Walking left** over a run of passed letters, rewriting each by `f`.
@isnad1 id=reach.1h11v.s7.df4bc1734ef3 from=translated src=- shape=27566782 vocab=b51330dc
-/
theorem reach_walkL_map (hq : ∀ σ, P σ → simStep q σ = some (f σ, q, false)) :
    ∀ (w : List (SimSym c)), (∀ σ ∈ w, P σ) → ∀ {s : SimSym c}, P s →
      ∀ (t : SimSym c) (L R : List (SimSym c)),
      Reach ⟨q, w ++ t :: L, s, R⟩ ⟨q, L, t, (w.map f).reverse ++ f s :: R⟩ := by
  intro w
  induction w with
  | nil =>
    intro _ s hs t L R
    exact Reach.single (lstep_left (hq s hs) t L R)
  | cons a w ih =>
    intro hw s hs t L R
    refine Reach.head (lstep_left (hq s hs) a (w ++ t :: L) R) ?_
    have h := ih (fun σ hσ => hw σ (by simp [hσ])) (hw a (by simp)) t L (f s :: R)
    simpa using h

/-- **Walking right** over a run of passed letters, unchanged.
@isnad1 id=reach.1h10v.s7.a1c5059c52d5 from=translated src=- shape=b8f09b48 vocab=e96e285f
-/
theorem reach_walkR (hq : ∀ σ, P σ → simStep q σ = some (σ, q, true)) :
    ∀ (w : List (SimSym c)), (∀ σ ∈ w, P σ) → ∀ {s : SimSym c}, P s →
      ∀ (L : List (SimSym c)) (t : SimSym c) (R : List (SimSym c)),
      Reach ⟨q, L, s, w ++ t :: R⟩ ⟨q, w.reverse ++ s :: L, t, R⟩ := by
  intro w hw s hs L t R
  have h := reach_walkR_map (f := id) (fun σ hσ => hq σ hσ) w hw hs L t R
  simpa using h

/-- **Walking left** over a run of passed letters, unchanged.
@isnad1 id=reach.1h10v.s7.2ba8e482f19b from=translated src=- shape=9bb540e0 vocab=27d16c99
-/
theorem reach_walkL (hq : ∀ σ, P σ → simStep q σ = some (σ, q, false)) :
    ∀ (w : List (SimSym c)), (∀ σ ∈ w, P σ) → ∀ {s : SimSym c}, P s →
      ∀ (t : SimSym c) (L R : List (SimSym c)),
      Reach ⟨q, w ++ t :: L, s, R⟩ ⟨q, L, t, w.reverse ++ s :: R⟩ := by
  intro w hw s hs t L R
  have h := reach_walkL_map (f := id) (fun σ hσ => hq σ hσ) w hw hs t L R
  simpa using h

end Walk

end HaltHard

end DescriptiveComplexity
