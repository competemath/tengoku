/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
module

public import Tengoku.LeanPool.LeanPool.MRiscX.Hoare.HoareCore
public import Tengoku
import Std.Tactic.BVDecide.Normalize.Prop

/-!
This file contains some minor lemmas to ease the prove in the "main" file "HoareRules".
Also, those lemmas can be used to deepen the understanding of the weak function.
-/

@[expose] public section
local notation:60 "(" k " ↦ "v"; "m")" => TMap.put k v m


/--
@isnad1 id=weak.1h6v.s5.20fbc85fc3f3 from=translated src=- shape=ac3ef74a vocab=e16e3d7b
-/
theorem weak_with_less_BL_weakens : ∀ (s s' : MState) (L_w L_b L : Set UInt64) (c : Code),
  weak s s' L_w L_b c →
  weak s s' L_w (L_b \ L) c
  := by
  intros s s' L_w L_b L c
  unfold weak
  intro H HCode
  specialize H HCode
  rcases H with ⟨n', ⟨H1, H2, H3, H4⟩⟩
  grind only [= Set.mem_union, = Set.mem_sdiff]

/--
@isnad1 id=weak.2h6v.s5.26084fb213fa from=translated src=- shape=8e5af46d vocab=9117e19d
-/
theorem weak_L_w_with_L_from_L_b : ∀ (s s' : MState) (L_w L_b L : Set UInt64) (c : Code),
  L ⊆ L_b →
  weak s s' L_w L_b c →
  weak s s' (L_w ∪ L) (L_b \ L) c
  := by
  intros s s' L_w L_b L c T
  unfold weak
  intro H HCode
  specialize H HCode
  rcases H with ⟨n', ⟨H1, H2, H3, H4⟩⟩
  grind only [= Set.subset_def, = Set.mem_union, = Set.mem_sdiff]

/-- Loop-style weakening relation used in proving the loop Hoare rule: from state
`s` at label `l`, the invariant `I` is maintained until the condition `C` is met. -/
def weakLoop (s : MState) (l : UInt64) (C I : Assertion) :=
  ∃(n:ℕ), 0 < n → (s.runNSteps n).pc = l ∧
  (∀ (n' : ℕ), 0 < n' ∧ n' < n →
  (s.runNSteps n').pc = l →
  I (s.runNSteps n')) ∧
  ¬C (s.runNSteps n) ∧ I (s.runNSteps n)
