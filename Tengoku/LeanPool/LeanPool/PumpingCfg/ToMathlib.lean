/-
Copyright (c) 2026 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/
module

public import Tengoku.LeanPool.LeanPool.PumpingCfg.ChomskyNormalForm.Basic

/-!
# Auxiliary grammar lemmas

Small facts about `ChomskyNormalFormRule.Rewrites` and `ChomskyNormalFormGrammar.Produces`
intended for upstreaming into Mathlib alongside the Chomsky-normal-form development.
-/

@[expose] public section

universe uT uN
variable {T : Type uT}

/--
@isnad1 id=false.1h5v.s5.ee42860a5e22 from=translated src=- shape=5cd88271 vocab=a934a6ba
-/
lemma ChomskyNormalFormRule.Rewrites.word {N : Type uN} {r : ChomskyNormalFormRule T N}
    {u : List T} {v : List (Symbol T N)}
    (hruv : r.Rewrites (u.map Symbol.terminal) v) :
    False := by
  induction u generalizing v with
  | nil => cases hruv
  | cons _ _ ih =>
    cases hruv with
    | cons _ _ hru => exact ih hru

/--
@isnad1 id=produces.1h3v.s6.c41cba53b866 from=translated src=- shape=7e689eac vocab=d216c2fa
-/
lemma ChomskyNormalFormGrammar.Produces.input_output
    {g : ChomskyNormalFormGrammar T} {r : ChomskyNormalFormRule T g.NT}
    (hrg : r ∈ g.rules) :
    g.Produces [.nonterminal r.input] r.output :=
  ⟨r, hrg, ChomskyNormalFormRule.Rewrites.input_output⟩
