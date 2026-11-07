/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Tengoku.Cslib.Cslib.Computability.Machines.Turing.MultiTape.Configuration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Tapes holding words and configurations of such tapes

The normal form in which "tape transformer" machines (cf. `TransformsTapes.lean`) start and finish:
every work tape holds a word in the cells `0, 1, …` and is blank everywhere else, with every head
at the start.

## Main definitions

* `Turing.tapeOfList`: the tape holding exactly a given word.
* `Turing.wordsCfg`: the configuration whose tapes hold given words.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/-- A tape containing exactly the symbols of `xs` at positions `0, ..., xs.length - 1`.-/
def tapeOfList (xs : List Symbol) : ℤ → Option Symbol
  | .ofNat n => xs[n]?
  | .negSucc _ => none

/--
@isnad1 id=eq.0h3v.s5.e9c18d73052b from=translated src=- shape=3250666a vocab=74b801ee
-/
@[simp]
lemma tapeOfList_ofNat (xs : List Symbol) (n : ℕ) : tapeOfList xs n = xs[n]? := rfl

/--
@isnad1 id=eq.0h3v.s4.c4468c6e4c57 from=translated src=- shape=3c58f2d9 vocab=af00495a
-/
@[simp]
lemma tapeOfList_negSucc (xs : List Symbol) (n : ℕ) :
    tapeOfList xs (.negSucc n) = none := rfl

/-- Appending one symbol writes precisely the cell after the existing word.
@isnad1 id=eq.0h3v.s5.0992910f208b from=translated src=- shape=35595b23 vocab=4083302b
-/
lemma tapeOfList_append_single (xs : List Symbol) (x : Symbol) :
    tapeOfList (xs ++ [x]) = Function.update (tapeOfList xs) (xs.length : ℤ) (some x) := by
  funext z
  cases z with
  | negSucc n => simp [tapeOfList]
  | ofNat n => grind [tapeOfList]

/-- A cell of `tapeOfList xs` is blank exactly outside the positions `0, …, xs.length - 1`.
@isnad1 id=iff.0h3v.s5.a5ac14e49429 from=translated src=- shape=a59c4e86 vocab=3cffd6ed
-/
lemma tapeOfList_eq_none_iff (xs : List Symbol) (z : ℤ) :
    tapeOfList xs z = none ↔ z < 0 ∨ (xs.length : ℤ) ≤ z := by
  cases z <;> simp

/-- The blank tape holds the empty word.
@isnad1 id=eq.0h1v.s3.91155bc89fac from=translated src=- shape=f02618de vocab=f40a04da
-/
@[simp]
lemma tapeOfList_nil : tapeOfList ([] : List Symbol) = fun _ => none := by
  funext z
  cases z <;> simp

/-- The cell at position `0` holds the first symbol of the word.
@isnad1 id=eq.0h2v.s4.7f9cdf82ff97 from=translated src=- shape=4c01aa78 vocab=91e59739
-/
lemma tapeOfList_zero (xs : List Symbol) : tapeOfList xs 0 = xs.head? := by
  have h : (0 : ℤ) = ((0 : ℕ) : ℤ) := rfl
  rw [h, tapeOfList_ofNat]
  cases xs <;> rfl

/-- The configuration whose work tape `i` holds exactly the word `ws i` with its head at the
start, whose input head is at the start of the input, in state `q` with output `out`.-/
@[simps]
def wordsCfg (input : List Symbol) (q : Option State)
    (ws : Fin k → List Symbol) (out : List Symbol) : Cfg k Symbol State input :=
  ⟨q, 1, fun i => tapeOfList (ws i), fun _ => 0, out⟩

/-- Remapping the state of a `wordsCfg` remaps its state and leaves the words alone.
@isnad1 id=eq.0h9v.s5.a92983ae2903 from=translated src=- shape=b6696d43 vocab=2c800ed0
-/
@[simp]
lemma mapState_wordsCfg {State' : Type*} (φ : Option State → Option State')
    (input : List Symbol) (q : Option State) (ws : Fin k → List Symbol) (out : List Symbol) :
    (wordsCfg input q ws out).mapState φ = wordsCfg input (φ q) ws out := rfl

/-- Changing the state of a `wordsCfg` leaves the words alone.
@isnad1 id=eq.0h9v.s5.f1e675ea4453 from=translated src=- shape=9ed8a5e2 vocab=141d36e1
-/
@[simp]
lemma withState_wordsCfg {State' : Type*} (input : List Symbol) (q : Option State)
    (ws : Fin k → List Symbol) (out : List Symbol) (q' : Option State') :
    (wordsCfg input q ws out).withState q' = wordsCfg input q' ws out := rfl

/-- The initial configuration is the word configuration with blank tapes and no output.
@isnad1 id=eq.0h5v.s5.e95cdba66ac3 from=translated src=- shape=4bd972df vocab=537c4e7d
-/
lemma Cfg.init_eq_wordsCfg (q₀ : State) (input : List Symbol) :
    Cfg.init (k := k) q₀ input = wordsCfg input (some q₀) (fun _ => []) [] := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i
  simp [Cfg.init, wordsCfg]

end Turing
