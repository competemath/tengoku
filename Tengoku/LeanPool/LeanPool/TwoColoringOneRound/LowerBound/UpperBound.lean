/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.LocalRule
public import Tengoku

/-!
## Upper bounds (explicit colorings)

The main formalized result of this project is a *lower bound*: every coloring has at least
`23.879%` monochromatic edges when `n = 1_000_000`.

This file provides small explicit *upper bounds* (i.e. constructions of colorings with relatively
few monochromatic edges), to complement the lower bounds.

The coloring used here is the simple rounding-based local rule from the report:

* round each symbol `a : Fin n` to a bit `r(a)` depending on whether `a < n/2`;
* apply a fixed local rule `g` to the rounded bits.
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace UpperBound

open scoped BigOperators
open LocalRule

/-- The cardinality of a 4-way disjunction subtype is bounded by the sum of the parts. -/
private lemma card_or4_le {α : Type*} [Fintype α] (p q r s : α → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r] [DecidablePred s] :
    Fintype.card {e : α // p e ∨ q e ∨ r e ∨ s e} ≤
      Fintype.card {e : α // p e} +
        (Fintype.card {e : α // q e} +
          (Fintype.card {e : α // r e} + Fintype.card {e : α // s e})) := by
  refine le_trans (Fintype.card_subtype_or (p := p) (q := fun e => q e ∨ r e ∨ s e)) ?_
  refine Nat.add_le_add_left ?_ _
  refine le_trans (Fintype.card_subtype_or (p := q) (q := fun e => r e ∨ s e)) ?_
  exact Nat.add_le_add_left (Fintype.card_subtype_or (p := r) (q := s)) _

/-!
### `n = 9`

We use the rounding threshold `4`, so `Small = {0,1,2,3}` and `Big = {4,5,6,7,8}`.
The resulting coloring has monochromatic fraction exactly `13/63 ≈ 20.63%`.
-/

namespace N9

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := 9
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Sym9 := Sym n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Coloring9 := Coloring n

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev two9 : Sym9 := ⟨4, by decide⟩
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Small9 : Type := Set.Iio two9
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Big9 : Type := Set.Ici two9

/--
@isnad1 id=eq.0h0v.s4.4555303f599e from=translated src=- shape=b0ae1d2b vocab=e82e5607
-/
lemma card_Small9 : Fintype.card Small9 = 4 := by simp [Small9, two9]

/--
@isnad1 id=eq.0h0v.s4.3019fc39a4ea from=translated src=- shape=b0ae1d2b vocab=15fcc5cf
-/
lemma card_Big9 : Fintype.card Big9 = 5 := by
  -- `simp` reduces the card to `n - 4`, then `decide` finishes.
  simpa [Big9, two9] using (by decide : (n - 4 : Nat) = 5)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def round9 (a : Sym9) : Bool :=
  decide (two9 ≤ a)

/--
@isnad1 id=iff.0h1v.s3.fcdf33a0d9cf from=translated src=- shape=b1284c08 vocab=19e1bd2d
-/
@[simp] lemma round9_eq_true {a : Sym9} : round9 a = true ↔ two9 ≤ a := by simp [round9]

/--
@isnad1 id=iff.0h1v.s3.11054cc71b7e from=translated src=- shape=37892c9f vocab=4c9b27d0
-/
@[simp] lemma round9_eq_false {a : Sym9} : round9 a = false ↔ a < two9 := by simp [round9, not_le]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev f9 : Coloring9 :=
  fun v => g (round9 (Vertex.a v)) (round9 (Vertex.b v)) (round9 (Vertex.c v))

private abbrev pat0000 : Edge n → Prop := EdgePatterns.Pat0000 (two := two9)
private abbrev pat1111 : Edge n → Prop := EdgePatterns.Pat1111 (two := two9)
private abbrev pat1001 : Edge n → Prop := EdgePatterns.Pat1001 (two := two9)
private abbrev pat0110 : Edge n → Prop := EdgePatterns.Pat0110 (two := two9)

private lemma monochromatic_iff_patterns (e : Edge n) :
    Edge.monochromatic f9 e ↔ pat0000 e ∨ pat1111 e ∨ pat1001 e ∨ pat0110 e := by
  simpa [f9, pat0000, pat1111, pat1001, pat0110] using
    (LocalRule.monochromatic_iff_patterns (round := round9) (two := two9)
      (hr_true := fun a => round9_eq_true (a := a))
      (hr_false := fun a => round9_eq_false (a := a))
      (e := e))

private abbrev Edge0000 : Type := {e : Edge n // pat0000 e}
private abbrev Edge1111 : Type := {e : Edge n // pat1111 e}
private abbrev Edge1001 : Type := {e : Edge n // pat1001 e}
private abbrev Edge0110 : Type := {e : Edge n // pat0110 e}

private lemma card_edge0000 : Fintype.card Edge0000 = 24 := by
  have h : Fintype.card Edge0000 = (Fintype.card Small9).descFactorial 4 :=
    EdgePatterns.card_pat0000 (n := n) (two := two9)
  simp_all

private lemma card_edge1111 : Fintype.card Edge1111 = 120 := by
  have h : Fintype.card Edge1111 = (Fintype.card Big9).descFactorial 4 :=
    EdgePatterns.card_pat1111 (n := n) (two := two9)
  rw [h, card_Big9]
  decide

private lemma card_edge1001 : Fintype.card Edge1001 = 240 := by
  have h : Fintype.card Edge1001 =
      (Fintype.card Big9).descFactorial 2 * (Fintype.card Small9).descFactorial 2 :=
    EdgePatterns.card_pat1001 (n := n) (two := two9)
  rw [h, card_Big9, card_Small9]
  decide

private lemma card_edge0110 : Fintype.card Edge0110 = 240 := by
  have h : Fintype.card Edge0110 =
      (Fintype.card Big9).descFactorial 2 * (Fintype.card Small9).descFactorial 2 :=
    EdgePatterns.card_pat0110 (n := n) (two := two9)
  rw [h, card_Big9, card_Small9]
  decide

private lemma edgeCount_9 : edgeCount n = 3024 := by
  classical
  have : edgeCount n = (9 : Nat).descFactorial 4 := by
    have : Fintype.card (Edge n) = Fintype.card (Fin 4 ↪ Sym n) :=
      Fintype.card_congr
        { toFun := fun e => ⟨e.1, e.2⟩
          invFun := fun x => ⟨x, x.injective⟩
          left_inv := by intro e; apply Subtype.ext; funext i; rfl
          right_inv := by intro x; ext i; rfl }
    have hcongr : edgeCount n = Fintype.card (Fin 4 ↪ Sym n) := by simpa [edgeCount] using this
    simp [hcongr, Sym, n, Fintype.card_embedding_eq]
  exact this.trans (by decide : (9 : Nat).descFactorial 4 = 3024)

/--
@isnad1 id=le.0h0v.s4.9d8b96b691e5 from=translated src=- shape=8dc2642f vocab=70da6575
-/
theorem monoFraction_f9_le_13_63 : monoFraction f9 ≤ (13 : ℚ) / 63 := by
  classical
  -- Upper bound `monoCount` by summing the four pattern counts.
  have hmonoCount :
      monoCount f9 = Fintype.card {e : Edge n // Edge.monochromatic f9 e} := by
    simpa [monoCount, monoEdges] using
      (Fintype.card_subtype (α := Edge n) (p := Edge.monochromatic f9)).symm
  have hEquiv :
      {e : Edge n // Edge.monochromatic f9 e}
        ≃ {e : Edge n // pat0000 e ∨ pat1111 e ∨ pat1001 e ∨ pat0110 e} :=
    Equiv.subtypeEquivRight (fun e => monochromatic_iff_patterns (e := e))
  have hmonoPatterns :
      monoCount f9 =
        Fintype.card {e : Edge n // pat0000 e ∨ pat1111 e ∨ pat1001 e ∨ pat0110 e} := by
    simpa [hmonoCount] using (Fintype.card_congr hEquiv)
  have hUnion :
      Fintype.card {e : Edge n // pat0000 e ∨ pat1111 e ∨ pat1001 e ∨ pat0110 e}
        ≤
          Fintype.card Edge0000
            + (Fintype.card Edge1111 + (Fintype.card Edge1001 + Fintype.card Edge0110)) := by
    dsimp only [Edge0000, Edge1111, Edge1001, Edge0110]
    exact card_or4_le pat0000 pat1111 pat1001 pat0110
  have hmonoNat : monoCount f9 ≤ 624 := by
    have : monoCount f9 ≤
        Fintype.card Edge0000
          + (Fintype.card Edge1111 + (Fintype.card Edge1001 + Fintype.card Edge0110)) := by
      simpa [hmonoPatterns] using hUnion
    simpa [card_edge0000, card_edge1111, card_edge1001, card_edge0110, Nat.add_assoc] using this
  have hcount : (monoCount f9 : ℚ) ≤ (624 : ℚ) := by exact_mod_cast hmonoNat
  have hE : (edgeCount n : ℚ) = 3024 := by exact_mod_cast edgeCount_9
  -- Divide both sides by `edgeCount`.
  have hdiv : monoFraction f9 ≤ (624 : ℚ) / (edgeCount n : ℚ) := by
    have hEpos : (0 : ℚ) ≤ (edgeCount n : ℚ) := by exact_mod_cast (Nat.zero_le (edgeCount n))
    simpa [monoFraction] using (div_le_div_of_nonneg_right hcount hEpos)
  have hred : (624 : ℚ) / (edgeCount n : ℚ) = (13 : ℚ) / 63 := by
    simp [hE, show (624 : ℚ) / 3024 = (13 : ℚ) / 63 by norm_num]
  simpa [hred] using hdiv

/--
@isnad1 id=ex.0h0v.s4.01d53bb2b144 from=translated src=- shape=b16fd8db vocab=dca324c2
-/
theorem exists_coloring_monoFraction_le_13_63 : ∃ f : Coloring9, monoFraction f ≤ (13 : ℚ) / 63 :=
  ⟨f9, monoFraction_f9_le_13_63⟩

end N9

/-!
### A clean universal upper bound (`≤ 1/4` for all `n ≥ 5`)

We give an explicit coloring (the same rounding-based rule as above) and show its monochromatic-edge
fraction is at most `1/4` for every `n ≥ 5`.
-/

namespace Universal

open scoped BigOperators

variable {n : Nat}

-- We assume `n ≥ 5` throughout this section.
variable (hn : 5 ≤ n)

/-- The rounding threshold `⌊n/2⌋`, viewed as an element of `Fin n`. -/
abbrev two (n : Nat) (hn : 5 ≤ n) : Sym n :=
  ⟨n / 2, Nat.div_lt_self (lt_of_lt_of_le (by decide : 0 < 5) hn) (by decide : 1 < 2)⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Small (n : Nat) (hn : 5 ≤ n) : Type := EdgePatterns.Small (two := two n hn)
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Big (n : Nat) (hn : 5 ≤ n) : Type := EdgePatterns.Big (two := two n hn)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def round (n : Nat) (hn : 5 ≤ n) (a : Sym n) : Bool :=
  decide (two n hn ≤ a)

/--
@isnad1 id=iff.1h2v.s5.7a50ea3a14b5 from=translated src=- shape=ed31a940 vocab=0369e597
-/
@[simp] lemma round_eq_true {a : Sym n} :
    round (n := n) hn a = true ↔ two n hn ≤ a := by
  simp [round]

/--
@isnad1 id=iff.1h2v.s5.49508ea61356 from=translated src=- shape=fbc9ed57 vocab=8ded100d
-/
@[simp] lemma round_eq_false {a : Sym n} :
    round (n := n) hn a = false ↔ a < two n hn := by
  simp [round, not_le]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev f (n : Nat) (hn : 5 ≤ n) : Coloring n :=
  fun v =>
    g (round n hn (Vertex.a v)) (round n hn (Vertex.b v)) (round n hn (Vertex.c v))

private abbrev pat0000 : Edge n → Prop := EdgePatterns.Pat0000 (two := two n hn)
private abbrev pat1111 : Edge n → Prop := EdgePatterns.Pat1111 (two := two n hn)
private abbrev pat1001 : Edge n → Prop := EdgePatterns.Pat1001 (two := two n hn)
private abbrev pat0110 : Edge n → Prop := EdgePatterns.Pat0110 (two := two n hn)

private abbrev Edge0000 : Type := {e : Edge n // pat0000 (n := n) hn e}
private abbrev Edge1111 : Type := {e : Edge n // pat1111 (n := n) hn e}
private abbrev Edge1001 : Type := {e : Edge n // pat1001 (n := n) hn e}
private abbrev Edge0110 : Type := {e : Edge n // pat0110 (n := n) hn e}

end Universal

end UpperBound

end Distributed2Coloring.LowerBound
