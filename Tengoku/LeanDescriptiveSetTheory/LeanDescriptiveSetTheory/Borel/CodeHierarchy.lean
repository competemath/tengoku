/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.Hierarchy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Borel-code hierarchy bounds

This file proves the countable-ordinal exhaustion theorem for the Borel hierarchy.  The hierarchy
uses the project's one-based convention: open and closed sets occur at level one, and level zero is
empty.  Every Borel code is placed in an ambiguous level strictly below `ω₁`; the particular
construction-rank bound used by the proof remains private because it is not a least pointclass rank.

The argument only needs perfect normality.  It therefore applies in particular to Polish spaces,
without restricting the public theorem to Baire or Cantor space.
-/

open Cardinal Ordinal Set

universe u

namespace DescriptiveSetTheory

variable {X : Type u} [TopologicalSpace X]

/-- A multiplicative Borel class embeds in the next additive class.
@isnad1 id=ordinals.1h3v.s5.f4b0c3f11fa7 from=translated src=- shape=b204919b vocab=ef5c7afd
-/
theorem OrdinalPi0.toSigma0_succ {i : Ordinal.{0}} {s : Set X} (hs : OrdinalPi0 i s) :
    OrdinalSigma0 (i + 1) s := by
  by_cases hi : i = 0
  · subst i
    exact (ordinalPi0_zero s hs).elim
  have h1i : (1 : Ordinal) ≤ i := Order.one_le_iff_ne_zero.mpr hi
  have h1succ : (1 : Ordinal) < i + 1 := h1i.trans_lt (lt_add_one i)
  refine (ordinalSigma0_of_ne_zero_one (ne_of_gt (zero_lt_one.trans h1succ))
    (ne_of_gt h1succ)).2 ⟨fun _ => s, fun _ => ⟨i, lt_add_one i⟩, fun _ => hs, ?_⟩
  ext x
  simp

/-- An additive Borel class embeds in the next multiplicative class.
@isnad1 id=ordinalp.1h3v.s5.053ef37d9b70 from=translated src=- shape=b204919b vocab=ef5c7afd
-/
theorem OrdinalSigma0.toPi0_succ {i : Ordinal.{0}} {s : Set X} (hs : OrdinalSigma0 i s) :
    OrdinalPi0 (i + 1) s := by
  exact (ordinalSigma0_compl_iff_pi0 (i + 1) s).1 hs.compl.toSigma0_succ

namespace BorelCode

section PerfectlyNormal

variable [PerfectlyNormalSpace X]

private theorem eval_mem_delta_bound (c : BorelCode X) :
    OrdinalDelta0 ((c.constructionRank + 1) + 1) c.eval := by
  induction c with
  | basic U =>
      change OrdinalDelta0 (((0 : Ordinal) + 1) + 1) (U : Set X)
      have hsigma : OrdinalSigma0 (2 : Ordinal) (U : Set X) :=
        (ordinalSigma0_one_iff.2 U.property).mono (by norm_num)
      have hpi : OrdinalPi0 (2 : Ordinal) (U : Set X) :=
        ordinalPi0_two_iff_isGδ.2 U.property.isGδ
      rw [zero_add, one_add_one_eq_two]
      change OrdinalSigma0 2 (U : Set X) ∧ OrdinalPi0 2 (U : Set X)
      exact ⟨hsigma, hpi⟩
  | empty =>
      change OrdinalDelta0 (((0 : Ordinal) + 1) + 1) (∅ : Set X)
      have hdelta : OrdinalDelta0 (2 : Ordinal) (∅ : Set X) :=
        ⟨ordinalSigma0_of_isClopen (by norm_num) isOpen_empty isClosed_empty,
          ordinalPi0_of_isClopen (by norm_num) isOpen_empty isClosed_empty⟩
      simpa only [zero_add, one_add_one_eq_two] using hdelta
  | compl c ih =>
      have hle : (c.constructionRank + 1) + 1 ≤ ((c.constructionRank + 1) + 1) + 1 :=
        le_of_lt (lt_add_one _)
      change OrdinalDelta0 (((c.constructionRank + 1) + 1) + 1)
        (GeneratedCode.eval c)ᶜ
      exact ih.compl.mono hle
  | iUnion c ih =>
      let r := GeneratedCode.constructionRank (.iUnion c)
      have hsigma : OrdinalSigma0 (r + 1) (⋃ n, GeneratedCode.eval (c n)) := by
        apply OrdinalSigma0.iUnion
        intro n
        apply (ih n).1.mono
        have hn : GeneratedCode.constructionRank (c n) + 1 ≤ r :=
          Order.add_one_le_iff.mpr (GeneratedCode.constructionRank_lt_iUnion c n)
        exact add_le_add_left hn 1
      have hdelta : OrdinalDelta0 ((r + 1) + 1) (⋃ n, GeneratedCode.eval (c n)) :=
        ⟨hsigma.mono (le_of_lt (lt_add_one _)), hsigma.toPi0_succ⟩
      change OrdinalDelta0 ((r + 1) + 1) (⋃ n, GeneratedCode.eval (c n))
      exact hdelta

/-- Every Borel code denotes a set in some ambiguous countable Borel level.
@isnad1 id=ex.0h2v.s6.e258c3a33a3a from=translated src=- shape=b0d84ed6 vocab=4502372b
-/
theorem exists_countable_ordinalDelta0 (c : BorelCode X) :
    ∃ i : Ordinal.{0}, i < ω₁ ∧ OrdinalDelta0 i c.eval := by
  refine ⟨(c.constructionRank + 1) + 1, ?_, eval_mem_delta_bound c⟩
  exact (isSuccLimit_omega 1).succ_lt ((isSuccLimit_omega 1).succ_lt
    c.constructionRank_lt_omega_one)

end PerfectlyNormal

end BorelCode

/-- Every Borel subset of a perfectly normal space lies in an ambiguous level below `ω₁`.
@isnad1 id=ex.1h2v.s6.8321ad2c49bb from=translated src=- shape=e3021283 vocab=ea943b40
-/
theorem borelMeasurableSet_exists_countable_ordinalDelta0 [PerfectlyNormalSpace X]
    {s : Set X} (hs : @MeasurableSet X (borel X) s) :
    ∃ i : Ordinal.{0}, i < ω₁ ∧ OrdinalDelta0 i s := by
  obtain ⟨c, rfl⟩ := BorelCode.borelMeasurableSet_iff_exists_code.1 hs
  exact c.exists_countable_ordinalDelta0

/-- In a Borel measurable space with perfectly normal topology, every measurable set lies in an
ambiguous countable Borel level.
@isnad1 id=ex.1h2v.s6.91b57b39f5b5 from=translated src=- shape=96312338 vocab=c72a1ab4
-/
theorem MeasurableSet.exists_countable_ordinalDelta0 [m : MeasurableSpace X] [BorelSpace X]
    [PerfectlyNormalSpace X] {s : Set X} (hs : MeasurableSet s) :
    ∃ i : Ordinal.{0}, i < ω₁ ∧ OrdinalDelta0 i s := by
  have h : m = borel X := BorelSpace.measurable_eq
  rw [h] at hs
  exact borelMeasurableSet_exists_countable_ordinalDelta0 hs

end DescriptiveSetTheory
