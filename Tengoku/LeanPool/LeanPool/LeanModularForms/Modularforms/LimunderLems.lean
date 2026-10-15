/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Tengoku
import Tengoku.LeanPool.LeanPool.LeanModularForms.Modularforms.IccIcoLems

/-! # LimunderLems -/

@[expose] public section

open TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

/--
@isnad1 id=eq.2h3v.s7.b71324f0301d from=translated src=- shape=bc012973 vocab=e194e216
-/
lemma limUnder_add {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f g : α → ℂ)
    (hf : CauchySeq f) (hg : CauchySeq g) :
    (limUnder atTop f) + (limUnder atTop g) = limUnder atTop (f + g) := by
  nth_rw 3 [Filter.Tendsto.limUnder_eq]
  exact (hf.tendsto_limUnder).add (hg.tendsto_limUnder)

/--
@isnad1 id=eq.1h3v.s6.5fc9f5003054 from=translated src=- shape=c9205a4a vocab=d2c40dbf
-/
lemma limUnder_mul_const {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f : α → ℂ)
    (hf : CauchySeq f) (c : ℂ) :
    c * (limUnder atTop f)= limUnder atTop (c • f) := by
  nth_rw 2 [Filter.Tendsto.limUnder_eq]
  exact (hf.tendsto_limUnder).const_mul c

/--
@isnad1 id=eq.2h3v.s7.d048c0c014c0 from=translated src=- shape=bc012973 vocab=34ed4ab8
-/
lemma limUnder_sub {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f g : α → ℂ)
    (hf : CauchySeq f) (hg : CauchySeq g) :
    (limUnder atTop f) - (limUnder atTop g) = limUnder atTop (f - g) := by
  nth_rw 3 [Filter.Tendsto.limUnder_eq]
  exact (hf.tendsto_limUnder).sub (hg.tendsto_limUnder)

/--
@isnad1 id=eq.3h2v.s6.1d15550ea60b from=translated src=- shape=8bd8ac26 vocab=770ddb29
-/
lemma limUnder_congr_eventually (f g : ℕ → ℂ) (h : ∀ᶠ n in atTop, f n = g n)
  (hf : CauchySeq f) (hg : CauchySeq g) :
  limUnder atTop f = limUnder atTop g := by
  have h0 := CauchySeq.tendsto_limUnder hf
  have h1 := CauchySeq.tendsto_limUnder hg
  rw [Filter.Tendsto.limUnder_eq (x := (limUnder atTop f)) ]
  · rw [Filter.Tendsto.limUnder_eq ]
    apply Filter.Tendsto.congr' _ h1
    symm
    apply h
  exact h0
