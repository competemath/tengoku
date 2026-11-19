/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Tengoku.Seed.Algebra.Category.ModuleCat.Ext.Finite
public import Tengoku.ZanelloLc.FormalDeps.Port.Mathlib.RingTheory.Regular.Depth
public import Tengoku.Seed.RingTheory.Ideal.KrullsHeightTheorem
public import Tengoku.Seed.RingTheory.KrullDimension.Field
public import Tengoku.Seed.RingTheory.KrullDimension.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# The Ischebeck theorem and its corollary

-/

@[expose] public section
namespace Tengoku.ZanelloLc end Tengoku.ZanelloLc open Tengoku.ZanelloLc 
open IsLocalRing LinearMap ModuleCat Pointwise
open RingTheory.Sequence Ideal CategoryTheory Abelian Limits

universe u v

variable {R : Type u} [CommRing R]

lemma _root_.Tengoku.ZanelloLc.quotSMulTop_nontrivial [IsLocalRing R] {x : R} (mem : x ∈ maximalIdeal R)
    (L : Type*) [AddCommGroup L] [Module R L] [Module.Finite R L] [Nontrivial L] :
    Nontrivial (QuotSMulTop x L) := by
  apply Submodule.Quotient.nontrivial_iff.mpr (Ne.symm _)
  apply Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
  exact IsLocalRing.maximalIdeal_le_jacobson _ mem

lemma _root_.Tengoku.ZanelloLc.quotient_prime_ringKrullDim_ne_bot {P : Ideal R} (prime : P.IsPrime) :
    ringKrullDim (R ⧸ P) ≠ ⊥ :=
  ne_bot_of_le_ne_bot WithBot.zero_ne_bot
    (@ringKrullDim_nonneg_of_nontrivial _ _ (Quotient.nontrivial_iff.mpr prime.ne_top'))

end
-- Tengoku: root names of this library moved to Tengoku.ZanelloLc so they do not collide with other libraries (generated)
