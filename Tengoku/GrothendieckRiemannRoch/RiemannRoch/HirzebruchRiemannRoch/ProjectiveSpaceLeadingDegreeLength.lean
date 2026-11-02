/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.LocalOrdSymmetry
import Tengoku.Seed.RingTheory.Ideal.AssociatedPrime.Finiteness
import Tengoku.Seed.RingTheory.Support

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The length formula for a hyperplane section (module form of Fulton, Lemma A.2.7)

Algebraic core of gate G2 of `LeadingCycleGate` (`notes/agents/G2TDEG-status.md`): for a
finitely generated module `M` over a noetherian ring `B` and `b ∈ B` such that every prime of the
support of `M` is either one of the finitely many "components" `q ∈ T` or a maximal ideal, and such
that `b` lies only in maximal primes of the support,

`ℓ(M/bM) + Σ_q ℓ(M_q)·ℓ(ker b|B/q) = ℓ(ker b|M) + Σ_q ℓ(M_q)·ℓ((B/q)/b)`   (`devissage_module`),

with `ℓ(M_q)` the length over `B_q` (`lengthAt`).  In particular, if `b` is a nonzerodivisor on `M`
and lies in no `q ∈ T`, `ℓ(M/bM) = Σ_q ℓ(M_q) · ord_{B/q}(b)` (`chiCoker_eq_sum_ord`): the
coefficient at a codimension-one point `W` of `[F/bF]` is the coefficient at `W` of
`Σ_V ℓ(F_V) div(b|_V)`, i.e. of `c₁(O(1)) ∩ [F]`.

The cyclic case is `AlgebraicGeometry.Chow.LocalOrdSymmetry.devissage`; here we pass to modules
with Mathlib's prime filtrations (`IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`).
-/

set_option autoImplicit false

noncomputable section

universe u v

open AlgebraicGeometry.Chow.LocalOrdSymmetry

namespace RRC.ProjectiveSpaceLeadingDegree.LengthFormula

variable {B : Type u} [CommRing B] [IsNoetherianRing B]

/-- A finitely generated module supported at maximal ideals has finite length.-/
theorem length_ne_top_of_support_maximal (N : Type v) [AddCommGroup N] [Module B N]
    [hN : Module.Finite B N] (h : ∀ p ∈ Module.support B N, p.asIdeal.IsMaximal) :
    Module.length B N ≠ ⊤ := by
  revert h
  induction hN using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime B with
  | subsingleton N =>
    intro _
    rw [Module.length_eq_zero]
    exact ENat.zero_ne_top
  | quotient N p e =>
    intro h
    have hp : p ∈ Module.support B N := by
      rw [e.support_eq, Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
    haveI := h p hp
    haveI : IsSimpleModule B (B ⧸ p.asIdeal) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
    rw [e.length_eq, Module.length_eq_one_iff.mpr inferInstance]
    exact ENat.one_ne_top
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro h
    rw [Module.length_eq_add_of_exact f g hf hg hfg]
    exact WithTop.add_ne_top.mpr
      ⟨h₁ fun p hp ↦ h p (Module.support_subset_of_injective f hf hp),
        h₃ fun p hp ↦ h p (Module.support_subset_of_surjective g hg hp)⟩

omit [IsNoetherianRing B] in
/-- A module killed by `b` is supported on `V(b)`.-/
theorem mem_of_mem_support_of_smul_eq_zero {N : Type v} [AddCommGroup N] [Module B N] {b : B}
    (hb : ∀ m : N, b • m = 0) {p : PrimeSpectrum B} (hp : p ∈ Module.support B N) :
    b ∈ p.asIdeal := by
  by_contra hbp
  exact (Module.notMem_support_iff'.mpr fun m ↦ ⟨b, hbp, hb m⟩) hp

variable (b : B)

/-- `chiKer b N` and `chiCoker b N` are finite when `b` only lies in maximal primes of `Supp N`.-/
theorem chi_ne_top (N : Type v) [AddCommGroup N] [Module B N] [Module.Finite B N]
    (hfin : ∀ p ∈ Module.support B N, b ∈ p.asIdeal → p.asIdeal.IsMaximal) :
    chiKer b N ≠ ⊤ ∧ chiCoker b N ≠ ⊤ := by
  constructor
  · refine length_ne_top_of_support_maximal _ fun p hp ↦ ?_
    have hp' : p ∈ Module.support B N :=
      Module.support_subset_of_injective _ (Submodule.subtype_injective _) hp
    refine hfin p hp' (mem_of_mem_support_of_smul_eq_zero (fun m ↦ ?_) hp)
    exact Subtype.ext (LinearMap.mem_ker.mp m.2)
  · refine length_ne_top_of_support_maximal _ fun p hp ↦ ?_
    have hp' : p ∈ Module.support B N :=
      Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _) hp
    refine hfin p hp' (mem_of_mem_support_of_smul_eq_zero (fun m ↦ ?_) hp)
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ m
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩

end RRC.ProjectiveSpaceLeadingDegree.LengthFormula
