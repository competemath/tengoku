/-
Copyright (c) 2026 Zachary Feng, Y. Samanda Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zachary Feng, Y. Samanda Zhang
-/
module

public import Tengoku.Flt.FLT.Slop.RepresentationTheory.OddAbsIrredSlop

/-!
# Compatibility aliases for the original odd-representation namespace

The maintained proof of the odd-representation irreducibility criterion now lives in
`FLT.Slop.RepresentationTheory.OddAbsIrredSlop`, under `Slop.OddRep`.  This file keeps the old
`Slop.OddRepOrig` names available without recompiling a duplicate copy of the same proofs.
-/

@[expose] public section

open scoped TensorProduct

open Module

namespace Slop
namespace OddRepOrig

variable {k : Type*} [Field k]
variable {G : Type*} [Monoid G]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- Compatibility alias for `Slop.OddRep.baseChange`. -/
noncomputable abbrev baseChange (l : Type*) [Field l] [Algebra k l]
    (ρ : Representation k G V) : Representation l G (l ⊗[k] V) :=
  _root_.Slop.OddRep.baseChange l ρ

/-- Compatibility alias for `Slop.OddRep.adjoinRange`. -/
abbrev adjoinRange (ρ : Representation k G V) : Subalgebra k (Module.End k V) :=
  _root_.Slop.OddRep.adjoinRange ρ

/-- Compatibility alias for `Slop.OddRep.IsAbsolutelyIrreducible`. -/
abbrev IsAbsolutelyIrreducible (ρ : Representation k G V) : Prop :=
  _root_.Slop.OddRep.IsAbsolutelyIrreducible ρ

/--
@isnad1 id=iff.0h4v.s9.ee9ab3a4a683 from=translated src=- shape=acc18368 vocab=4ca320c0
-/
lemma isIrreducible_iff_forall (ρ : Representation k G V) :
    ρ.IsIrreducible ↔
      Nontrivial V ∧
        ∀ W : Submodule k V, (∀ g : G, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤ :=
  _root_.Slop.OddRep.isIrreducible_iff_forall ρ

/--
@isnad1 id=iff.1h5v.s11.59e3f97529da from=translated src=- shape=af3884d9 vocab=eea0d307
-/
lemma smul_tmul_mem_range_iff (l : Type*) [Field l] [Algebra k l]
    {e : V} (he : e ≠ 0) (c : l) :
    c ⊗ₜ[k] e ∈ LinearMap.range (TensorProduct.mk k l V 1) ↔
      ∃ a : k, algebraMap k l a = c :=
  _root_.Slop.OddRep.smul_tmul_mem_range_iff l he c

/--
@isnad1 id=ex.3h6v.s10.911bf5e300bb from=translated src=- shape=a26c1e84 vocab=a2d4531c
-/
lemma exists_smul_eq_of_commute
    (ρ : Representation k G V)
    (hirr : ρ.IsIrreducible)
    {g : G} (hg : finrank k (Module.End.eigenspace (ρ g) 1) = 1)
    (T : Module.End k V) (hT : ∀ h : G, Commute (ρ h) T) :
    ∃ μ : k, T = μ • (1 : Module.End k V) :=
  _root_.Slop.OddRep.exists_smul_eq_of_commute ρ hirr hg T hT

/--
@isnad1 id=eq.2h4v.s10.25f4b0f6fed0 from=translated src=- shape=1995d9f2 vocab=b46cad1b
-/
lemma adjoinRange_eq_top (ρ : Representation k G V) [FiniteDimensional k V]
    (hirr : ρ.IsIrreducible)
    (hEnd : ∀ T : Module.End k V, (∀ h : G, Commute (ρ h) T) →
      ∃ μ : k, T = μ • (1 : Module.End k V)) :
    adjoinRange ρ = ⊤ :=
  _root_.Slop.OddRep.adjoinRange_eq_top ρ hirr hEnd

/--
@isnad1 id=eq.1h5v.s13.c472fc868850 from=translated src=- shape=d83e686f vocab=e3003816
-/
lemma adjoinRange_baseChange_eq_top (ρ : Representation k G V) [FiniteDimensional k V]
    (l : Type*) [Field l] [Algebra k l]
    (h : adjoinRange ρ = ⊤) :
    adjoinRange (baseChange l ρ) = ⊤ :=
  _root_.Slop.OddRep.adjoinRange_baseChange_eq_top ρ l h

/--
@isnad1 id=isirredu.1h4v.s10.2d3b29e41014 from=translated src=- shape=76ad7d3d vocab=a8274bc7
-/
lemma isIrreducible_of_adjoinRange_eq_top (ρ : Representation k G V) [Nontrivial V]
    (h : adjoinRange ρ = ⊤) :
    ρ.IsIrreducible :=
  _root_.Slop.OddRep.isIrreducible_of_adjoinRange_eq_top ρ h

/--
@isnad1 id=isirredu.1h5v.s7.0ef8d279d2e8 from=translated src=- shape=6acd91b5 vocab=a2f6be18
-/
lemma isIrreducible_of_baseChange (ρ : Representation k G V)
    (l : Type*) [Field l] [Algebra k l]
    (h : (baseChange l ρ).IsIrreducible) :
    ρ.IsIrreducible :=
  _root_.Slop.OddRep.isIrreducible_of_baseChange ρ l h

/--
@isnad1 id=isirredu.2h6v.s10.5c9e7a8d07a4 from=translated src=- shape=255cac6c vocab=c3d87a5f
-/
theorem isIrreducible_baseChange_of_finrank_eigenspace_eq_one
    (ρ : Representation k G V) [FiniteDimensional k V]
    (l : Type*) [Field l] [Algebra k l]
    (hirr : ρ.IsIrreducible)
    {g : G} (hg : finrank k (Module.End.eigenspace (ρ g) 1) = 1) :
    (baseChange l ρ).IsIrreducible :=
  _root_.Slop.OddRep.isIrreducible_baseChange_of_finrank_eigenspace_eq_one ρ l hirr hg

/--
@isnad1 id=iff.1h5v.s9.62edc2d409a2 from=translated src=- shape=60435193 vocab=db822d45
-/
theorem isIrreducible_iff_isAbsolutelyIrreducible
    (ρ : Representation k G V) [FiniteDimensional k V]
    {g : G} (hg : finrank k (Module.End.eigenspace (ρ g) 1) = 1) :
    ρ.IsIrreducible ↔ IsAbsolutelyIrreducible ρ :=
  _root_.Slop.OddRep.isIrreducible_iff_isAbsolutelyIrreducible_slop ρ hg

end OddRepOrig
end Slop
