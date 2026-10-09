/-
Copyright (c) 2026 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker, Yongxi Lin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.RingTheory.Finiteness.Cofinite
public import Tengoku.Seed.Algebra.Module.Submodule.EqLocus

/-!
# `HasFiniteRange` predicate on linear maps, and the associated equivalence relation

In this file, we define:

* `LinearMap.HasFiniteRange`: a predicate expressing that a linear map has finitely generated range.
* `LinearMap.HasNoetherianRange`: a predicate expressing that a linear map has noetherian range,
  i.e, all submodules of the range are finitely generated. This should be thought of as the
  "better behaved" version of `LinearMap.HasFiniteRange`: for example, `HasNoetherianRange`
  is always stable by addition, whereas `HasFiniteRange` might not be. The two notions agree
  over noetherian rings (hence, in particular, over fields).
* `LinearMap.finiteRange`: the submodule of `E →ₗ[K] F` consisting of linear maps with
  *noetherian* ranges. We allow ourself this slightly abusive name because the more natural
  definition (the submodule of linear maps with finitely generated ranges) only makes sense over a
  noetherian ring, in which case the two notions agree.
* `LinearMap.FiniteRangeSetoid.setoid`: the setoid on `E →ₗ[K] F` associated to
  `LinearMap.finiteRange`. This identifies linear maps which differ by a linear map with
  noetherian range. Equivalently, two linear maps are equivalent for this
  relation if and only if they agree on a subspace `A` of the domain such that `E ⧸ A` is
  noetherian. As with `LinearMap.finiteRange`, we allow ourself a slightly abusive name because the
  more natural definition in terms of `LinearMap.HasFiniteRange` is only well behaved over a
  noetherian ring, in which case the two notions agree.
  This is an instance in the scope `LinearMap.FiniteRangeSetoid`,
  so opening this scope allows this relation to be denoted by `≈`.
* `LinearMap.IsQuasiInverse`: two linear maps `u` and `v` are **quasi-inverses** if we have
  `u ∘ₗ v ≈ id` and `v ∘ₗ u ≈ id` modulo linear maps with noetherian ranges.

-/

@[expose] public section

open LinearMap Submodule Module

namespace LinearMap

variable {K V V₂ V₃ : Type*}

section Semiring

variable [Semiring K]
  [AddCommMonoid V] [Module K V]
  [AddCommMonoid V₂] [Module K V₂]
  [AddCommMonoid V₃] [Module K V₃]

/-- A linear map **has Noetherian range** if its range is a Noetherian module. -/
def HasNoetherianRange (f : V →ₗ[K] V₂) : Prop :=
  IsNoetherian K f.range

/-- A linear map **has finite range** if its range is finitely generated. -/
def HasFiniteRange (f : V →ₗ[K] V₂) : Prop :=
  f.range.FG

/--
@isnad1 id=iff.0h4v.s7.5a0f400ba4a3 from=seed src=0 shape=33e8123f vocab=a0de9c69
-/
lemma hasNoetherianRange_iff_range {f : V →ₗ[K] V₂} :
    f.HasNoetherianRange ↔ IsNoetherian K f.range :=
  Iff.rfl

/--
@isnad1 id=iff.0h4v.s6.e55181d1b73d from=seed src=0 shape=af252f80 vocab=47b5ad6d
-/
lemma hasFiniteRange_iff_range {f : V →ₗ[K] V₂} :
    f.HasFiniteRange ↔ f.range.FG :=
  Iff.rfl

/--
@isnad1 id=isnoethe.1h4v.s7.a5350b6fae66 from=seed src=0 shape=a0d5f7b6 vocab=a0de9c69
-/
alias ⟨HasNoetherianRange.isNoetherian_range, _⟩ := hasNoetherianRange_iff_range
/--
@isnad1 id=fg.1h4v.s6.fded6a97ce60 from=seed src=0 shape=ff0da7ad vocab=47b5ad6d
-/
alias ⟨HasFiniteRange.fg_range, _⟩ := hasFiniteRange_iff_range

/--
@isnad1 id=hasfinit.1h4v.s6.6e5da0f060d1 from=seed src=0 shape=b898131c vocab=518bb08b
-/
lemma HasNoetherianRange.hasFiniteRange {u : V →ₗ[K] V₂} (h : u.HasNoetherianRange) :
    u.HasFiniteRange :=
  have := h.isNoetherian_range; FG.of_finite

/--
@isnad1 id=hasnoeth.0h3v.s6.f4b76244df68 from=seed src=0 shape=923a5d08 vocab=a457e3b1
-/
@[simp] lemma HasNoetherianRange.zero : (0 : V →ₗ[K] V₂).HasNoetherianRange := by
  simp [HasNoetherianRange, isNoetherian_submodule, Submodule.fg_bot]

/--
@isnad1 id=hasfinit.0h3v.s6.98c1ceaf8ba5 from=seed src=0 shape=923a5d08 vocab=14a86ed4
-/
@[simp] lemma HasFiniteRange.zero : (0 : V →ₗ[K] V₂).HasFiniteRange :=
  HasNoetherianRange.zero.hasFiniteRange

/--
@isnad1 id=hasnoeth.1h6v.s6.89136b7b710c from=seed src=0 shape=8b23632d vocab=68ed1ce0
-/
lemma HasNoetherianRange.comp_left {u : V →ₗ[K] V₂} (h : u.HasNoetherianRange)
    (v : V₂ →ₗ[K] V₃) : (v ∘ₗ u).HasNoetherianRange := by
  rw [LinearMap.HasNoetherianRange, LinearMap.range_comp] at *
  infer_instance

/--
@isnad1 id=hasfinit.1h6v.s6.629582938b90 from=seed src=0 shape=8b23632d vocab=cb2575e7
-/
lemma HasFiniteRange.comp_left {u : V →ₗ[K] V₂} (h : u.HasFiniteRange)
    (v : V₂ →ₗ[K] V₃) : (v ∘ₗ u).HasFiniteRange := by
  rw [LinearMap.HasFiniteRange, LinearMap.range_comp] at *
  exact Submodule.FG.map v h

/--
@isnad1 id=hasnoeth.0h4v.s5.f24a043ed894 from=seed src=0 shape=73df72b9 vocab=e264dd24
-/
@[simp] lemma HasNoetherianRange.of_isNoetherian_dom [IsNoetherian K V] {f : V →ₗ[K] V₂} :
    f.HasNoetherianRange :=
  hasNoetherianRange_iff_range.mpr inferInstance

/--
@isnad1 id=hasfinit.0h4v.s5.bd0357d081e8 from=seed src=0 shape=73df72b9 vocab=a36cc5c7
-/
@[simp] lemma HasFiniteRange.of_finite_dom [Module.Finite K V] {f : V →ₗ[K] V₂} :
    f.HasFiniteRange := by
  simp [HasFiniteRange]

/--
@isnad1 id=hasnoeth.0h4v.s5.5a69e63650fa from=seed src=0 shape=ec9e8d92 vocab=e264dd24
-/
@[simp] lemma HasNoetherianRange.of_isNoetherian_rng [IsNoetherian K V₂] {f : V →ₗ[K] V₂} :
    f.HasNoetherianRange :=
  hasNoetherianRange_iff_range.mpr inferInstance

/--
@isnad1 id=hasfinit.0h4v.s5.6bef8d029f5a from=seed src=0 shape=ec9e8d92 vocab=47c77aaf
-/
@[simp] lemma HasFiniteRange.of_isNoetherian_rng [IsNoetherian K V₂] {f : V →ₗ[K] V₂} :
    f.HasFiniteRange :=
  HasNoetherianRange.of_isNoetherian_rng.hasFiniteRange

end Semiring

section Ring

variable [Ring K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

/--
@isnad1 id=hasnoeth.1h4v.s6.2f12a439c009 from=seed src=0 shape=4f42e446 vocab=f42a0689
-/
lemma HasFiniteRange.hasNoetherianRange [IsNoetherianRing K] {u : V →ₗ[K] V₂}
    (h : u.HasFiniteRange) : u.HasNoetherianRange := by
  rw [HasNoetherianRange]
  have := Finite.of_fg h.fg_range
  infer_instance

/--
@isnad1 id=iff.0h4v.s6.fb07dd66e78b from=seed src=0 shape=490a1f19 vocab=f42a0689
-/
lemma hasNoetherianRange_iff_hasFiniteRange [IsNoetherianRing K] {u : V →ₗ[K] V₂} :
    u.HasNoetherianRange ↔ u.HasFiniteRange :=
  ⟨HasNoetherianRange.hasFiniteRange, HasFiniteRange.hasNoetherianRange⟩

/--
@isnad1 id=hasnoeth.1h6v.s7.b93605f59bbc from=seed src=0 shape=d073b450 vocab=b8dcf5e9
-/
lemma HasNoetherianRange.comp_right {v : V₂ →ₗ[K] V₃} (h : v.HasNoetherianRange)
    (u : V →ₗ[K] V₂) : (v ∘ₗ u).HasNoetherianRange := by
  rw [HasNoetherianRange, LinearMap.range_comp] at *
  exact isNoetherian_of_le map_le_range

/--
@isnad1 id=hasfinit.1h6v.s7.fc62ca3acbbd from=seed src=0 shape=7de0b51f vocab=3fc03ecd
-/
lemma HasFiniteRange.comp_right [IsNoetherianRing K] {v : V₂ →ₗ[K] V₃} (h : v.HasFiniteRange)
    (u : V →ₗ[K] V₂) : (v ∘ₗ u).HasFiniteRange :=
  h.hasNoetherianRange.comp_right _ |>.hasFiniteRange

/--
@isnad1 id=hasnoeth.1h4v.s7.22359dbc3d08 from=seed src=0 shape=263038b6 vocab=c23af111
-/
@[simp] lemma HasNoetherianRange.neg {f : V →ₗ[K] V₂}
    (hf : f.HasNoetherianRange) : (-f).HasNoetherianRange := by
  rwa [HasNoetherianRange, LinearMap.range_neg]

/--
@isnad1 id=hasfinit.1h4v.s7.a5ba3730b6a9 from=seed src=0 shape=263038b6 vocab=72f0ab44
-/
@[simp] lemma HasFiniteRange.neg {f : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) : (-f).HasFiniteRange := by
  rwa [HasFiniteRange, LinearMap.range_neg]

/--
@isnad1 id=hasnoeth.2h5v.s8.088b6a318ae1 from=seed src=0 shape=99b0622b vocab=eec50837
-/
@[simp] lemma HasNoetherianRange.add {f g : V →ₗ[K] V₂}
    (hf : f.HasNoetherianRange) (hg : g.HasNoetherianRange) : (f + g).HasNoetherianRange := by
  rw [HasNoetherianRange] at *
  exact isNoetherian_of_le (range_add_le f g)

/--
@isnad1 id=hasfinit.2h5v.s8.5671bf02b0f2 from=seed src=0 shape=6da743c1 vocab=cab0d9fd
-/
@[simp] lemma HasFiniteRange.add [IsNoetherianRing K] {f g : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) (hg : g.HasFiniteRange) : (f + g).HasFiniteRange :=
  hf.hasNoetherianRange.add hg.hasNoetherianRange |>.hasFiniteRange

/--
@isnad1 id=hasnoeth.2h5v.s8.ed4f5149991b from=seed src=0 shape=99b0622b vocab=38fc5a4d
-/
@[simp] lemma HasNoetherianRange.sub {f g : V →ₗ[K] V₂}
    (hf : f.HasNoetherianRange) (hg : g.HasNoetherianRange) : (f - g).HasNoetherianRange :=
  sub_eq_add_neg f g ▸ hf.add hg.neg

/--
@isnad1 id=hasfinit.2h5v.s8.1f9fd4bc60d3 from=seed src=0 shape=6da743c1 vocab=31dc1d1e
-/
@[simp] lemma HasFiniteRange.sub [IsNoetherianRing K] {f g : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) (hg : g.HasFiniteRange) : (f - g).HasFiniteRange :=
  sub_eq_add_neg f g ▸ hf.add hg.neg

/--
@isnad1 id=iff.0h4v.s7.cfd3276ecb6f from=seed src=0 shape=55b26e08 vocab=06dd9fcf
-/
theorem hasNoetherianRange_iff_quotient_ker {f : V →ₗ[K] V₂} :
    f.HasNoetherianRange ↔ IsNoetherian K (V ⧸ f.ker) :=
  f.quotKerEquivRange.isNoetherian_iff.symm

/--
@isnad1 id=iff.0h4v.s6.79289a86669e from=seed src=0 shape=662afbc6 vocab=58a12708
-/
@[simp]
theorem ker_coFG_iff_hasFiniteRange {f : V →ₗ[K] V₂} :
    f.ker.CoFG ↔ f.HasFiniteRange :=
  range_fg_iff_ker_cofg.symm

/--
@isnad1 id=isnoethe.1h4v.s7.59f3ac53f2a1 from=seed src=0 shape=eac6a204 vocab=06dd9fcf
-/
alias ⟨HasNoetherianRange.quotient_ker, _⟩ := hasNoetherianRange_iff_quotient_ker
/--
@isnad1 id=cofg.1h4v.s6.abe57fdb0926 from=seed src=0 shape=174d32b2 vocab=58a12708
-/
alias ⟨_, HasFiniteRange.cofg_ker⟩ := ker_coFG_iff_hasFiniteRange

end Ring

section CommRing

variable [CommRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

/--
@isnad1 id=hasnoeth.1h5v.s8.14a1841e167e from=seed src=0 shape=81ecb6fa vocab=50fd3e7e
-/
@[simp] lemma HasNoetherianRange.smul {f : V →ₗ[K] V₂}
    (hf : f.HasNoetherianRange) (c : K) : (c • f).HasNoetherianRange :=
  hf.comp_left (lsmul K V₂ c)

/--
@isnad1 id=hasfinit.1h5v.s8.543044fd86d8 from=seed src=0 shape=81ecb6fa vocab=148cb7d5
-/
@[simp] lemma HasFiniteRange.smul {f : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) (c : K) : (c • f).HasFiniteRange :=
  hf.comp_left (lsmul K V₂ c)

variable (K V V₂) in
/-- `LinearMap.finiteRange` is the submodule of `V →ₗ[K] W` consisting of linear maps satisfying
`LinearMap.HasNoetherianRange`. We allow ourself this slightly abusive name because the set of
linear maps satisfying `LinearMap.HasFiniteRange` is only a submodule over a noetherian ring,
in which case the two notions agree. -/
def finiteRange : Submodule K (V →ₗ[K] V₂) where
  carrier := {u | u.HasNoetherianRange}
  add_mem' hu hv := by simp_all
  zero_mem' := by simp
  smul_mem' c hu := by simp_all

/--
@isnad1 id=iff.0h4v.s8.9be008c4d6c8 from=seed src=0 shape=cefca370 vocab=acd6b400
-/
lemma mem_finiteRange_iff_hasNoetherianRange {f : V →ₗ[K] V₂} :
    f ∈ finiteRange K V V₂ ↔ f.HasNoetherianRange :=
  Iff.rfl

/--
@isnad1 id=iff.0h4v.s8.a01fb56f2d9a from=seed src=0 shape=1a67d07c vocab=008ee08b
-/
lemma mem_finiteRange_iff_hasFiniteRange [IsNoetherianRing K] {f : V →ₗ[K] V₂} :
    f ∈ finiteRange K V V₂ ↔ f.HasFiniteRange := by
  rw [mem_finiteRange_iff_hasNoetherianRange, hasNoetherianRange_iff_hasFiniteRange]

end CommRing

section Setoid

variable [CommRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

namespace FiniteRangeSetoid

/-- This is the equivalence relation on linear maps such that `u ≈ v` precisely
when `u - v` is a linear map with noetherian range. We allow ourself this slightly abusive name
because the more natural definition (`u - v` has finitely generated range) only yields a
well-behaved relation (more precisely, an additive congruence relation compatible with composition
on both sides) over a noetherian ring, in which case the two notions agree.

This setoid is declared as an instance in scope `LinearMap.FiniteRangeSetoid`. -/
scoped instance setoid : Setoid (V →ₗ[K] V₂) := (LinearMap.finiteRange K V V₂).quotientRel

/--
@isnad1 id=iff.0h5v.s8.d2715444caa7 from=seed src=0 shape=9e4303c6 vocab=42d21174
-/
lemma equiv_iff_hasNoetherianRange {u v : V →ₗ[K] V₂} : u ≈ v ↔ (u - v).HasNoetherianRange :=
  Submodule.quotientRel_def _

/--
@isnad1 id=iff.0h5v.s8.e3c38c8019de from=seed src=0 shape=bc7042b5 vocab=163f1121
-/
lemma equiv_iff_hasFiniteRange [IsNoetherianRing K] {u v : V →ₗ[K] V₂} :
    u ≈ v ↔ (u - v).HasFiniteRange := by
  rw [equiv_iff_hasNoetherianRange, hasNoetherianRange_iff_hasFiniteRange]

/--
@isnad1 id=iff.0h4v.s8.e0915d64c01f from=seed src=0 shape=718b0eb5 vocab=c9f4e561
-/
lemma equiv_zero_iff_hasNoetherianRange {u : V →ₗ[K] V₂} : u ≈ 0 ↔ u.HasNoetherianRange := by
  simp [equiv_iff_hasNoetherianRange]

alias ⟨_, _root_.LinearMap.HasNoetherianRange.equiv_zero⟩ := equiv_zero_iff_hasNoetherianRange

/--
@isnad1 id=iff.0h4v.s8.878a1f08de46 from=seed src=0 shape=de72badd vocab=474affe3
-/
lemma equiv_zero_iff_hasFiniteRange [IsNoetherianRing K] {u : V →ₗ[K] V₂} :
    u ≈ 0 ↔ u.HasFiniteRange := by
  simp [equiv_iff_hasFiniteRange]

alias ⟨_, _root_.LinearMap.HasFiniteRange.equiv_zero⟩ := equiv_zero_iff_hasFiniteRange

/--
@isnad1 id=iff.0h5v.s8.8a70707a54c6 from=seed src=0 shape=29aea88b vocab=b0649d5d
-/
lemma equiv_iff_isNoetherian_quotient_eqLocus {u v : V →ₗ[K] V₂} :
    u ≈ v ↔ IsNoetherian K (V ⧸ eqLocus u v) := by
  rw [equiv_iff_hasNoetherianRange, hasNoetherianRange_iff_quotient_ker, eqLocus_eq_ker_sub]

/--
@isnad1 id=iff.0h5v.s7.9445075e7817 from=seed src=0 shape=8cfbb03e vocab=2c941f25
-/
lemma equiv_iff_eqLocus_coFG [IsNoetherianRing K] {u v : V →ₗ[K] V₂} :
    u ≈ v ↔ (eqLocus u v).CoFG := by
  rw [eqLocus_eq_ker_sub, ker_coFG_iff_hasFiniteRange, equiv_iff_hasFiniteRange]

/--
@isnad1 id=equiv.1h6v.s8.b1e167424b17 from=seed src=0 shape=b2a10a16 vocab=973e4785
-/
lemma equiv_of_eqOn_of_isNoetherian {u v : V →ₗ[K] V₂} (A : Submodule K V)
    [quot_A_noeth : IsNoetherian K (V ⧸ A)] (eqOn_A : Set.EqOn u v A) : u ≈ v := by
  have A_le : A ≤ eqLocus u v := le_eqLocus.mpr eqOn_A
  rw [equiv_iff_isNoetherian_quotient_eqLocus]
  refine isNoetherian_of_surjective (A.mapQ (eqLocus u v) id A_le) (by simp [range_mapQ])

/--
@isnad1 id=equiv.2h6v.s8.0036547d1e97 from=seed src=0 shape=211fe54d vocab=4dc4f0e3
-/
lemma equiv_of_eqOn_coFG [IsNoetherianRing K] {u v : V →ₗ[K] V₂} {A : Submodule K V}
    (A_coFG : A.CoFG) (eqOn_A : Set.EqOn u v A) : u ≈ v :=
  equiv_iff_eqLocus_coFG.mpr <| A_coFG.of_le <| le_eqLocus.mpr eqOn_A

/--
@isnad1 id=equiv.0h8v.s8.82313ef7bfa1 from=seed src=0 shape=82863564 vocab=0887ad57
-/
@[gcongr]
lemma equiv_comp_right {u : V →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃} (h' : v ≈ v') :
    v ∘ₗ u ≈ v' ∘ₗ u := by
  rw [equiv_iff_hasNoetherianRange] at *
  exact h'.comp_right u

/--
@isnad1 id=equiv.0h8v.s8.708ad92ee072 from=seed src=0 shape=0df35fac vocab=0887ad57
-/
@[gcongr]
lemma equiv_comp_left {u v : V →ₗ[K] V₂} {u' : V₂ →ₗ[K] V₃} (h : u ≈ v) :
    u' ∘ₗ u ≈ u' ∘ₗ v := by
  rw [equiv_iff_hasNoetherianRange] at *
  simpa only [LinearMap.comp_sub] using h.comp_left u'

/--
@isnad1 id=equiv.0h10v.s9.8e1eff9c69ff from=seed src=0 shape=d201448d vocab=0887ad57
-/
lemma equiv_comp {u v : V →ₗ[K] V₂} {u' v' : V₂ →ₗ[K] V₃} (h : u ≈ v) (h' : u' ≈ v') :
    u' ∘ₗ u ≈ v' ∘ₗ v := by
  grw [equiv_comp_right h', equiv_comp_left h]

/--
@isnad1 id=iff.1h4v.s8.39426ae1c56b from=seed src=0 shape=ec679d99 vocab=ee860f4a
-/
lemma projection_equiv_zero_iff_isNoetherian {S T : Submodule K V} (hST : IsCompl S T) :
    S.projection T hST ≈ 0 ↔ IsNoetherian K S := by
  rw [equiv_zero_iff_hasNoetherianRange, hasNoetherianRange_iff_range, range_projection]

/--
@isnad1 id=equiv.1h4v.s8.9d2dfbbdc2f1 from=seed src=0 shape=bc12a341 vocab=ee860f4a
-/
lemma projection_equiv_zero {S T : Submodule K V} [IsNoetherian K S] (hST : IsCompl S T) :
    S.projection T hST ≈ 0 :=
  projection_equiv_zero_iff_isNoetherian hST |>.mpr inferInstance

/--
@isnad1 id=iff.1h4v.s8.8d2fc779240c from=seed src=0 shape=1948e22d vocab=2ed5d7c6
-/
lemma projection_equiv_id_iff_isNoetherian {S T : Submodule K V} (hST : IsCompl S T) :
    S.projection T hST ≈ id ↔ IsNoetherian K T := by
  rw [Setoid.comm, equiv_iff_hasNoetherianRange, ← projection_eq_id_sub_projection,
    hasNoetherianRange_iff_range, range_projection]

/--
@isnad1 id=equiv.1h4v.s8.34c4017e9c81 from=seed src=0 shape=749702da vocab=2ed5d7c6
-/
lemma projection_equiv_id {S T : Submodule K V} [IsNoetherian K T] (hST : IsCompl S T) :
    S.projection T hST ≈ id :=
  projection_equiv_id_iff_isNoetherian hST |>.mpr inferInstance

end FiniteRangeSetoid

end Setoid

section QuasiInverse

variable [CommRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

open scoped LinearMap.FiniteRangeSetoid

/-- `u` is a **left quasi-inverse** to `v` if `u ∘ₗ v ≈ id` modulo
linear maps with noetherian ranges. Recall that if the scalar ring is noetherian
(e.g a field), then "noetherian range" can be replaced by "finitely generated range". -/
def IsLeftQuasiInverse (u : V →ₗ[K] V₂) (v : V₂ →ₗ[K] V) : Prop :=
  u ∘ₗ v ≈ .id

/-- `u` is a **right quasi-inverse** to `v` if `v ∘ₗ u ≈ id` modulo
linear maps with noetherian ranges. Recall that if the scalar ring is noetherian
(e.g a field), then "noetherian range" can be replaced by "finitely generated range". -/
def IsRightQuasiInverse (u : V₃ →ₗ[K] V₂) (v : V₂ →ₗ[K] V₃) : Prop :=
  v ∘ₗ u ≈ .id

/-- `u` is a **quasi-inverse** to `v` if `u ∘ₗ v ≈ id` and `v ∘ₗ u ≈ id` modulo
linear maps with noetherian ranges. Recall that if the scalar ring is noetherian
(e.g a field), then "noetherian range" can be replaced by "finitely generated range". -/
def IsQuasiInverse (u : V₃ →ₗ[K] V₂) (v : V₂ →ₗ[K] V₃) : Prop :=
  u.IsLeftQuasiInverse v ∧ u.IsRightQuasiInverse v

/--
@isnad1 id=iff.0h5v.s7.881e20923a4b from=seed src=0 shape=30d0da3d vocab=cf5ea03d
-/
lemma isLeftQuasiInverse_iff_isRightQuasiInverse_swap {u : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} :
    u.IsLeftQuasiInverse v ↔ v.IsRightQuasiInverse u := Iff.rfl

alias ⟨IsLeftQuasiInverse.isRightQuasiInverse, IsRightQuasiInverse.isLeftQuasiInverse⟩ :=
  isLeftQuasiInverse_iff_isRightQuasiInverse_swap

/--
@isnad1 id=equiv.1h5v.s8.8b8dc149e989 from=seed src=0 shape=ac82906b vocab=215bdd06
-/
lemma IsLeftQuasiInverse.equiv {u : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    (h : u.IsLeftQuasiInverse v) : u ∘ₗ v ≈ .id := h

/--
@isnad1 id=equiv.1h5v.s8.af552c3cd887 from=seed src=0 shape=b004f265 vocab=1ab469d7
-/
lemma IsRightQuasiInverse.equiv {u : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    (h : u.IsRightQuasiInverse v) : v ∘ₗ u ≈ .id := h

lemma _root_.LinearEquiv.isQuasiInverse (e : V ≃ₗ[K] V₂) :
    e.symm.IsQuasiInverse e := by
  simp [IsQuasiInverse, IsLeftQuasiInverse, IsRightQuasiInverse]

/--
@isnad1 id=isquasii.1h5v.s7.aad2fcebaf6a from=seed src=0 shape=c4ddcace vocab=157fbdfd
-/
@[symm]
lemma IsQuasiInverse.symm {u : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    (h : u.IsQuasiInverse v) : v.IsQuasiInverse u :=
  And.symm h

/--
@isnad1 id=isleftqu.1h9v.s8.049f7de97243 from=seed src=0 shape=b81df6f9 vocab=b0ebc59c
-/
@[gcongr]
lemma IsLeftQuasiInverse.congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.IsLeftQuasiInverse v) (hu : u' ≈ u) (hv : v' ≈ v) :
    u'.IsLeftQuasiInverse v' := by
  unfold IsLeftQuasiInverse at *
  grw [hu, hv]
  assumption

/--
@isnad1 id=iff.0h9v.s8.0098b189cc86 from=seed src=0 shape=88463c5c vocab=b0ebc59c
-/
@[gcongr]
lemma isLeftQuasiInverse_congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (hu : u' ≈ u) (hv : v' ≈ v) :
    u.IsLeftQuasiInverse v ↔ u'.IsLeftQuasiInverse v' :=
  ⟨fun H ↦ H.congr hu hv, fun H ↦ H.congr (Setoid.symm hu) (Setoid.symm hv)⟩

/--
@isnad1 id=isrightq.1h9v.s8.4eccaa33483c from=seed src=0 shape=d602300a vocab=4ae6803a
-/
@[gcongr]
lemma IsRightQuasiInverse.congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.IsRightQuasiInverse v) (hu : u' ≈ u) (hv : v' ≈ v) :
    u'.IsRightQuasiInverse v' :=
  h.isLeftQuasiInverse.congr hv hu |>.isRightQuasiInverse

/--
@isnad1 id=iff.0h9v.s8.c359cfa643f0 from=seed src=0 shape=0a9af869 vocab=4ae6803a
-/
lemma isRightQuasiInverse_congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (hu : u' ≈ u) (hv : v' ≈ v) :
    u.IsRightQuasiInverse v ↔ u'.IsRightQuasiInverse v' :=
  ⟨fun H ↦ H.congr hu hv, fun H ↦ H.congr (Setoid.symm hu) (Setoid.symm hv)⟩

/--
@isnad1 id=isquasii.1h9v.s8.e5d97c7f5321 from=seed src=0 shape=d602300a vocab=739384ef
-/
@[gcongr]
lemma IsQuasiInverse.congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.IsQuasiInverse v) (hu : u' ≈ u) (hv : v' ≈ v) :
    u'.IsQuasiInverse v' :=
  ⟨h.1.congr hu hv, h.2.congr hu hv⟩

/--
@isnad1 id=iff.0h9v.s8.b94a8bc79183 from=seed src=0 shape=0a9af869 vocab=739384ef
-/
lemma isQuasiInverse_congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (hu : u' ≈ u) (hv : v' ≈ v) :
    u.IsQuasiInverse v ↔ u'.IsQuasiInverse v' := by
  simp [IsQuasiInverse, isLeftQuasiInverse_congr hu hv, isRightQuasiInverse_congr hu hv]

/--
@isnad1 id=equiv.2h8v.s8.379fa27cc47b from=seed src=0 shape=553d0540 vocab=739384ef
-/
lemma IsQuasiInverse.equiv_of_left {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.IsQuasiInverse v) (h' : u'.IsQuasiInverse v') (hu : u ≈ u') :
    v ≈ v' := by
  calc
    v = v ∘ₗ .id := by simp
    _ ≈ v ∘ₗ (u' ∘ₗ v') := by grw [h'.1.equiv]
    _ ≈ v ∘ₗ (u ∘ₗ v') := by grw [hu]
    _ = (v ∘ₗ u) ∘ₗ v' := by rw [comp_assoc]
    _ ≈ .id ∘ₗ v' := by grw [h.2.equiv]
    _ = v' := by simp

/--
@isnad1 id=equiv.2h8v.s8.549a20497f45 from=seed src=0 shape=0feb93c4 vocab=739384ef
-/
lemma IsQuasiInverse.equiv_of_right {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.IsQuasiInverse v) (h' : u'.IsQuasiInverse v') (hv : v ≈ v') :
    u ≈ u' :=
  h.symm.equiv_of_left h'.symm hv

/-- Left quasi-inverses compose in the opposite order.
@isnad1 id=isleftqu.2h8v.s8.65bd241e3895 from=seed src=0 shape=fe7db1a3 vocab=81808630
-/
lemma IsLeftQuasiInverse.comp {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V}
    {v' : V₃ →ₗ[K] V₂} (hu : u'.IsLeftQuasiInverse u) (hv : v'.IsLeftQuasiInverse v) :
    (u' ∘ₗ v').IsLeftQuasiInverse (v ∘ₗ u) :=
  calc
    _ = u' ∘ₗ (v' ∘ₗ v) ∘ₗ u := rfl
    _ ≈ u' ∘ₗ .id ∘ₗ u := by grw [hv.equiv]
    _ ≈ .id := hu.equiv

/-- Right quasi-inverses compose in the opposite order.
@isnad1 id=isrightq.2h8v.s8.56a7ae24cdf1 from=seed src=0 shape=e2b7ee96 vocab=efec5284
-/
lemma IsRightQuasiInverse.comp {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V}
    {v' : V₃ →ₗ[K] V₂} (hu : u'.IsRightQuasiInverse u) (hv : v'.IsRightQuasiInverse v) :
    (u' ∘ₗ v').IsRightQuasiInverse (v ∘ₗ u) :=
  hv.isLeftQuasiInverse.comp hu.isLeftQuasiInverse |>.isRightQuasiInverse

/-- Quasi-inverses compose in the opposite order.
@isnad1 id=isquasii.2h8v.s8.5739365c3c51 from=seed src=0 shape=e2b7ee96 vocab=abada906
-/
lemma IsQuasiInverse.comp {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V}
    {v' : V₃ →ₗ[K] V₂} (hu : u'.IsQuasiInverse u) (hv : v'.IsQuasiInverse v) :
    (u' ∘ₗ v').IsQuasiInverse (v ∘ₗ u) :=
  ⟨hu.1.comp hv.1, hu.2.comp hv.2⟩

/-- If `u'` is a right quasi-inverse of `u` and `w` is a left quasi-inverse of `v ∘ₗ u`,
then `u ∘ₗ w` is a left quasi-inverse of `v`.
@isnad1 id=isleftqu.2h8v.s8.654734dfffc9 from=seed src=0 shape=4a7e2e21 vocab=ad1134f5
-/
lemma IsLeftQuasiInverse.of_comp_left {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {u' : V₂ →ₗ[K] V} {w : V₃ →ₗ[K] V} (hu : u'.IsRightQuasiInverse u)
    (hw : w.IsLeftQuasiInverse (v ∘ₗ u)) :
    (u ∘ₗ w).IsLeftQuasiInverse v := by
  calc
    _ = ((u ∘ₗ w) ∘ₗ v) ∘ₗ .id := rfl
    _ ≈ ((u ∘ₗ w) ∘ₗ v) ∘ₗ (u ∘ₗ u') := by grw [hu.equiv]
    _ = u ∘ₗ (w ∘ₗ (v ∘ₗ u)) ∘ₗ u' := rfl
    _ ≈ u ∘ₗ .id ∘ₗ u' := by grw [hw.equiv]
    _ ≈ .id := hu.equiv

/-- If `u'` is a quasi-inverse of `u` and `w` is a quasi-inverse of `v ∘ₗ u`, then
`u ∘ₗ w` is a quasi-inverse of `v`.
@isnad1 id=isquasii.2h8v.s8.ba1846c6ffb9 from=seed src=0 shape=4b71bdcc vocab=abada906
-/
lemma IsQuasiInverse.of_comp_left {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {u' : V₂ →ₗ[K] V} {w : V₃ →ₗ[K] V} (hu : u'.IsQuasiInverse u)
    (hw : w.IsQuasiInverse (v ∘ₗ u)) :
    (u ∘ₗ w).IsQuasiInverse v :=
  ⟨.of_comp_left hu.2 hw.1, hw.2⟩

/-- If `v'` is a left quasi-inverse of `v` and `w` is a right quasi-inverse of `v ∘ₗ u`,
then `w ∘ₗ v` is a right quasi-inverse of `u`.
@isnad1 id=isrightq.2h8v.s8.e19d167ddf0a from=seed src=0 shape=c6f315ad vocab=ad1134f5
-/
lemma IsRightQuasiInverse.of_comp_right {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {v' : V₃ →ₗ[K] V₂} {w : V₃ →ₗ[K] V} (hv : v'.IsLeftQuasiInverse v)
    (hw : w.IsRightQuasiInverse (v ∘ₗ u)) :
    (w ∘ₗ v).IsRightQuasiInverse u := by
  calc
    _ = .id ∘ₗ (u ∘ₗ (w ∘ₗ v)) := rfl
    _ ≈ (v' ∘ₗ v) ∘ₗ (u ∘ₗ (w ∘ₗ v)) := by grw [hv.equiv]
    _ = v' ∘ₗ ((v ∘ₗ u) ∘ₗ w) ∘ₗ v := rfl
    _ ≈ v' ∘ₗ .id ∘ₗ v := by grw [hw.equiv]
    _ ≈ .id := hv.equiv

/-- If `v'` is a quasi-inverse of `v` and `w` is a quasi-inverse of `v ∘ₗ u`, then
`w ∘ₗ v` is a quasi-inverse of `u`.
@isnad1 id=isquasii.2h8v.s8.e032fd31854e from=seed src=0 shape=ce9f02be vocab=abada906
-/
lemma IsQuasiInverse.of_comp_right {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {v' : V₃ →ₗ[K] V₂} {w : V₃ →ₗ[K] V} (hv : v'.IsQuasiInverse v)
    (hw : w.IsQuasiInverse (v ∘ₗ u)) :
    (w ∘ₗ v).IsQuasiInverse u :=
  ⟨hw.1, IsRightQuasiInverse.of_comp_right hv.1 hw.2⟩

/--
@isnad1 id=iff.1h4v.s8.1d111279c721 from=seed src=0 shape=5c23289c vocab=bbfd123e
-/
lemma isQuasiInverse_subtype_projectionOnto_iff {S T : Submodule K V} (hST : IsCompl S T) :
    IsQuasiInverse S.subtype (S.projectionOnto T hST) ↔ IsNoetherian K T := by
  rw [IsQuasiInverse, and_iff_left (by simp [IsRightQuasiInverse, projectionOnto_comp_subtype]),
    IsLeftQuasiInverse, ← projection,
    FiniteRangeSetoid.projection_equiv_id_iff_isNoetherian hST]

/--
@isnad1 id=isquasii.1h4v.s8.c43416a996dd from=seed src=0 shape=16b067e1 vocab=bbfd123e
-/
lemma isQuasiInverse_subtype_projectionOnto {S T : Submodule K V} [IsNoetherian K T]
    (hST : IsCompl S T) :
    IsQuasiInverse S.subtype (S.projectionOnto T hST) :=
  isQuasiInverse_subtype_projectionOnto_iff hST |>.mpr inferInstance

end QuasiInverse

end LinearMap
