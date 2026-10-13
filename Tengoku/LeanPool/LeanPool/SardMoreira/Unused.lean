/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.SardMoreira.ContDiff

/-!
# LeanPool.SardMoreira.Unused
-/

@[expose] public section

open scoped Topology
open Filter Set

-- TODO: add before `HasFDerivAt.of_local_left_inverse`
theorem HasFDerivWithinAt.of_local_leftInverse {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
    {s : Set E} {t : Set F} (hg : Tendsto g (𝓝[t] a) (𝓝[s] (g a)))
    (hf : HasFDerivWithinAt f (f' : E →L[𝕜] F) s (g a)) (ha : a ∈ t)
    (hfg : ∀ᶠ y in 𝓝[t] a, f (g y) = y) :
    HasFDerivWithinAt g (f'.symm : F →L[𝕜] E) t a :=
  HasFDerivWithinAt.of_local_left_inverse hg hf ha hfg

/-- Continuous linear equivalence between a submodule of a submodule and its mapped subtype. -/
@[simps! -fullyApplied apply_coe symm_apply_coe_coe]
def Submodule.continuousEquivSubtypeMap {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [TopologicalSpace M] (p : Submodule R M) (q : Submodule R p) :
    q ≃L[R] q.map p.subtype where
  toLinearEquiv := p.equivSubtypeMap q
  continuous_toFun := .codRestrict (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := .codRestrict (.codRestrict continuous_subtype_val _) _

/-- Continuous linear equivalence from the top submodule to the ambient module. -/
@[simps!]
def Submodule.topContinuousEquiv {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [TopologicalSpace M] :
    (⊤ : Submodule R M) ≃L[R] M where
  toLinearEquiv := topEquiv
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem ContinuousLinearEquiv.map_nhdsWithin_eq {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (e : M ≃L[R] N) (s : Set M) (x : M) :
    (𝓝[s] x).map e = 𝓝[e '' s] (e x) :=
  e.toHomeomorph.isInducing.map_nhdsWithin_eq _ _

theorem ContinuousLinearEquiv.map_nhdsWithin_preimage_eq {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (e : M ≃L[R] N) (s : Set N) (x : M) :
    (𝓝[e ⁻¹' s] x).map e = 𝓝[s] (e x) := by rw [e.map_nhdsWithin_eq, e.surjective.image_preimage]

namespace Submodule

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Linear equivalence between a product submodule and the product of submodules.

This duplicates `Submodule.prodEquiv`, which Mathlib has since acquired; it is kept under a
primed name to avoid the clash. -/
def prodEquiv'
    (s : Submodule R M) (t : Submodule R N) : s.prod t ≃ₗ[R] s × t :=
  { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

@[simp]
theorem rank_prod_eq_lift [StrongRankCondition R] (s : Submodule R M) (t : Submodule R N)
    [Module.Free R s] [Module.Free R t] :
    Module.rank R (s.prod t) = (Module.rank R s).lift + (Module.rank R t).lift := by
  simp [(s.prodEquiv' t).rank_eq]

@[simp]
theorem finrank_prod [StrongRankCondition R] (s : Submodule R M) (t : Submodule R N)
    [Module.Free R s] [Module.Free R t] [Module.Finite R s] [Module.Finite R t] :
    Module.finrank R (s.prod t) = Module.finrank R s + Module.finrank R t := by
  simp [(s.prodEquiv' t).finrank_eq]

end Submodule

section ContDiff

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {n : WithTop ℕ∞} {k : ℕ} {a : E}

protected theorem UniqueDiffOn.frequently_smallSets {s : Set E} (hs : UniqueDiffOn 𝕜 s) (a : E) :
    ∃ᶠ t in (𝓝[s] a).smallSets, t ∈ 𝓝[s] a ∧ UniqueDiffOn 𝕜 t := by
  rw [(nhdsWithin_basis_open _ _).smallSets.frequently_iff]
  exact fun U ⟨haU, hUo⟩ ↦ ⟨s ∩ U, (inter_comm _ _).le,
    inter_mem_nhdsWithin _ (hUo.mem_nhds haU), hs.inter hUo⟩

theorem iteratedFDeriv_apply_congr_order
    {k l : ℕ} (h : k = l) (f : E → F) (x : E) (m : Fin k → E) :
    iteratedFDeriv 𝕜 k f x m = iteratedFDeriv 𝕜 l f x (m ∘ Fin.cast h.symm) := by
  subst l
  simp

end ContDiff

namespace OrderedFinpartition

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {n : ℕ} (c : OrderedFinpartition n)

/-- Cover `[0, n)`, `n ≠ 0`, by a single subset. -/
@[simps -fullyApplied]
def single (n : ℕ) (hn : n ≠ 0) : OrderedFinpartition n where
  length := 1
  partSize _ := n
  partSize_pos _ := hn.bot_lt
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := subsingleton_univ.pairwise _
  cover x := ⟨0, x, rfl⟩

@[simp]
theorem applyOrderedFinpartition_single (hn : n ≠ 0)
    (p : ∀ i : Fin (single n hn).length, E [×(single n hn).partSize i]→L[𝕜] F)
    (m : Fin n → E) (i : Fin (single n hn).length) :
    (single n hn).applyOrderedFinpartition p m i = p i m :=
  rfl

end OrderedFinpartition
