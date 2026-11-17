/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.Lie.UniversalEnveloping.TensorNaturalEval
import Tengoku.LieLean.LieLean.Algebra.Lie.UniversalEnveloping.TensorNaturalNilpotent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Natural transformations between tensoring functors

A natural transformation `φ : − ⊗ V → − ⊗ W` of functors on `L`-modules (`TensorNatTrans`) is
determined, on modules killed by a two-sided ideal `I` of `U(L)`, by its value at one module
`M₀` whose annihilator is `I` (`TensorNatTrans.app_eq_of_app_eq`).

Summands `F = e(− ⊗ V)`, `G = e'(− ⊗ W)` of tensoring functors are given by natural idempotents
`e`, `e'`. Morphisms `φ : F → G`, `φ' : G → F` that are mutually inverse at `M₀` are mutually
inverse at every module `M` with a finite filtration whose subquotients are killed by `I`
(`TensorNatTrans.exists_inverse_of_hasKilledFiltration`): the defect `φ' φ - e` vanishes on
modules killed by `I`, hence is nilpotent on `M`. This is the argument of Humphreys' proof of
Theorem 10.7 (b), with `M₀ = M(λ)` for `λ` dominant.

## Main definitions

* `UniversalEnvelopingAlgebra.TensorNatTrans`: natural transformations `− ⊗ V → − ⊗ W`;
  `TensorNatTrans.ofTensorNatMap`, the one attached to `g : V → U^{ad} ⊗ W`.
* `UniversalEnvelopingAlgebra.IsKilledByPow I n M`: products of `n` elements of `I` kill `M`.

## Main results

* `UniversalEnvelopingAlgebra.hasKilledFiltration_of_isKilledByPow`: such an `M` has the
  filtration `M ⊇ I M ⊇ ⋯ ⊇ Iⁿ M = 0`.
* `UniversalEnvelopingAlgebra.TensorNatTrans.app_eq_of_app_eq`.
* `exists_mul_eq_of_isNilpotent_sub`: a nilpotent perturbation of an idempotent `e` in the
  corner `eAe` is invertible there.
* `UniversalEnvelopingAlgebra.TensorNatTrans.exists_inverse_of_hasKilledFiltration`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8, proof of Thm. 10.7.
-/

noncomputable section

open TensorProduct

namespace UniversalEnvelopingAlgebra

universe u v

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  {V W X : Type*} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
  [AddCommGroup X] [Module K X] [LieRingModule L X] [LieModule K L X]

universe w

variable (K L V W) in
/-- A natural transformation `M ⊗ V → M ⊗ W` of functors on `L`-modules in `Type w`.-/
structure TensorNatTrans where
  /-- The component at `M`.-/
  app : ∀ (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M],
    M ⊗[K] V →ₗ⁅K,L⁆ M ⊗[K] W
  naturality : ∀ (M N : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
    (f : M →ₗ⁅K,L⁆ N) (t : M ⊗[K] V),
    (f : M →ₗ[K] N).rTensor W (app M t) = app N ((f : M →ₗ[K] N).rTensor V t)

/-! ### Modules killed by a power of `I` -/

section Power

variable (I : TwoSidedIdeal (UniversalEnvelopingAlgebra K L)) (n : ℕ)
  (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- Every product of `n` elements of `I` acts by zero on `M`.-/
def IsKilledByPow : Prop :=
  ∀ l : List (UniversalEnvelopingAlgebra K L), l.length = n → (∀ a ∈ l, a ∈ I) →
    actionHom (R := K) (L := L) M l.prod = 0

/-- The Lie submodule `I M`, spanned by the vectors `a m` with `a ∈ I`.-/
def idealSMul : LieSubmodule K L M where
  toSubmodule := Submodule.span K {m | ∃ a ∈ I, ∃ m', actionHom (R := K) (L := L) M a m' = m}
  lie_mem {x m} hm := by
    change m ∈ Submodule.span K _ at hm
    change ⁅x, m⁆ ∈ Submodule.span K _
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨a, ha, m', rfl⟩ := hm
      have hx : ⁅x, actionHom (R := K) (L := L) M a m'⁆ =
          actionHom (R := K) (L := L) M (ι K x * a - a * ι K x) m' +
            actionHom (R := K) (L := L) M a ⁅x, m'⁆ := by
        rw [map_sub, LinearMap.sub_apply, map_mul, map_mul, Module.End.mul_apply,
          Module.End.mul_apply, actionHom_ι, LieModule.toEnd_apply_apply,
          LieModule.toEnd_apply_apply, sub_add_cancel]
      rw [hx]
      refine add_mem (Submodule.subset_span ⟨_, ?_, m', rfl⟩)
        (Submodule.subset_span ⟨a, ha, _, rfl⟩)
      exact sub_mem (I.mul_mem_left _ _ ha) (I.mul_mem_right _ _ ha)
    | zero => rw [lie_zero]; exact zero_mem _
    | add m m' _ _ hm hm' => rw [lie_add]; exact add_mem hm hm'
    | smul c m _ hm => rw [lie_smul]; exact Submodule.smul_mem _ c hm

variable {I n M}

/-- A module killed by all products of `n` elements of `I` has the filtration
`M ⊇ I M ⊇ I² M ⊇ ⋯ ⊇ Iⁿ M = 0` with subquotients killed by `I`.
@isnad1 id=haskille.1h5v.s6.7e1260c24904 from=translated src=- shape=06d5ab06 vocab=c034ef10
-/
theorem hasKilledFiltration_of_isKilledByPow (hM : IsKilledByPow I n M) :
    HasKilledFiltration I M n := by
  induction n generalizing M with
  | zero =>
    have h := hM [] rfl (by simp)
    rw [List.prod_nil, map_one] at h
    have hz : ∀ z : M, z = 0 := fun z ↦ LinearMap.congr_fun h z
    have : Subsingleton M := ⟨fun x y ↦ by rw [hz x, hz y]⟩
    exact HasKilledFiltration.zero (R := K) (L := L) (I := I) M
  | succ n ih =>
    refine .succ M (idealSMul I M) n (ih fun l hl hlI ↦ LinearMap.ext fun ⟨m, hm⟩ ↦ ?_) ?_
    · refine Subtype.ext ?_
      change (idealSMul I M).incl (actionHom _ l.prod ⟨m, hm⟩) = 0
      rw [LieModuleHom.map_actionHom]
      change actionHom (R := K) (L := L) M l.prod m = 0
      induction hm using Submodule.span_induction with
      | mem m hm =>
        obtain ⟨a, ha, m', rfl⟩ := hm
        rw [← Module.End.mul_apply, ← map_mul, ← List.prod_concat]
        rw [hM _ (by simp [hl]) (fun b hb ↦ by
          rcases List.mem_append.mp (List.concat_eq_append ▸ hb) with hb | hb
          exacts [hlI b hb, (List.mem_singleton.mp hb) ▸ ha]), LinearMap.zero_apply]
      | zero => rw [map_zero]
      | add m m' _ _ hm hm' => rw [map_add, hm, hm', add_zero]
      | smul c m _ hm => rw [map_smul, hm, smul_zero]
    · intro a ha
      refine LinearMap.ext fun q ↦ ?_
      induction q using Submodule.Quotient.induction_on with
      | H m =>
        change actionHom _ a (LieSubmodule.Quotient.mk' (idealSMul I M) m) = 0
        rw [← LieModuleHom.map_actionHom]
        change LieSubmodule.Quotient.mk _ = 0
        rw [LieSubmodule.Quotient.mk_eq_zero']
        exact Submodule.subset_span ⟨a, ha, m, rfl⟩

end Power

namespace TensorNatTrans

/-- The composite of two natural transformations.-/
def comp (ψ : TensorNatTrans.{u, v, w} K L W X) (φ : TensorNatTrans.{u, v, w} K L V W) :
    TensorNatTrans.{u, v, w} K L V X where
  app M _ _ _ _ := (ψ.app M).comp (φ.app M)
  naturality M N _ _ _ _ _ _ _ _ f t := by
    rw [LieModuleHom.comp_apply, ψ.naturality, φ.naturality, LieModuleHom.comp_apply]

/--
@isnad1 id=eq.0h8v.s9.b69bef3233d9 from=translated src=- shape=98d6d6b2 vocab=fbf44070
-/
@[simp] theorem comp_app (ψ : TensorNatTrans.{u, v, w} K L W X)
    (φ : TensorNatTrans.{u, v, w} K L V W)
    (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] :
    (ψ.comp φ).app M = (ψ.app M).comp (φ.app M) := rfl

variable {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K L)}

end TensorNatTrans

end UniversalEnvelopingAlgebra
