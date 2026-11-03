/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.FiniteMappingChain
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.Proposition_4_76
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.Lemma_4_74
import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR Proposition 4.77: Noether normalization

Let `𝒫 = {P₁, …, P_s} ⊂ K[X₁, …, X_k]`. Then either `1 ∈ Ideal(𝒫, K)`, or there is a linear
automorphism `v : K^k → K^k` and `k' ≤ k` such that the projection `Π : C^k → C^{k'}` (forgetting
the last `k - k'` coordinates) is a finite mapping from `v(Zer(𝒫, C^k))` onto `C^{k'}` (`C`
algebraically closed).

As elsewhere in §4.4 we single out `X₀`. A linear change `v` is encoded by an algebra
automorphism `σ` with each `σ(Xᵢ)` homogeneous of degree `1` (`IsLinearAlgAut`); the set
`v(Zer(𝒫))` is `Zer(𝒫.image σ)`, and "finite mapping onto `C^{k'}`" is `IsFiniteMappingChain`
down to the empty target set (`Zer(∅) = C^{k'}`).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

open scoped Classical

variable {K : Type*} [Field K]

/-- A *linear* algebra automorphism of `K[X₁, …, X_k]`: one sending each variable to a
homogeneous degree-`1` form (i.e. induced by a linear automorphism of `K^k`).-/
def IsLinearAlgAut {k : ℕ} (σ : MvPolynomial (Fin k) K ≃ₐ[K] MvPolynomial (Fin k) K) : Prop :=
  ∀ i, (σ (X i)).IsHomogeneous 1

/-! ### A linear strengthening of Lemma 4.74 -/

/-! ### Lifting a `Fin m` automorphism to `Fin (m+1)`, fixing `X₀` -/

/-- The values for the lift: `X 0 ↦ X 0`, `X i.succ ↦ rename Fin.succ (f (X i))`.-/
private noncomputable def liftMap {m : ℕ} (f : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K) :
    Fin (m + 1) → MvPolynomial (Fin (m + 1)) K :=
  Fin.cases (X 0) (fun i => rename Fin.succ (f (X i)))

/-- The algebra hom lifting `f : K[X₁,…,X_m] → K[X₁,…,X_m]` to `K[X₀,…,X_m]`, fixing `X₀`.-/
private noncomputable def liftHom {m : ℕ}
    (f : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K) :
    MvPolynomial (Fin (m + 1)) K →ₐ[K] MvPolynomial (Fin (m + 1)) K :=
  aeval (liftMap f)

@[simp] private theorem liftMap_zero {m : ℕ}
    (f : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K) : liftMap f 0 = X 0 := by
  simp [liftMap]

@[simp] private theorem liftMap_succ {m : ℕ}
    (f : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K) (i : Fin m) :
    liftMap f i.succ = rename Fin.succ (f (X i)) := by
  simp [liftMap]

/-- `liftHom (g ∘ f) = liftHom g ∘ liftHom f`.-/
private theorem liftHom_comp {m : ℕ}
    (f g : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K) :
    (liftHom g).comp (liftHom f) = liftHom (g.comp f) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftHom]
  · simp only [liftHom, AlgHom.comp_apply, aeval_X, liftMap_succ]
    -- `liftHom g (rename Fin.succ (f (X j))) = rename Fin.succ (g (f (X j)))`
    rw [aeval_rename]
    have : (liftMap g ∘ Fin.succ) = fun i => rename Fin.succ (g (X i)) := by
      funext i; simp [liftMap]
    rw [this]
    -- aeval (fun i => rename Fin.succ (g (X i))) (f (X j)) = rename Fin.succ (g (f (X j)))
    rw [show (fun i => rename (R := K) Fin.succ (g (X i)))
          = fun i => (rename Fin.succ).comp g (X i) from rfl]
    rw [← comp_aeval]
    simp [aeval_X_left]

/-- `liftHom` of the identity is the identity.-/
private theorem liftHom_id {m : ℕ} :
    liftHom (AlgHom.id K (MvPolynomial (Fin m) K)) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftHom]
  · simp [liftHom]

/-- The lift of a `Fin m` algebra automorphism to a `Fin (m+1)` algebra automorphism, fixing
`X₀` and acting as `σ'` on the embedded `X₁, …, X_m`.-/
private noncomputable def liftAut {m : ℕ}
    (σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K) :
    MvPolynomial (Fin (m + 1)) K ≃ₐ[K] MvPolynomial (Fin (m + 1)) K :=
  AlgEquiv.ofAlgHom (liftHom σ'.toAlgHom) (liftHom σ'.symm.toAlgHom)
    (by rw [liftHom_comp]; rw [show σ'.toAlgHom.comp σ'.symm.toAlgHom = AlgHom.id K _ from ?_,
          liftHom_id]
        ext x; simp)
    (by rw [liftHom_comp]; rw [show σ'.symm.toAlgHom.comp σ'.toAlgHom = AlgHom.id K _ from ?_,
          liftHom_id]
        ext x; simp)

@[simp] private theorem liftAut_apply {m : ℕ}
    (σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K) (P : MvPolynomial (Fin (m + 1)) K) :
    liftAut σ' P = liftHom σ'.toAlgHom P := rfl

/-- `liftAut σ'` fixes `X₀`.-/
@[simp] private theorem liftAut_X_zero {m : ℕ}
    (σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K) :
    liftAut σ' (X 0) = X 0 := by simp [liftAut, liftHom]

/-- `liftAut σ'` sends `X i.succ` to `rename Fin.succ (σ' (X i))`.-/
@[simp] private theorem liftAut_X_succ {m : ℕ}
    (σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K) (i : Fin m) :
    liftAut σ' (X i.succ) = rename Fin.succ (σ' (X i)) := by simp [liftAut, liftHom]

/-! ### The geometric point map of an algebra hom -/

section PointMap

variable {C : Type*} [CommRing C] [Algebra K C]

/-- The point map of an algebra hom `τ` at a point `x`: `i ↦ aeval x (τ (X i))`.-/
noncomputable def ptMap {N : ℕ} (τ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K)
    (x : Fin N → C) : Fin N → C := fun i => aeval x (τ (X i))

/-- `aeval x (τ P) = aeval (ptMap τ x) P`.
@isnad1 id=eq.0h6v.s9.6d1d50d3ddc1 from=translated src=- shape=95e42425 vocab=7143b7f9
-/
theorem aeval_comp_algHom {N : ℕ}
    (τ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K) (x : Fin N → C)
    (P : MvPolynomial (Fin N) K) :
    aeval x (τ P) = aeval (ptMap τ x) P := by
  have key : (aeval x : MvPolynomial (Fin N) K →ₐ[K] C).comp τ
      = (aeval (ptMap τ x) : MvPolynomial (Fin N) K →ₐ[K] C) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [ptMap]
  exact DFunLike.congr_fun key P

/-- Membership in the zero set of an image: `x ∈ Zer(Ps.image τ) ↔ ptMap τ x ∈ Zer(Ps)`.
@isnad1 id=iff.0h6v.s9.837897374f41 from=translated src=- shape=82f88b09 vocab=4987da9a
-/
theorem mem_zerOfFinset_image {N : ℕ} [DecidableEq (MvPolynomial (Fin N) K)]
    (τ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K)
    (Ps : Finset (MvPolynomial (Fin N) K)) (x : Fin N → C) :
    x ∈ zerOfFinset C (Ps.image τ) ↔ ptMap τ x ∈ zerOfFinset C Ps := by
  unfold zerOfFinset
  simp only [Set.mem_ofPred_eq, Finset.mem_image, forall_exists_index, and_imp]
  constructor
  · intro h p hp
    rw [← aeval_comp_algHom]
    exact h (τ p) p hp rfl
  · intro h _ p hp hpq
    rw [← hpq, aeval_comp_algHom]
    exact h p hp

/-- Membership in the zero set of an image by an algebra *equiv*.
@isnad1 id=iff.0h6v.s9.a0f50adf086b from=translated src=- shape=403c2cbe vocab=e9a02427
-/
theorem mem_zerOfFinset_image_equiv {N : ℕ} [DecidableEq (MvPolynomial (Fin N) K)]
    (σ : MvPolynomial (Fin N) K ≃ₐ[K] MvPolynomial (Fin N) K)
    (Ps : Finset (MvPolynomial (Fin N) K)) (x : Fin N → C) :
    x ∈ zerOfFinset C (Ps.image σ) ↔ ptMap σ.toAlgHom x ∈ zerOfFinset C Ps := by
  rw [show (Ps.image σ) = Ps.image σ.toAlgHom from rfl]
  exact mem_zerOfFinset_image σ.toAlgHom Ps x

end PointMap

/-! ### Quasi-monic is preserved under the lift -/

/-! ### The change-of-variables congruence for single-step finite mappings -/

/-! ### Helpers for the main induction -/

end Azurite.BPR.Chapter4
