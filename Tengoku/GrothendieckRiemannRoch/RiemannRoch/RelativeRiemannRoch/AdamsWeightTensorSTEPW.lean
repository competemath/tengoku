/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.RingTheory.Flat.Basic
import Tengoku.Seed.RingTheory.TensorProduct.Basic
import Tengoku.Seed.RingTheory.Flat.TorsionFree
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.RelativeRiemannRoch.AdamsWeightAlgSTEPW
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.RelativeRiemannRoch.AdamsIdealFiltSTEPW

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# STEPW: from a filtered ring `T` to weight filtrations on `ℚ ⊗ R`

`FiltData`: an additive filtration `F m` of a commutative ring `T` (as produced by
`AdamsIdealFiltSTEPW.F`).  `ℚ ⊗ T` gets the weight filtration `V m = ℚ·(1 ⊗ F m)`
(`filt_tensor`), and along an injective ring map `q : R → T` compatible with the Adams operations it
pulls back to a weight filtration on `ℚ ⊗ R` (`Filt.comap`, `HasTower.hasFilt`).
-/

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace STEPW

universe u v

section Maps

variable {R T : Type*} [CommRing R] [CommRing T]

/-- `ℚ ⊗ ψ`.-/
def psiQ (ψ : R →+* R) : ℚ ⊗[ℤ] R →ₐ[ℚ] ℚ ⊗[ℤ] R :=
  Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) ψ.toIntAlgHom

/-- `ℚ ⊗ ρ`, for a rank function `ρ : R → ℤ`.-/
def rhoQ (f : R →+* ℤ) : ℚ ⊗[ℤ] R →ₐ[ℚ] ℚ :=
  (Algebra.TensorProduct.rid ℤ ℚ ℚ).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) f.toIntAlgHom)

/-- `ℚ ⊗ q`.-/
def qQ (q : R →+* T) : ℚ ⊗[ℤ] R →ₐ[ℚ] ℚ ⊗[ℤ] T :=
  Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) q.toIntAlgHom

/--
@isnad1 id=eq.0h4v.s8.75440d5fc1e6 from=translated src=- shape=06f033a0 vocab=8c5c98f6
-/
@[simp] theorem psiQ_tmul (ψ : R →+* R) (c : ℚ) (r : R) : psiQ ψ (c ⊗ₜ r) = c ⊗ₜ ψ r := by
  simp [psiQ]

/--
@isnad1 id=eq.0h5v.s9.fc0984d2327f from=translated src=- shape=8f4d45ae vocab=da83efa2
-/
@[simp] theorem qQ_tmul (q : R →+* T) (c : ℚ) (r : R) : qQ q (c ⊗ₜ r) = c ⊗ₜ q r := by
  simp [qQ]

/--
@isnad1 id=eq.0h4v.s8.a31b2d0bb58c from=translated src=- shape=b3cff857 vocab=bd2e9b7f
-/
@[simp] theorem rhoQ_tmul (f : R →+* ℤ) (c : ℚ) (r : R) : rhoQ f (c ⊗ₜ r) = c * (f r : ℚ) := by
  simp [rhoQ, mul_comm]

/--
@isnad1 id=injectiv.1h3v.s8.f0c383046dc9 from=translated src=- shape=c8a3e1f4 vocab=591c401d
-/
theorem qQ_injective (q : R →+* T) (hq : Function.Injective q) : Function.Injective (qQ q) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (R := ℤ) (M := ℚ)
    q.toIntAlgHom.toLinearMap hq
  have : ⇑(qQ q) = ⇑(LinearMap.lTensor ℚ q.toIntAlgHom.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [this]
  exact h

end Maps

section FiltDataSec

variable {T : Type*} [CommRing T]

/-- An additive filtration of `T` with the properties of `AdamsIdealFiltSTEPW.F`.-/
structure FiltData (φ : ℕ → T →+* T) (ρ : T →+* ℤ) (F : ℕ → AddSubgroup T) (M : ℕ) : Prop where
  /-- decreasing-/
  anti : ∀ m, F (m + 1) ≤ F m
  /-- exhausted-/
  bot : F (M + 1) = ⊥
  /-- `F 1` is nilpotent-/
  nil : ∀ t ∈ F 1, IsNilpotent t
  /-- `F 0 = ℤ + F 1`-/
  zero : ∀ t ∈ F 0, ∃ n : ℤ, t - (n : T) ∈ F 1
  /-- `F 1` has rank `0`-/
  rank : ∀ t ∈ F 1, ρ t = 0
  /-- `φ j = j^m` on `F m / F (m+1)`-/
  eig : ∀ j : ℕ, 2 ≤ j → ∀ m, ∀ t ∈ F m, φ j t - (j : T) ^ m * t ∈ F (m + 1)

variable {φ : ℕ → T →+* T} {ρ : T →+* ℤ} {F : ℕ → AddSubgroup T} {M : ℕ}

/-- The filtration `V m = ℚ · (1 ⊗ F m)` of `ℚ ⊗ T`.-/
def Vq (F : ℕ → AddSubgroup T) (m : ℕ) : Submodule ℚ (ℚ ⊗[ℤ] T) :=
  Submodule.span ℚ ((fun t : T ↦ (1 : ℚ) ⊗ₜ[ℤ] t) '' (F m : Set T))

/--
@isnad1 id=mem.1h4v.s8.36a22575af1b from=translated src=- shape=346c268a vocab=b19eb8ec
-/
theorem one_tmul_mem_Vq {m : ℕ} {t : T} (ht : t ∈ F m) : (1 : ℚ) ⊗ₜ[ℤ] t ∈ Vq F m :=
  Submodule.subset_span ⟨t, ht, rfl⟩

/--
@isnad1 id=filt.1h5v.s7.985e5eb1b0f1 from=translated src=- shape=c5c0793c vocab=81d16bc3
-/
theorem filt_tensor (h : FiltData φ ρ F M) : Filt (fun j ↦ psiQ (φ j)) (rhoQ ρ) (Vq F) M := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    exact Submodule.span_mono (Set.image_mono (h.anti m))
  · have : ((F (M + 1) : AddSubgroup T) : Set T) = {0} := by rw [h.bot]; rfl
    simp [Vq, this]
  · intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      obtain ⟨n, hn⟩ := h.nil t ht
      exact ⟨n, by
        show ((1 : ℚ) ⊗ₜ[ℤ] t) ^ n = 0
        rw [Algebra.TensorProduct.tmul_pow, hn, one_pow, tmul_zero]⟩
    | zero => exact IsNilpotent.zero
    | add x y _ _ hx hy => exact Commute.isNilpotent_add (Commute.all _ _) hx hy
    | smul c x _ hx =>
      obtain ⟨n, hn⟩ := hx
      exact ⟨n, by rw [smul_pow, hn, smul_zero]⟩
  · intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      obtain ⟨n, hn⟩ := h.zero t ht
      refine Submodule.mem_sup.mpr ⟨(n : ℚ) • (1 : ℚ ⊗[ℤ] T), ?_, (1 : ℚ) ⊗ₜ[ℤ] (t - (n : T)),
        one_tmul_mem_Vq hn, ?_⟩
      · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · rw [TensorProduct.tmul_sub]
        have : (n : ℚ) • (1 : ℚ ⊗[ℤ] T) = (1 : ℚ) ⊗ₜ[ℤ] (n : T) := by
          have h1 : (n : ℚ) ⊗ₜ[ℤ] (1 : T) = (1 : ℚ) ⊗ₜ[ℤ] (n : T) := by
            have := TensorProduct.smul_tmul (R := ℤ) n (1 : ℚ) (1 : T)
            simpa using this
          rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one, h1]
        rw [this]; abel
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul c x _ hx => exact Submodule.smul_mem _ c hx
  · intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      rw [rhoQ_tmul, h.rank t ht]; simp
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  · intro j hj m v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      have := one_tmul_mem_Vq (h.eig j hj m t ht)
      have e : ((j : ℚ) ^ m) • ((1 : ℚ) ⊗ₜ[ℤ] t) = (1 : ℚ) ⊗ₜ[ℤ] ((j : T) ^ m * t) := by
        have : ((j : ℚ) ^ m) = ((j ^ m : ℕ) : ℚ) := by push_cast; rfl
        rw [this, Nat.cast_smul_eq_nsmul, ← TensorProduct.tmul_smul, nsmul_eq_mul]
        push_cast; rfl
      rw [psiQ_tmul, e, ← TensorProduct.tmul_sub]
      exact this
    | zero => simp
    | add x y _ _ hx hy =>
      have : psiQ (φ j) (x + y) - ((j : ℚ) ^ m) • (x + y) =
          (psiQ (φ j) x - ((j : ℚ) ^ m) • x) + (psiQ (φ j) y - ((j : ℚ) ^ m) • y) := by
        rw [map_add, smul_add]; abel
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      have : psiQ (φ j) (c • x) - ((j : ℚ) ^ m) • (c • x) =
          c • (psiQ (φ j) x - ((j : ℚ) ^ m) • x) := by
        rw [map_smul, smul_sub, smul_comm]
      rw [this]; exact Submodule.smul_mem _ c hx

end FiltDataSec

section Comap

variable {K K' : Type*} [CommRing K] [Algebra ℚ K] [CommRing K'] [Algebra ℚ K']
  {Ψ : ℕ → K →ₐ[ℚ] K} {Ψ' : ℕ → K' →ₐ[ℚ] K'} {ρ : K →ₐ[ℚ] ℚ} {ρ' : K' →ₐ[ℚ] ℚ}

/-- Pulling a weight filtration back along an injective compatible algebra map.
@isnad1 id=filt.4h9v.s9.e1f5cfef0c91 from=translated src=- shape=f50f561b vocab=e5128ff2
-/
theorem Filt.comap (Q : K →ₐ[ℚ] K') (hQ : Function.Injective Q)
    (hΨ : ∀ j, 2 ≤ j → ∀ x, Q (Ψ j x) = Ψ' j (Q x)) (hρ : ∀ x, ρ' (Q x) = ρ x)
    {V' : ℕ → Submodule ℚ K'} {M : ℕ} (h : Filt Ψ' ρ' V' M) :
    Filt Ψ ρ (fun m ↦ (V' m).comap Q.toLinearMap) M := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    exact Submodule.comap_mono (h.anti m)
  · rw [h.bot, Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.mpr hQ
  · intro v hv
    obtain ⟨n, hn⟩ := h.nil _ hv
    have hn' : Q v ^ n = 0 := hn
    exact ⟨n, hQ (by rw [map_pow, hn', map_zero])⟩
  · intro v hv
    obtain ⟨c, hc, y, hy, hcy⟩ := Submodule.mem_sup.mp (h.zero hv)
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hc
    refine Submodule.mem_sup.mpr ⟨r • (1 : K), Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self _), v - r • (1 : K), ?_, by abel⟩
    show Q.toLinearMap (v - r • (1 : K)) ∈ V' 1
    have : Q.toLinearMap (v - r • (1 : K)) = y := by
      simp only [AlgHom.toLinearMap_apply, map_sub, map_smul, map_one]
      have hcy' : r • (1 : K') + y = Q v := hcy
      rw [← hcy']
      abel
    rw [this]; exact hy
  · intro v hv
    rw [← hρ]
    exact h.rank _ hv
  · intro j hj m v hv
    show Q.toLinearMap (Ψ j v - ((j : ℚ) ^ m) • v) ∈ V' (m + 1)
    simp only [AlgHom.toLinearMap_apply, map_sub, map_smul, hΨ j hj]
    exact h.eig j hj m _ hv

end Comap

section Tower

variable {R : Type u} [CommRing R]

/-- `r : R` embeds, compatibly with the Adams operations `ψ` and a rank function `ρ`, into a ring
`T` with a nilpotent filtration containing the image of `r` in its bottom step.-/
def HasTower.{w'} (ψ : ℕ → R →+* R) (ρ : R →+* ℤ) (r : R) : Prop :=
  ∃ (T : Type w') (_ : CommRing T) (q : R →+* T) (φ : ℕ → T →+* T) (ρT : T →+* ℤ)
    (F : ℕ → AddSubgroup T) (M : ℕ),
    Function.Injective q ∧ (∀ j x, q (ψ j x) = φ j (q x)) ∧ (∀ x, ρT (q x) = ρ x) ∧
      FiltData φ ρT F M ∧ q r ∈ F 0

/--
@isnad1 id=hasfilt.1h4v.s7.75d48aed9fa7 from=translated src=- shape=a5be7ef3 vocab=6e6c482b
-/
theorem HasTower.hasFilt {ψ : ℕ → R →+* R} {ρ : R →+* ℤ} {r : R} (h : HasTower.{u, v} ψ ρ r) :
    HasFilt (fun j ↦ psiQ (ψ j)) (rhoQ ρ) ((1 : ℚ) ⊗ₜ[ℤ] r) := by
  obtain ⟨T, _, q, φ, ρT, F, M, hq, hψ, hρ, hF, hr⟩ := h
  have hΨ : ∀ j x, qQ q (psiQ (ψ j) x) = psiQ (φ j) (qQ q x) := by
    intro j x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y => simp [hψ]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  have hρ' : ∀ x, rhoQ ρT (qQ q x) = rhoQ ρ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y => simp [hρ]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  refine ⟨_, M, Filt.comap (qQ q) (qQ_injective q hq) (fun j _ ↦ hΨ j) hρ' (filt_tensor hF), ?_⟩
  show (qQ q).toLinearMap ((1 : ℚ) ⊗ₜ[ℤ] r) ∈ Vq F 0
  simpa using one_tmul_mem_Vq hr

/--
@isnad1 id=hasfilt.1h4v.s8.7968fd4e2e9c from=translated src=- shape=f3ffda2e vocab=2aa145b6
-/
theorem HasFilt.neg_tmul {Ψ : ℕ → ℚ ⊗[ℤ] R →ₐ[ℚ] ℚ ⊗[ℤ] R} {ρ : ℚ ⊗[ℤ] R →ₐ[ℚ] ℚ} {a : R}
    (h : HasFilt Ψ ρ ((1 : ℚ) ⊗ₜ[ℤ] a)) : HasFilt Ψ ρ ((1 : ℚ) ⊗ₜ[ℤ] (-a)) := by
  have e : (1 : ℚ) ⊗ₜ[ℤ] (-a) = (-1 : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] a) :=
    (TensorProduct.tmul_neg (R := ℤ) (1 : ℚ) a).trans (neg_one_smul ℚ _).symm
  rw [e]
  exact h.smul _

end Tower

end STEPW
