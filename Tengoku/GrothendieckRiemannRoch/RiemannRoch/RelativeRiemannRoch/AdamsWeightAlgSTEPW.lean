/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.RingTheory.GradedAlgebra.Basic
import Tengoku.Seed.LinearAlgebra.Eigenspace.Basic
import Tengoku.Seed.Algebra.DirectSum.Module
import Tengoku.Seed.Algebra.Polynomial.AlgebraMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# STEPW: the Adams-weight grading from a nilpotent filtration (pure algebra)

`K` is a commutative `ℚ`-algebra with a family `Ψ j : K →ₐ[ℚ] K` (Adams operations), `ρ : K →ₐ[ℚ] ℚ`
(rank).  An element `x` *has a weight filtration* (`HasFilt`) if it lies in `V 0` for a decreasing
family of `ℚ`-subspaces `V m` with `V (M+1) = ⊥`, `V 1` consisting of nilpotents killed by `ρ`,
`V 0 ≤ ℚ·1 + V 1`, and `Ψ j v - j^m v ∈ V (m+1)` for `v ∈ V m` (all `j ≥ 2`).

If every element has a weight filtration and the `Ψ j` commute, then:
* every `x` is killed by `∏_{m ≤ M} (Ψ j - j^m)` (`exists_killing`);
* `K = ⨁_p W j p`, `W j p = ker (Ψ j - j^p)` (`isInternal`), a `GradedAlgebra` (`gradedAlgebra`);
* `W j p` does not depend on `j` (`eigenspace_eq`);
* `W 0 = ℚ·1`, positive weights are killed by `ρ` and nilpotent.
-/

set_option autoImplicit false

noncomputable section

open Module Polynomial

namespace STEPW

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- A weight filtration.-/
structure Filt (Ψ : ℕ → K →ₐ[ℚ] K) (ρ : K →ₐ[ℚ] ℚ) (V : ℕ → Submodule ℚ K) (M : ℕ) : Prop where
  /-- the filtration is decreasing-/
  anti : ∀ m, V (m + 1) ≤ V m
  /-- it is exhausted after `M + 1` steps-/
  bot : V (M + 1) = ⊥
  /-- `V 1` consists of nilpotents-/
  nil : ∀ v ∈ V 1, IsNilpotent v
  /-- `V 0` is the scalars plus `V 1`-/
  zero : V 0 ≤ Submodule.span ℚ {(1 : K)} ⊔ V 1
  /-- `V 1` has rank `0`-/
  rank : ∀ v ∈ V 1, ρ v = 0
  /-- `Ψ j = j^m` on `V m / V (m+1)`-/
  eig : ∀ j : ℕ, 2 ≤ j → ∀ m, ∀ v ∈ V m, Ψ j v - ((j : ℚ) ^ m) • v ∈ V (m + 1)

/-- `x` lies in the bottom step of some weight filtration.-/
def HasFilt (Ψ : ℕ → K →ₐ[ℚ] K) (ρ : K →ₐ[ℚ] ℚ) (x : K) : Prop :=
  ∃ (V : ℕ → Submodule ℚ K) (M : ℕ), Filt Ψ ρ V M ∧ x ∈ V 0

variable {Ψ : ℕ → K →ₐ[ℚ] K} {ρ : K →ₐ[ℚ] ℚ}

theorem Filt.mono_nat {V : ℕ → Submodule ℚ K} {M : ℕ} (h : Filt Ψ ρ V M) {a b : ℕ} (hab : a ≤ b) :
    V b ≤ V a := by
  induction hab with
  | refl => exact le_rfl
  | step _ ih => exact (h.anti _).trans ih

theorem Filt.bot_of_le {V : ℕ → Submodule ℚ K} {M : ℕ} (h : Filt Ψ ρ V M) {m : ℕ} (hm : M + 1 ≤ m) :
    V m = ⊥ := by
  have := h.mono_nat hm
  rw [h.bot] at this
  exact le_bot_iff.mp this

theorem HasFilt.zero : HasFilt Ψ ρ (0 : K) := by
  refine ⟨fun _ ↦ ⊥, 0, ⟨fun _ ↦ le_rfl, rfl, ?_, ?_, ?_, ?_⟩, Submodule.zero_mem _⟩
  · intro v hv
    rw [Submodule.mem_bot] at hv
    subst hv
    exact IsNilpotent.zero
  · exact bot_le
  · intro v hv
    rw [Submodule.mem_bot] at hv
    subst hv
    exact map_zero _
  · intro j _ m v hv
    rw [Submodule.mem_bot] at hv
    subst hv
    simp

theorem HasFilt.add {x y : K} (hx : HasFilt Ψ ρ x) (hy : HasFilt Ψ ρ y) : HasFilt Ψ ρ (x + y) := by
  obtain ⟨V, M, hV, hxV⟩ := hx
  obtain ⟨V', M', hV', hyV⟩ := hy
  refine ⟨fun m ↦ V m ⊔ V' m, max M M', ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Submodule.add_mem_sup hxV hyV⟩
  · intro m
    exact sup_le_sup (hV.anti m) (hV'.anti m)
  · rw [hV.bot_of_le (by omega), hV'.bot_of_le (by omega)]
    simp
  · intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    exact Commute.isNilpotent_add (Commute.all _ _) (hV.nil a ha) (hV'.nil b hb)
  · intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, hc, a', ha', rfl⟩ := Submodule.mem_sup.mp (hV.zero ha)
    obtain ⟨d, hd, b', hb', rfl⟩ := Submodule.mem_sup.mp (hV'.zero hb)
    refine Submodule.mem_sup.mpr ⟨c + d, Submodule.add_mem _ hc hd, a' + b',
      Submodule.mem_sup.mpr ⟨a', ha', b', hb', rfl⟩, by abel⟩
  · intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hV.rank a ha, hV'.rank b hb, add_zero]
  · intro j hj m v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    have h1 := hV.eig j hj m a ha
    have h2 := hV'.eig j hj m b hb
    have : Ψ j (a + b) - ((j : ℚ) ^ m) • (a + b) =
        (Ψ j a - ((j : ℚ) ^ m) • a) + (Ψ j b - ((j : ℚ) ^ m) • b) := by
      rw [map_add, smul_add]; abel
    rw [this]
    exact Submodule.add_mem_sup h1 h2

theorem HasFilt.smul {x : K} (c : ℚ) (hx : HasFilt Ψ ρ x) : HasFilt Ψ ρ (c • x) := by
  obtain ⟨V, M, hV, hxV⟩ := hx
  exact ⟨V, M, hV, Submodule.smul_mem _ c hxV⟩

/-- If a family of elements spanning `K` all have weight filtrations, so does everything.-/
theorem hasFilt_of_span {S : Set K} (hS : ∀ s ∈ S, HasFilt Ψ ρ s)
    {x : K} (hx : x ∈ Submodule.span ℚ S) : HasFilt Ψ ρ x := by
  induction hx using Submodule.span_induction with
  | mem s hs => exact hS s hs
  | zero => exact HasFilt.zero
  | add a b _ _ ha hb => exact ha.add hb
  | smul c a _ ha => exact ha.smul c

/-! ## Killing polynomial and eigenspace decomposition -/

section Decomp

variable (Ψ) (j : ℕ)

/-- The weight space `W j p = ker (Ψ j - j^p)`.-/
def W (j p : ℕ) : Submodule ℚ K :=
  Module.End.eigenspace (Ψ j).toLinearMap ((j : ℚ) ^ p)

variable {Ψ}

theorem mem_W {j p : ℕ} {x : K} : x ∈ W Ψ j p ↔ Ψ j x = ((j : ℚ) ^ p) • x :=
  Module.End.mem_eigenspace_iff

/-- The operator `∏_{m < n} (Ψ j - j^m)`.-/
def kp (Ψ : ℕ → K →ₐ[ℚ] K) (j n : ℕ) : Module.End ℚ K :=
  aeval (Ψ j).toLinearMap (∏ m ∈ Finset.range n, (X - C ((j : ℚ) ^ m)))

theorem kp_zero (x : K) : kp Ψ j 0 x = x := by simp [kp]

theorem kp_succ_eq (n : ℕ) : kp Ψ j (n + 1) =
    ((Ψ j).toLinearMap - algebraMap ℚ (Module.End ℚ K) ((j : ℚ) ^ n)) * kp Ψ j n := by
  have : ∏ m ∈ Finset.range (n + 1), (X - C ((j : ℚ) ^ m)) =
      (X - C ((j : ℚ) ^ n)) * ∏ m ∈ Finset.range n, (X - C ((j : ℚ) ^ m)) := by
    rw [Finset.prod_range_succ, mul_comm]
  rw [kp, kp, this, map_mul, map_sub, aeval_X, aeval_C]

theorem kp_succ_apply' (n : ℕ) (x : K) :
    kp Ψ j (n + 1) x = Ψ j (kp Ψ j n x) - ((j : ℚ) ^ n) • kp Ψ j n x := by
  rw [kp_succ_eq]
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
    AlgHom.toLinearMap_apply]

theorem kp_succ_apply (n : ℕ) (x : K) :
    kp Ψ j (n + 1) x = kp Ψ j n (Ψ j x - ((j : ℚ) ^ n) • x) := by
  have : kp Ψ j (n + 1) = kp Ψ j n * ((Ψ j).toLinearMap -
      algebraMap ℚ (Module.End ℚ K) ((j : ℚ) ^ n)) := by
    rw [kp, kp, Finset.prod_range_succ, map_mul, map_sub, aeval_X, aeval_C]
  rw [this]
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
    AlgHom.toLinearMap_apply]

theorem kp_mem {V : ℕ → Submodule ℚ K} {M : ℕ} (hV : Filt Ψ ρ V M) (hj : 2 ≤ j) {v : K}
    (hv : v ∈ V 0) (n : ℕ) : kp Ψ j n v ∈ V n := by
  induction n with
  | zero => rw [kp_zero]; exact hv
  | succ n ih =>
    rw [kp_succ_apply']
    exact hV.eig j hj n _ ih

/-- **Killing polynomial.**-/
theorem exists_killing {x : K} (hx : HasFilt Ψ ρ x) (hj : 2 ≤ j) : ∃ M, kp Ψ j (M + 1) x = 0 := by
  obtain ⟨V, M, hV, hv⟩ := hx
  refine ⟨M, ?_⟩
  have := kp_mem j hV hj hv (M + 1)
  rwa [hV.bot, Submodule.mem_bot] at this

theorem pow_injective (hj : 2 ≤ j) : Function.Injective fun p : ℕ ↦ ((j : ℚ) ^ p) := by
  intro a b h
  have h0 : (j : ℚ) ^ a = (j : ℚ) ^ b := h
  have h' : j ^ a = j ^ b := by exact_mod_cast h0
  exact Nat.pow_right_injective hj h'

theorem iSupIndep_W (hj : 2 ≤ j) : iSupIndep (W Ψ j) :=
  (Module.End.eigenspaces_iSupIndep (Ψ j).toLinearMap).comp (pow_injective j hj)

theorem exists_preimage (hj : 2 ≤ j) (n : ℕ) (z : K) (hz : z ∈ ⨆ p : Fin n, W Ψ j p) :
    ∃ w ∈ (⨆ p : Fin n, W Ψ j p), Ψ j w - ((j : ℚ) ^ n) • w = z := by
  induction hz using Submodule.iSup_induction' with
  | mem i x hx =>
    have hne : ((j : ℚ) ^ (i : ℕ)) - (j : ℚ) ^ n ≠ 0 := by
      intro h
      have := pow_injective j hj (sub_eq_zero.mp h)
      have := i.2
      omega
    refine ⟨(((j : ℚ) ^ (i : ℕ)) - (j : ℚ) ^ n)⁻¹ • x,
      Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i hx), ?_⟩
    rw [map_smul, mem_W.mp hx, smul_smul, smul_smul, ← sub_smul]
    have : ((j : ℚ) ^ (i : ℕ) - (j : ℚ) ^ n)⁻¹ * (j : ℚ) ^ (i : ℕ) -
        (j : ℚ) ^ n * ((j : ℚ) ^ (i : ℕ) - (j : ℚ) ^ n)⁻¹ = 1 := by
      field_simp
    rw [this, one_smul]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨w₁, h₁, e₁⟩ := ha
    obtain ⟨w₂, h₂, e₂⟩ := hb
    refine ⟨w₁ + w₂, Submodule.add_mem _ h₁ h₂, ?_⟩
    rw [map_add, smul_add, ← e₁, ← e₂]
    abel

theorem mem_iSup_of_kp (hj : 2 ≤ j) :
    ∀ (n : ℕ) (y : K), kp Ψ j n y = 0 → y ∈ ⨆ p : Fin n, W Ψ j p := by
  intro n
  induction n with
  | zero =>
    intro y hy
    rw [kp_zero] at hy
    subst hy
    exact Submodule.zero_mem _
  | succ n ih =>
    intro y hy
    have hz0 : kp Ψ j n (Ψ j y - ((j : ℚ) ^ n) • y) = 0 := by rw [← kp_succ_apply]; exact hy
    have hzS := ih _ hz0
    have hSle : (⨆ p : Fin n, W Ψ j p) ≤ ⨆ p : Fin (n + 1), W Ψ j p :=
      iSup_le fun p ↦ le_iSup (fun q : Fin (n + 1) ↦ W Ψ j q) p.castSucc
    obtain ⟨w, hwS, hw⟩ := exists_preimage j hj n _ hzS
    have hyw : y - w ∈ W Ψ j n := by
      rw [mem_W, map_sub, smul_sub]
      have : Ψ j y - Ψ j w = ((j : ℚ) ^ n) • y - ((j : ℚ) ^ n) • w := by
        have h1 := sub_eq_sub_iff_sub_eq_sub.mp hw
        rw [← neg_sub, h1, neg_sub]
      exact this
    have : y = w + (y - w) := by abel
    rw [this]
    exact Submodule.add_mem _ (hSle hwS)
      (Submodule.mem_iSup_of_mem (Fin.last n) hyw)

theorem iSup_W_eq_top (H : ∀ x : K, HasFilt Ψ ρ x) (hj : 2 ≤ j) : ⨆ p : ℕ, W Ψ j p = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨M, hM⟩ := exists_killing j (H x) hj
  have := mem_iSup_of_kp j hj (M + 1) x hM
  exact (iSup_le fun p : Fin (M + 1) ↦ le_iSup (fun q : ℕ ↦ W Ψ j q) (p : ℕ)) this

theorem isInternal (H : ∀ x : K, HasFilt Ψ ρ x) (hj : 2 ≤ j) :
    DirectSum.IsInternal (W Ψ j) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨iSupIndep_W j hj, iSup_W_eq_top j H hj⟩

theorem W_mul_mem {p q : ℕ} {x y : K} (hx : x ∈ W Ψ j p) (hy : y ∈ W Ψ j q) :
    x * y ∈ W Ψ j (p + q) := by
  rw [mem_W] at *
  rw [map_mul, hx, hy, smul_mul_smul_comm, pow_add]

theorem one_mem_W (j : ℕ) : (1 : K) ∈ W Ψ j 0 := by
  rw [mem_W, map_one]; simp

/-- **The Adams-weight grading** `K = ⨁ p, W j p` as a `GradedAlgebra`.-/
@[implicit_reducible] def gradedAlgebra (H : ∀ x : K, HasFilt Ψ ρ x) (hj : 2 ≤ j) : GradedAlgebra (W Ψ j) :=
  letI := (isInternal j H hj).chooseDecomposition
  { toGradedMonoid := { one_mem := one_mem_W j, mul_mem := fun {_ _ _ _} hx hy ↦ W_mul_mem j hx hy }
    toDecomposition := this }

end Decomp

/-! ## Levels, independence of `j`, `W 0`, positive weights -/

section Level

variable (j : ℕ) {V : ℕ → Submodule ℚ K} {M : ℕ}

/-- Every nonzero `x ∈ V 0` has a level: `x ∈ V m`, `x ∉ V (m+1)`.-/
theorem exists_level (hV : Filt Ψ ρ V M) {x : K} (hx0 : x ∈ V 0) (hne : x ≠ 0) :
    ∃ m, x ∈ V m ∧ x ∉ V (m + 1) := by
  classical
  have hex : ∃ n, x ∉ V (n + 1) := by
    refine ⟨M, fun h ↦ hne ?_⟩
    rw [hV.bot, Submodule.mem_bot] at h
    exact h
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  cases h : Nat.find hex with
  | zero => exact hx0
  | succ k =>
    have := Nat.find_min hex (m := k) (by omega)
    simpa using this

/-- An eigenvector of `Ψ j` for the eigenvalue `j^p` has level exactly `p`.-/
theorem eigen_level (hV : Filt Ψ ρ V M) (hj : 2 ≤ j) {x : K} (hx0 : x ∈ V 0) (hne : x ≠ 0) {p : ℕ}
    (hx : x ∈ W Ψ j p) : x ∈ V p ∧ x ∉ V (p + 1) := by
  obtain ⟨m, hm, hm'⟩ := exists_level hV hx0 hne
  have hpm : p = m := by
    by_contra hpm
    apply hm'
    have h1 := hV.eig j hj m x hm
    rw [mem_W.mp hx, ← sub_smul] at h1
    have hne' : ((j : ℚ) ^ p - (j : ℚ) ^ m) ≠ 0 := fun h ↦ hpm (pow_injective j hj (sub_eq_zero.mp h))
    have := Submodule.smul_mem _ (((j : ℚ) ^ p - (j : ℚ) ^ m)⁻¹) h1
    rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at this
  subst hpm
  exact ⟨hm, hm'⟩

variable (Ψ ρ)

/-- Eigenvectors for `j` and `j'` agree: `W j p ≤ W j' p` (given commuting `Ψ`).-/
theorem W_le_W (H : ∀ x : K, HasFilt Ψ ρ x)
    (hcomm : ∀ j j', 2 ≤ j → 2 ≤ j' → ∀ x, Ψ j (Ψ j' x) = Ψ j' (Ψ j x))
    {j j' : ℕ} (hj : 2 ≤ j) (hj' : 2 ≤ j') (p : ℕ) : W Ψ j p ≤ W Ψ j' p := by
  intro x hx
  by_cases hx0 : x = 0
  · subst hx0; exact Submodule.zero_mem _
  obtain ⟨V, M, hV, hxV⟩ := H x
  obtain ⟨hxp, -⟩ := eigen_level j hV hj hxV hx0 hx
  have hy : Ψ j' x - ((j' : ℚ) ^ p) • x ∈ V (p + 1) := hV.eig j' hj' p x hxp
  have hyW : Ψ j' x - ((j' : ℚ) ^ p) • x ∈ W Ψ j p := by
    rw [mem_W, map_sub, map_smul, hcomm j j' hj hj', mem_W.mp hx, map_smul, smul_sub, smul_comm]
  by_cases hy0 : Ψ j' x - ((j' : ℚ) ^ p) • x = 0
  · rw [mem_W]; exact sub_eq_zero.mp hy0
  · exact absurd hy
      (eigen_level j hV hj (hV.mono_nat (Nat.zero_le _) hy) hy0 hyW).2

theorem W_eq (H : ∀ x : K, HasFilt Ψ ρ x)
    (hcomm : ∀ j j', 2 ≤ j → 2 ≤ j' → ∀ x, Ψ j (Ψ j' x) = Ψ j' (Ψ j x))
    {j j' : ℕ} (hj : 2 ≤ j) (hj' : 2 ≤ j') (p : ℕ) : W Ψ j p = W Ψ j' p :=
  le_antisymm (W_le_W Ψ ρ H hcomm hj hj' p) (W_le_W Ψ ρ H hcomm hj' hj p)

variable {Ψ ρ}

theorem W_zero_eq_span (H : ∀ x : K, HasFilt Ψ ρ x) (hj : 2 ≤ j) :
    W Ψ j 0 = Submodule.span ℚ {(1 : K)} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨V, M, hV, hxV⟩ := H x
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.mp (hV.zero hxV)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    have hyW : y ∈ W Ψ j 0 := by
      have h1 : c • (1 : K) ∈ W Ψ j 0 :=
        Submodule.smul_mem _ c (one_mem_W j)
      have := Submodule.sub_mem _ hx h1
      rwa [add_sub_cancel_left] at this
    by_cases hy0 : y = 0
    · subst hy0
      simpa using ha
    · exact absurd hy (eigen_level j hV hj (hV.anti 0 hy) hy0 hyW).2
  · rw [Submodule.span_le]
    rintro _ rfl
    exact one_mem_W j

theorem rank_eq_zero_of_mem_W (H : ∀ x : K, HasFilt Ψ ρ x) (hj : 2 ≤ j) {p : ℕ} (hp : 1 ≤ p)
    {x : K} (hx : x ∈ W Ψ j p) : ρ x = 0 ∧ IsNilpotent x := by
  by_cases hx0 : x = 0
  · subst hx0; exact ⟨map_zero _, IsNilpotent.zero⟩
  obtain ⟨V, M, hV, hxV⟩ := H x
  obtain ⟨hxp, -⟩ := eigen_level j hV hj hxV hx0 hx
  have h1 : x ∈ V 1 := hV.mono_nat hp hxp
  exact ⟨hV.rank x h1, hV.nil x h1⟩

end Level

end STEPW
