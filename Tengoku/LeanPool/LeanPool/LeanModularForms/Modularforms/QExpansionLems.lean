/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Tengoku.Seed.Analysis.CStarAlgebra.Classes
public import Tengoku.Seed.NumberTheory.ModularForms.QExpansion
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool
namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # QExpansionLems -/

@[expose] public section

open ModularForm UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

open scoped Real MatrixGroups CongruenceSubgroup

/--
@isnad1 id=tendsto.0h4v.s8.956b38f88c16 from=translated src=- shape=69f707e4 vocab=4bcd9d5e
-/
theorem modform_tendto_ndhs_zero {k : ℤ} (n : ℕ) [ModularFormClass F Γ(n) k] [inst : NeZero n] :
    Tendsto (fun x ↦ (⇑f ∘ ↑ofComplex) (Periodic.invQParam (↑n) x)) (𝓝[≠] 0)
    (𝓝 (cuspFunction n f 0)) := by
  simp only [comp_apply]
  have hi : IsCusp OnePoint.infty Γ(n) :=
    Γ(n).isCusp_of_mem_strictPeriods (h := n) (by have h := inst.1; positivity) (by simp)
  have h1 := Function.Periodic.boundedAtFilter_cuspFunction (h := n)
    (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n)
    ((OnePoint.isBoundedAt_infty_iff.mp (ModularFormClass.bdd_at_cusps f hi)).comp_tendsto
      tendsto_comap_im_ofComplex)
  have h2 : Tendsto (cuspFunction n f) (𝓝[≠] 0) (𝓝 (cuspFunction n f 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply (Function.Periodic.differentiableAt_cuspFunction_zero (h := n)
      (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n) ?_ ?_ ?_).continuousAt.tendsto
    · apply SlashInvariantFormClass.periodic_comp_ofComplex
      simp
    · simp only [eventually_comap, eventually_atTop]
      use 1
      intro b hb a ha
      refine UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo f ⟨a, ?_⟩)
      rw [ha]
      linarith
    exact (OnePoint.isBoundedAt_infty_iff.mp (ModularFormClass.bdd_at_cusps f hi)).comp_tendsto
      tendsto_comap_im_ofComplex
  apply h2.congr'
  rw [@eventuallyEq_nhdsWithin_iff, eventually_iff_exists_mem]
  use ball 0 1
  constructor
  · apply Metric.ball_mem_nhds
    exact Real.zero_lt_one
  intro y hy hy0
  apply Function.Periodic.cuspFunction_eq_of_nonzero
  simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using hy0

/--
@isnad1 id=eq.2h3v.s8.c04d5b670d9f from=translated src=- shape=e7cf2930 vocab=e725603c
-/
theorem derivWithin_mul2 (f g : ℂ → ℂ) (s : Set ℂ) (hf : DifferentiableOn ℂ f s)
    (hd : DifferentiableOn ℂ g s) :
    s.domRestrict (derivWithin (fun y => f y * g y) s) =
      s.domRestrict (derivWithin f s * g + f * derivWithin g s) := by
  ext y
  simp only [domRestrict_apply, Pi.add_apply, Pi.mul_apply]
  rw [derivWithin_fun_mul (hf y y.2) (hd y y.2)]

/--
@isnad1 id=eq.4h5v.s7.dcb76bdaa0a4 from=translated src=- shape=19232849 vocab=b5bf270d
-/
lemma iteratedDerivWithin_mul' (f g : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s)
    (x : ℂ) (hx : x ∈ s) (m : ℕ)
    (hf : ContDiffOn ℂ ⊤ f s) (hg : ContDiffOn ℂ ⊤ g s) :
    iteratedDerivWithin m (f * g) s x =
    ∑ i ∈ Finset.range m.succ, (m.choose i) * (iteratedDerivWithin i f s x) *
    (iteratedDerivWithin (m - i) g s x) := by
  induction m generalizing f g with
  | zero => simp_all
  | succ m hm =>
    have h1 :=
      derivWithin_mul2 f g s (hf.differentiableOn (by simp)) (hg.differentiableOn (by simp))
    have h2 : (fun y => f y * g y) = f * g := by ext y; simp
    rw [iteratedDerivWithin_succ']
    have hset : s.EqOn (derivWithin (f * g) s) (derivWithin f s * g + f * derivWithin g s) := by
      rw [← h2]
      exact Set.domRestrict_eq_domRestrict_iff.mp h1
    rw [iteratedDerivWithin_congr hset hx, iteratedDerivWithin_add hx hs.uniqueDiffOn, hm _ _ hf,
      hm _ _ _ hg]
    · simp_rw [←iteratedDerivWithin_succ']
      have := Finset.sum_choose_succ_mul (fun i => fun j =>
        ((iteratedDerivWithin i f s x) * (iteratedDerivWithin j g s x)) ) m
      simp only [Nat.succ_eq_add_one] at *
      rw [show m + 1 + 1 = m + 2 by ring]
      simp_rw [← mul_assoc] at *
      rw [this, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intros i hi
      congr
      simp at hi
      omega
    · exact ContDiffOn.derivWithin hf (by exact IsOpen.uniqueDiffOn hs) (m := ⊤) (by simp)
    · exact ContDiffOn.derivWithin hg (by exact IsOpen.uniqueDiffOn hs) (m := ⊤) (by simp)
    · apply ContDiffOn.mul
      · exact ContDiffOn.derivWithin hf (by exact IsOpen.uniqueDiffOn hs) (m := m) (by simp)
      · apply ContDiffOn.of_le hg (by simp)
      exact hx
    · apply ContDiffOn.mul
      · apply ContDiffOn.of_le hf (by simp)
      · apply ContDiffOn.derivWithin hg (by exact IsOpen.uniqueDiffOn hs) (m := m) (by simp)
      exact hx

/--
@isnad1 id=eq.0h5v.s10.9fd94006edf0 from=translated src=- shape=4559be1d vocab=ffd7e88f
-/
lemma qExpansion_mul_coeff (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [hn : NeZero n] : qExpansion n (f.mul g) = qExpansion n f * qExpansion n g := by
  simpa using
    (ModularForm.qExpansion_mul (Γ := Γ(n)) (h := n)
      (hh := by exact Nat.cast_pos.mpr (Nat.pos_of_neZero n))
      (hΓ := by simp) f g)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/--
@isnad1 id=eq.0h3v.s6.ff4eba00277c from=translated src=- shape=73a6c98a vocab=3a22b3f3
-/
lemma IteratedDeriv_smul (a : ℂ) (f : ℂ → ℂ) (m : ℕ) :
    iteratedDeriv m (a • f) = a • iteratedDeriv m f := by
  induction m with
  | zero => simp
  | succ m hm =>
    ext x; simp_all

/--
@isnad1 id=eq.0h4v.s9.582908fe98ce from=translated src=- shape=b89bfe35 vocab=95d60d7d
-/
lemma qExpansion_smul2 (a : ℂ) (f : ModularForm Γ(n) k) [NeZero n] :
    (a • qExpansion n f) = (qExpansion n (a • f)) :=
  (ModularForm.qExpansion_smul (Γ := Γ(n)) (h := n)
      (hh := Nat.cast_pos.mpr (Nat.pos_of_neZero n)) (hΓ := by simp) a f).symm

instance instFunLikeUpperHalfPlaneFun :
    FunLike (ℍ → ℂ) ℍ ℂ := { coe := fun ⦃a₁⦄ ↦ a₁, coe_injective := fun ⦃_ _⦄ a ↦ a}

/--
@isnad1 id=eq.1h2v.s5.331e43efcb81 from=translated src=- shape=20e6682e vocab=0ad5e463
-/
lemma qExpansion_ext (f g : ℍ → ℂ) (h : f = g) : qExpansion 1 f =
    qExpansion 1 g := by rw [h]

/--
@isnad1 id=eq.1h5v.s6.de997c0906a5 from=translated src=- shape=bce166db vocab=caae2f1b
-/
lemma cuspFunction_congr_funLike
    {α β : Type*} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ] (n : ℕ) (f : α) (g : β) (h : ⇑f = ⇑g) :
    cuspFunction n f = cuspFunction n g := by
  simp_all

/--
@isnad1 id=eq.1h4v.s6.01c8930b5e51 from=translated src=- shape=8075f59f vocab=dfb95bad
-/
lemma qExpansion_ext2 {α β : Type*} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ] (f : α) (g : β) (h : ⇑f = ⇑g) :
    qExpansion 1 f = qExpansion 1 g := by
  ext m; simp [qExpansion_coeff, congrArg (cuspFunction 1) h]

--generalize this away from ℂ
/--
@isnad1 id=eq.0h2v.s5.2fe2af800cfb from=translated src=- shape=98c7f06b vocab=7c718352
-/
lemma IteratedDeriv_zero_fun (n : ℕ) (z : ℂ) : iteratedDeriv n (fun _ : ℂ => (0 : ℂ)) z = 0 := by
  induction n <;> simp

/--
@isnad1 id=eq.1h2v.s5.2dbf80ec7edb from=translated src=- shape=5ec886e2 vocab=8e535b1d
-/
lemma iteratedDeriv_const_eq_zero (m : ℕ) (hm : 0 < m) (c : ℂ) :
    iteratedDeriv m (fun _ : ℂ => c) = fun _ : ℂ => 0 := by
  ext z; simpa only [add_zero, IteratedDeriv_zero_fun] using
    iteratedDeriv_const_add hm (f := fun (x : ℂ) => (0 : ℂ)) c (x := z)

/--
@isnad1 id=eq.0h3v.s13.431577353842 from=translated src=- shape=250e9e76 vocab=053e569c
-/
lemma qExpansion_pow (f : ModularForm Γ(1) k) (n : ℕ) :
  qExpansion 1 ((((DirectSum.of (ModularForm Γ(1)) k ) f) ^ n) (n * k)) = (qExpansion 1 f) ^ n := by
  exact_mod_cast
    (qExpansion_of_pow (Γ := Γ(1)) (h := (1 : ℕ))
      (hh := by positivity) (hΓ := by simp) (f := f) (n := n))
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
