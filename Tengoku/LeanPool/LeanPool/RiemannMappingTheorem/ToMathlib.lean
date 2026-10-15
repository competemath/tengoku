/-
Copyright (c) 2026 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
module

public import Tengoku

/-!
# LeanPool.RiemannMappingTheorem.ToMathlib
-/

@[expose] public section

open intervalIntegral Real MeasureTheory Filter Topology Set Metric Interval

variable {𝕜 E V : Type*} {r : ℝ} {z : ℂ} {a b t : ℝ} {n : ℕ}

/--
@isnad1 id=iscompac.0h4v.s7.0a16b61e234f from=translated src=- shape=3b7fecd4 vocab=fa0de422
-/
lemma isCompact_segment [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalAddGroup 𝕜] [CompactIccSpace 𝕜] [TopologicalSpace E] [AddCommGroup E]
    [ContinuousAdd E] [Module 𝕜 E] [ContinuousSMul 𝕜 E] {x y : E} :
    IsCompact (segment 𝕜 x y) := by
  simpa only [segment_eq_image] using isCompact_Icc.image (by continuity)

/--
@isnad1 id=eq.4h4v.s8.9fdf1e629b81 from=translated src=- shape=3e6b6dc8 vocab=01ac5bac
-/
lemma DifferentiableAt.deriv_eq_deriv_pow_div_pow {n : ℕ} (n_pos : 0 < n) {f g : ℂ → ℂ}
    (hg : ∀ᶠ z in 𝓝 z, f z = (g z) ^ n) (g_diff : DifferentiableAt ℂ g z) (fz_nonzero : f z ≠ 0) :
    deriv g z = deriv f z / (n * (g z) ^ (n - 1)) := by
  have h1 : g z ≠ 0 := fun h =>
    fz_nonzero (by simp [Eventually.self_of_nhds hg, h, n_pos.ne.symm])
  have h2 : n * (g z) ^ (n - 1) ≠ 0 := by simp [h1, n_pos.ne.symm]
  rw [(EventuallyEq.deriv hg).self_of_nhds, deriv_fun_pow g_diff, eq_div_iff h2]
  ring

/--
@isnad1 id=hasderiv.6h7v.s8.efe317cd74ef from=translated src=- shape=d93b269d vocab=915ac42c
-/
lemma has_deriv_at_integral_of_continuous_of_lip
    {φ : ℂ → ℝ → ℂ} {ψ : ℝ → ℂ} {z₀ : ℂ} {a b C δ : ℝ} (hab : a ≤ b) (δ_pos : 0 < δ)
    (φ_cts : ∀ᶠ z in 𝓝 z₀, ContinuousOn (φ z) (Icc a b))
    (φ_der : ∀ t ∈ Ioc a b, HasDerivAt (fun x => φ x t) (ψ t) z₀)
    (φ_lip : ∀ t ∈ Ioc a b, LipschitzOnWith (Real.nnabs C) (fun x => φ x t) (ball z₀ δ))
    (ψ_cts : ContinuousOn ψ (Ioc a b)) :
    HasDerivAt (fun z => ∫ t in a..b, φ z t) (∫ t in a..b, ψ t) z₀ := by
  simp only [intervalIntegral, not_lt, hab, Ioc_eq_empty, Measure.restrict_empty,
    integral_zero_measure, sub_zero]
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  have h1 : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (φ z) μ :=
    φ_cts.mono (fun z h => (h.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
  have h2 : Integrable (φ z₀) μ :=
    φ_cts.self_of_nhds.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h3 : AEStronglyMeasurable ψ μ := ψ_cts.aestronglyMeasurable measurableSet_Ioc
  have h4 : ∀ᵐ t ∂μ, LipschitzOnWith (Real.nnabs C) (fun z => φ z t) (ball z₀ δ) :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall φ_lip)
  have h5 : Integrable (fun _ => C) μ := integrable_const _
  have h6 : ∀ᵐ t ∂μ, HasDerivAt (fun z => φ z t) (ψ t) z₀ :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall φ_der)
  exact (_root_.hasDerivAt_integral_of_dominated_loc_of_lip (Metric.ball_mem_nhds z₀ δ_pos)
    h1 h2 h3 h4 h5 h6).2

section uIoo

/--
@isnad1 id=eq.0h2v.s4.917986178314 from=translated src=- shape=cd3ae65e vocab=5a4f47f7
-/
lemma uIoo_eq_union : uIoo a b = (Ioo a b) ∪ (Ioo b a) := by
  cases le_total a b <;> simp [*, uIoo]

/--
@isnad1 id=iff.0h3v.s5.ffd9a22d468d from=translated src=- shape=5f9d29ea vocab=b386b51b
-/
lemma mem_uIoo : t ∈ uIoo a b ↔ (a < t ∧ t < b) ∨ (b < t ∧ t < a) := by simp [uIoo_eq_union]

/--
@isnad1 id=eq.0h2v.s5.36fdfb5c6b0f from=translated src=- shape=d04bd30d vocab=b9640f25
-/
lemma uIoo_eq_uIoc_sdiff_ends : uIoo a b = Ι a b \ {a, b} := by
  ext t
  constructor <;> intro hh
  · rw [mem_uIoo] at hh
    rcases hh with h | h <;> simp [uIoc, h, h.2.le, h.1.ne.symm, h.2.ne]
  · simp_rw [uIoc, Set.mem_sdiff, mem_Ioc, mem_insert_iff, mem_singleton_iff] at hh
    push Not at hh
    refine ⟨hh.1.1, lt_of_le_of_ne hh.1.2 ?_⟩
    cases le_total a b <;> simp [*]

/--
@isnad1 id=eq.0h2v.s5.154b16690b19 from=translated src=- shape=d04bd30d vocab=63f69841
-/
lemma uIoo_eq_uIcc_sdiff_ends : uIoo a b = uIcc a b \ {a, b} := by
  cases le_total a b
  · simp [uIoo, uIcc, *]
  · simp [uIoo, uIcc, *, pair_comm a b]

/--
@isnad1 id=mem.1h3v.s5.5cb3979773f4 from=translated src=- shape=cc63fe7c vocab=3037b165
-/
lemma uIcc_mem_nhds (h : t ∈ uIoo a b) : uIcc a b ∈ 𝓝 t :=
  mem_of_superset (isOpen_Ioo.mem_nhds h) Set.uIoo_subset_uIcc_self

/--
@isnad1 id=mem.1h3v.s5.2e4742624a2c from=translated src=- shape=35921839 vocab=d99ac7e8
-/
lemma uIcc_mem_nhds_within (h : t ∈ uIoo a b) : uIcc a b ∈ 𝓝[Ioi t] t :=
  nhdsWithin_le_nhds (uIcc_mem_nhds h)

/--
@isnad1 id=eventual.0h2v.s5.3b38c475d6e0 from=translated src=- shape=250b1872 vocab=a46e69f9
-/
lemma eventually_mem_uIoo_of_mem_uIoc : ∀ᵐ x, x ∈ Ι a b → x ∈ uIoo a b := by
  apply eventually_of_mem (U := {a, b}ᶜ)
  · simpa only [mem_ae_iff, compl_compl, Set.insert_eq] using
      measure_union_null volume_singleton volume_singleton
  · rw [uIoo_eq_uIoc_sdiff_ends]
    exact fun t h1 h2 => ⟨h2, h1⟩
end uIoo

section helper_integral

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ℝ → E}

/--
@isnad1 id=eq.1h5v.s6.33d52bd919fe from=translated src=- shape=fafbc842 vocab=e1e22e9a
-/
lemma derivWithin_of_mem_uIoo {f : ℝ → E} (ht : t ∈ uIoo a b) :
    derivWithin f (uIcc a b) t = deriv f t := by
  rw [derivWithin, deriv, fderivWithin_of_mem_nhds (uIcc_mem_nhds ht)]

/--
@isnad1 id=eq.1h5v.s6.067cba8a18b8 from=translated src=- shape=c428a222 vocab=7d725074
-/
lemma intervalIntegral.integral_congr_uIoo' (h : EqOn f g (uIoo a b)) :
    ∫ t in a..b, f t = ∫ t in a..b, g t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [eventually_mem_uIoo_of_mem_uIoc] with t ht1 ht2 using h (ht1 ht2)

end helper_integral

namespace ContDiffOn

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {g : ℝ → ℝ}

omit [CompleteSpace E] in
/--
@isnad1 id=continuo.2h5v.s6.800db417c7bc from=translated src=- shape=8824e346 vocab=fcf25c60
-/
theorem continuousOn_derivWithin'' {n : ℕ∞} (h : ContDiffOn ℝ n f (uIcc a b)) (hn : 1 ≤ n) :
    ContinuousOn (derivWithin f (uIcc a b)) (uIcc a b) := by
  by_cases hab : a = b
  · simp [continuousOn_singleton, hab]
  · refine h.continuousOn_derivWithin (uniqueDiffOn_Icc (min_lt_max.2 hab)) ?_
    simpa

/--
@isnad1 id=eq.2h4v.s7.1b20845dc93c from=translated src=- shape=ad31f859 vocab=6c4cafcc
-/
theorem integral_eq_sub' (h : ContDiffOn ℝ 1 f (Icc a b)) (hab : a < b) :
    ∫ y in a..b, derivWithin f (Icc a b) y = f b - f a := by
  apply integral_eq_sub_of_hasDerivAt_of_le hab.le h.continuousOn
  · intro t ht
    apply ((h.differentiableOn one_ne_zero) t
      (Ioo_subset_Icc_self ht)).hasDerivWithinAt.hasDerivAt
    exact Icc_mem_nhds ht.1 ht.2
  · apply ContinuousOn.intervalIntegrable_of_Icc hab.le
    exact h.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl

/--
@isnad1 id=eq.2h4v.s7.4b807a90f4f1 from=translated src=- shape=ad31f859 vocab=5733d946
-/
theorem integral_eq_sub (h : ContDiffOn ℝ 1 f (Icc a b)) (hab : a ≤ b) :
    ∫ y in a..b, derivWithin f (Icc a b) y = f b - f a := by
  rcases lt_or_eq_of_le hab with hab | hab
  · exact h.integral_eq_sub' hab
  · simp [hab]

omit [CompleteSpace E] in
/--
@isnad1 id=eq.2h5v.s7.a695e8e4c17e from=translated src=- shape=cb44435f vocab=5addf9ed
-/
theorem integral_derivWithin_smul_comp
    (hg : ContDiffOn ℝ 1 g (uIcc a b)) (hf : ContinuousOn f (g '' uIcc a b)) :
    (∫ x in a..b, derivWithin g (uIcc a b) x • (f ∘ g) x) = (∫ x in g a..g b, f x) := by
  refine integral_deriv_smul_comp'' hg.continuousOn (fun t ht => ?_)
    (hg.continuousOn_derivWithin'' le_rfl) hf
  apply (hg.differentiableOn one_ne_zero t
    (Set.uIoo_subset_uIcc_self ht)).hasDerivWithinAt.mono_of_mem_nhdsWithin
  exact uIcc_mem_nhds_within ht

/--
@isnad1 id=eq.2h4v.s7.cbf24fa92178 from=translated src=- shape=c8e3924d vocab=77fc8ad9
-/
theorem integral_eq_sub''' (h : ContDiffOn ℝ 1 f (Icc a b)) (hab : a ≤ b) :
    ∫ y in a..b, deriv f y = f b - f a := by
  convert h.integral_eq_sub hab using 1
  apply integral_congr_uIoo
  intro t ht
  convert (derivWithin_of_mem_uIoo ht).symm using 2
  simp [uIcc, hab]

/--
@isnad1 id=eq.1h4v.s7.0f2fd59572f6 from=translated src=- shape=fb3e273d vocab=95539b92
-/
theorem integral_eq_sub_u (h : ContDiffOn ℝ 1 f (uIcc a b)) :
    ∫ y in a..b, deriv f y = f b - f a := by
  cases le_total a b <;> simp only [uIcc_of_le, uIcc_of_ge, *] at h
  · simp [integral_eq_sub''', *]
  · simp [integral_symm b a, integral_eq_sub''', *]

/--
@isnad1 id=eq.3h5v.s7.57da2c740ca2 from=translated src=- shape=51b63f6a vocab=7650abd3
-/
theorem integral_eq_sub'' (h : ContDiffOn ℝ 1 f (Icc a b)) (hab : a ≤ b) (ht : t ∈ Icc a b) :
    ∫ y in a..t, derivWithin f (Icc a b) y = f t - f a := by
  have l1 : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have l2 := (h.mono l1).integral_eq_sub''' ht.1
  rw [← l2]
  apply integral_congr_uIoo
  intro u hu
  have l3 : u ∈ uIoo a b := by
    rw [uIoo_eq_uIoc_sdiff_ends, Set.mem_sdiff, mem_uIoc, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hu
    rw [mem_uIoo]
    rcases hu.1 with ⟨hau, hut⟩ | ⟨htu, hua⟩
    · refine Or.inl ⟨hau, lt_of_le_of_ne (hut.trans ht.2) ?_⟩
      exact fun h => hu.2 (Or.inr (le_antisymm hut (h ▸ ht.2)))
    · linarith [ht.1]
  convert (derivWithin_of_mem_uIoo l3) using 2
  simp [uIcc, hab]

end ContDiffOn

/--
@isnad1 id=ex.1h2v.s5.64c228e6bf08 from=translated src=- shape=a6721e83 vocab=2ebc971d
-/
lemma exists_div_lt (a : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ n : ℕ, a / ↑(n + 1) < ε :=
  Tendsto.eventually_lt_const hε
    (tendsto_const_div_atTop_nhds_zero_nat a |>.comp (tendsto_add_atTop_nat 1)) |>.exists

section sort_finset

variable {α : Type*} [LinearOrder α] {l l1 l2 : List α} {s : Finset α}

/--
@isnad1 id=eq.5h3v.s6.90d674d67200 from=translated src=- shape=8797583d vocab=5c398c4e
-/
lemma List.Pairwise.ext (h1 : l1.Pairwise (· ≤ ·)) (h2 : l2.Pairwise (· ≤ ·))
    (h'1 : l1.Nodup) (h'2 : l2.Nodup) (h : ∀ x, x ∈ l1 ↔ x ∈ l2) : l1 = l2 :=
  List.Perm.eq_of_pairwise' h1 h2 ((List.perm_ext_iff_of_nodup h'1 h'2).2 h)

/--
@isnad1 id=eq.3h3v.s6.6f7b11003f5c from=translated src=- shape=98c81bbd vocab=94200b24
-/
lemma List.Pairwise.ext' (h1 : l1.Pairwise (· < ·)) (h2 : l2.Pairwise (· < ·))
    (h4 : ∀ x, x ∈ l1 ↔ x ∈ l2) : l1 = l2 :=
  List.Pairwise.ext h1.sortedLT.sortedLE.pairwise h2.sortedLT.sortedLE.pairwise
    h1.nodup h2.nodup h4

/--
@isnad1 id=eq.1h2v.s6.b35321adc1ef from=translated src=- shape=bf694c56 vocab=c6ec664e
-/
@[simp] lemma List.Pairwise.toFinset_sort (hl : l.Pairwise (· < ·)) :
    (l.toFinset).sort (· ≤ ·) = l :=
  List.Pairwise.ext' (l.toFinset).sortedLT_sort.pairwise hl (by simp)

end sort_finset
