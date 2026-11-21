/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Seed.Topology.UniformSpace.Ascoli
import Tengoku.Seed.Topology.MetricSpace.Equicontinuity
import Tengoku.Seed.Topology.ContinuousMap.Compact
import Tengoku.Seed.MeasureTheory.Measure.Tight

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A compact-containment criterion for continuous stochastic processes

The deterministic core below turns a uniform norm bound together with a
countable vanishing modulus into a compact subset of `C(T, ℝ)`.  It is the
Arzelà--Ascoli block used by the `L²` support-process tightness proof.
-/

open Filter Real Set MeasureTheory Topology
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {T : Type*} [PseudoMetricSpace T] [CompactSpace T]

/-- Continuous paths satisfying a uniform norm bound and a prescribed
countable modulus of continuity.-/
def continuousProcessModulusFamily
    (delta eta : ℕ → ℝ) (B : ℝ) : Set C(T, ℝ) :=
  {f | ‖f‖ ≤ B ∧ ∀ k s t, dist s t < delta k → dist (f s) (f t) ≤ eta k}

theorem uniformEquicontinuous_continuousProcessModulusFamily
    {delta eta : ℕ → ℝ} {B : ℝ}
    (hdelta : ∀ k, 0 < delta k)
    (heta : Tendsto eta atTop (nhds 0)) :
    UniformEquicontinuous
      (fun f : continuousProcessModulusFamily delta eta B ↦
        (f.1 : T → ℝ)) := by
  rw [Metric.uniformEquicontinuous_iff]
  intro epsilon hepsilon
  have hevent : ∀ᶠ k in atTop, eta k < epsilon :=
    heta (Iio_mem_nhds hepsilon)
  obtain ⟨k, hk⟩ := (eventually_atTop.1 hevent)
  refine ⟨delta k, hdelta k, fun s t hst f ↦ ?_⟩
  exact (f.property.2 k s t hst).trans_lt (hk k le_rfl)

/-- The closure of a uniformly bounded family with a vanishing countable
modulus is compact in the uniform topology on continuous paths.-/
theorem isCompact_closure_continuousProcessModulusFamily
    {delta eta : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hdelta : ∀ k, 0 < delta k)
    (heta : Tendsto eta atTop (nhds 0)) :
    IsCompact (closure
      (continuousProcessModulusFamily (T := T) delta eta B)) := by
  let S : Set C(T, ℝ) :=
    continuousProcessModulusFamily (T := T) delta eta B
  let F : C(T, ℝ) → T → ℝ := fun f ↦ f
  let compactSets : Set (Set T) := {Set.univ}
  have hcompactSets : ∀ K ∈ compactSets, IsCompact K := by
    intro K hK
    simpa only [compactSets, Set.mem_singleton_iff] using
      (hK ▸ (isCompact_univ : IsCompact (Set.univ : Set T)))
  have hclosedEmbedding : IsClosedEmbedding
      (UniformOnFun.ofFun compactSets ∘ F) := by
    let e := UniformOnFun.uniformEquivUniformFun ℝ compactSets
      (show Set.univ ∈ compactSets by simp only [compactSets, Set.mem_singleton_iff])
    have he : IsClosedEmbedding e.symm :=
      e.symm.toHomeomorph.isClosedEmbedding
    have hfun : IsClosedEmbedding
        (fun f : C(T, ℝ) ↦ UniformFun.ofFun (f : T → ℝ)) :=
      ContinuousMap.isUniformEmbedding_uniformFunOfFun.isClosedEmbedding
    have hcomp := he.comp hfun
    convert hcomp using 1
    funext f
    rfl
  have heq : ∀ K ∈ compactSets,
      EquicontinuousOn (F ∘ ((↑) : S → C(T, ℝ))) K := by
    intro K hK
    exact (uniformEquicontinuous_continuousProcessModulusFamily
      hdelta heta).equicontinuous.equicontinuousOn K
  have hpoint : ∀ K ∈ compactSets, ∀ x ∈ K,
      ∃ Q : Set ℝ, IsCompact Q ∧ ∀ f ∈ S, F f x ∈ Q := by
    intro K hK x hx
    refine ⟨Set.Icc (-B) B, isCompact_Icc, ?_⟩
    intro f hf
    have hfx : |f x| ≤ B := by
      simpa only [Real.norm_eq_abs] using
        (f.norm_coe_le_norm x).trans hf.1
    exact (abs_le.mp hfx)
  simpa only [S] using
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      hcompactSets hclosedEmbedding heq hpoint

/-- A family of laws on continuous paths is tight as soon as a uniform norm
tail and a summable family of modulus tails are available.  This formulation
is deliberately measure-theoretic: later chaining arguments only have to
provide the two displayed probability estimates.-/
theorem isTightMeasureSet_range_of_norm_and_modulus
    {I : Type*} [MeasurableSpace C(T, ℝ)]
    (nu : I → Measure C(T, ℝ))
    (delta : ℕ → ℝ) (hdelta : ∀ k, 0 < delta k)
    (hcontrol : ∀ epsilon : ℝ≥0∞, 0 < epsilon →
      ∃ B : ℝ, 0 ≤ B ∧
        ∃ eta : ℕ → ℝ, Tendsto eta atTop (nhds 0) ∧
          ∃ p : ℕ → ℝ≥0∞,
            (∑' k, p k) ≤ epsilon / 2 ∧
            (∀ i, nu i {f | B < ‖f‖} ≤ epsilon / 2) ∧
            ∀ i k, nu i {f | ∃ s t, dist s t < delta k ∧
              eta k < dist (f s) (f t)} ≤ p k) :
    IsTightMeasureSet (Set.range nu) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro epsilon hepsilon
  obtain ⟨B, hB, eta, heta, p, hp, hnorm, hmodulus⟩ :=
    hcontrol epsilon hepsilon
  let S : Set C(T, ℝ) :=
    continuousProcessModulusFamily (T := T) delta eta B
  let K : Set C(T, ℝ) := closure S
  refine ⟨K, ?_, ?_⟩
  · exact isCompact_closure_continuousProcessModulusFamily
      hB hdelta heta
  · intro m hm
    obtain ⟨i, rfl⟩ := hm
    let normBad : Set C(T, ℝ) := {f | B < ‖f‖}
    let modulusBad : ℕ → Set C(T, ℝ) := fun k ↦
      {f | ∃ s t, dist s t < delta k ∧ eta k < dist (f s) (f t)}
    have hScompl : Sᶜ ⊆ normBad ∪ ⋃ k, modulusBad k := by
      intro f hf
      by_cases hfnorm : ‖f‖ ≤ B
      · have hnotmodulus : ¬ ∀ k s t,
            dist s t < delta k → dist (f s) (f t) ≤ eta k := by
          intro h
          exact hf ⟨hfnorm, h⟩
        push_neg at hnotmodulus
        obtain ⟨k, s, t, hst, hbad⟩ := hnotmodulus
        exact Set.mem_union_right normBad
          (Set.mem_iUnion.2 ⟨k, s, t, hst, hbad⟩)
      · exact Set.mem_union_left _ (lt_of_not_ge hfnorm)
    calc
      nu i Kᶜ ≤ nu i Sᶜ := measure_mono (compl_subset_compl.mpr subset_closure)
      _ ≤ nu i (normBad ∪ ⋃ k, modulusBad k) := measure_mono hScompl
      _ ≤ nu i normBad + nu i (⋃ k, modulusBad k) := measure_union_le _ _
      _ ≤ epsilon / 2 + ∑' k, nu i (modulusBad k) :=
        add_le_add (hnorm i) (measure_iUnion_le _)
      _ ≤ epsilon / 2 + ∑' k, p k :=
        add_le_add_right (ENNReal.tsum_le_tsum (hmodulus i)) _
      _ ≤ epsilon / 2 + epsilon / 2 := add_le_add_right hp _
      _ = epsilon := ENNReal.add_halves epsilon

/-- The strict modulus-violation event is open in the uniform topology.-/
theorem isOpen_continuousProcessModulusBad (delta eta : ℝ) :
    IsOpen {f : C(T, ℝ) | ∃ s t, dist s t < delta ∧
      eta < dist (f s) (f t)} := by
  rw [isOpen_iff_forall_mem_open]
  intro f hf
  obtain ⟨s, t, hst, hft⟩ := hf
  let U : Set C(T, ℝ) := {g | eta < dist (g s) (g t)}
  refine ⟨U, ?_, ?_, hft⟩
  · intro g hg
    exact ⟨s, t, hst, hg⟩
  · exact isOpen_lt continuous_const
      ((continuous_eval_const s).dist (continuous_eval_const t))

/-- Real-probability version of the compact-containment criterion, stated
directly for stochastic processes.  It handles the conversion to pushforward
laws and to `ENNReal` internally.-/
theorem isTightMeasureSet_range_map_of_real_norm_and_modulus
    {I Omega : Type*} [MeasurableSpace Omega]
    [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (Y : I → Omega → C(T, ℝ))
    (hY : ∀ i, AEMeasurable (Y i) mu)
    (delta : ℕ → ℝ) (hdelta : ∀ k, 0 < delta k)
    (hcontrol : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ B : ℝ, 0 ≤ B ∧
        ∃ eta : ℕ → ℝ, Tendsto eta atTop (nhds 0) ∧
          ∃ p : ℕ → ℝ,
            (∀ k, 0 ≤ p k) ∧ Summable p ∧
            (∑' k, p k) ≤ epsilon / 2 ∧
            (∀ i, mu.real {omega | B < ‖Y i omega‖} ≤ epsilon / 2) ∧
            ∀ i k, mu.real {omega | ∃ s t, dist s t < delta k ∧
              eta k < dist (Y i omega s) (Y i omega t)} ≤ p k) :
    IsTightMeasureSet (Set.range fun i ↦ mu.map (Y i)) := by
  apply isTightMeasureSet_range_of_norm_and_modulus
    (fun i ↦ mu.map (Y i)) delta hdelta
  intro epsilon hepsilon
  by_cases hepsilonTop : epsilon = ∞
  · have hhalf : epsilon / 2 = ∞ := by
      rw [hepsilonTop, ENNReal.top_div_of_ne_top]
      norm_num
    refine ⟨0, by norm_num, fun _ ↦ 0, tendsto_const_nhds, fun _ ↦ ∞,
        ?_, ?_, ?_⟩
    · rw [hhalf]
      exact le_top
    · intro i
      rw [hhalf]
      exact le_top
    · intro i k
      exact le_top
  · let epsilonReal := epsilon.toReal
    have hepsilonReal : 0 < epsilonReal :=
      ENNReal.toReal_pos hepsilon.ne' hepsilonTop
    obtain ⟨B, hB, eta, heta, p, hpnonneg, hpsum, hp,
      hnorm, hmodulus⟩ := hcontrol epsilonReal hepsilonReal
    let pENN : ℕ → ℝ≥0∞ := fun k ↦ ENNReal.ofReal (p k)
    refine ⟨B, hB, eta, heta, pENN, ?_, ?_, ?_⟩
    · rw [← ENNReal.ofReal_tsum_of_nonneg hpnonneg hpsum]
      have hepsilonEq : ENNReal.ofReal epsilonReal = epsilon := by
        exact ENNReal.ofReal_toReal hepsilonTop
      calc
        ENNReal.ofReal (∑' k, p k) ≤
            ENNReal.ofReal (epsilonReal / 2) :=
          ENNReal.ofReal_le_ofReal hp
        _ = ENNReal.ofReal epsilonReal / ENNReal.ofReal 2 :=
          ENNReal.ofReal_div_of_pos (by norm_num)
        _ = epsilon / 2 := by rw [hepsilonEq]; norm_num
    · intro i
      let normBad : Set C(T, ℝ) := {f | B < ‖f‖}
      have hnormBad : MeasurableSet normBad :=
        (isOpen_lt continuous_const continuous_norm).measurableSet
      rw [Measure.map_apply_of_aemeasurable (hY i) hnormBad]
      apply (ENNReal.toReal_le_toReal (measure_ne_top mu _)
        (ENNReal.div_ne_top hepsilonTop (by norm_num))).1
      change mu.real {omega | B < ‖Y i omega‖} ≤ (epsilon / 2).toReal
      rw [ENNReal.toReal_div]
      norm_num
      exact hnorm i
    · intro i k
      let modulusBad : Set C(T, ℝ) :=
        {f | ∃ s t, dist s t < delta k ∧
          eta k < dist (f s) (f t)}
      have hmodulusBad : MeasurableSet modulusBad :=
        (isOpen_continuousProcessModulusBad (T := T)
          (delta k) (eta k)).measurableSet
      rw [Measure.map_apply_of_aemeasurable (hY i) hmodulusBad]
      apply (ENNReal.toReal_le_toReal (measure_ne_top mu _)
        (ENNReal.ofReal_ne_top)).1
      change mu.real {omega | ∃ s t, dist s t < delta k ∧
        eta k < dist (Y i omega s) (Y i omega t)} ≤
          (ENNReal.ofReal (p k)).toReal
      rw [ENNReal.toReal_ofReal (hpnonneg k)]
      exact hmodulus i k

/-- Direct compact-containment form of the preceding criterion.  A single
bad event may simultaneously account for the norm and all modulus scales;
this is useful when one shared truncation remainder controls every scale.-/
theorem isTightMeasureSet_range_map_of_real_compactContainment
    {I Omega : Type*} [MeasurableSpace Omega]
    [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (Y : I → Omega → C(T, ℝ))
    (hY : ∀ i, AEMeasurable (Y i) mu)
    (delta : ℕ → ℝ) (hdelta : ∀ k, 0 < delta k)
    (hcontrol : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ B : ℝ, 0 ≤ B ∧
        ∃ eta : ℕ → ℝ, Tendsto eta atTop (nhds 0) ∧
          ∀ i, mu.real {omega |
            B < ‖Y i omega‖ ∨
              ∃ k s t, dist s t < delta k ∧
                eta k < dist (Y i omega s) (Y i omega t)} ≤ epsilon) :
    IsTightMeasureSet (Set.range fun i ↦ mu.map (Y i)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro epsilon hepsilon
  by_cases hepsilonTop : epsilon = ∞
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro m hm
    rw [hepsilonTop]
    exact le_top
  · let epsilonReal := epsilon.toReal
    have hepsilonReal : 0 < epsilonReal :=
      ENNReal.toReal_pos hepsilon.ne' hepsilonTop
    obtain ⟨B, hB, eta, heta, hbad⟩ :=
      hcontrol epsilonReal hepsilonReal
    let S : Set C(T, ℝ) :=
      continuousProcessModulusFamily (T := T) delta eta B
    let K : Set C(T, ℝ) := closure S
    refine ⟨K, isCompact_closure_continuousProcessModulusFamily
      hB hdelta heta, ?_⟩
    intro m hm
    obtain ⟨i, rfl⟩ := hm
    let bad : Set C(T, ℝ) := {f |
      B < ‖f‖ ∨ ∃ k s t, dist s t < delta k ∧
        eta k < dist (f s) (f t)}
    have hbadOpen : IsOpen bad := by
      rw [show bad = ({f : C(T, ℝ) | B < ‖f‖} ∪
          ⋃ k, {f : C(T, ℝ) | ∃ s t, dist s t < delta k ∧
            eta k < dist (f s) (f t)}) by
        ext f
        simp only [bad, Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion]]
      apply IsOpen.union (isOpen_lt continuous_const continuous_norm)
      exact isOpen_iUnion fun k ↦
        isOpen_continuousProcessModulusBad (T := T) (delta k) (eta k)
    have hKcompl : Kᶜ ⊆ bad := by
      intro f hf
      have hfS : f ∉ S := fun hfmem ↦ hf (subset_closure hfmem)
      by_cases hfnorm : ‖f‖ ≤ B
      · right
        have hnotmodulus : ¬ ∀ k s t,
            dist s t < delta k → dist (f s) (f t) ≤ eta k := by
          intro h
          exact hfS ⟨hfnorm, h⟩
        push Not at hnotmodulus
        exact hnotmodulus
      · exact Or.inl (lt_of_not_ge hfnorm)
    calc
      (mu.map (Y i)) Kᶜ ≤ (mu.map (Y i)) bad := measure_mono hKcompl
      _ = mu (Y i ⁻¹' bad) :=
        Measure.map_apply_of_aemeasurable (hY i) hbadOpen.measurableSet
      _ ≤ epsilon := by
        apply (ENNReal.toReal_le_toReal (measure_ne_top mu _) hepsilonTop).1
        change mu.real {omega |
          B < ‖Y i omega‖ ∨ ∃ k s t, dist s t < delta k ∧
            eta k < dist (Y i omega s) (Y i omega t)} ≤ epsilon.toReal
        exact hbad i

end ProbabilityTheory
