import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MeasureTheory_exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul

set_option autoImplicit false

open MeasureTheory Topology Filter Set
open scoped Pointwise

namespace P2mBruhatSection

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Average

variable (T : Subgroup G) [MeasurableSpace T] [BorelSpace T] (τ : Measure T)

/--
@isnad1 id=isclosed.1h3v.s7.53722408ab21 from=translated src=- shape=4a6b6e2a vocab=3c296878
-/
theorem isClosedEmbedding_val_mul (hT : IsClosed (T : Set G)) (x : G) : IsClosedEmbedding fun t : T => (t : G) * x :=
  (Homeomorph.mulRight x).isClosedEmbedding.comp hT.isClosedEmbedding_subtypeVal

noncomputable def avg (ψ : G → ℝ) (x : G) : ℝ := ∫ t : T, ψ ((t : G) * x) ∂τ

variable {T τ}

/--
@isnad1 id=eq.0h6v.s7.53134c81bb50 from=translated src=- shape=b613e5fd vocab=f7614a52
-/
theorem avg_mul [τ.IsMulRightInvariant] (ψ : G → ℝ) (t₀ : T) (x : G) :
    avg T τ ψ ((t₀ : G) * x) = avg T τ ψ x := by
  unfold avg
  have : (fun t : T => ψ ((t : G) * ((t₀ : G) * x))) = fun t : T => (fun s : T => ψ ((s : G) * x)) (t * t₀) := by
    funext t
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [this, integral_mul_right_eq_self (fun s : T => ψ ((s : G) * x)) t₀]

/--
@isnad1 id=le.1h5v.s7.c0dcfc5a703c from=translated src=- shape=b57281ab vocab=1739960b
-/
theorem avg_nonneg {ψ : G → ℝ} (hψ : ∀ x, 0 ≤ ψ x) (x : G) : 0 ≤ avg T τ ψ x :=
  integral_nonneg fun _ => hψ _

/--
@isnad1 id=lt.5h5v.s8.d8a7d21d8071 from=translated src=- shape=154f201f vocab=7b2d057a
-/
theorem avg_pos [LocallyCompactSpace G] (hT : IsClosed (T : Set G)) [τ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts τ] {ψ : G → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hψ : ∀ x, 0 ≤ ψ x) {x : G} (hx : ψ x ≠ 0) : 0 < avg T τ ψ x := by
  unfold avg
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (1 : T)) ?_ ?_ (fun t => hψ _) ?_
  · exact hψc.comp (isClosedEmbedding_val_mul T hT x).continuous
  · exact hψs.comp_isClosedEmbedding (isClosedEmbedding_val_mul T hT x)
  · simpa using hx

/--
@isnad1 id=continuo.3h4v.s7.e034b77abf5a from=translated src=- shape=d9ff6c9d vocab=3355c2f0
-/
theorem continuous_avg [LocallyCompactSpace G] [SecondCountableTopology G] (hT : IsClosed (T : Set G))
    [IsLocallyFiniteMeasure τ] {ψ : G → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    Continuous (avg T τ ψ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨N, hN, hNx₀⟩ := exists_compact_mem_nhds x₀

  set s : Set T := ((↑) : T → G) ⁻¹' (tsupport ψ * N⁻¹) with hs
  have hsc : IsCompact s :=
    hT.isClosedEmbedding_subtypeVal.isCompact_preimage (hψs.mul hN.inv)
  have hF : Continuous (fun p : G × T => ψ ((p.2 : G) * p.1)) :=
    hψc.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  have hcont : Continuous fun x => ∫ t in s, ψ ((t : G) * x) ∂τ :=
    continuous_parametric_integral_of_continuous (f := fun x (t : T) => ψ ((t : G) * x))
      (by exact hF) hsc
  have heq : ∀ x ∈ N, avg T τ ψ x = ∫ t in s, ψ ((t : G) * x) ∂τ := by
    intro x hx
    unfold avg
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    by_contra hne
    apply ht
    rw [hs, mem_preimage]
    have h1 : (t : G) * x ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hne)
    refine Set.mem_mul.mpr ⟨(t : G) * x, h1, x⁻¹, Set.inv_mem_inv.mpr hx, ?_⟩
    simp
  have hev : avg T τ ψ =ᶠ[𝓝 x₀] fun x => ∫ t in s, ψ ((t : G) * x) ∂τ :=
    Filter.eventually_of_mem hNx₀ heq
  exact (hcont.continuousAt.congr hev.symm)

end Average

/--
@isnad1 id=ex.3h5v.s8.6c56c57f42c9 from=translated src=- shape=051ce943 vocab=7ba72d65
-/
theorem main [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    {E C : Set G} (hC : IsCompact C) (hE : E ⊆ (T : Set G) * C) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      ∀ x ∈ E, ∫ t : T, w ((t : G) * x) ∂τ = 1 := by
  obtain ⟨ψ, hψC, -, hψs, hψ01⟩ := exists_continuous_one_zero_of_isCompact hC isClosed_empty
    (Set.disjoint_empty C)
  have hψc : Continuous ψ := ψ.continuous
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => (hψ01 x).1
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hΨc : Continuous (avg T τ ψ) := continuous_avg hT hψc hψs
  refine ⟨fun x => ψ x / avg T τ ψ x, fun x => div_nonneg (hψ0 x) (avg_nonneg hψ0 x),
    hψc.measurable.div hΨc.measurable, ?_, ?_⟩
  · refine hψs.mono ?_
    intro x hx
    rw [Function.mem_support] at hx ⊢
    exact fun h => hx (by simp [h])
  · intro x hx
    obtain ⟨t₀, ht₀, c, hc, rfl⟩ := Set.mem_mul.mp (hE hx)
    have hpos : 0 < avg T τ ψ (t₀ * c) := by
      have := avg_mul (T := T) (τ := τ) ψ ⟨t₀, ht₀⟩ c
      simp only at this
      rw [this]
      exact avg_pos hT hψc hψs hψ0 (by rw [hψC hc]; simp)
    have hinv : ∀ t : T, avg T τ ψ ((t : G) * (t₀ * c)) = avg T τ ψ (t₀ * c) := fun t =>
      avg_mul ψ t (t₀ * c)
    simp_rw [hinv]
    rw [integral_div, div_eq_one_iff_eq hpos.ne']
    rfl

end P2mBruhatSection

/--
@isnad1 id=ex.3h5v.s8.6c56c57f42c9 from=translated src=- shape=051ce943 vocab=7ba72d65
-/
theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : MeasureTheory.Measure T) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    {E C : Set G} (hC : IsCompact C) (hE : E ⊆ (T : Set G) * C) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      ∀ x ∈ E, ∫ t : T, w ((t : G) * x) ∂τ = 1 :=
  P2mBruhatSection.main T hT τ hC hE
