import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.FiniteMultiplicity
import Tengoku.Seed.MeasureTheory.Function.Jacobian
import Tengoku.Seed.Data.Set.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Finite multiplicity and nonnegative Jacobian integration on countably many
injective measurable pieces. A null exceptional set of target values is allowed.
The final family theorem combines these analytic estimates with the conditional
semialgebraic fiber count, retaining all set and target parameters. Construction
of the pieces, control of exceptional targets, and integration on strata remain
separate manuscript obligations. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal

/--
@isnad1 id=eq.1h4v.s6.cdddb7e822f6 from=translated src=- shape=57bc3e42 vocab=1086a229
-/
theorem tsum_indicator_one_eq_ncard {ι X : Type*} (A : ι → Set X) (x : X)
    (hf : ({i | x ∈ A i}).Finite) :
    (∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x) = ({i | x ∈ A i}).ncard := by
  classical
  rw [tsum_eq_sum (s := hf.toFinset)]
  · have h (i) (hi : i ∈ hf.toFinset) : (A i).indicator (fun _ => (1 : ℝ≥0∞)) x = 1 := by
      exact Set.indicator_of_mem (s := A i) (a := x) (hf.mem_toFinset.mp hi) _
    rw [Finset.sum_congr rfl h]
    simp [Set.ncard_eq_toFinset_card _ hf]
  · intro i hi
    exact Set.indicator_of_notMem (s := A i) (a := x) (fun hx => hi (hf.mem_toFinset.mpr hx)) _

/-- The countable sheet estimate permits an exceptional null set in the target.
@isnad1 id=le.2h5v.s7.b1e69d40d1bb from=translated src=- shape=cd63d0d7 vocab=7d75b8c3
-/
theorem tsum_measure_le_mul_measure_union_of_ae_multiplicity
    {ι X : Type*} [Countable ι] [MeasurableSpace X] (μ : Measure X)
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) (N : ℕ)
    (hN : ∀ᵐ x ∂μ, ({i | x ∈ A i}).Finite ∧ ({i | x ∈ A i}).ncard ≤ N) :
    (∑' i, μ (A i)) ≤ (N : ℝ≥0∞) * μ (⋃ i, A i) := by
  have hsum : (∑' i, μ (A i)) =
      ∫⁻ x, ∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
    rw [lintegral_tsum (fun i => (measurable_const.indicator (hA i)).aemeasurable)]
    simp only [lintegral_indicator_const (hA _), one_mul]
  rw [hsum, ← lintegral_indicator_const (MeasurableSet.iUnion hA)]
  apply lintegral_mono_ae
  filter_upwards [hN] with x hx
  by_cases hm : x ∈ ⋃ i, A i
  · rw [Set.indicator_of_mem hm, tsum_indicator_one_eq_ncard A x hx.1]
    exact_mod_cast hx.2
  · rw [Set.indicator_of_notMem hm]
    have hzero (i) : (A i).indicator (fun _ => (1 : ℝ≥0∞)) x = 0 := by
      exact Set.indicator_of_notMem (fun h => hm (mem_iUnion.mpr ⟨i, h⟩)) _
    simp only [hzero, tsum_zero, le_refl]

/--
@isnad1 id=and.3h7v.s7.0d261a523873 from=translated src=- shape=362e4d9b vocab=284ad8a3
-/
theorem image_membership_count_le_fiber {ι X Y : Type*}
    (A : ι → Set X) (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (S : Set X)
    (hAS : ∀ i, A i ⊆ S) (f : X → Y) (y : Y)
    (hfinite : ({x | x ∈ S ∧ f x = y}).Finite) :
    ({i | y ∈ f '' A i}).Finite ∧
      ({i | y ∈ f '' A i}).ncard ≤ ({x | x ∈ S ∧ f x = y}).ncard := by
  classical
  let T : Set ι := {i | y ∈ f '' A i}
  let F : Set X := {x | x ∈ S ∧ f x = y}
  have hx (i : T) : ∃ x, x ∈ A i.val ∧ f x = y := i.property
  choose x hx he using hx
  let g (i : T) : F := ⟨x i, hAS i.val (hx i), he i⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have heq : x i = x j := congrArg Subtype.val hij
    exact Set.disjoint_left.mp (hdisj hne) (hx i) (heq.symm ▸ hx j)
  let : Finite F := hfinite
  let : Finite T := Finite.of_injective g hg
  exact ⟨Set.toFinite T, Nat.card_le_card_of_injective g hg⟩

/-- A finite-multiplicity Jacobian estimate for countably many disjoint
injective pieces. Construction of such pieces for the manuscript strata, and
the negligible exceptional-target set, are separate geometric obligations.
@isnad1 id=le.5h7v.s8.19377778e2ab from=translated src=- shape=f45e6a9a vocab=a4106113
-/
theorem lintegral_abs_det_le_mul_image_of_countable_pieces
    {ι E : Type*} [Countable ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (f : E → E) (f' : E → E →L[ℝ] E)
    (hderiv : ∀ i, ∀ x ∈ A i, HasFDerivWithinAt f (f' x) (A i) x)
    (hinj : ∀ i, Set.InjOn f (A i)) (N : ℕ)
    (hN : ∀ᵐ y ∂μ, ({i | y ∈ f '' A i}).Finite ∧ ({i | y ∈ f '' A i}).ncard ≤ N) :
    (∫⁻ x in ⋃ i, A i, ENNReal.ofReal |(f' x).det| ∂μ) ≤
      (N : ℝ≥0∞) * μ (f '' (⋃ i, A i)) := by
  rw [lintegral_iUnion hA hdisj]
  have he (i : ι) : (∫⁻ x in A i, ENNReal.ofReal |(f' x).det| ∂μ) = μ (f '' A i) :=
    lintegral_abs_det_fderiv_eq_addHaar_image μ (hA i) (hderiv i) (hinj i)
  simp only [he]
  rw [Set.image_iUnion]
  exact tsum_measure_le_mul_measure_union_of_ae_multiplicity μ (fun i => f '' A i)
    (fun i => measurable_image_of_fderivWithin (hA i) (hderiv i) (hinj i)) N hN

/-- The same analytic estimate with the actual whole-fiber cardinality as input,
rather than a separately assumed count of images of the injective pieces.
@isnad1 id=le.5h7v.s8.a2ed27e388e9 from=translated src=- shape=17fc8cb8 vocab=a4106113
-/
theorem lintegral_abs_det_le_mul_image_of_ae_finite_fibers
    {ι E : Type*} [Countable ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (f : E → E) (f' : E → E →L[ℝ] E)
    (hderiv : ∀ i, ∀ x ∈ A i, HasFDerivWithinAt f (f' x) (A i) x)
    (hinj : ∀ i, Set.InjOn f (A i)) (N : ℕ)
    (hN : ∀ᵐ y ∂μ, ({x | x ∈ ⋃ i, A i ∧ f x = y}).Finite ∧
      ({x | x ∈ ⋃ i, A i ∧ f x = y}).ncard ≤ N) :
    (∫⁻ x in ⋃ i, A i, ENNReal.ofReal |(f' x).det| ∂μ) ≤
      (N : ℝ≥0∞) * μ (f '' (⋃ i, A i)) := by
  apply lintegral_abs_det_le_mul_image_of_countable_pieces μ A hA hdisj f f' hderiv hinj N
  filter_upwards [hN] with y hy
  have h := image_membership_count_le_fiber A hdisj (⋃ i, A i)
    (fun i => subset_iUnion A i) f y hy.1
  exact ⟨h.1, h.2.trans hy.2⟩

end
end DuistermaatVanDerKallen
