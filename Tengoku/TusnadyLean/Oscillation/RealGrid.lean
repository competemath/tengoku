import Tengoku.TusnadyLean.Oscillation.Model
import Tengoku.TusnadyLean.Oscillation.FiniteAverage
import Tengoku.TusnadyLean.Riesz.ConditionalGridProduct
import Tengoku.TusnadyLean.Riesz.Colorings
import Tengoku.Seed.Analysis.Normed.Group.Bounded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The finite endpoint model is realized by genuine uniform real coordinates. -/
namespace Oscillation
noncomputable section
open MeasureTheory Riesz Riesz.PointSets Riesz.Occupancy
open scoped BigOperators

/--
@isnad1 id=le.1h6v.s5.fdbfdcf7c21d from=translated src=- shape=881cf7d3 vocab=813c743a
-/
lemma endpointValue_abs_le {n : ℕ} (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1)
    (p Y : Fin n → ℕ) (c y : ℕ) : |endpointValue χ p Y c y| ≤ n := by
  unfold endpointValue
  calc
    |∑ i, χ i * (if Y i < y then 1 else 0) * endpointWeight (p i) c|
      ≤ ∑ i, |χ i * (if Y i < y then 1 else 0) * endpointWeight (p i) c| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · simp only [mul_one, abs_mul, abs_of_nonneg (endpointWeight_nonneg _ _)]
        exact (mul_le_mul_of_nonneg_right (hχ i) (endpointWeight_nonneg _ _)).trans
          (by simpa using endpointWeight_le_one (p i) c)
      · simp
    _ = n := by simp

/--
@isnad1 id=le.2h7v.s6.a3845c34552c from=translated src=- shape=9f627447 vocab=449b4314
-/
lemma gridPotential_le_two_n {n : ℕ} (K V m : ℕ) (hm : 0 < m)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1) (p Y : Fin n → ℕ) :
    gridPotential K V m hm χ p Y ≤ 2 * n := by
  by_cases hKV : K * V = 0
  · simp [gridPotential, hKV]
  have hKVp : 0 < (K * V : ℕ) := Nat.pos_of_ne_zero hKV
  unfold gridPotential
  apply (div_le_iff₀ (by exact_mod_cast hKVp)).mpr
  calc
    (∑ c : Fin K, ∑ v : Fin V, gridOsc hm (blockValues χ p Y c.val v.val))
      ≤ ∑ _ : Fin K, ∑ _ : Fin V, (2 * n : ℝ) := by
        apply Finset.sum_le_sum
        intro c _
        apply Finset.sum_le_sum
        intro v _
        exact gridOsc_le hm _ (fun t ↦ endpointValue_abs_le χ hχ p Y _ _)
    _ = 2 * n * (K * V : ℕ) := by simp; ring

def sampleCells (n K : ℕ) (hK : 0 < K) (U : Fin n → ℝ) : Fin n → ℕ :=
  fun i ↦ (finiteGridIndex K hK (U i)).val

/--
@isnad1 id=measurab.1h2v.s5.3a44ac42ab10 from=translated src=- shape=0df4fd8e vocab=ab614242
-/
lemma measurable_sampleCells (n K : ℕ) (hK : 0 < K) : Measurable (sampleCells n K hK) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_of_countable (fun x : Fin K ↦ x.val)).comp
    ((measurable_finiteGridIndex K hK).comp (measurable_pi_apply i))

/--
@isnad1 id=eq.1h2v.s6.21b09167f914 from=translated src=- shape=17e03c73 vocab=37ab7436
-/
lemma finiteGridIndex_val_eq (K : ℕ) (hK : 0 < K) (x : ℝ) :
    (finiteGridIndex K hK x).val =
      if 0 ≤ gridIndex K x ∧ gridIndex K x < (K : ℤ) then (gridIndex K x).toNat else 0 := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
  · obtain ⟨hl, hu⟩ := gridIndex_bounds K hK hx
    have hlZ : (0 : ℤ) ≤ gridIndex K x := by exact_mod_cast hl
    have huZ : gridIndex K x < (K : ℤ) := by
      have hh : (gridIndex K x : ℝ) < K := by linarith
      exact_mod_cast hh
    simp [finiteGridIndex, hx, hlZ, huZ]
  · have hnot : ¬(0 ≤ gridIndex K x ∧ gridIndex K x < (K : ℤ)) := by
      rintro ⟨hl, hu⟩
      have hlo : (1 : ℤ) ≤ ⌈(K : ℝ) * x⌉ := by unfold gridIndex at hl; omega
      have hhi : ⌈(K : ℝ) * x⌉ ≤ (K : ℤ) := by unfold gridIndex at hu; omega
      apply hx
      have hhlo := Int.one_le_ceil_iff.mp hlo
      have hhhi := Int.ceil_le.mp hhi
      norm_cast at hhhi
      exact ⟨by nlinarith, by nlinarith⟩
    simp [finiteGridIndex, hx, hnot]

/--
@isnad1 id=measurab.1h2v.s5.d13e764e9436 from=translated src=- shape=0df4fd8e vocab=1130dc3e
-/
lemma measurable_sampleCells_grid (n K : ℕ) (hK : 0 < K) :
    Measurable[sampleGridSigma n K] (sampleCells n K hK) := by
  let g : (Fin n → ℤ) → (Fin n → ℕ) := fun p i ↦
    if 0 ≤ p i ∧ p i < (K : ℤ) then (p i).toNat else 0
  have he : sampleCells n K hK = g ∘ sampleGridIndex n K := by
    funext U i
    exact finiteGridIndex_val_eq K hK (U i)
  rw [he]
  exact (measurable_of_countable g).comp (Measurable.of_comap_le le_rfl)

/--
@isnad1 id=eventual.0h1v.s6.adc46f5b5015 from=translated src=- shape=fba2ebe8 vocab=2b7d3541
-/
lemma ae_sample_unit (n : ℕ) : ∀ᵐ U ∂(Measure.pi (fun _ : Fin n ↦ μI)),
    ∀ i, U i ∈ Set.Ioc (0 : ℝ) 1 := by
  apply ae_all_iff.mpr
  intro i
  exact Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n ↦ μI)
    (i := i) (by change ∀ᵐ x ∂μI, x ∈ Set.Ioc (0 : ℝ) 1; rw [ae_iff]; exact μI_compl_Ioc)

/--
@isnad1 id=eq.2h3v.s6.504f99054ffb from=translated src=- shape=ac5c1c04 vocab=b291eb4c
-/
lemma sampleCells_eq_toNat {n K : ℕ} (hK : 0 < K) (U : Fin n → ℝ)
    (hU : ∀ i, U i ∈ Set.Ioc (0 : ℝ) 1) :
    sampleCells n K hK U = fun i ↦ (sampleGridIndex n K U i).toNat := by
  funext i
  have he := finiteGridIndex_eq hK (hU i)
  simpa [sampleCells, sampleGridIndex] using congrArg Int.toNat he

/--
@isnad1 id=eq.3h3v.s6.224c3b3579c6 from=translated src=- shape=e17c2152 vocab=ff318c84
-/
lemma finiteGridIndex_refine {K b : ℕ} (hK : 0 < K) (hb : 0 < b) {x : ℝ}
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    (finiteGridIndex (b * K) (Nat.mul_pos hb hK) x).val =
      b * (finiteGridIndex K hK x).val + (freshGridIndex K b hb x).val := by
  have hq := gridIndex_mul_ediv K b hb x
  have hr := freshGridIndex_eq_emod K b hK hb x
  have h1 := finiteGridIndex_eq hK hx
  have h2 := finiteGridIndex_eq (Nat.mul_pos hb hK) hx
  have hid := Int.emod_add_mul_ediv (gridIndex (K * b) x) (b : ℤ)
  rw [hq, ← hr, ← h1, Nat.mul_comm K b, ← h2] at hid
  have hh : (finiteGridIndex (b*K) (Nat.mul_pos hb hK) x).val =
      (freshGridIndex K b hb x).val + b * (finiteGridIndex K hK x).val := by
    exact_mod_cast hid.symm
  simpa only [add_comm] using hh

/--
@isnad1 id=eq.3h4v.s6.c76c90939554 from=translated src=- shape=5a3387e8 vocab=346aea46
-/
lemma sampleCells_refine {n K b : ℕ} (hK : 0 < K) (hb : 0 < b) (U : Fin n → ℝ)
    (hU : ∀ i, U i ∈ Set.Ioc (0 : ℝ) 1) :
    sampleCells n (b * K) (Nat.mul_pos hb hK) U =
      refinedPositions (sampleCells n K hK U) (sampleFreshIndex n K b hb U) := by
  funext i
  exact finiteGridIndex_refine hK hb (hU i)

def actualPotential {n : ℕ} (K V m : ℕ) (hK : 0 < K) (hm : 0 < m)
    (χ : Fin n → ℝ) (Y : Fin n → ℕ) (U : Fin n → ℝ) : ℝ :=
  gridPotential K V m hm χ (sampleCells n K hK U) Y

/--
@isnad1 id=measurab.2h6v.s6.357935977ea7 from=translated src=- shape=334531db vocab=f22d6518
-/
lemma measurable_actualPotential {n : ℕ} (K V m : ℕ) (hK : 0 < K) (hm : 0 < m)
    (χ : Fin n → ℝ) (Y : Fin n → ℕ) :
    Measurable (actualPotential K V m hK hm χ Y) := by
  exact (measurable_of_countable (fun p : Fin n → ℕ ↦ gridPotential K V m hm χ p Y)).comp
    (measurable_sampleCells n K hK)

/--
@isnad1 id=integrab.4h10v.s7.524c3135a401 from=translated src=- shape=6514921d vocab=ec7a14fe
-/
lemma integrable_continuous_gridPotential {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n : ℕ} (K V m : ℕ) (hm : 0 < m)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1) (Y : Fin n → ℕ)
    (p : Ω → (Fin n → ℕ)) (hp : Measurable p) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    Integrable (fun ω ↦ φ (gridPotential K V m hm χ (p ω) Y)) μ := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) (2 * n)) hφ.continuousOn
  apply Integrable.of_bound
    (hφ.measurable.comp ((measurable_of_countable
      (fun q : Fin n → ℕ ↦ gridPotential K V m hm χ q Y)).comp hp)).aestronglyMeasurable B
  exact Filter.Eventually.of_forall (fun ω ↦ hB _ ⟨gridPotential_nonneg _ _ _ _ _ _ _,
    gridPotential_le_two_n K V m hm χ hχ (p ω) Y⟩)

/--
@isnad1 id=eventual.5h8v.s8.e983d91071f6 from=translated src=- shape=67f14774 vocab=f7c89d97
-/
theorem condExp_actualPotential_refined {n K V m b : ℕ} (hK : 0 < K)
    (hm : 0 < m) (hb : 0 < b) (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1)
    (Y : Fin n → ℕ) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    (Measure.pi (fun _ : Fin n ↦ μI))[
      (fun U ↦ φ (actualPotential (b*K) V (b*m) (Nat.mul_pos hb hK)
        (Nat.mul_pos hb hm) χ Y U)) | sampleGridSigma n K] =ᵐ[Measure.pi (fun _ : Fin n ↦ μI)]
    (fun U ↦ finAvg (fun r : Fin n → Fin b ↦ φ (gridPotential (b*K) V (b*m)
      (Nat.mul_pos hb hm) χ (refinedPositions (sampleCells n K hK U) r) Y))) := by
  let μ := Measure.pi (fun _ : Fin n ↦ μI)
  let H : (Fin n → ℤ) → (Fin n → Fin b) → ℝ := fun p r ↦
    φ (gridPotential (b*K) V (b*m) (Nat.mul_pos hb hm) χ
      (refinedPositions (fun i ↦ (p i).toNat) r) Y)
  have hp : Measurable (fun U ↦ refinedPositions
      (fun i ↦ (sampleGridIndex n K U i).toNat) (sampleFreshIndex n K b hb U)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_of_countable (fun p : ℤ × Fin b ↦ b * p.1.toNat + p.2.val)).comp
      (((measurable_pi_apply i).comp (measurable_sampleGridIndex n K)).prodMk
        ((measurable_pi_apply i).comp (measurable_sampleFreshIndex n K b hb)))
  have hH : Integrable (fun U ↦ H (sampleGridIndex n K U) (sampleFreshIndex n K b hb U)) μ :=
    integrable_continuous_gridPotential μ (b*K) V (b*m) (Nat.mul_pos hb hm) χ hχ Y _ hp φ hφ
  have hcond := condExp_freshGrid_with_past n K b hK hb H hH
  have heq : (fun U ↦ φ (actualPotential (b*K) V (b*m) (Nat.mul_pos hb hK)
      (Nat.mul_pos hb hm) χ Y U)) =ᵐ[μ]
      (fun U ↦ H (sampleGridIndex n K U) (sampleFreshIndex n K b hb U)) := by
    filter_upwards [ae_sample_unit n] with U hU
    unfold actualPotential
    rw [sampleCells_refine hK hb U hU, sampleCells_eq_toNat hK U hU]
  have hc := condExp_congr_ae (m := sampleGridSigma n K) heq
  filter_upwards [hc, hcond, ae_sample_unit n] with U h1 h2 hU
  rw [h1, h2]
  rw [sampleCells_eq_toNat hK U hU]
  simp only [finAvg, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rfl

/--
@isnad1 id=iff.2h3v.s6.6414a030e888 from=translated src=- shape=6b0dab94 vocab=4ed5ec7c
-/
lemma finiteGridIndex_lt_iff {K : ℕ} (hK : 0 < K) {x : ℝ}
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) (s : ℕ) :
    (finiteGridIndex K hK x).val < s ↔ x ≤ (s : ℝ) / K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have he := finiteGridIndex_eq hK hx
  constructor
  · intro h
    have hz : gridIndex K x < (s : ℤ) := by rw [← he]; exact_mod_cast h
    have hc : ⌈(K : ℝ) * x⌉ ≤ (s : ℤ) := by unfold gridIndex at hz; omega
    have hr := Int.ceil_le.mp hc
    exact (le_div_iff₀ hKR).mpr (by simpa [mul_comm] using hr)
  · intro h
    have hr := (le_div_iff₀ hKR).mp h
    have hc : ⌈(K : ℝ) * x⌉ ≤ (s : ℤ) := Int.ceil_le.mpr (by simpa [mul_comm] using hr)
    have hz : gridIndex K x < (s : ℤ) := by unfold gridIndex; omega
    rw [← he] at hz
    exact_mod_cast hz

def finiteCount {n : ℕ} (χ : Fin n → ℝ) (p Y : Fin n → ℕ) (x y : ℕ) : ℝ :=
  ∑ i, if p i < x ∧ Y i < y then χ i else 0

/--
@isnad1 id=eq.0h2v.s6.de6d6eb07a92 from=translated src=- shape=07ea14fb vocab=bb6995f6
-/
lemma endpointWeight_eq_average (p c : ℕ) : endpointWeight p c =
    ((if p < c then (1 : ℝ) else 0) + (if p < c + 1 then 1 else 0)) / 2 := by
  unfold endpointWeight
  split_ifs <;> norm_num at * <;> omega

/--
@isnad1 id=eq.0h6v.s6.4b292d9268a5 from=translated src=- shape=75d3445c vocab=75abbd01
-/
lemma endpointValue_eq_average {n : ℕ} (χ : Fin n → ℝ) (p Y : Fin n → ℕ)
    (c y : ℕ) : endpointValue χ p Y c y = (finiteCount χ p Y c y +
      finiteCount χ p Y (c + 1) y) / 2 := by
  unfold endpointValue finiteCount
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [endpointWeight_eq_average]
  by_cases hY : Y i < y <;> by_cases hp : p i < c <;>
    by_cases hp' : p i < c + 1 <;> simp [hY, hp, hp'] <;> ring

/--
@isnad1 id=eq.4h8v.s8.535f47de94a7 from=translated src=- shape=4a80f301 vocab=739b59a9
-/
lemma finiteCount_eq_real_count {n K N : ℕ} (hK : 0 < K) (hN : 0 < N)
    (χ : Fin n → ℝ) (U W : Fin n → ℝ)
    (hU : ∀ i, U i ∈ Set.Ioc (0 : ℝ) 1) (hW : ∀ i, W i ∈ Set.Ioc (0 : ℝ) 1)
    (x y : ℕ) : finiteCount χ (sampleCells n K hK U) (sampleCells n N hN W) x y =
      ∑ i ∈ Finset.univ.filter (fun i ↦ 0 ≤ U i ∧ U i ≤ (x : ℝ)/K ∧
        0 ≤ W i ∧ W i ≤ (y : ℝ)/N), χ i := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have h1 := finiteGridIndex_lt_iff hK (hU i) x
  have h2 := finiteGridIndex_lt_iff hN (hW i) y
  simp only [sampleCells, h1, h2, (hU i).1.le, (hW i).1.le, true_and]

/--
@isnad1 id=le.7h9v.s7.d8a39dad5a9c from=translated src=- shape=479bc075 vocab=5daa7814
-/
lemma finiteCount_abs_le_of_fixedColorBad {n K N : ℕ} (hK : 0 < K) (hN : 0 < N)
    (χ : Fin n → Bool) (U W : Fin n → ℝ)
    (hU : ∀ i, U i ∈ Set.Ioc (0 : ℝ) 1) (hW : ∀ i, W i ∈ Set.Ioc (0 : ℝ) 1)
    {B : ℝ} (hbad : (fun i ↦ (U i, W i)) ∈ fixedColorBad n B χ)
    (x y : ℕ) (hx : x ≤ K) (hy : y ≤ N) :
    |finiteCount (fun i ↦ (PointSets.boolSign (χ i) : ℝ))
      (sampleCells n K hK U) (sampleCells n N hN W) x y| ≤ B := by
  rw [finiteCount_eq_real_count hK hN _ U W hU hW]
  apply hbad
  · exact ⟨by positivity, (div_le_one (by exact_mod_cast hK)).mpr (by exact_mod_cast hx)⟩
  · exact ⟨by positivity, (div_le_one (by exact_mod_cast hN)).mpr (by exact_mod_cast hy)⟩

/--
@isnad1 id=le.6h8v.s7.484c30ff7831 from=translated src=- shape=a0db7d67 vocab=8040eb6a
-/
theorem actualPotential_le_of_fixedColorBad {n K V m : ℕ} (hK : 0 < K)
    (hV : 0 < V) (hm : 0 < m) (χ : Fin n → Bool) (U W : Fin n → ℝ)
    (hU : ∀ i, U i ∈ Set.Ioc (0 : ℝ) 1) (hW : ∀ i, W i ∈ Set.Ioc (0 : ℝ) 1)
    {B : ℝ} (hbad : (fun i ↦ (U i, W i)) ∈ fixedColorBad n B χ) :
    actualPotential K V m hK hm (fun i ↦ (PointSets.boolSign (χ i) : ℝ))
      (sampleCells n (V*m) (Nat.mul_pos hV hm) W) U ≤ 2 * B := by
  unfold actualPotential gridPotential
  apply (div_le_iff₀ (by exact_mod_cast Nat.mul_pos hK hV)).mpr
  calc
    (∑ c : Fin K, ∑ v : Fin V, gridOsc hm (blockValues
      (fun i ↦ (PointSets.boolSign (χ i) : ℝ)) (sampleCells n K hK U)
        (sampleCells n (V*m) (Nat.mul_pos hV hm) W) c.val v.val))
      ≤ ∑ _ : Fin K, ∑ _ : Fin V, (2 * B) := by
        apply Finset.sum_le_sum
        intro c _
        apply Finset.sum_le_sum
        intro v _
        apply gridOsc_le
        intro t
        have hy : v.val * m + t.val + 1 ≤ V * m := by
          have hv := Nat.mul_le_mul_right m (Nat.succ_le_of_lt v.isLt)
          nlinarith [t.isLt]
        have h0 := finiteCount_abs_le_of_fixedColorBad hK (Nat.mul_pos hV hm) χ U W hU hW hbad
          c.val (v.val*m+t.val+1) c.isLt.le hy
        have h1 := finiteCount_abs_le_of_fixedColorBad hK (Nat.mul_pos hV hm) χ U W hU hW hbad
          (c.val+1) (v.val*m+t.val+1) c.isLt hy
        unfold blockValues
        rw [endpointValue_eq_average, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        apply (div_le_iff₀ (by norm_num)).mpr
        exact (abs_add_le _ _).trans (by linarith)
    _ = 2 * B * (K * V : ℕ) := by simp; ring

end
end Oscillation
