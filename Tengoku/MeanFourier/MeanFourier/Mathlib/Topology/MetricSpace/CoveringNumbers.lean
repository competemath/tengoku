module

public import Tengoku
public import Tengoku.MeanFourier.MeanFourier.Mathlib.Data.ENat.BigOperators
public import Tengoku.MeanFourier.MeanFourier.Mathlib.Data.Set.Prod
public import Tengoku.MeanFourier.MeanFourier.Mathlib.Topology.MetricSpace.Cover
public import Tengoku.MeanFourier.MeanFourier.Mathlib.Topology.MetricSpace.MetricSeparated

attribute [local simp] ENat.prod_eq_top

open scoped NNReal ENNReal

public section

namespace Metric
variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {f : X → Y} {s C P : Set X}
  {t C' : Set Y} {K ε : ℝ≥0} {n : ℕ∞}

/--
@isnad1 id=iff.0h4v.s5.56b9abbb9000 from=translated src=- shape=0edc4562 vocab=b39f6882
-/
lemma le_coveringNumber_iff : n ≤ coveringNumber ε s ↔ ∀ C ⊆ s, IsCover ε s C → n ≤ C.encard := by
  simp [coveringNumber]

/--
@isnad1 id=iff.0h4v.s5.70fdd0877d9f from=translated src=- shape=fbe9b075 vocab=c7253a3b
-/
lemma packingNumber_le_iff : packingNumber ε s ≤ n ↔ ∀ P ⊆ s, IsSeparated ε P → P.encard ≤ n := by
  simp [packingNumber]

/--
@isnad1 id=iff.0h3v.s4.1087d194f769 from=translated src=- shape=77f5791c vocab=a94d1770
-/
@[simp] lemma one_le_coveringNumber_iff : 1 ≤ coveringNumber ε s ↔ s.Nonempty := by
  simp [Order.one_le_iff_ne_zero, Set.nonempty_iff_ne_empty]

/--
@isnad1 id=iff.0h3v.s4.9a6ef2f426bf from=translated src=- shape=a8f28b8d vocab=f61b4f12
-/
lemma coveringNumber_ne_zero_iff : coveringNumber ε s ≠ 0 ↔ s.Nonempty := by
  simp [Set.nonempty_iff_ne_empty]

-- Nicked from brownian-motion

/--
@isnad1 id=iff.0h3v.s4.c86d9d53ed3d from=translated src=- shape=77f5791c vocab=4f20e932
-/
@[local simp] lemma one_le_externalCoveringNumber_iff : 1 ≤ externalCoveringNumber ε s ↔ s.Nonempty := by
  simp [Order.one_le_iff_ne_zero, Set.nonempty_iff_ne_empty]

/--
@isnad1 id=iff.0h3v.s4.142d0b139f29 from=translated src=- shape=a8f28b8d vocab=183d05bd
-/
lemma externalCoveringNumber_ne_zero_iff : externalCoveringNumber ε s ≠ 0 ↔ s.Nonempty := by
  simp [Set.nonempty_iff_ne_empty]

/--
@isnad1 id=iff.0h3v.s4.bd775bb8c9f9 from=translated src=- shape=77f5791c vocab=21aca5c2
-/
@[local simp] lemma one_le_packingNumber_iff : 1 ≤ packingNumber ε s ↔ s.Nonempty := by
  simp [Order.one_le_iff_ne_zero, Set.nonempty_iff_ne_empty]

/--
@isnad1 id=iff.0h3v.s4.1b21bf01fb4b from=translated src=- shape=a8f28b8d vocab=184b4cc8
-/
lemma packingNumber_ne_zero_iff : packingNumber ε s ≠ 0 ↔ s.Nonempty := by
  simp [Set.nonempty_iff_ne_empty]

/--
@isnad1 id=lt.1h3v.s4.d1e8d935897c from=translated src=- shape=f37dd7bc vocab=b6b1b5de
-/
@[local simp] alias ⟨_, coveringNumber_pos⟩ := coveringNumber_pos_iff
/--
@isnad1 id=ne.1h3v.s4.fb6a4abd9f89 from=translated src=- shape=2b8038c2 vocab=f61b4f12
-/
@[simp] alias ⟨_, coveringNumber_ne_zero⟩ := coveringNumber_ne_zero_iff
/--
@isnad1 id=le.1h3v.s4.c3b12db8ec16 from=translated src=- shape=f37dd7bc vocab=a94d1770
-/
@[simp] alias ⟨_, one_le_coveringNumber⟩ := one_le_coveringNumber_iff

/--
@isnad1 id=lt.1h3v.s4.e36c9fc393e6 from=translated src=- shape=f37dd7bc vocab=e642d15e
-/
@[local simp] alias ⟨_, externalCoveringNumber_pos⟩ := externalCoveringNumber_pos_iff
/--
@isnad1 id=ne.1h3v.s4.759b069dabcf from=translated src=- shape=2b8038c2 vocab=183d05bd
-/
@[local simp] alias ⟨_, externalCoveringNumber_ne_zero⟩ := externalCoveringNumber_ne_zero_iff
/--
@isnad1 id=le.1h3v.s4.35c306f408eb from=translated src=- shape=f37dd7bc vocab=4f20e932
-/
@[simp] alias ⟨_, one_le_externalCoveringNumber⟩ := one_le_externalCoveringNumber_iff

/--
@isnad1 id=lt.1h3v.s4.faab5d4671ee from=translated src=- shape=f37dd7bc vocab=5ad847b5
-/
@[local simp] alias ⟨_, packingNumber_pos⟩ := packingNumber_pos_iff
/--
@isnad1 id=ne.1h3v.s4.891864908e02 from=translated src=- shape=2b8038c2 vocab=184b4cc8
-/
@[local simp] alias ⟨_, packingNumber_ne_zero⟩ := packingNumber_ne_zero_iff
/--
@isnad1 id=le.1h3v.s4.637515286718 from=translated src=- shape=f37dd7bc vocab=21aca5c2
-/
@[simp] alias ⟨_, one_le_packingNumber⟩ := one_le_packingNumber_iff

/--
@isnad1 id=le.0h3v.s5.c5bb409cc623 from=translated src=- shape=44a975b1 vocab=4e3e2287
-/
lemma packingNumber_two_mul_le_coveringNumber : packingNumber (2 * ε) s ≤ coveringNumber ε s := by
  grw [packingNumber_two_mul_le_externalCoveringNumber, externalCoveringNumber_le_coveringNumber]

/-- The smallness of the packing number is quantitatively pulled back under antilipschitz maps.
@isnad1 id=le.2h7v.s6.951b8846570f from=translated src=- shape=f9c61fdd vocab=1820e9fe
-/
lemma packingNumber_le_packingNumber_of_antilipschitzWith (hst : s.MapsTo f t)
    (hf : AntilipschitzWith K f) : packingNumber (K * ε) s ≤ packingNumber ε t := by
  refine packingNumber_le_iff.2 fun P hPs hP ↦ ?_
  rw [← (hf.injOn hP).encard_image]
  exact (hP.image_of_antilipschitzWith hf).encard_le_packingNumber (by grw [hPs, hst.image_subset])

/-- The smallness of the covering number is quantitatively pulled back under antilipschitz maps.
@isnad1 id=le.2h7v.s6.6aa5801e5ce7 from=translated src=- shape=3e270471 vocab=5b4fedcd
-/
lemma coveringNumber_le_coveringNumber_of_antilipschitzWith (hst : s.MapsTo f t)
    (hf : AntilipschitzWith K f) : coveringNumber (2 * K * ε) s ≤ coveringNumber ε t := by
  grw [coveringNumber_le_packingNumber, mul_assoc, mul_left_comm,
    packingNumber_le_packingNumber_of_antilipschitzWith hst hf,
    packingNumber_two_mul_le_coveringNumber]

/-- The smallness of the covering number is quantitatively pushed forward under surjective lipschitz
maps.
@isnad1 id=le.3h7v.s6.b3c0cc9e74eb from=translated src=- shape=05e6acc0 vocab=c93e757e
-/
lemma coveringNumber_le_coveringNumber_of_lipschitzOnWith (hst : s.SurjOn f t) (hst' : s.MapsTo f t)
    (hf : LipschitzOnWith K f s) : coveringNumber (K * ε) t ≤ coveringNumber ε s := by
  rw [le_coveringNumber_iff]
  rintro C hCs hC
  grw [← Set.encard_image_le (f := f)]
  exact (hC.image hf hst hCs).coveringNumber_le_encard (by grw [hCs, hst'.image_subset])

/-- The smallness of the covering number is quantitatively pushed forward under surjective lipschitz
maps.
@isnad1 id=le.3h7v.s6.f35603a262bf from=translated src=- shape=89633bc3 vocab=57a98a61
-/
lemma packingNumber_le_packingNumber_of_lipschitzOnWith (hst : s.SurjOn f t) (hst' : s.MapsTo f t)
    (hf : LipschitzOnWith K f s) : packingNumber (2 * K * ε) t ≤ packingNumber ε s := by
  grw [mul_assoc, packingNumber_two_mul_le_coveringNumber,
    coveringNumber_le_coveringNumber_of_lipschitzOnWith hst hst' hf,
    coveringNumber_le_packingNumber]

/--
@isnad1 id=le.0h5v.s6.ea5022a4a47e from=translated src=- shape=3a94a465 vocab=5e6d6d2f
-/
lemma coveringNumber_prod_le :
    coveringNumber ε (s ×ˢ t) ≤ coveringNumber ε s * coveringNumber ε t := by
  obtain rfl | hs₀ := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht₀ := t.eq_empty_or_nonempty
  · simp
  by_cases hs : coveringNumber ε s = ⊤
  · simp [hs, coveringNumber_ne_zero ht₀]
  by_cases ht : coveringNumber ε t = ⊤
  · simp [ht, coveringNumber_ne_zero hs₀]
  rw [← encard_minimalCover hs, ← encard_minimalCover ht, ← Set.encard_prod]
  exact ((isCover_minimalCover hs).prod <| isCover_minimalCover ht).coveringNumber_le_encard
    (by grw [minimalCover_subset, minimalCover_subset])

/--
@isnad1 id=le.0h5v.s6.5d771b35ad1e from=translated src=- shape=4bf57e2d vocab=dcbfe32b
-/
lemma packingNumber_prod_le :
    packingNumber ε (s ×ˢ t) ≤ packingNumber (ε / 2) s * packingNumber (ε / 2) t := by
  grw [← coveringNumber_le_packingNumber _ s, ← coveringNumber_le_packingNumber _ t,
    ← coveringNumber_prod_le, ← packingNumber_two_mul_le_coveringNumber]
  field_simp
  rfl

-- TODO: Remove the `/ 2` by introducing the external version of `minimalCover`.
/--
@isnad1 id=le.0h5v.s6.db1ecb140dd5 from=translated src=- shape=4bf57e2d vocab=95c8051a
-/
lemma externalCoveringNumber_prod_le :
    externalCoveringNumber ε (s ×ˢ t) ≤
      externalCoveringNumber (ε / 2) s * externalCoveringNumber (ε / 2) t := by
  grw [externalCoveringNumber_le_coveringNumber, coveringNumber_prod_le,
    ← coveringNumber_two_mul_le_externalCoveringNumber,
    ← coveringNumber_two_mul_le_externalCoveringNumber]
  field_simp
  rfl

variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, PseudoEMetricSpace (X i)]
  {s : ∀ i, Set (X i)}

/--
@isnad1 id=le.0h4v.s6.6859a74bd3b1 from=translated src=- shape=e1988012 vocab=2699355c
-/
lemma coveringNumber_pi_univ_le : coveringNumber ε (.pi .univ s) ≤ ∏ i, coveringNumber ε (s i) := by
  classical
  obtain hs₀ | hs₀ := (Set.univ.pi s).eq_empty_or_nonempty
  · simp [hs₀]
  simp [Set.univ_pi_nonempty_iff] at hs₀
  by_cases hs : ∏ i, coveringNumber ε (s i) = ⊤
  · simp [hs]
  simp only [ENat.prod_eq_top, Finset.mem_univ, true_and, ne_eq, coveringNumber_eq_zero,
    (hs₀ _).ne_empty, not_false_eq_true, imp_self, implies_true, and_true, not_exists] at hs
  calc
    coveringNumber ε (Set.univ.pi s)
    _ ≤ (Set.univ.pi fun i ↦ minimalCover ε (s i)).encard :=
      (IsCover.pi fun i _ ↦ isCover_minimalCover <| hs _).coveringNumber_le_encard
        (by gcongr with i; exact minimalCover_subset)
    _ = ∏ i, (minimalCover ε (s i)).encard := by simp
    _ = ∏ i, coveringNumber ε (s i) := by
      congr! 1 with i hi; exact encard_minimalCover (hs i)

/--
@isnad1 id=le.0h4v.s6.6b11d4e503ab from=translated src=- shape=34e58c6f vocab=2fdabf2b
-/
lemma packingNumber_pi_univ_le :
    packingNumber ε (.pi .univ s) ≤ ∏ i, packingNumber (ε / 2) (s i) := by
  trans ∏ i, coveringNumber (ε / 2) (s i)
  · grw [← coveringNumber_pi_univ_le, ← packingNumber_two_mul_le_coveringNumber]
    field_simp
    rfl
  · gcongr with i
    exact coveringNumber_le_packingNumber ..

-- TODO: Remove the `/ 2` by introducing the external version of `minimalCover`.
/--
@isnad1 id=le.0h4v.s6.ab14fec133ec from=translated src=- shape=34e58c6f vocab=8f01e522
-/
lemma externalCoveringNumber_pi_univ_le :
    externalCoveringNumber ε (.pi .univ s) ≤ ∏ i, externalCoveringNumber (ε / 2) (s i) := by
  grw [externalCoveringNumber_le_coveringNumber, coveringNumber_pi_univ_le]
  gcongr with i
  grw [← coveringNumber_two_mul_le_externalCoveringNumber]
  field_simp
  rfl

end Metric
-- Tengoku: 7 registration(s) of this module made local so they do not change other libraries (generated)
