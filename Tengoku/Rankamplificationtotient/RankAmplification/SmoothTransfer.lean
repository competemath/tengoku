import Tengoku.Rankamplificationtotient.RankAmplification.Counting
import Tengoku.Seed.Analysis.Asymptotics.Defs
import Tengoku.Seed.Data.Finset.Lattice.Fold
import Tengoku.Seed.Order.Filter.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite transfer for the smooth shifted branch This file isolates the exact, unconditional counting layer used when a BFPS smooth-totient estimate is inserted into the shifted problem. -/

namespace RankAmplification

/-- Shifted equal-totient solutions whose common totient is `y`-smooth.-/
noncomputable def smoothShiftedSet (x h y : ℕ) : Finset ℕ := by
  classical
  exact (shiftedEqualTotientSet x h).filter fun n ↦ IsSmooth y n.totient

/-- The exact cardinality of the smooth branch of the shifted problem.-/
noncomputable def smoothShiftedCount (x h y : ℕ) : ℕ :=
  (smoothShiftedSet x h y).card

@[simp]
theorem mem_smoothShiftedSet {x h y n : ℕ} :
    n ∈ smoothShiftedSet x h y ↔
      1 ≤ n ∧ n ≤ x ∧ n.totient = (n + h).totient ∧ IsSmooth y n.totient := by
  classical
  simp [smoothShiftedSet, and_assoc]

/-- Forgetting the shifted equality injects the smooth branch into the ordinary smooth-totient census at the same `x` and `y`.-/
theorem smoothShiftedSet_subset_smoothTotientSet (x h y : ℕ) :
    smoothShiftedSet x h y ⊆ smoothTotientSet x y := by
  intro n hn
  rw [mem_smoothShiftedSet] at hn
  rw [mem_smoothTotientSet]
  exact ⟨hn.1, hn.2.1, hn.2.2.2⟩

/-- Exact finite smooth-part transfer: the shifted smooth count is at most `Φ(x,y)`.-/
theorem smoothShiftedCount_le_smoothTotientCount (x h y : ℕ) :
    smoothShiftedCount x h y ≤ smoothTotientCount x y := by
  exact Finset.card_le_card (smoothShiftedSet_subset_smoothTotientSet x h y)

/-- Away from zero, rank zero is exactly smoothness.-/
theorem largePrimeRank_eq_zero_iff_isSmooth {y n : ℕ} (hn : n ≠ 0) :
    largePrimeRank y n = 0 ↔ IsSmooth y n := by
  constructor
  · intro hrank
    refine ⟨hn, ?_⟩
    intro p hp
    by_contra hpy
    have hylt : y < p := Nat.lt_of_not_ge hpy
    have hpfilter : p ∈ (primeSupport n).filter (y < ·) := by
      exact Finset.mem_filter.mpr ⟨hp, hylt⟩
    have hsum : ∑ q ∈ (primeSupport n).filter (y < ·), n.factorization q = 0 := by
      exact hrank
    have hpzero : n.factorization p = 0 := by
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ ↦ Nat.zero_le _)).mp hsum
      exact hall p hpfilter
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hppos : 0 < n.factorization p :=
      hpprime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
    exact (Nat.ne_of_gt hppos) hpzero
  · intro hsmooth
    rw [largePrimeRank]
    apply Finset.sum_eq_zero
    intro p hp
    obtain ⟨hpsupport, hylt⟩ := Finset.mem_filter.mp hp
    exact (Nat.not_lt_of_ge (hsmooth.2 p hpsupport) hylt).elim

/-- Rank zero for a positive integer's totient is equivalent to smoothness of that totient.-/
theorem largePrimeRank_totient_eq_zero_iff_isSmooth {y n : ℕ} (hn : 0 < n) :
    largePrimeRank y n.totient = 0 ↔ IsSmooth y n.totient :=
  largePrimeRank_eq_zero_iff_isSmooth (Nat.totient_pos.mpr hn).ne'

/-- Membership in the smooth shifted branch can equivalently be expressed by rank zero.-/
theorem mem_smoothShiftedSet_iff_rank_zero {x h y n : ℕ} :
    n ∈ smoothShiftedSet x h y ↔
      n ∈ shiftedEqualTotientSet x h ∧ largePrimeRank y n.totient = 0 := by
  rw [mem_smoothShiftedSet, mem_shiftedEqualTotientSet]
  constructor
  · rintro ⟨hn, hnx, heq, hsmooth⟩
    refine ⟨⟨hn, hnx, heq⟩, ?_⟩
    exact (largePrimeRank_totient_eq_zero_iff_isSmooth (zero_lt_one.trans_le hn)).mpr hsmooth
  · rintro ⟨⟨hn, hnx, heq⟩, hrank⟩
    refine ⟨hn, hnx, heq, ?_⟩
    exact (largePrimeRank_totient_eq_zero_iff_isSmooth (zero_lt_one.trans_le hn)).mp hrank

/-- Largest-prime-factor form of membership, matching the smooth/nonsmooth split used in the paper.-/
theorem mem_smoothShiftedSet_iff_largestPrimeFactor_le {x h y n : ℕ} (hy : 1 ≤ y) :
    n ∈ smoothShiftedSet x h y ↔
      n ∈ shiftedEqualTotientSet x h ∧ largestPrimeFactor n.totient ≤ y := by
  rw [mem_smoothShiftedSet, mem_shiftedEqualTotientSet]
  constructor
  · rintro ⟨hn, hnx, heq, hsmooth⟩
    exact ⟨⟨hn, hnx, heq⟩, hsmooth.largestPrimeFactor_le hy⟩
  · rintro ⟨⟨hn, hnx, heq⟩, hlpf⟩
    have htotient : n.totient ≠ 0 :=
      (Nat.totient_pos.mpr (zero_lt_one.trans_le hn)).ne'
    exact ⟨hn, hnx, heq, (isSmooth_iff_largestPrimeFactor_le hy htotient).mpr hlpf⟩

/-- Smoothness is monotone in its prime cutoff.-/
theorem IsSmooth.mono {y Y n : ℕ} (hyY : y ≤ Y) (hn : IsSmooth y n) : IsSmooth Y n := by
  exact ⟨hn.1, fun p hp ↦ (hn.2 p hp).trans hyY⟩

/-- The smooth shifted branch is contained in the full shifted solution set.-/
theorem smoothShiftedSet_subset_shiftedEqualTotientSet (x h y : ℕ) :
    smoothShiftedSet x h y ⊆ shiftedEqualTotientSet x h := by
  intro n hn
  rw [mem_smoothShiftedSet] at hn
  rw [mem_shiftedEqualTotientSet]
  exact ⟨hn.1, hn.2.1, hn.2.2.1⟩

/-- The smooth and nonsmooth branches are disjoint once the conventional cutoff satisfies `1 ≤ y`.-/
theorem smoothShiftedSet_disjoint_nonsmoothShiftedSet {x h y : ℕ} (hy : 1 ≤ y) :
    Disjoint (smoothShiftedSet x h y) (nonsmoothShiftedSet x h y) := by
  rw [Finset.disjoint_left]
  intro n hsmooth hnonsmooth
  have hsmoothData := mem_smoothShiftedSet.mp hsmooth
  have hnonsmoothData := mem_nonsmoothShiftedSet.mp hnonsmooth
  have hle := hsmoothData.2.2.2.largestPrimeFactor_le hy
  exact (Nat.not_lt_of_ge hle) hnonsmoothData.2.2.2

/-- Exact smooth/nonsmooth partition of the shifted solution set.-/
theorem smoothShiftedSet_union_nonsmoothShiftedSet {x h y : ℕ} (hy : 1 ≤ y) :
    smoothShiftedSet x h y ∪ nonsmoothShiftedSet x h y = shiftedEqualTotientSet x h := by
  apply Finset.Subset.antisymm
  · intro n hn
    rcases Finset.mem_union.mp hn with hsmooth | hnonsmooth
    · exact smoothShiftedSet_subset_shiftedEqualTotientSet x h y hsmooth
    · exact nonsmoothShiftedSet_subset x h y hnonsmooth
  · intro n hn
    have hnData := mem_shiftedEqualTotientSet.mp hn
    by_cases hsmooth : IsSmooth y n.totient
    · apply Finset.mem_union_left
      exact mem_smoothShiftedSet.mpr ⟨hnData.1, hnData.2.1, hnData.2.2, hsmooth⟩
    · apply Finset.mem_union_right
      rw [mem_nonsmoothShiftedSet]
      refine ⟨hnData.1, hnData.2.1, hnData.2.2, ?_⟩
      have htotient : n.totient ≠ 0 :=
        (Nat.totient_pos.mpr (zero_lt_one.trans_le hnData.1)).ne'
      have hnotle : ¬largestPrimeFactor n.totient ≤ y := by
        intro hle
        exact hsmooth ((isSmooth_iff_largestPrimeFactor_le hy htotient).mpr hle)
      exact Nat.lt_of_not_ge hnotle

/-- Cardinal form of the exact smooth/nonsmooth partition.-/
theorem shiftedEqualTotientCount_eq_smooth_add_nonsmooth {x h y : ℕ} (hy : 1 ≤ y) :
    shiftedEqualTotientCount x h =
      smoothShiftedCount x h y + nonsmoothShiftedCount x h y := by
  rw [shiftedEqualTotientCount, ← smoothShiftedSet_union_nonsmoothShiftedSet hy,
    Finset.card_union_of_disjoint (smoothShiftedSet_disjoint_nonsmoothShiftedSet hy),
    smoothShiftedCount, nonsmoothShiftedCount]

/-- The smooth-totient census is monotone in its size cutoff.-/
theorem smoothTotientSet_mono_size {W X y : ℕ} (hWX : W ≤ X) :
    smoothTotientSet W y ⊆ smoothTotientSet X y := by
  intro n hn
  rw [mem_smoothTotientSet] at hn ⊢
  exact ⟨hn.1, hn.2.1.trans hWX, hn.2.2⟩

/-- The smooth-totient census is monotone in its smoothness cutoff.-/
theorem smoothTotientSet_mono_cutoff {X y Y : ℕ} (hyY : y ≤ Y) :
    smoothTotientSet X y ⊆ smoothTotientSet X Y := by
  intro n hn
  rw [mem_smoothTotientSet] at hn ⊢
  exact ⟨hn.1, hn.2.1, hn.2.2.mono hyY⟩

/-- Cardinal monotonicity of `Φ` in its size variable.-/
theorem smoothTotientCount_mono_size {W X y : ℕ} (hWX : W ≤ X) :
    smoothTotientCount W y ≤ smoothTotientCount X y := by
  exact Finset.card_le_card (smoothTotientSet_mono_size hWX)

/-- Cardinal monotonicity of `Φ` in its smoothness variable.-/
theorem smoothTotientCount_mono_cutoff {X y Y : ℕ} (hyY : y ≤ Y) :
    smoothTotientCount X y ≤ smoothTotientCount X Y := by
  exact Finset.card_le_card (smoothTotientSet_mono_cutoff hyY)

/-- A smooth shifted count below `W` is controlled by any larger-size smooth census.-/
theorem smoothShiftedCount_le_smoothTotientCount_of_le {W X h y : ℕ} (hWX : W ≤ X) :
    smoothShiftedCount W h y ≤ smoothTotientCount X y :=
  (smoothShiftedCount_le_smoothTotientCount W h y).trans (smoothTotientCount_mono_size hWX)

/-! ## Monotone envelopes and supplied analytic bounds -/

/-- The least finite upper envelope obtained by taking the supremum of `F` over `0 ≤ W ≤ X`.-/
def monotoneEnvelope {α : Type*} [SemilatticeSup α] (F : ℕ → α) (X : ℕ) : α :=
  (Finset.range (X + 1)).sup' (by
    exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ X)⟩) F

/-- Every value below the cutoff is bounded by the finite monotone envelope.-/
theorem le_monotoneEnvelope {α : Type*} [SemilatticeSup α] (F : ℕ → α)
    {W X : ℕ} (hWX : W ≤ X) :
    F W ≤ monotoneEnvelope F X := by
  unfold monotoneEnvelope
  apply Finset.le_sup'
  exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hWX)

/-- The finite envelope is monotone in its endpoint, independently of whether `F` is monotone.-/
theorem monotone_monotoneEnvelope {α : Type*} [SemilatticeSup α] (F : ℕ → α) :
    Monotone (monotoneEnvelope F) := by
  intro W X hWX
  rw [monotoneEnvelope]
  apply Finset.sup'_le
  intro n hn
  apply le_monotoneEnvelope F
  have hnW : n ≤ W := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  exact hnW.trans hWX

/-- Taking the envelope does not change an already monotone function.-/
theorem monotoneEnvelope_eq_of_monotone {α : Type*} [SemilatticeSup α] {F : ℕ → α}
    (hF : Monotone F) (X : ℕ) :
    monotoneEnvelope F X = F X := by
  apply le_antisymm
  · rw [monotoneEnvelope]
    apply Finset.sup'_le
    intro W hW
    apply hF
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hW)
  · exact le_monotoneEnvelope F le_rfl

/-- A supplied natural-valued estimate for `Φ(W,y)` transfers verbatim to the shifted smooth branch.-/
theorem smoothShiftedCount_le_of_smoothTotientBound {W h y B : ℕ}
    (hBFPS : smoothTotientCount W y ≤ B) :
    smoothShiftedCount W h y ≤ B :=
  (smoothShiftedCount_le_smoothTotientCount W h y).trans hBFPS

/-- A bound proved at a larger size cutoff transfers to every smaller shifted problem.-/
theorem smoothShiftedCount_le_of_larger_smoothTotientBound {W X h y B : ℕ}
    (hWX : W ≤ X) (hBFPS : smoothTotientCount X y ≤ B) :
    smoothShiftedCount W h y ≤ B :=
  (smoothShiftedCount_le_smoothTotientCount_of_le hWX).trans hBFPS

/-- Natural-valued uniform BFPS transfer through a monotone envelope.-/
theorem smoothShiftedCount_le_monotoneEnvelope (B : ℕ → ℕ → ℕ) {W X h y : ℕ}
    (hWX : W ≤ X) (hBFPS : smoothTotientCount W y ≤ B W y) :
    smoothShiftedCount W h y ≤ monotoneEnvelope (fun Z ↦ B Z y) X := by
  exact (smoothShiftedCount_le_smoothTotientCount W h y).trans
    (hBFPS.trans (le_monotoneEnvelope (fun Z ↦ B Z y) hWX))

/-- Uniform natural-valued transfer over all `W ≤ X`, with the analytic theorem supplied as a hypothesis rather than postulated in the library.-/
theorem smoothShiftedCount_le_monotoneEnvelope_of_uniform_bound
    (B : ℕ → ℕ → ℕ) {X y : ℕ}
    (hBFPS : ∀ W, W ≤ X → smoothTotientCount W y ≤ B W y) :
    ∀ W, W ≤ X → ∀ h,
      smoothShiftedCount W h y ≤ monotoneEnvelope (fun Z ↦ B Z y) X := by
  intro W hWX h
  exact smoothShiftedCount_le_monotoneEnvelope B hWX (hBFPS W hWX)

/-- Cast form of the basic finite transfer inequality.-/
theorem smoothShiftedCount_cast_le_smoothTotientCount (x h y : ℕ) :
    (smoothShiftedCount x h y : ℝ) ≤ smoothTotientCount x y := by
  exact_mod_cast smoothShiftedCount_le_smoothTotientCount x h y

/-- A supplied real-valued BFPS-style bound transfers verbatim to the shifted smooth branch.-/
theorem smoothShiftedCount_cast_le_of_smoothTotientBound {W h y : ℕ} {B : ℝ}
    (hBFPS : (smoothTotientCount W y : ℝ) ≤ B) :
    (smoothShiftedCount W h y : ℝ) ≤ B :=
  (smoothShiftedCount_cast_le_smoothTotientCount W h y).trans hBFPS

/-- Pointwise real bound transferred through a larger finite envelope.-/
theorem smoothShiftedCount_cast_le_monotoneEnvelope_of_bound
    (B : ℕ → ℕ → ℝ) {W X h y : ℕ} (hWX : W ≤ X)
    (hBFPS : (smoothTotientCount W y : ℝ) ≤ B W y) :
    (smoothShiftedCount W h y : ℝ) ≤ monotoneEnvelope (fun Z ↦ B Z y) X := by
  exact (smoothShiftedCount_cast_le_smoothTotientCount W h y).trans
    (hBFPS.trans (le_monotoneEnvelope (fun Z ↦ B Z y) hWX))

/-- Real-valued uniform BFPS transfer through the same finite monotone envelope.-/
theorem smoothShiftedCount_cast_le_monotoneEnvelope
    (B : ℕ → ℕ → ℝ) {W X h y : ℕ} (hWX : W ≤ X)
    (hBFPS : ∀ Z, Z ≤ X → (smoothTotientCount Z y : ℝ) ≤ B Z y) :
    (smoothShiftedCount W h y : ℝ) ≤ monotoneEnvelope (fun Z ↦ B Z y) X := by
  exact smoothShiftedCount_cast_le_monotoneEnvelope_of_bound B hWX (hBFPS W hWX)

/-- Eventual wrapper for any explicitly supplied pointwise real bound.-/
theorem eventually_smoothShiftedCount_cast_le_of_smoothTotientBound
    {ι : Type*} {l : Filter ι} (X H Y : ι → ℕ) (B : ι → ℝ)
    (hBFPS : ∀ᶠ i in l, (smoothTotientCount (X i) (Y i) : ℝ) ≤ B i) :
    ∀ᶠ i in l, (smoothShiftedCount (X i) (H i) (Y i) : ℝ) ≤ B i := by
  filter_upwards [hBFPS] with i hi
  exact smoothShiftedCount_cast_le_of_smoothTotientBound hi

/-- Eventual larger-cutoff wrapper, useful when a uniform analytic estimate is stated at an enclosing endpoint such as `C x`.-/
theorem eventually_smoothShiftedCount_cast_le_of_larger_smoothTotientBound
    {ι : Type*} {l : Filter ι} (W X H Y : ι → ℕ) (B : ι → ℝ)
    (hWX : ∀ᶠ i in l, W i ≤ X i)
    (hBFPS : ∀ᶠ i in l, (smoothTotientCount (X i) (Y i) : ℝ) ≤ B i) :
    ∀ᶠ i in l, (smoothShiftedCount (W i) (H i) (Y i) : ℝ) ≤ B i := by
  filter_upwards [hWX, hBFPS] with i hiX hiB
  have hcount := smoothShiftedCount_le_smoothTotientCount_of_le
    (h := H i) (y := Y i) hiX
  have hcountℝ : (smoothShiftedCount (W i) (H i) (Y i) : ℝ) ≤
      smoothTotientCount (X i) (Y i) := by
    exact_mod_cast hcount
  exact hcountℝ.trans hiB

/-- Big-O wrapper for a supplied BFPS-style asymptotic theorem.-/
theorem smoothShiftedCount_isBigO_of_smoothTotientCount_isBigO
    {ι : Type*} (l : Filter ι) (X H Y : ι → ℕ) (F : ι → ℝ)
    (hBFPS : (fun i ↦ (smoothTotientCount (X i) (Y i) : ℝ)) =O[l] F) :
    (fun i ↦ (smoothShiftedCount (X i) (H i) (Y i) : ℝ)) =O[l] F := by
  have hdom : (fun i ↦ (smoothShiftedCount (X i) (H i) (Y i) : ℝ)) =O[l]
      fun i ↦ (smoothTotientCount (X i) (Y i) : ℝ) := by
    apply Asymptotics.isBigO_of_le
    intro i
    rw [Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ smoothShiftedCount (X i) (H i) (Y i) by positivity),
      Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ smoothTotientCount (X i) (Y i) by positivity)]
    exact smoothShiftedCount_cast_le_smoothTotientCount (X i) (H i) (Y i)
  exact hdom.trans hBFPS

/-- Big-O wrapper when the supplied census estimate is stated at an eventually larger endpoint.-/
theorem smoothShiftedCount_isBigO_of_larger_smoothTotientCount_isBigO
    {ι : Type*} {l : Filter ι} (W X H Y : ι → ℕ) (F : ι → ℝ)
    (hWX : ∀ᶠ i in l, W i ≤ X i)
    (hBFPS : (fun i ↦ (smoothTotientCount (X i) (Y i) : ℝ)) =O[l] F) :
    (fun i ↦ (smoothShiftedCount (W i) (H i) (Y i) : ℝ)) =O[l] F := by
  have hdom : (fun i ↦ (smoothShiftedCount (W i) (H i) (Y i) : ℝ)) =O[l]
      fun i ↦ (smoothTotientCount (X i) (Y i) : ℝ) := by
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards [hWX] with i hi
    have hcount := smoothShiftedCount_le_smoothTotientCount_of_le
      (h := H i) (y := Y i) hi
    have hcountℝ : (smoothShiftedCount (W i) (H i) (Y i) : ℝ) ≤
        smoothTotientCount (X i) (Y i) := by
      exact_mod_cast hcount
    rw [Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ smoothShiftedCount (W i) (H i) (Y i) by positivity),
      Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ smoothTotientCount (X i) (Y i) by positivity)]
    exact hcountℝ
  exact hdom.trans hBFPS

end RankAmplification
