import Tengoku.Rankamplificationtotient.RankAmplification.SkeletonPartition
import Tengoku.Rankamplificationtotient.RankAmplification.Section9Assembly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Canonical nonsmooth transfer assembly This module selects the largest-prime provider skeleton on every nonsquare off-diagonal solution, then applies the exact small/large-cofactor partition. -/

namespace RankAmplification

open scoped BigOperators

noncomputable section

/-! ## Square/nonsquare finite partitions -/

/-- Nonsmooth solutions outside the witnessed square-source branch.-/
def nonsmoothNonSquareSet (x h y : ℕ) : Finset ℕ :=
  nonsmoothShiftedSet x h y \ squareSourceSet x h y (2 * x).sqrt

@[simp]
theorem mem_nonsmoothNonSquareSet {x h y n : ℕ} :
    n ∈ nonsmoothNonSquareSet x h y ↔
      n ∈ nonsmoothShiftedSet x h y ∧
        n ∉ squareSourceSet x h y (2 * x).sqrt := by
  simp [nonsmoothNonSquareSet]

theorem nonsmoothSquareSourceSet_disjoint_nonSquareSet (x h y : ℕ) :
    Disjoint (nonsmoothSquareSourceSet x h y (2 * x).sqrt)
      (nonsmoothNonSquareSet x h y) := by
  rw [Finset.disjoint_left]
  intro n hsquare hnonsquare
  have hsquare' :
      n ∈ nonsmoothShiftedSet x h y ∩ squareSourceSet x h y (2 * x).sqrt := by
    simpa [nonsmoothSquareSourceSet] using hsquare
  exact (mem_nonsmoothNonSquareSet.mp hnonsquare).2
    (Finset.mem_inter.mp hsquare').2

/-- The square-source and nonsquare branches partition the entire nonsmooth set.-/
theorem nonsmoothSquareSourceSet_union_nonSquareSet (x h y : ℕ) :
    nonsmoothSquareSourceSet x h y (2 * x).sqrt ∪ nonsmoothNonSquareSet x h y =
      nonsmoothShiftedSet x h y := by
  ext n
  simp only [nonsmoothSquareSourceSet, Finset.mem_union, Finset.mem_inter,
    mem_nonsmoothNonSquareSet]
  tauto

theorem nonsmoothShiftedCount_eq_square_add_nonSquare (x h y : ℕ) :
    nonsmoothShiftedCount x h y =
      (nonsmoothSquareSourceSet x h y (2 * x).sqrt).card +
        (nonsmoothNonSquareSet x h y).card := by
  rw [nonsmoothShiftedCount,
    ← nonsmoothSquareSourceSet_union_nonSquareSet x h y,
    Finset.card_union_of_disjoint
      (nonsmoothSquareSourceSet_disjoint_nonSquareSet x h y)]

/-! ## Canonical largest-prime skeleton selection -/

/-- The canonical provider is the largest prime factor of the common totient.-/
def canonicalLargestPrimeProvider (n : ℕ) : ℕ :=
  largestPrimeFactor n.totient

theorem canonicalLargestPrimeProvider_gt_of_mem_offDiagonalNonSquare
    {x h y n : ℕ}
    (hn : n ∈ offDiagonalNonSquareSet x h y (2 * x).sqrt) :
    y < canonicalLargestPrimeProvider n := by
  have hoff := (mem_offDiagonalNonSquareSet.mp hn).1
  have hnonsmooth := mem_nonsmoothShiftedSet.mp
    (mem_offDiagonalNonsmoothSet.mp hoff).1
  exact hnonsmooth.2.2.2

theorem canonicalLargestPrimeProvider_prime_of_mem_offDiagonalNonSquare
    {x h y n : ℕ} (hy : 0 < y)
    (hn : n ∈ offDiagonalNonSquareSet x h y (2 * x).sqrt) :
    (canonicalLargestPrimeProvider n).Prime := by
  apply largestPrimeFactor_prime
  have hgt := canonicalLargestPrimeProvider_gt_of_mem_offDiagonalNonSquare hn
  change y < largestPrimeFactor n.totient at hgt
  change 1 < largestPrimeFactor n.totient
  omega

/-- Nonsquare membership removes the only obstruction to the provider lemma for the canonical largest prime.-/
theorem canonicalLargestPrimeProvider_sq_not_dvd
    {x h y n : ℕ} (hh : 0 < h) (hhy : h ≤ y) (hxy : y ≤ x)
    (hn : n ∈ offDiagonalNonSquareSet x h y (2 * x).sqrt) :
    ¬(canonicalLargestPrimeProvider n) ^ 2 ∣ n * (n + h) := by
  intro hsquare
  have hnData := mem_offDiagonalNonSquareSet.mp hn
  have hnonsmooth := mem_nonsmoothShiftedSet.mp
    (mem_offDiagonalNonsmoothSet.mp hnData.1).1
  apply hnData.2
  rw [mem_squareSourceSet_sqrt_cutoff hh hhy (hhy.trans hxy)]
  refine ⟨hnonsmooth.1, hnonsmooth.2.1, canonicalLargestPrimeProvider n,
    canonicalLargestPrimeProvider_gt_of_mem_offDiagonalNonSquare hn, ?_, hsquare⟩
  exact canonicalLargestPrimeProvider_prime_of_mem_offDiagonalNonSquare
    (hh.trans_le hhy) hn

/-- The provider theorem supplies a skeleton canonically indexed by the largest prime factor.-/
theorem nonempty_canonicalLargestPrimeSkeleton
    {x h y n : ℕ} (hh : 0 < h) (hhy : h ≤ y) (hxy : y ≤ x)
    (hn : n ∈ offDiagonalNonSquareSet x h y (2 * x).sqrt) :
    Nonempty (LargePrimeSkeleton h n (canonicalLargestPrimeProvider n)) := by
  have hnonsmooth := mem_nonsmoothShiftedSet.mp
    (mem_offDiagonalNonsmoothSet.mp
      (mem_offDiagonalNonSquareSet.mp hn).1).1
  apply exists_largePrimeSkeleton hnonsmooth.1
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hh))
    (M := n.totient)
  · rfl
  · exact hnonsmooth.2.2.1.symm
  · rfl
  · exact hhy.trans_lt hnonsmooth.2.2.2
  · exact canonicalLargestPrimeProvider_sq_not_dvd hh hhy hxy hn

/-- Chosen canonical skeleton on the entire off-diagonal nonsquare family.-/
def canonicalLargestPrimeSkeleton {x h y : ℕ}
    (hh : 0 < h) (hhy : h ≤ y) (hxy : y ≤ x)
    (n : {n // n ∈ offDiagonalNonSquareSet x h y (2 * x).sqrt}) :
    LargePrimeSkeleton h n.1 (canonicalLargestPrimeProvider n.1) :=
  Classical.choice (nonempty_canonicalLargestPrimeSkeleton hh hhy hxy n.2)

/-- For odd shifts, every nonsquare nonsmooth solution is off diagonal, so the selector above is defined on the whole nonsquare branch.-/
theorem offDiagonalNonSquareSet_eq_nonsmoothNonSquareSet_of_odd
    {x h y : ℕ} (hodd : Odd h) :
    offDiagonalNonSquareSet x h y (2 * x).sqrt = nonsmoothNonSquareSet x h y := by
  rw [offDiagonalNonSquareSet, nonsmoothNonSquareSet,
    offDiagonalNonsmoothSet_eq_nonsmoothShiftedSet_of_odd hodd]

theorem nonempty_canonicalLargestPrimeSkeleton_of_mem_nonsmoothNonSquare
    {x h y n : ℕ} (hodd : Odd h) (hhy : h ≤ y) (hxy : y ≤ x)
    (hn : n ∈ nonsmoothNonSquareSet x h y) :
    Nonempty (LargePrimeSkeleton h n (canonicalLargestPrimeProvider n)) := by
  apply nonempty_canonicalLargestPrimeSkeleton hodd.pos hhy hxy
  rw [offDiagonalNonSquareSet_eq_nonsmoothNonSquareSet_of_odd hodd]
  exact hn

/-! ## Fixed-cofactor uniqueness off the diagonal -/

/-- Lemma 3.3 needs only nonvanishing normalized slope.-/
theorem LargePrimeSkeleton.n_eq_of_same_cofactors_of_not_diagonal
    {h n p n' p' : ℕ} (s : LargePrimeSkeleton h n p)
    (hnotdiag : ¬s.IsDiagonal) (t : LargePrimeSkeleton h n' p')
    (hm₁ : s.m1 = t.m1) (hm₂ : s.m2 = t.m2) :
    n = n' := by
  obtain ⟨c, _hc, hsk₁, hsk₂⟩ := s.exists_pos_normalized_common_multiplier
  obtain ⟨d, _hd, htk₁, htk₂⟩ := t.exists_pos_normalized_common_multiplier
  let C := c * p
  let D := d * p'
  have hsShift := s.normalized_shift_equation hsk₁ hsk₂
  have htShift := t.normalized_shift_equation htk₁ htk₂
  have hsLinear :
      (s.m1 * normalizedA s.m1 s.m2) * C + (s.m1 + h) =
        (s.m2 * normalizedB s.m1 s.m2) * C + s.m2 := by
    calc
      (s.m1 * normalizedA s.m1 s.m2) * C + (s.m1 + h) =
          s.m1 * (normalizedA s.m1 s.m2 * (c * p) + 1) + h := by
        simp only [C]
        ring
      _ = s.m2 * (normalizedB s.m1 s.m2 * (c * p) + 1) := hsShift
      _ = (s.m2 * normalizedB s.m1 s.m2) * C + s.m2 := by
        simp only [C]
        ring
  have htLinear :
      (t.m1 * normalizedA t.m1 t.m2) * D + (t.m1 + h) =
        (t.m2 * normalizedB t.m1 t.m2) * D + t.m2 := by
    calc
      (t.m1 * normalizedA t.m1 t.m2) * D + (t.m1 + h) =
          t.m1 * (normalizedA t.m1 t.m2 * (d * p') + 1) + h := by
        simp only [D]
        ring
      _ = t.m2 * (normalizedB t.m1 t.m2 * (d * p') + 1) := htShift
      _ = (t.m2 * normalizedB t.m1 t.m2) * D + t.m2 := by
        simp only [D]
        ring
  have htLinear' :
      (s.m1 * normalizedA s.m1 s.m2) * D + (s.m1 + h) =
        (s.m2 * normalizedB s.m1 s.m2) * D + s.m2 := by
    simpa only [hm₁, hm₂] using htLinear
  have hslope :
      s.m1 * normalizedA s.m1 s.m2 ≠ s.m2 * normalizedB s.m1 s.m2 := by
    simpa only [LargePrimeSkeleton.IsDiagonal] using hnotdiag
  have hCD : C = D := affine_parameter_unique hslope hsLinear htLinear'
  have hnS : n = s.m1 * (normalizedA s.m1 s.m2 * C + 1) := by
    calc
      n = s.m1 * s.q1 := s.n_eq
      _ = s.m1 * (normalizedA s.m1 s.m2 * C + 1) := by
        rw [s.q1_eq, hsk₁]
        simp only [C]
        ring
  have hnT : n' = t.m1 * (normalizedA t.m1 t.m2 * D + 1) := by
    calc
      n' = t.m1 * t.q1 := t.n_eq
      _ = t.m1 * (normalizedA t.m1 t.m2 * D + 1) := by
        rw [t.q1_eq, htk₁]
        simp only [D]
        ring
  calc
    n = s.m1 * (normalizedA s.m1 s.m2 * C + 1) := hnS
    _ = s.m1 * (normalizedA s.m1 s.m2 * D + 1) := by rw [hCD]
    _ = t.m1 * (normalizedA t.m1 t.m2 * D + 1) := by rw [hm₁, hm₂]
    _ = n' := hnT.symm

/-- Chosen cofactor pairs are injective whenever every selected skeleton is off diagonal.-/
theorem cofactorPair_injective_of_not_diagonal {h : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n))
    (hoff : ∀ n, ¬(skeleton n).IsDiagonal) :
    Function.Injective (fun n ↦ ((skeleton n).m1, (skeleton n).m2)) := by
  intro a b hab
  apply Subtype.ext
  exact (skeleton a).n_eq_of_same_cofactors_of_not_diagonal (hoff a) (skeleton b)
    (congrArg Prod.fst hab) (congrArg Prod.snd hab)

/-- Off-diagonal version of Corollary 3.4, valid for every shift rather than only odd shifts.-/
theorem card_skeletonNumbers_le_cofactor_bound_of_not_diagonal
    {h X : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n))
    (hoff : ∀ n, ¬(skeleton n).IsDiagonal)
    (hsmall : ∀ n, (skeleton n).m1 * (skeleton n).m2 ≤ X) :
    (S.card : ℝ) ≤ X * (1 + Real.log X) := by
  let imagePairs := S.attach.image fun n ↦ ((skeleton n).m1, (skeleton n).m2)
  have hsubset : imagePairs ⊆ cofactorPairSet X := by
    intro pair hpair
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hpair
    exact mem_cofactorPairSet.mpr
      ⟨(skeleton n).m1_pos, (skeleton n).m2_pos, hsmall n⟩
  have hcard : imagePairs.card ≤ (cofactorPairSet X).card :=
    Finset.card_le_card hsubset
  have himage : imagePairs.card = S.card := by
    change (S.attach.image fun n ↦ ((skeleton n).m1, (skeleton n).m2)).card = S.card
    rw [Finset.card_image_of_injective _
      (cofactorPair_injective_of_not_diagonal S provider skeleton hoff)]
    exact Finset.card_attach
  rw [himage] at hcard
  exact (Nat.cast_le.mpr hcard).trans (card_cofactorPairSet_cast_le X)

/-! ## Prime-filtered refinement of the large-cofactor family API -/

private def sigmaToPrimeProviderCode : (Σ _ : ℕ, ℕ × ℕ) ↪ ProviderCode where
  toFun z := ⟨z.1, z.2.1, z.2.2⟩
  inj' := by
    rintro ⟨p, k₁, k₂⟩ ⟨q, l₁, l₂⟩ h
    cases h
    rfl

/-- Canonical code universe with the provider variable restricted to actual primes.-/
def primeLargeCofactorCodeSet (x y P : ℕ) : Finset ProviderCode :=
  ((squareSourcePrimeRange y P).sigma fun p ↦
    smoothFactorPairSet p ((2 * x * y) / p ^ 2)).map sigmaToPrimeProviderCode

@[simp]
theorem mem_primeLargeCofactorCodeSet {x y P : ℕ} {c : ProviderCode} :
    c ∈ primeLargeCofactorCodeSet x y P ↔
      y < c.p ∧ c.p ≤ P ∧ c.p.Prime ∧
        (c.k1, c.k2) ∈ smoothFactorPairSet c.p ((2 * x * y) / c.p ^ 2) := by
  constructor
  · intro hc
    obtain ⟨z, hz, hzc⟩ := Finset.mem_map.mp hc
    obtain ⟨p, k₁, k₂⟩ := z
    have hzData := Finset.mem_sigma.mp hz
    have hpData := mem_squareSourcePrimeRange.mp hzData.1
    cases hzc
    exact ⟨hpData.1, hpData.2.1, hpData.2.2, hzData.2⟩
  · rintro ⟨hyp, hpP, hp, hk⟩
    apply Finset.mem_map.mpr
    refine ⟨⟨c.p, (c.k1, c.k2)⟩, ?_, rfl⟩
    exact Finset.mem_sigma.mpr
      ⟨mem_squareSourcePrimeRange.mpr ⟨hyp, hpP, hp⟩, hk⟩

theorem providerCodeImage_subset_primeLargeCofactorCodeSet
    {x h y : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n))
    (hnx : ∀ n : {n // n ∈ S}, n.1 ≤ x)
    (hp : ∀ n : {n // n ∈ S}, (provider n).Prime)
    (hyp : ∀ n : {n // n ∈ S}, y < provider n)
    (hy : 0 < y) (hhy : h ≤ y) (hxy : y ≤ x)
    (hlarge : ∀ n : {n // n ∈ S},
      x / y < (skeleton n).m1 * (skeleton n).m2) :
    providerCodeImage S provider skeleton ⊆
      primeLargeCofactorCodeSet x y (2 * x * y).sqrt := by
  intro c hc
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
  let s := skeleton n
  apply mem_primeLargeCofactorCodeSet.mpr
  refine ⟨hyp n, s.provider_le_sqrt_two_mul_xy
    (hnx n) hy hhy hxy (hlarge n), hp n, ?_⟩
  exact s.multiplier_pair_mem_large_cofactor_set
    (hnx n) (hp n).pos hy hhy hxy (hlarge n)

/-! ## Canonical small/large partition -/

/-- The canonical small-cofactor branch of the off-diagonal nonsquare family.-/
def canonicalSmallCofactorSet {x h y : ℕ}
    (hh : 0 < h) (hhy : h ≤ y) (hxy : y ≤ x) : Finset ℕ :=
  smallCofactorSkeletonSet (offDiagonalNonSquareSet x h y (2 * x).sqrt)
    (fun n ↦ canonicalLargestPrimeProvider n.1)
    (canonicalLargestPrimeSkeleton hh hhy hxy) (x / y)

/-- The complementary canonical large-cofactor branch.-/
def canonicalLargeCofactorSet {x h y : ℕ}
    (hh : 0 < h) (hhy : h ≤ y) (hxy : y ≤ x) : Finset ℕ :=
  largeCofactorSkeletonSet (offDiagonalNonSquareSet x h y (2 * x).sqrt)
    (fun n ↦ canonicalLargestPrimeProvider n.1)
    (canonicalLargestPrimeSkeleton hh hhy hxy) (x / y)

theorem canonicalSmall_union_large_eq {x h y : ℕ}
    (hh : 0 < h) (hhy : h ≤ y) (hxy : y ≤ x) :
    canonicalSmallCofactorSet hh hhy hxy ∪ canonicalLargeCofactorSet hh hhy hxy =
      offDiagonalNonSquareSet x h y (2 * x).sqrt := by
  exact small_union_large_eq _ _ _

theorem canonicalSmall_disjoint_large {x h y : ℕ}
    (hh : 0 < h) (hhy : h ≤ y) (hxy : y ≤ x) :
    Disjoint (canonicalSmallCofactorSet hh hhy hxy)
      (canonicalLargeCofactorSet hh hhy hxy) := by
  exact small_disjoint_large _ _ _

/-- Exact four-way finite backbone: square sources, then canonical small and large nonsquare cofactors.-/
theorem offDiagonalNonSquare_card_eq_canonicalSmall_add_large {x h y : ℕ}
    (hh : 0 < h) (hhy : h ≤ y) (hxy : y ≤ x) :
    (offDiagonalNonSquareSet x h y (2 * x).sqrt).card =
      (canonicalSmallCofactorSet hh hhy hxy).card +
        (canonicalLargeCofactorSet hh hhy hxy).card := by
  exact card_eq_small_add_large _ _ _

/-- Exact square/small/large partition for the odd-shift nonsmooth set.-/
theorem nonsmoothShiftedCount_eq_square_add_canonicalSmall_add_large
    {x h y : ℕ} (hodd : Odd h) (hhy : h ≤ y) (hxy : y ≤ x) :
    nonsmoothShiftedCount x h y =
      (nonsmoothSquareSourceSet x h y (2 * x).sqrt).card +
        ((canonicalSmallCofactorSet hodd.pos hhy hxy).card +
          (canonicalLargeCofactorSet hodd.pos hhy hxy).card) := by
  rw [nonsmoothShiftedCount_eq_square_add_nonSquare,
    ← offDiagonalNonSquareSet_eq_nonsmoothNonSquareSet_of_odd hodd,
    offDiagonalNonSquare_card_eq_canonicalSmall_add_large hodd.pos hhy hxy]

theorem canonicalSkeleton_n_le {x h y : ℕ}
    (n : {n // n ∈ offDiagonalNonSquareSet x h y (2 * x).sqrt}) :
    n.1 ≤ x := by
  have hoff := (mem_offDiagonalNonSquareSet.mp n.2).1
  exact (mem_nonsmoothShiftedSet.mp
    (mem_offDiagonalNonsmoothSet.mp hoff).1).2.1

theorem canonicalSkeleton_provider_prime {x h y : ℕ}
    (hh : 0 < h) (hhy : h ≤ y) (_hxy : y ≤ x)
    (n : {n // n ∈ offDiagonalNonSquareSet x h y (2 * x).sqrt}) :
    (canonicalLargestPrimeProvider n.1).Prime := by
  exact canonicalLargestPrimeProvider_prime_of_mem_offDiagonalNonSquare
    (hh.trans_le hhy) n.2

theorem canonicalSkeleton_provider_gt {x h y : ℕ}
    (n : {n // n ∈ offDiagonalNonSquareSet x h y (2 * x).sqrt}) :
    y < canonicalLargestPrimeProvider n.1 :=
  canonicalLargestPrimeProvider_gt_of_mem_offDiagonalNonSquare n.2

theorem canonicalSkeleton_not_diagonal {x h y : ℕ}
    (hh : 0 < h) (hhy : h ≤ y) (hxy : y ≤ x)
    (n : {n // n ∈ offDiagonalNonSquareSet x h y (2 * x).sqrt}) :
    ¬(canonicalLargestPrimeSkeleton hh hhy hxy n).IsDiagonal := by
  exact (canonicalLargestPrimeSkeleton hh hhy hxy n).not_isDiagonal_of_mem_offDiagonalNonsmoothSet
    (canonicalSkeleton_provider_prime hh hhy hxy n)
    (mem_offDiagonalNonSquareSet.mp n.2).1

/-- The exact finite nonsquare majorant left by the skeleton calculation.-/
def nonsquareSkeletonMajorant (x y : ℕ) : ℝ :=
  (x / y : ℕ) * (1 + Real.log (x / y : ℕ)) +
    ∑ p ∈ squareSourcePrimeRange y (2 * x * y).sqrt,
      smoothProviderPairMajorant x p ((2 * x * y) / p ^ 2)

/-! ## Closing the Section 9 transfer hypothesis -/

theorem nonsmoothShiftedSet_eq_empty_of_size_lt_cutoff
    {x h y : ℕ} (hxy : x < y) :
    nonsmoothShiftedSet x h y = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro n hn
  have hnData := mem_nonsmoothShiftedSet.mp hn
  have hpgt : 1 < largestPrimeFactor n.totient := by omega
  have hpdvd : largestPrimeFactor n.totient ∣ n.totient :=
    largestPrimeFactor_dvd hpgt
  have hphiPos : 0 < n.totient :=
    Nat.totient_pos.mpr (Nat.zero_lt_of_lt hnData.1)
  have hple : largestPrimeFactor n.totient ≤ n.totient :=
    Nat.le_of_dvd hphiPos hpdvd
  have hphin : n.totient ≤ n := Nat.totient_le n
  omega

theorem offDiagonalNonSquareSet_eq_empty_of_size_lt_cutoff
    {x h y : ℕ} (hxy : x < y) :
    offDiagonalNonSquareSet x h y (2 * x).sqrt = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro n hn
  have hnonsmooth := (mem_offDiagonalNonsmoothSet.mp
    (mem_offDiagonalNonSquareSet.mp hn).1).1
  rw [nonsmoothShiftedSet_eq_empty_of_size_lt_cutoff hxy] at hnonsmooth
  exact Finset.notMem_empty n hnonsmooth

theorem nonsquareSkeletonMajorant_nonneg (x y : ℕ) :
    0 ≤ nonsquareSkeletonMajorant x y := by
  have hlog : 0 ≤ Real.log (x / y : ℕ) := by
    cases hq : x / y with
    | zero => norm_num
    | succ q =>
        exact Real.log_nonneg (by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le q)))
  unfold nonsquareSkeletonMajorant
  apply add_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro p _hp
    unfold smoothProviderPairMajorant
    apply Finset.sum_nonneg
    intro k _hk
    positivity

/-! ## Strong finite form of Theorem 1.6 -/

/-- The last analytic input required to convert the exact finite skeleton sum into a chosen paper-style majorant.-/
def OuterSmoothPairEstimate (F : ℕ → ℕ → ℝ) : Prop :=
  ∀ x y, 2 ≤ y → y ≤ x →
    (∑ p ∈ squareSourcePrimeRange y (2 * x * y).sqrt,
      smoothProviderPairMajorant x p ((2 * x * y) / p ^ 2)) ≤ F x y

end

end RankAmplification
