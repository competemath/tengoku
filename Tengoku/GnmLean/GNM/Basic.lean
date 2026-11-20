import Tengoku.GnmLean.GNM.Defs
import Tengoku.GnmLean.GN.Main

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The number of good partitions and its toolkit

The pinned predicate `IsGoodPartition n` is the partition predicate of the underlying development on
the interval `{1, …, n}`, so the good partitions of `{1, …, n}` form a finite set of finite sets and
`count n` is its cardinality. This module records that bridge and the elementary counting steps used
throughout: lower bounds from explicit partitions, exact values from uniqueness, monotonicity along
an injection, and the arithmetic of the two exceptional sets `N_u` and `E_2`.
-/

namespace GNM

open GN

noncomputable section

/-- The pinned predicate is the partition predicate of the underlying development, read on the
interval `{1, …, n}`.
@isnad1 id=iff.0h2v.s3.273e2dcc593e from=translated src=- shape=a780af23 vocab=400b4335
-/
theorem isGoodPartition_iff (n : ℕ) (bs : Finset (Finset ℤ)) :
    IsGoodPartition n bs ↔ GoodOn (interval n) bs := by
  constructor
  · rintro ⟨hcover, hdisj, hblocks⟩
    refine ⟨?_, hdisj, hblocks⟩
    ext x
    simpa only [Finset.mem_biUnion, id_eq, interval, Finset.mem_Icc] using hcover x
  · rintro ⟨hcover, hdisj, hblocks⟩
    refine ⟨?_, hdisj, hblocks⟩
    intro x
    simpa only [Finset.mem_biUnion, id_eq, interval, Finset.mem_Icc] using
      Finset.ext_iff.mp hcover x

/-- Every block of a good partition of `{1, …, n}` lies in the interval, so the partition is a set
of subsets of the interval.
@isnad1 id=mem.1h2v.s5.5d2e197cef1c from=translated src=- shape=3aea3e76 vocab=2b1ab7f8
-/
theorem IsGoodPartition.mem_powerset {n : ℕ} {bs : Finset (Finset ℤ)} (h : IsGoodPartition n bs) :
    bs ∈ (interval n).powerset.powerset := by
  simp only [Finset.mem_powerset]
  intro b hb
  simp only [Finset.mem_powerset]
  exact ((isGoodPartition_iff n bs).mp h).subset hb

/-- The good partitions of `{1, …, n}` as a finite set.-/
def goodPartitions (n : ℕ) : Finset (Finset (Finset ℤ)) :=
  letI := Classical.decPred (IsGoodPartition n)
  (interval n).powerset.powerset.filter (IsGoodPartition n)

/--
@isnad1 id=iff.0h2v.s5.ef9dad234716 from=translated src=- shape=23f83a1a vocab=6a459088
-/
theorem mem_goodPartitions {n : ℕ} {bs : Finset (Finset ℤ)} :
    bs ∈ goodPartitions n ↔ IsGoodPartition n bs := by
  simp only [goodPartitions, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.mem_powerset, h⟩⟩

/-- `count n` is the cardinality of that finite set.
@isnad1 id=eq.0h1v.s3.91a10ce4de1a from=translated src=- shape=b36dd912 vocab=adcbac76
-/
theorem count_eq_card (n : ℕ) : count n = (goodPartitions n).card := by
  have h : count n = Nat.card {bs : Finset (Finset ℤ) // bs ∈ goodPartitions n} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_goodPartitions.symm)
  rw [h]
  exact Nat.card_eq_finsetCard _

/-- The empty interval has the empty partition and nothing else.
@isnad1 id=eq.0h0v.s3.a068c6437ea8 from=translated src=- shape=3c26ae4f vocab=fc22515e
-/
theorem count_zero : count 0 = 1 := by
  rw [count_eq_card]
  have h : goodPartitions 0 = {∅} := by
    ext bs
    simp only [Finset.mem_singleton, mem_goodPartitions]
    constructor
    · intro h
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨b, hb⟩
      obtain ⟨x, hx⟩ := (h.2.2 b hb).1
      exact absurd ((h.1 x).mp ⟨b, hb, hx⟩) (by omega)
    · rintro rfl
      refine ⟨fun x => ⟨?_, ?_⟩, ?_, ?_⟩
      · rintro ⟨b, hb, -⟩
        simp at hb
      · intro hx
        exact absurd hx (by omega)
      · intro b hb
        simp at hb
      · intro b hb
        simp at hb
  rw [h, Finset.card_singleton]

/-- Every interval has a good partition, so the count is at least one.
@isnad1 id=le.0h1v.s3.0d8eeb37e55a from=translated src=- shape=8a62b088 vocab=c3945a2c
-/
theorem one_le_count (n : ℕ) : 1 ≤ count n := by
  obtain ⟨bs, hbs⟩ := GN.gurvich_naumova n
  rw [count_eq_card]
  have hmem : bs ∈ goodPartitions n := mem_goodPartitions.mpr ((isGoodPartition_iff n bs).mpr hbs)
  have := Finset.card_pos.mpr ⟨bs, hmem⟩
  omega

/-- Three pairwise distinct good partitions give a count of at least three.
@isnad1 id=le.6h4v.s5.7fd2d90c154a from=translated src=- shape=22a70bb3 vocab=27d7935b
-/
theorem three_le_count {n : ℕ} {b₁ b₂ b₃ : Finset (Finset ℤ)} (h₁ : IsGoodPartition n b₁)
    (h₂ : IsGoodPartition n b₂) (h₃ : IsGoodPartition n b₃) (h₁₂ : b₁ ≠ b₂) (h₁₃ : b₁ ≠ b₃)
    (h₂₃ : b₂ ≠ b₃) : 3 ≤ count n := by
  rw [count_eq_card]
  have hsub : ({b₁, b₂, b₃} : Finset (Finset (Finset ℤ))) ⊆ goodPartitions n := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    · exact mem_goodPartitions.mpr h₁
    · exact mem_goodPartitions.mpr h₂
    · exact mem_goodPartitions.mpr h₃
  have hcard : ({b₁, b₂, b₃} : Finset (Finset (Finset ℤ))).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h₁₂, h₁₃]),
      Finset.card_insert_of_notMem (by simp [h₂₃]), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  omega

/-- A good partition that every good partition equals gives a count of one.
@isnad1 id=eq.2h2v.s5.0924262efff1 from=translated src=- shape=b7237c4f vocab=91e5cd05
-/
theorem count_eq_one_of {n : ℕ} {w : Finset (Finset ℤ)} (hw : IsGoodPartition n w)
    (huniq : ∀ bs, IsGoodPartition n bs → bs = w) : count n = 1 := by
  rw [count_eq_card]
  have h : goodPartitions n = {w} := by
    ext bs
    simp only [Finset.mem_singleton, mem_goodPartitions]
    exact ⟨fun h => huniq bs h, fun h => h ▸ hw⟩
  rw [h, Finset.card_singleton]

/-- Two distinct good partitions that exhaust the good partitions give a count of two.
@isnad1 id=eq.4h3v.s5.4a5d27833fc9 from=translated src=- shape=5df2e4b7 vocab=91e5cd05
-/
theorem count_eq_two_of {n : ℕ} {w₁ w₂ : Finset (Finset ℤ)} (h₁ : IsGoodPartition n w₁)
    (h₂ : IsGoodPartition n w₂) (hne : w₁ ≠ w₂)
    (hall : ∀ bs, IsGoodPartition n bs → bs = w₁ ∨ bs = w₂) : count n = 2 := by
  rw [count_eq_card]
  have h : goodPartitions n = {w₁, w₂} := by
    ext bs
    simp only [Finset.mem_insert, Finset.mem_singleton, mem_goodPartitions]
    constructor
    · exact fun h => hall bs h
    · rintro (rfl | rfl)
      · exact h₁
      · exact h₂
  rw [h, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]

/-- An injection of the good partitions of `{1, …, m}` into those of `{1, …, n}` bounds the
counts.
@isnad1 id=le.2h3v.s6.4586f3ffec59 from=translated src=- shape=73b06966 vocab=27d7935b
-/
theorem count_le_of_injOn {m n : ℕ} (f : Finset (Finset ℤ) → Finset (Finset ℤ))
    (hmaps : ∀ bs, IsGoodPartition m bs → IsGoodPartition n (f bs))
    (hinj : ∀ bs cs, IsGoodPartition m bs → IsGoodPartition m cs → f bs = f cs → bs = cs) :
    count m ≤ count n := by
  rw [count_eq_card, count_eq_card]
  refine Finset.card_le_card_of_injOn f (fun bs hbs => ?_) (fun bs hbs cs hcs hfe => ?_)
  · simp only [Finset.mem_coe, mem_goodPartitions] at hbs ⊢
    exact hmaps bs hbs
  · simp only [Finset.mem_coe, mem_goodPartitions] at hbs hcs
    exact hinj bs cs hbs hcs hfe

/-- A transport of good partitions with a left inverse bounds the counts.
@isnad1 id=le.2h4v.s5.cc6eb42b72b3 from=translated src=- shape=5746e85a vocab=27d7935b
-/
theorem count_le_of_leftInverse {m n : ℕ} (f g : Finset (Finset ℤ) → Finset (Finset ℤ))
    (hmaps : ∀ bs, IsGoodPartition m bs → IsGoodPartition n (f bs))
    (hg : ∀ bs, IsGoodPartition m bs → g (f bs) = bs) : count m ≤ count n := by
  refine count_le_of_injOn f hmaps (fun bs cs hbs hcs hfe => ?_)
  rw [← hg bs hbs, ← hg cs hcs, hfe]

/-- Powers of three at least nine are multiples of nine, and those at least twenty-seven are
multiples of twenty-seven.-/
private theorem pow_three_nine {t : ℕ} (ht : 2 ≤ t) :
    9 ≤ 3 ^ t ∧ 3 ^ t % 9 = 0 ∧ (3 ^ t = 9 ∨ 3 ^ t % 27 = 0) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = 2 + s := ⟨t - 2, by omega⟩
  have h9 : (3 : ℕ) ^ (2 + s) = 9 * 3 ^ s := by
    rw [pow_add]
    norm_num
  have hs1 : 1 ≤ (3 : ℕ) ^ s := Nat.one_le_pow _ _ (by norm_num)
  refine ⟨by rw [h9]; omega, by rw [h9]; omega, ?_⟩
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · left
    rw [h9]
    norm_num
  · right
    obtain ⟨u, rfl⟩ : ∃ u, s = 1 + u := ⟨s - 1, by omega⟩
    have h27 : (3 : ℕ) ^ (2 + (1 + u)) = 27 * 3 ^ u := by
      rw [show 2 + (1 + u) = 3 + u by omega, pow_add]
      norm_num
    rw [h27]
    omega

private theorem pow_three_twentyseven {t : ℕ} (ht : 3 ≤ t) : 27 ≤ 3 ^ t ∧ 3 ^ t % 27 = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = 3 + s := ⟨t - 3, by omega⟩
  have h27 : (3 : ℕ) ^ (3 + s) = 27 * 3 ^ s := by
    rw [pow_add]
    norm_num
  have hs1 : 1 ≤ (3 : ℕ) ^ s := Nat.one_le_pow _ _ (by norm_num)
  exact ⟨by rw [h27]; omega, by rw [h27]; omega⟩

/-- The two exceptional sets are disjoint: the members of each near a common power of three differ
by at most eleven, while distinct powers of three from nine on are multiples of nine at distance at
least eighteen.
@isnad1 id=false.2h1v.s3.8369e23c2c26 from=translated src=- shape=0fd25248 vocab=6df59d0b
-/
theorem not_e2_of_nu {n : ℕ} (h₁ : Nu n) (h₂ : E2 n) : False := by
  rcases h₂ with rfl | ⟨u, hu, hE⟩ | ⟨u, hu, hE⟩
  · rcases h₁ with h | h | h | h | ⟨t, ht, hN⟩
    · omega
    · omega
    · omega
    · omega
    · obtain ⟨hge, h9, -⟩ := pow_three_nine ht
      rcases hN with h | h | h | h | h | h | h | h <;> omega
  · obtain ⟨hgeu, h9u, -⟩ := pow_three_nine hu
    rcases h₁ with h | h | h | h | ⟨t, ht, hN⟩
    · omega
    · omega
    · omega
    · omega
    · obtain ⟨hge, h9, -⟩ := pow_three_nine ht
      rcases hN with h | h | h | h | h | h | h | h <;> omega
  · obtain ⟨hgeu, h27u⟩ := pow_three_twentyseven hu
    rcases h₁ with h | h | h | h | ⟨t, ht, hN⟩
    · omega
    · omega
    · omega
    · omega
    · obtain ⟨hge, h9, h27⟩ := pow_three_nine ht
      rcases hN with h | h | h | h | h | h | h | h <;> rcases h27 with h27 | h27 <;> omega

/-- Membership in `N_u` below `250`, as an explicit list.
@isnad1 id=iff.1h1v.s8.ec0330a0ac8e from=translated src=- shape=e7287af6 vocab=cf872011
-/
theorem nu_iff_of_le (n : ℕ) (hn : n ≤ 250) :
    Nu n ↔ n ∈ ({1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 14, 23, 25, 26, 27, 28, 29, 30, 32, 77, 79,
      80, 81, 82, 83, 84, 86, 239, 241, 242, 243, 244, 245, 246, 248} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl | rfl | ⟨t, ht, h⟩)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · have hle : 3 ^ t ≤ 254 := by rcases h with h | h | h | h | h | h | h | h <;> omega
      have hb : t ≤ 5 := by
        by_contra hc
        have h6 : (3 : ℕ) ^ 6 ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at h6
        omega
      interval_cases t <;> norm_num at h <;> omega
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨4, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨4, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨4, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨4, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨4, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨4, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨4, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨4, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by norm_num⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by norm_num⟩)))

/-- Membership in `E_2` below `250`, as an explicit list.
@isnad1 id=iff.1h1v.s6.a0f9cab4083b from=translated src=- shape=a1b3c1b9 vocab=75ce3313
-/
theorem e2_iff_of_le (n : ℕ) (hn : n ≤ 250) :
    E2 n ↔ n ∈ ({6, 13, 21, 24, 75, 78, 237, 240} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | ⟨t, ht, h⟩ | ⟨t, ht, h⟩)
    · norm_num
    · have hb : t ≤ 5 := by
        by_contra hc
        have h6 : (3 : ℕ) ^ 6 ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at h6
        omega
      interval_cases t <;> norm_num at h <;> omega
    · have hb : t ≤ 5 := by
        by_contra hc
        have h6 : (3 : ℕ) ^ 6 ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at h6
        omega
      interval_cases t <;> norm_num at h <;> omega
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨2, by norm_num⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨3, by norm_num⟩)
    · exact Or.inr (Or.inl ⟨3, by norm_num⟩)
    · exact Or.inr (Or.inr ⟨4, by norm_num⟩)
    · exact Or.inr (Or.inl ⟨4, by norm_num⟩)
    · exact Or.inr (Or.inr ⟨5, by norm_num⟩)
    · exact Or.inr (Or.inl ⟨5, by norm_num⟩)

/-- Powers of three are separated: a power of three in `[3^t, 3·3^t)` is `3^t`.
@isnad1 id=eq.2h2v.s6.822d88108df6 from=translated src=- shape=88a74282 vocab=2a3f5b88
-/
theorem pow_three_eq_of_lt {u t : ℕ} (h1 : 3 ^ t ≤ 3 ^ u) (h2 : 3 ^ u < 3 * 3 ^ t) : u = t := by
  by_contra hne
  rcases Nat.lt_or_ge u t with h | h
  · have hlt : (3 : ℕ) ^ u < 3 ^ t := Nat.pow_lt_pow_right (by norm_num) h
    omega
  · have hut : t + 1 ≤ u := by omega
    have hle : (3 : ℕ) ^ (t + 1) ≤ 3 ^ u := Nat.pow_le_pow_right (by norm_num) hut
    rw [pow_succ] at hle
    omega

/-- Above the fourth power, membership of `3^t + r` in `N_u` is decided by the offset alone.
@isnad1 id=iff.2h2v.s6.7d9b9cdf163c from=translated src=- shape=7a4c00b3 vocab=24ab1041
-/
theorem nu_add_iff {t r : ℕ} (ht : 4 ≤ t) (hr : 2 * r < 3 ^ t) :
    Nu (3 ^ t + r) ↔ (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 5) := by
  obtain ⟨-, h9t, -⟩ := pow_three_nine (show 2 ≤ t by omega)
  have hmono : (3 : ℕ) ^ 4 ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  have hlit : (3 : ℕ) ^ 4 = 81 := by norm_num
  constructor
  · rintro (h | h | h | h | ⟨u, hu, hN⟩)
    · omega
    · omega
    · omega
    · omega
    · obtain ⟨-, h9u, -⟩ := pow_three_nine hu
      have hut : u = t := by
        refine pow_three_eq_of_lt ?_ ?_
        · rcases hN with h | h | h | h | h | h | h | h <;> omega
        · rcases hN with h | h | h | h | h | h | h | h <;> omega
      subst hut
      rcases hN with h | h | h | h | h | h | h | h <;> omega
  · intro h
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨t, by omega, ?_⟩)))
    rcases h with rfl | rfl | rfl | rfl | rfl <;> omega

/-- No `3^t + r` with a small offset lies in `E_2`.
@isnad1 id=not.2h2v.s6.70623c640e19 from=translated src=- shape=f248e516 vocab=87185dde
-/
theorem not_e2_add {t r : ℕ} (ht : 4 ≤ t) (hr : 2 * r < 3 ^ t) : ¬ E2 (3 ^ t + r) := by
  obtain ⟨-, h9t, -⟩ := pow_three_nine (show 2 ≤ t by omega)
  have hmono : (3 : ℕ) ^ 4 ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  have hlit : (3 : ℕ) ^ 4 = 81 := by norm_num
  rintro (h | ⟨u, hu, hE⟩ | ⟨u, hu, hE⟩)
  · omega
  · obtain ⟨-, h9u, -⟩ := pow_three_nine hu
    have hut : u = t := pow_three_eq_of_lt (by omega) (by omega)
    subst hut
    omega
  · obtain ⟨-, h9u, -⟩ := pow_three_nine (show 2 ≤ u by omega)
    have hut : u = t := pow_three_eq_of_lt (by omega) (by omega)
    subst hut
    omega

/-- Above the fourth power, membership of `3^t − r` in `N_u` is decided by the offset alone.
@isnad1 id=iff.4h3v.s6.bd70a7c60173 from=translated src=- shape=21e056f2 vocab=24ab1041
-/
theorem nu_sub_iff {t r n : ℕ} (ht : 4 ≤ t) (hr : 1 ≤ r) (h2 : 2 * r < 3 ^ t)
    (hn : n + r = 3 ^ t) : Nu n ↔ (r = 1 ∨ r = 2 ∨ r = 4) := by
  obtain ⟨-, h9t, -⟩ := pow_three_nine (show 2 ≤ t by omega)
  have hmono : (3 : ℕ) ^ 4 ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  have hlit : (3 : ℕ) ^ 4 = 81 := by norm_num
  constructor
  · rintro (h | h | h | h | ⟨u, hu, hN⟩)
    · omega
    · omega
    · omega
    · omega
    · obtain ⟨-, h9u, -⟩ := pow_three_nine hu
      have hut : t = u := by
        refine pow_three_eq_of_lt (u := t) (t := u) ?_ ?_
        · rcases hN with h | h | h | h | h | h | h | h <;> omega
        · rcases hN with h | h | h | h | h | h | h | h <;> omega
      subst hut
      rcases hN with h | h | h | h | h | h | h | h <;> omega
  · intro h
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨t, by omega, ?_⟩)))
    rcases h with rfl | rfl | rfl <;> omega

/-- Above the fourth power, membership of `3^t − r` in `E_2` is decided by the offset alone.
@isnad1 id=iff.4h3v.s6.6f9d83252200 from=translated src=- shape=43c2cad9 vocab=87185dde
-/
theorem e2_sub_iff {t r n : ℕ} (ht : 4 ≤ t) (hr : 1 ≤ r) (h2 : 2 * r < 3 ^ t)
    (hn : n + r = 3 ^ t) : E2 n ↔ (r = 3 ∨ r = 6) := by
  obtain ⟨-, h9t, -⟩ := pow_three_nine (show 2 ≤ t by omega)
  have hmono : (3 : ℕ) ^ 4 ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  have hlit : (3 : ℕ) ^ 4 = 81 := by norm_num
  constructor
  · rintro (h | ⟨u, hu, hE⟩ | ⟨u, hu, hE⟩)
    · omega
    · obtain ⟨-, h9u, -⟩ := pow_three_nine hu
      have hut : t = u := pow_three_eq_of_lt (u := t) (t := u) (by omega) (by omega)
      subst hut
      omega
    · obtain ⟨-, h9u, -⟩ := pow_three_nine (show 2 ≤ u by omega)
      have hut : t = u := pow_three_eq_of_lt (u := t) (t := u) (by omega) (by omega)
      subst hut
      omega
  · intro h
    rcases h with rfl | rfl
    · exact Or.inr (Or.inl ⟨t, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨t, by omega, by omega⟩)

/-- A member of the exceptional set at least `33` is `3^s − e` with `e ∈ {1, 2, 3, 4, 6}` or `3^s +
c` with `c ∈ {0, 1, 2, 3, 5}`, for some `s ≥ 4`.
@isnad1 id=ex.2h1v.s7.4b8b7f91417d from=translated src=- shape=782f3928 vocab=35d37fa4
-/
theorem exceptional_form {m : ℕ} (hm : 33 ≤ m) (h : Nu m ∨ E2 m) :
    ∃ s : ℕ, 4 ≤ s ∧ ((∃ e, (e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) ∧ m + e = 3 ^ s) ∨
      (∃ c, (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 5) ∧ m = 3 ^ s + c)) := by
  have key : ∀ u : ℕ, 28 ≤ 3 ^ u → 4 ≤ u := by
    intro u hu
    by_contra hc
    have h27 : (3 : ℕ) ^ u ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hlit : (3 : ℕ) ^ 3 = 27 := by norm_num
    omega
  rcases h with (h | h | h | h | ⟨u, hu, hN⟩) | (h | ⟨u, hu, hE⟩ | ⟨u, hu, hE⟩)
  · omega
  · omega
  · omega
  · omega
  · rcases hN with h | h | h | h | h | h | h | h
    · exact ⟨u, key u (by omega), Or.inl ⟨4, by omega, by omega⟩⟩
    · exact ⟨u, key u (by omega), Or.inl ⟨2, by omega, by omega⟩⟩
    · exact ⟨u, key u (by omega), Or.inl ⟨1, by omega, by omega⟩⟩
    · exact ⟨u, key u (by omega), Or.inr ⟨0, by omega, by omega⟩⟩
    · exact ⟨u, key u (by omega), Or.inr ⟨1, by omega, by omega⟩⟩
    · exact ⟨u, key u (by omega), Or.inr ⟨2, by omega, by omega⟩⟩
    · exact ⟨u, key u (by omega), Or.inr ⟨3, by omega, by omega⟩⟩
    · exact ⟨u, key u (by omega), Or.inr ⟨5, by omega, by omega⟩⟩
  · omega
  · exact ⟨u, key u (by omega), Or.inl ⟨3, by omega, by omega⟩⟩
  · exact ⟨u, key u (by omega), Or.inl ⟨6, by omega, by omega⟩⟩

end

end GNM
