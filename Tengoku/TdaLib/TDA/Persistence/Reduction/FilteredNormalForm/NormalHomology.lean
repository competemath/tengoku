import Tengoku.TdaLib.TDA.Persistence.Reduction.FilteredNormalForm.NormalMatrix
import Tengoku.TdaLib.TDA.Persistence.Interval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms lowers_mulVec_homogeneous` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms PivotAlive` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms EssentialAlive` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AliveCoordinate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pairedInterval` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms essentialInterval` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pairedInterval_alive_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms essentialInterval_alive_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pivotAlive_iff_pairedInterval` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms essentialAlive_iff_essentialInterval` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Homogeneous` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms NormalCycle` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms NormalBoundary` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pivotAlive_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalBoundary_alive_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveRepresentative` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms expiredPreimage` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms expiredPreimage_prefix` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms expiredPreimage_degree` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms expiredPreimage_pivot` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms expiredBoundary_pivot` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalDifferential_sq_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalBoundary_isCycle` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveRepresentative_prefix` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveRepresentative_degree` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveRepresentative_cycle` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalCycle_decompose` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalCycle_boundary_iff_live_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalCycle_prefix_inclusion` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalBoundary_prefix_inclusion` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveRepresentative_transition` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveRepresentative_single_survives` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveRepresentative_single_dies` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalCycleSpace` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveSpace` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveRepresentative_mem_aliveSpace` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveRepresentative_of_mem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms cycleLiveMap` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms cycleLiveMap_surjective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalHomology` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalHomologyEquivAlive` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalHomology_kernel_eq_boundaries` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveSpace_eq_spanSubset` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveSpace_prefix` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveSpaceMap` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveSpaceMap_id` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveSpaceMap_comp` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalHomologyMap` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalHomologyMap_mk` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Survivor` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms survivorFinset` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveSpaceMap_range_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveSpaceMap_rangeEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveSpaceMap_rank` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms survivor_iff_pairs_or_essential` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pairSurvivorFinset` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms essentialSurvivorFinset` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms deathSurvivorFinset` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms survivorFinset_partition` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pair_essential_disjoint` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pair_survivor_card_eq_death_card` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms aliveSpaceMap_rank_formula` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalHomologyMap_transport` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalHomologyMap_rangeEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalHomologyMap_rank_formula` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Filtered normal form: homology in normal coordinates

Cycles, boundaries and homology of the normal differential `normalDifferential R`,
described by the surviving pivot and essential coordinates, together with the
structure maps between prefix stages and their rank formula.
-/

namespace TDA.Persistence.Reduction

variable {m : ℕ} {k : Type*} [Field k] [DecidableEq k]

/-- A pivot row is active at stage `t` exactly from its birth through the
last stage before its paired death generator enters.-/
def PivotAlive (R : Matrix (Fin m) (Fin m) k)
    (t : ℕ) (i : Fin m) : Prop :=
  ∃ hi : IsPivot R i, i.val < t ∧ t ≤ (deathOfPivot R i hi).val

/-- An essential cycle is active from its birth through the final stage.-/
def EssentialAlive (R : Matrix (Fin m) (Fin m) k)
    (t : ℕ) (i : Fin m) : Prop :=
  IsEssential R i ∧ i.val < t

/-- The explicit surviving coordinates of degree `p` at stage `t`.-/
def AliveCoordinate (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (i : Fin m) : Prop :=
  degree i = p ∧ (PivotAlive R t i ∨ EssentialAlive R t i)

/-- Finite-interval encoding uses stage `i+1` for the birth at index `i`
and stage `j+1` for the death at index `j`.-/
noncomputable def pairedInterval (R : Matrix (Fin m) (Fin m) k)
    (hstrict : StrictBoundary R) (j i : Fin m)
    (hji : columnPivot (R.col j) = some i) :
    TDA.Persistence.FiniteInterval (m + 1) :=
  ⟨i.val + 1, j.val + 1,
    by have hn := ((columnPivot_some_iff (R.col j) i).mp hji).1
       exact Nat.add_lt_add_right (hstrict i j hn) 1,
    by omega⟩

/-- A surviving birth has terminal sentinel `m+1`, a finite observation
boundary rather than an infinite tail.-/
noncomputable def essentialInterval (i : Fin m) :
    TDA.Persistence.FiniteInterval (m + 1) :=
  ⟨i.val + 1, m + 1, by omega, le_refl _⟩

/--
@isnad1 id=iff.2h6v.s7.ff982edcd0ec from=translated src=- shape=97567921 vocab=6eea6b4d
-/
theorem pairedInterval_alive_iff (R : Matrix (Fin m) (Fin m) k)
    (hstrict : StrictBoundary R) (j i : Fin m)
    (hji : columnPivot (R.col j) = some i) (t : Fin (m + 1)) :
    (pairedInterval R hstrict j i hji).alive t ↔
      i.val < t.val ∧ t.val ≤ j.val := by
  simp only [TDA.Persistence.FiniteInterval.alive, pairedInterval]
  omega

/--
@isnad1 id=iff.0h3v.s5.ab570d5d58a6 from=translated src=- shape=56370c5b vocab=9ad00d8d
-/
theorem essentialInterval_alive_iff (i : Fin m) (t : Fin (m + 1)) :
    (essentialInterval i).alive t ↔ i.val < t.val := by
  simp only [TDA.Persistence.FiniteInterval.alive, essentialInterval]
  omega

/--
@isnad1 id=iff.1h5v.s6.3b9a1b397a6e from=translated src=- shape=2c19ee2f vocab=34f83be5
-/
theorem essentialAlive_iff_essentialInterval (R : Matrix (Fin m) (Fin m) k)
    (i : Fin m) (hi : IsEssential R i) (t : Fin (m + 1)) :
    EssentialAlive R t.val i ↔ (essentialInterval i).alive t := by
  simp [EssentialAlive, hi, essentialInterval_alive_iff]

/-- Exact homological grading of a coordinate vector.-/
def Homogeneous (degree : Fin m → ℕ) (p : ℕ) (x : Fin m → k) : Prop :=
  ∀ i, degree i ≠ p → x i = 0

/--
@isnad1 id=homogene.2h6v.s6.6df2a5402303 from=translated src=- shape=1dd497ea vocab=96de8326
-/
theorem lowers_mulVec_homogeneous (degree : Fin m → ℕ)
    (M : Matrix (Fin m) (Fin m) k) (hM : LowersDegree degree M)
    (p : ℕ) (x : Fin m → k) (hx : Homogeneous degree (p + 1) x) :
    Homogeneous degree p (M.mulVec x) := by
  intro r hr
  rw [Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : M r j = 0
  · simp [h]
  · have hj : degree j ≠ p + 1 := by
      intro he
      exact hr (Nat.add_right_cancel ((hM r j h).symm.trans he))
    simp [hx j hj]

/-- Cycles in the normal coordinates at a filtration prefix.-/
def NormalCycle (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) : Prop :=
  PrefixSupported t x ∧ Homogeneous degree p x ∧
    (normalDifferential R).mulVec x = 0

/-- Boundaries in the normal coordinates at a prefix.-/
def NormalBoundary (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) : Prop :=
  ∃ y : Fin m → k, PrefixSupported t y ∧ Homogeneous degree (p + 1) y ∧
    (normalDifferential R).mulVec y = x

/--
@isnad1 id=iff.1h5v.s5.9fe03e1e4a96 from=translated src=- shape=5dfa3c8c vocab=7343b9f2
-/
theorem pivotAlive_iff (R : Matrix (Fin m) (Fin m) k)
    (t : ℕ) (i : Fin m) (hi : IsPivot R i) :
    PivotAlive R t i ↔ i.val < t ∧ t ≤ (deathOfPivot R i hi).val := by
  constructor
  · rintro ⟨hi', hlt, hdeath⟩
    simpa only [Subsingleton.elim hi' hi] using (show i.val < t ∧
      t ≤ (deathOfPivot R i hi').val from ⟨hlt, hdeath⟩)
  · intro h
    exact ⟨hi, h⟩

/-- Each pivot coordinate is present exactly on the corresponding finite
interval, with birth `i+1` and death `j+1`.
@isnad1 id=iff.2h5v.s6.8120ba4f1130 from=translated src=- shape=8ea5dcff vocab=9615da8f
-/
theorem pivotAlive_iff_pairedInterval (R : Matrix (Fin m) (Fin m) k)
    (hstrict : StrictBoundary R) (i : Fin m) (hi : IsPivot R i)
    (t : Fin (m + 1)) :
    PivotAlive R t.val i ↔
      (pairedInterval R hstrict (deathOfPivot R i hi) i
        (deathOfPivot_spec R i hi)).alive t := by
  rw [pivotAlive_iff R t.val i hi,
    pairedInterval_alive_iff R hstrict _ i (deathOfPivot_spec R i hi) t]

/-- Boundaries have zero coefficient on every live homology coordinate.
@isnad1 id=eq.3h8v.s6.182cf959d0e6 from=translated src=- shape=0498a1da vocab=3460e2a5
-/
theorem normalBoundary_alive_zero (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hpivR : DistinctPivots R) (p t : ℕ)
    (x : Fin m → k) (hx : NormalBoundary degree R p t x)
    (i : Fin m) (hi : AliveCoordinate degree R p t i) : x i = 0 := by
  obtain ⟨y, hy, _, rfl⟩ := hx
  rcases hi.2 with hp | he
  · obtain ⟨hpivot, _, hdeath⟩ := hp
    rw [normalDifferential_mulVec_pivot R hpivR y i hpivot]
    simp [hy _ hdeath]
  · exact normalDifferential_mulVec_nonpivot R y i he.1.2

/-- The canonical representative keeps precisely the live homology coordinates.-/
noncomputable def aliveRepresentative (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) : Fin m → k := by
  classical
  exact fun i => if AliveCoordinate degree R p t i then x i else 0

/-- To erase an expired pivot coordinate, divide it by its pivot
coefficient and place it at the paired death generator.-/
noncomputable def expiredPreimage (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) : Fin m → k :=
  fun j => match h : columnPivot (R.col j) with
    | none => 0
    | some i => if j.val < t ∧ degree i = p then x i / R i j else 0

/--
@isnad1 id=prefixsu.0h7v.s5.52335bf93056 from=translated src=- shape=7e89911f vocab=e801a2b5
-/
theorem expiredPreimage_prefix (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) :
    PrefixSupported t (expiredPreimage degree R p t x) := by
  intro j hj
  unfold expiredPreimage
  split
  · rfl
  · simp [show ¬j.val < t by omega]

/--
@isnad1 id=homogene.1h7v.s6.bed5ec2f2d5d from=translated src=- shape=09edf61b vocab=eb396f76
-/
theorem expiredPreimage_degree (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k)
    (hdegree : LowersDegree degree R) (p t : ℕ) (x : Fin m → k) :
    Homogeneous degree (p + 1) (expiredPreimage degree R p t x) := by
  intro j hj
  unfold expiredPreimage
  split
  · rfl
  · next i hji =>
      by_cases h : j.val < t ∧ degree i = p
      · have hn : R i j ≠ 0 := ((columnPivot_some_iff (R.col j) i).mp hji).1
        exact (hj ((hdegree i j hn).trans (congrArg (· + 1) h.2))).elim
      · simp [h]

/--
@isnad1 id=eq.1h9v.s7.751411089a6e from=translated src=- shape=a97ee3b7 vocab=796c4ea3
-/
theorem expiredPreimage_pivot (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ)
    (x : Fin m → k) (j i : Fin m)
    (hji : columnPivot (R.col j) = some i) :
    expiredPreimage degree R p t x j =
      if j.val < t ∧ degree i = p then x i / R i j else 0 := by
  unfold expiredPreimage
  split
  · next h => rw [h] at hji; cases hji
  · next i' h =>
      have he : i' = i := Option.some.inj (h.symm.trans hji)
      subst i'
      rfl

/--
@isnad1 id=eq.2h8v.s7.85724c05b10e from=translated src=- shape=5d8c5a44 vocab=37e6ba1c
-/
theorem expiredBoundary_pivot (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hpiv : DistinctPivots R)
    (p t : ℕ) (x : Fin m → k) (i : Fin m) (hi : IsPivot R i) :
    (normalDifferential R).mulVec (expiredPreimage degree R p t x) i =
      if (deathOfPivot R i hi).val < t ∧ degree i = p then x i else 0 := by
  rw [normalDifferential_mulVec_pivot R hpiv _ i hi,
    expiredPreimage_pivot degree R p t x _ i (deathOfPivot_spec R i hi)]
  by_cases h : (deathOfPivot R i hi).val < t ∧ degree i = p
  · simp only [ite_eq_left h]
    have hn : R i (deathOfPivot R i hi) ≠ 0 :=
      ((columnPivot_some_iff (R.col (deathOfPivot R i hi)) i).mp
        (deathOfPivot_spec R i hi)).1
    field_simp [hn]
  · simp [h]

/--
@isnad1 id=eq.4h8v.s8.31c32d37187f from=translated src=- shape=6b355255 vocab=676b80c1
-/
theorem normalDifferential_sq_zero (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (x : Fin m → k) :
    (normalDifferential R).mulVec ((normalDifferential R).mulVec x) = 0 := by
  apply (normalDifferential_cycle_iff R hpiv _).2
  intro j hj
  have hn : ¬ IsPivot R j := by
    intro hp
    have hz := pivot_not_death degree D R V W hD2 hR hcert hpiv j hp
    simp [IsDeath, hz] at hj
  exact normalDifferential_mulVec_nonpivot R x j hn

/--
@isnad1 id=eq.5h10v.s8.298daf63b0e0 from=translated src=- shape=7082243a vocab=9541d26b
-/
theorem normalBoundary_isCycle (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p t : ℕ)
    (x : Fin m → k) (hx : NormalBoundary degree R p t x) :
    (normalDifferential R).mulVec x = 0 := by
  obtain ⟨y, _, _, rfl⟩ := hx
  exact normalDifferential_sq_zero degree D R V W hD2 hR hcert hpiv y

/--
@isnad1 id=prefixsu.0h7v.s5.d3c88000cf63 from=translated src=- shape=7e89911f vocab=200520d1
-/
theorem aliveRepresentative_prefix (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) :
    PrefixSupported t (aliveRepresentative degree R p t x) := by
  intro i hi
  have hnot : ¬ AliveCoordinate degree R p t i := by
    rintro ⟨_, hp | he⟩
    · exact (not_lt_of_ge hi) hp.2.1
    · exact (not_lt_of_ge hi) he.2
  simp [aliveRepresentative, hnot]

/--
@isnad1 id=homogene.0h7v.s5.96e8578f2a81 from=translated src=- shape=81878db5 vocab=518dd65a
-/
theorem aliveRepresentative_degree (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) :
    Homogeneous degree p (aliveRepresentative degree R p t x) := by
  intro i hi
  have hnot : ¬ AliveCoordinate degree R p t i := fun h => hi h.1
  simp [aliveRepresentative, hnot]

/--
@isnad1 id=normalcy.4h10v.s7.f20d4104e284 from=translated src=- shape=4c82177b vocab=ac2d32db
-/
theorem aliveRepresentative_cycle (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p t : ℕ) (x : Fin m → k) :
    NormalCycle degree R p t (aliveRepresentative degree R p t x) := by
  refine ⟨aliveRepresentative_prefix degree R p t x,
    aliveRepresentative_degree degree R p t x, ?_⟩
  apply (normalDifferential_cycle_iff R hpiv _).2
  intro j hj
  have hnot : ¬ AliveCoordinate degree R p t j := by
    rintro ⟨_, hp | he⟩
    · obtain ⟨hp', _, _⟩ := hp
      have hz := pivot_not_death degree D R V W hD2 hR hcert hpiv j hp'
      simp [IsDeath, hz] at hj
    · simp [IsEssential, IsDeath, he.1.1] at hj
  simp [aliveRepresentative, hnot]

/-- Every graded prefix cycle is a live-coordinate representative plus the
boundary of the explicit expired-coordinate preimage.
@isnad1 id=eq.5h10v.s8.9a496b8bdbb7 from=translated src=- shape=09378b9e vocab=96fd7d91
-/
theorem normalCycle_decompose (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p t : ℕ)
    (x : Fin m → k) (hx : NormalCycle degree R p t x) :
    x = aliveRepresentative degree R p t x +
      (normalDifferential R).mulVec (expiredPreimage degree R p t x) := by
  obtain ⟨hprefix, hhom, hcycle⟩ := hx
  have hdeath := (normalDifferential_cycle_iff R hpiv x).mp hcycle
  ext i
  simp only [Pi.add_apply]
  by_cases hp : IsPivot R i
  · have hz := pivot_not_death degree D R V W hD2 hR hcert hpiv i hp
    have ha := (pivotAlive_iff R t i hp)
    rw [expiredBoundary_pivot degree R hpiv p t x i hp]
    by_cases hlt : i.val < t
    · by_cases hdeg : degree i = p
      · by_cases hd : (deathOfPivot R i hp).val < t
        · have hn : ¬ AliveCoordinate degree R p t i := by
            rintro ⟨_, hb | he⟩
            · have hge := (ha.mp hb).2
              omega
            · exact he.1.2 hp
          simp [aliveRepresentative, hn, hd, hdeg]
        · have halive : AliveCoordinate degree R p t i :=
            ⟨hdeg, Or.inl ((ha).2 ⟨hlt, by omega⟩)⟩
          simp [aliveRepresentative, halive, hd]
      · have hxi : x i = 0 := hhom i hdeg
        have hn : ¬ AliveCoordinate degree R p t i := fun h => hdeg h.1
        simp [aliveRepresentative, hn, hdeg, hxi]
    · have hxi : x i = 0 := hprefix i (by omega)
      have hn : ¬ AliveCoordinate degree R p t i := by
        rintro ⟨_, hb | he⟩
        · exact (not_lt_of_ge (by omega : t ≤ i.val)) (ha.mp hb).1
        · exact (not_lt_of_ge (by omega : t ≤ i.val)) he.2
      simp [aliveRepresentative, hn, hlt, hxi]
  · rw [normalDifferential_mulVec_nonpivot R _ i hp]
    by_cases hd : IsDeath R i
    · have hxi := hdeath i hd
      have hn : ¬ AliveCoordinate degree R p t i := by
        rintro ⟨_, hb | he⟩
        · exact hp hb.1
        · have hz := he.1.1
          simp [IsDeath, hz] at hd
      simp [aliveRepresentative, hn, hxi]
    · have hz : columnPivot (R.col i) = none := by
        cases h : columnPivot (R.col i) with
        | none => rfl
        | some q => exact (hd (by simp [IsDeath, h])).elim
      have he : IsEssential R i := ⟨hz, hp⟩
      by_cases hlt : i.val < t
      · by_cases hdeg : degree i = p
        · have ha : AliveCoordinate degree R p t i := ⟨hdeg, Or.inr ⟨he, hlt⟩⟩
          simp [aliveRepresentative, ha]
        · have hxi : x i = 0 := hhom i hdeg
          have hn : ¬ AliveCoordinate degree R p t i := fun h => hdeg h.1
          simp [aliveRepresentative, hn, hxi]
      · have hxi : x i = 0 := hprefix i (by omega)
        have hn : ¬ AliveCoordinate degree R p t i := by
          rintro ⟨_, hb | he'⟩
          · exact hp hb.1
          · exact hlt he'.2
        simp [aliveRepresentative, hn, hxi]

/-- Two cycles represent the same prefix-homology class exactly when all
live coordinates agree. In particular, this is an explicit family of
homology bases, not merely a stagewise dimension calculation.
@isnad1 id=iff.6h10v.s8.d50a12a2f522 from=translated src=- shape=9b4645e6 vocab=ef9abf79
-/
theorem normalCycle_boundary_iff_live_zero (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hdegreeR : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p t : ℕ)
    (x : Fin m → k) (hx : NormalCycle degree R p t x) :
    NormalBoundary degree R p t x ↔
      aliveRepresentative degree R p t x = 0 := by
  constructor
  · intro hb
    ext i
    by_cases hi : AliveCoordinate degree R p t i
    · simp [aliveRepresentative, hi,
        normalBoundary_alive_zero degree R hpiv p t x hb i hi]
    · simp [aliveRepresentative, hi]
  · intro hzero
    have hd := normalCycle_decompose degree D R V W hD2 hR hcert hpiv p t x hx
    refine ⟨expiredPreimage degree R p t x,
      expiredPreimage_prefix degree R p t x,
      expiredPreimage_degree degree R hdegreeR p t x, ?_⟩
    simpa [hzero] using hd.symm

/-- Prefix inclusion is the identity on a cycle's original coordinate vector.
@isnad1 id=normalcy.2h8v.s5.76e9ccecb6c8 from=translated src=- shape=924a558f vocab=0ad45c0f
-/
theorem normalCycle_prefix_inclusion (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) (hst : s ≤ t)
    (x : Fin m → k) (hx : NormalCycle degree R p s x) :
    NormalCycle degree R p t x := by
  refine ⟨?_, hx.2.1, hx.2.2⟩
  intro i hi
  exact hx.1 i (le_trans hst hi)

/--
@isnad1 id=normalbo.2h8v.s5.e41c914c6913 from=translated src=- shape=924a558f vocab=f4b69e69
-/
theorem normalBoundary_prefix_inclusion (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) (hst : s ≤ t)
    (x : Fin m → k) (hx : NormalBoundary degree R p s x) :
    NormalBoundary degree R p t x := by
  obtain ⟨y, hy, hg, he⟩ := hx
  exact ⟨y, fun i hi => hy i (le_trans hst hi), hg, he⟩

/-- The coefficient map of every prefix inclusion is coordinate projection:
live generators survive unchanged, and expired ones go to zero.
@isnad1 id=eq.2h8v.s6.0d805d4dd1ff from=translated src=- shape=50a64b63 vocab=386dc1d0
-/
theorem aliveRepresentative_transition (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) (hst : s ≤ t)
    (x : Fin m → k) (hx : PrefixSupported s x) :
    aliveRepresentative degree R p t (aliveRepresentative degree R p s x) =
      aliveRepresentative degree R p t x := by
  ext i
  by_cases ht : AliveCoordinate degree R p t i
  · by_cases his : i.val < s
    · have hs : AliveCoordinate degree R p s i := by
        refine ⟨ht.1, ?_⟩
        rcases ht.2 with hp | he
        · obtain ⟨hi, _, hdeath⟩ := hp
          exact Or.inl ⟨hi, his, le_trans hst hdeath⟩
        · exact Or.inr ⟨he.1, his⟩
      simp [aliveRepresentative, ht, hs]
    · have hxi : x i = 0 := hx i (by omega)
      simp [aliveRepresentative, ht, hxi]
  · simp [aliveRepresentative, ht]

/-- The coordinate-level interval map sends a live pivot or essential class
identically while it remains live, and sends it to zero after death.
@isnad1 id=eq.1h7v.s7.3193f79c25ed from=translated src=- shape=371d7806 vocab=14b85133
-/
theorem aliveRepresentative_single_survives (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ)
    (i : Fin m) (hi : AliveCoordinate degree R p t i) :
    aliveRepresentative degree R p t ((Pi.single i (1 : k)) : Fin m → k) =
      Pi.single i (1 : k) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [aliveRepresentative, hi]
  · simp [aliveRepresentative, Pi.single_apply, hji]

/--
@isnad1 id=eq.1h7v.s6.ac689c635887 from=translated src=- shape=acaa17a8 vocab=14b85133
-/
theorem aliveRepresentative_single_dies (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ)
    (i : Fin m) (hi : ¬ AliveCoordinate degree R p t i) :
    aliveRepresentative degree R p t ((Pi.single i (1 : k)) : Fin m → k) = 0 := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [aliveRepresentative, hi]
  · simp [aliveRepresentative, Pi.single_apply, hji]

/-- The graded cycles of a prefix form a vector subspace.-/
noncomputable def normalCycleSpace (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) :
    Submodule k (Fin m → k) where
  carrier := {x | NormalCycle degree R p t x}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro i _; rfl
    · intro i _; rfl
    · simp
  add_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp [hx.1 i hi, hy.1 i hi]
    · intro i hi
      simp [hx.2.1 i hi, hy.2.1 i hi]
    · rw [Matrix.mulVec_add, hx.2.2, hy.2.2, add_zero]
  smul_mem' := by
    intro c x hx
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp [hx.1 i hi]
    · intro i hi
      simp [hx.2.1 i hi]
    · rw [Matrix.mulVec_smul, hx.2.2, smul_zero]

/-- Vectors supported exactly on the currently live homology coordinates.-/
noncomputable def aliveSpace (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) :
    Submodule k (Fin m → k) where
  carrier := {x | ∀ i, ¬ AliveCoordinate degree R p t i → x i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro c x hx i hi
    simp [hx i hi]

/--
@isnad1 id=mem.0h7v.s7.4eb72809bac7 from=translated src=- shape=d0dabe08 vocab=d3914dda
-/
theorem aliveRepresentative_mem_aliveSpace (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) :
    aliveRepresentative degree R p t x ∈ aliveSpace degree R p t := by
  intro i hi
  simp [aliveRepresentative, hi]

/-- Every live-coordinate vector already is its own representative.
@isnad1 id=eq.1h7v.s7.da90fe257ed0 from=translated src=- shape=1de91858 vocab=d3914dda
-/
theorem aliveRepresentative_of_mem (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ)
    (x : Fin m → k) (hx : x ∈ aliveSpace degree R p t) :
    aliveRepresentative degree R p t x = x := by
  ext i
  by_cases hi : AliveCoordinate degree R p t i
  · simp [aliveRepresentative, hi]
  · simp [aliveRepresentative, hi, hx i hi]

/-- Projection from cycles to their explicit homology coordinates.-/
noncomputable def cycleLiveMap (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) :
    normalCycleSpace degree R p t →ₗ[k] aliveSpace degree R p t where
  toFun x := ⟨aliveRepresentative degree R p t x.1,
    aliveRepresentative_mem_aliveSpace degree R p t x.1⟩
  map_add' x y := by
    apply Subtype.ext
    ext i
    by_cases hi : AliveCoordinate degree R p t i
    · simp [aliveRepresentative, hi]
    · simp [aliveRepresentative, hi]
  map_smul' c x := by
    apply Subtype.ext
    ext i
    by_cases hi : AliveCoordinate degree R p t i
    · simp [aliveRepresentative, hi]
    · simp [aliveRepresentative, hi]

/--
@isnad1 id=surjecti.4h9v.s11.2d0626dbad20 from=translated src=- shape=3f3434bd vocab=12293515
-/
theorem cycleLiveMap_surjective (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p t : ℕ) :
    Function.Surjective (cycleLiveMap degree R p t) := by
  intro y
  have hycycle : NormalCycle degree R p t y.1 := by
    have h := aliveRepresentative_cycle degree D R V W hD2 hR hcert hpiv p t y.1
    rwa [aliveRepresentative_of_mem degree R p t y.1 y.2] at h
  refine ⟨⟨y.1, hycycle⟩, ?_⟩
  apply Subtype.ext
  exact aliveRepresentative_of_mem degree R p t y.1 y.2

/-- The quotient of cycles by the kernel of live-coordinate projection is
the degree-`p` homology at this prefix. The next theorem identifies that
kernel with boundaries.-/
abbrev normalHomology (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) : Type _ :=
  (normalCycleSpace degree R p t) ⧸
    LinearMap.ker (cycleLiveMap degree R p t)

noncomputable def normalHomologyEquivAlive (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p t : ℕ) :
    normalHomology degree R p t ≃ₗ[k] aliveSpace degree R p t :=
  (cycleLiveMap degree R p t).quotKerEquivOfSurjective
    (cycleLiveMap_surjective degree D R V W hD2 hR hcert hpiv p t)

/--
@isnad1 id=iff.5h10v.s11.f0183f51ed20 from=translated src=- shape=13d46942 vocab=32882642
-/
theorem normalHomology_kernel_eq_boundaries (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hdegreeR : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p t : ℕ)
    (x : normalCycleSpace degree R p t) :
    x ∈ LinearMap.ker (cycleLiveMap degree R p t) ↔
      NormalBoundary degree R p t x.1 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    change aliveRepresentative degree R p t x.1 = 0 at hv
    exact (normalCycle_boundary_iff_live_zero degree D R V W hD2 hR hcert
      hdegreeR hpiv p t x.1 x.2).mpr hv
  · intro h
    apply Subtype.ext
    exact (normalCycle_boundary_iff_live_zero degree D R V W hD2 hR hcert
      hdegreeR hpiv p t x.1 x.2).mp h

/--
@isnad1 id=eq.0h6v.s6.9e0133ccd7f1 from=translated src=- shape=a0ef37c9 vocab=57f4a1d6
-/
theorem aliveSpace_eq_spanSubset (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) :
    aliveSpace degree R p t =
      Pi.spanSubset k {i | AliveCoordinate degree R p t i} := by
  ext x
  exact (Pi.mem_spanSubset_iff (R := k)).symm

/--
@isnad1 id=prefixsu.0h7v.s8.6ecf8a59ba14 from=translated src=- shape=6c4475af vocab=58bd6a2f
-/
theorem aliveSpace_prefix (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ)
    (x : aliveSpace degree R p t) : PrefixSupported t x.1 := by
  rw [← aliveRepresentative_of_mem degree R p t x.1 x.2]
  exact aliveRepresentative_prefix degree R p t x.1

/-- The coefficient map between homology bases at `s ≤ t`.-/
noncomputable def aliveSpaceMap (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) :
    aliveSpace degree R p s →ₗ[k] aliveSpace degree R p t where
  toFun x := ⟨aliveRepresentative degree R p t x.1,
    aliveRepresentative_mem_aliveSpace degree R p t x.1⟩
  map_add' x y := by
    apply Subtype.ext
    ext i
    by_cases hi : AliveCoordinate degree R p t i
    · simp [aliveRepresentative, hi]
    · simp [aliveRepresentative, hi]
  map_smul' c x := by
    apply Subtype.ext
    ext i
    by_cases hi : AliveCoordinate degree R p t i
    · simp [aliveRepresentative, hi]
    · simp [aliveRepresentative, hi]

/--
@isnad1 id=eq.0h6v.s10.451f1b4c04a0 from=translated src=- shape=b6eb3120 vocab=b93cfc92
-/
theorem aliveSpaceMap_id (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) :
    aliveSpaceMap degree R p t t = LinearMap.id := by
  ext x i
  change aliveRepresentative degree R p t x.1 i = x.1 i
  rw [aliveRepresentative_of_mem degree R p t x.1 x.2]

/--
@isnad1 id=eq.2h8v.s10.335aa1ffd093 from=translated src=- shape=676dc503 vocab=851573e9
-/
theorem aliveSpaceMap_comp (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t u : ℕ)
    (hst : s ≤ t) (htu : t ≤ u) :
    (aliveSpaceMap degree R p t u).comp (aliveSpaceMap degree R p s t) =
      aliveSpaceMap degree R p s u := by
  ext x i
  change aliveRepresentative degree R p u (aliveRepresentative degree R p t x.1) i =
    aliveRepresentative degree R p u x.1 i
  have hx : PrefixSupported t x.1 := by
    intro j hj
    exact aliveSpace_prefix degree R p s x j (le_trans hst hj)
  exact congrFun (aliveRepresentative_transition degree R p t u htu x.1 hx) i

/-- The normal-coordinate homology map is transported through the
proved quotient/basis equivalences.-/
noncomputable def normalHomologyMap (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p s t : ℕ) :
    normalHomology degree R p s →ₗ[k] normalHomology degree R p t :=
  ((normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p t).symm.toLinearMap).comp
    ((aliveSpaceMap degree R p s t).comp
      (normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p s).toLinearMap)

/-- The homology transition is exactly the coordinate projection of the
underlying inclusion of prefix cycles.
@isnad1 id=eq.5h11v.s14.1f97855a7f21 from=translated src=- shape=726830e5 vocab=33a967d3
-/
theorem normalHomologyMap_mk (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p s t : ℕ) (hst : s ≤ t)
    (x : normalCycleSpace degree R p s) :
    (normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p t)
      (normalHomologyMap degree D R V W hD2 hR hcert hpiv p s t
        (Submodule.Quotient.mk x)) =
      ⟨aliveRepresentative degree R p t x.1,
        aliveRepresentative_mem_aliveSpace degree R p t x.1⟩ := by
  simp only [normalHomologyMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  have hsource :
      (normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p s)
        (Submodule.Quotient.mk x) = cycleLiveMap degree R p s x := by
    exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ x
  rw [hsource]
  exact aliveRepresentative_transition degree R p s t hst x.1 x.2.1

/-- Coordinates surviving both endpoints of a structure map.-/
def Survivor (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) (i : Fin m) : Prop :=
  AliveCoordinate degree R p s i ∧ AliveCoordinate degree R p t i

noncomputable def survivorFinset (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => Survivor degree R p s t i)

/--
@isnad1 id=iff.0h8v.s11.d092b21471e0 from=translated src=- shape=bdcb05e3 vocab=f7c23587
-/
theorem aliveSpaceMap_range_iff (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ)
    (y : aliveSpace degree R p t) :
    y ∈ LinearMap.range (aliveSpaceMap degree R p s t) ↔
      ∀ i, ¬ AliveCoordinate degree R p s i → y.1 i = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ i hi
    have hx : x.1 i = 0 := x.2 i hi
    simp [aliveSpaceMap, aliveRepresentative, hx]
  · intro hy
    let x : aliveSpace degree R p s := ⟨y.1, hy⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact aliveRepresentative_of_mem degree R p t y.1 y.2

noncomputable def aliveSpaceMap_rangeEquiv (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) :
    LinearMap.range (aliveSpaceMap degree R p s t) ≃ₗ[k]
      Pi.spanSubset k {i | Survivor degree R p s t i} where
  toFun y := ⟨y.1.1, by
    rw [Pi.mem_spanSubset_iff]
    intro i hi
    by_cases hs : AliveCoordinate degree R p s i
    · have ht : ¬ AliveCoordinate degree R p t i := by
        intro ht
        exact hi ⟨hs, ht⟩
      exact y.1.2 i ht
    · exact (aliveSpaceMap_range_iff degree R p s t y.1).mp y.2 i hs⟩
  invFun y :=
    ⟨⟨y.1, by
      intro i hi
      apply (Pi.mem_spanSubset_iff.mp y.2) i
      intro h
      exact hi h.2⟩, by
      apply (aliveSpaceMap_range_iff degree R p s t _).mpr
      intro i hi
      apply (Pi.mem_spanSubset_iff.mp y.2) i
      intro h
      exact hi h.1⟩
  left_inv := by intro y; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro y; apply Subtype.ext; rfl
  map_add' := by intro x y; apply Subtype.ext; rfl
  map_smul' := by intro c x; apply Subtype.ext; rfl

/-- The rank of the coefficient map is the number of coordinates live at
both stages.
@isnad1 id=eq.0h7v.s12.63e4a6d4fda4 from=translated src=- shape=a75bc181 vocab=aa4e0160
-/
theorem aliveSpaceMap_rank (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) :
    Module.finrank k (LinearMap.range (aliveSpaceMap degree R p s t)) =
      (survivorFinset degree R p s t).card := by
  classical
  rw [(aliveSpaceMap_rangeEquiv degree R p s t).finrank_eq, Pi.dim_spanSubset]
  have hset : ({i | Survivor degree R p s t i} : Set (Fin m)) =
      ↑(survivorFinset degree R p s t) := by
    ext i
    simp [survivorFinset]
  rw [hset]
  simp

/--
@isnad1 id=iff.1h8v.s6.1891011681e7 from=translated src=- shape=dfe3821e vocab=caf011d5
-/
theorem survivor_iff_pairs_or_essential (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) (hst : s ≤ t)
    (i : Fin m) :
    Survivor degree R p s t i ↔
      (∃ hi : IsPivot R i, degree i = p ∧ i.val < s ∧
        t ≤ (deathOfPivot R i hi).val) ∨
      (IsEssential R i ∧ degree i = p ∧ i.val < s) := by
  constructor
  · rintro ⟨hs, ht⟩
    rcases hs.2 with hp | he
    · have htp : PivotAlive R t i := by
        rcases ht.2 with htp | hte
        · exact htp
        · exact (hte.1.2 hp.1).elim
      left
      refine ⟨hp.1, hs.1, hp.2.1, ?_⟩
      exact (pivotAlive_iff R t i hp.1).mp htp |>.2
    · right
      exact ⟨he.1, hs.1, he.2⟩
  · rintro (⟨hi, hdeg, hbirth, hdeath⟩ | ⟨he, hdeg, hbirth⟩)
    · have hs : PivotAlive R s i :=
        (pivotAlive_iff R s i hi).mpr ⟨hbirth, le_trans hst hdeath⟩
      have ht : PivotAlive R t i :=
        (pivotAlive_iff R t i hi).mpr ⟨lt_of_lt_of_le hbirth hst, hdeath⟩
      exact ⟨⟨hdeg, Or.inl hs⟩, ⟨hdeg, Or.inl ht⟩⟩
    · exact ⟨⟨hdeg, Or.inr ⟨he, hbirth⟩⟩,
        ⟨hdeg, Or.inr ⟨he, lt_of_lt_of_le hbirth hst⟩⟩⟩

noncomputable def pairSurvivorFinset (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => ∃ hi : IsPivot R i, degree i = p ∧
    i.val < s ∧ t ≤ (deathOfPivot R i hi).val)

noncomputable def essentialSurvivorFinset (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => IsEssential R i ∧ degree i = p ∧ i.val < s)

noncomputable def deathSurvivorFinset (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => ∃ i, columnPivot (R.col j) = some i ∧
    degree i = p ∧ i.val < s ∧ t ≤ j.val)

/--
@isnad1 id=eq.1h7v.s6.528563728aa8 from=translated src=- shape=c68081a0 vocab=993512e7
-/
theorem survivorFinset_partition (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) (hst : s ≤ t) :
    survivorFinset degree R p s t =
      pairSurvivorFinset degree R p s t ∪
        essentialSurvivorFinset degree R p s := by
  classical
  ext i
  simp only [survivorFinset, pairSurvivorFinset, essentialSurvivorFinset,
    Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  exact survivor_iff_pairs_or_essential degree R p s t hst i

/--
@isnad1 id=disjoint.0h7v.s5.c98394487132 from=translated src=- shape=4f2948d2 vocab=1b505256
-/
theorem pair_essential_disjoint (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) :
    Disjoint (pairSurvivorFinset degree R p s t)
      (essentialSurvivorFinset degree R p s) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hp he
  have hp' := (Finset.mem_filter.mp hp).2
  have he' := (Finset.mem_filter.mp he).2
  exact he'.1.2 hp'.choose

/--
@isnad1 id=eq.1h7v.s5.180787c10a00 from=translated src=- shape=e2cd89c8 vocab=111b3da1
-/
theorem pair_survivor_card_eq_death_card (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hpiv : DistinctPivots R)
    (p s t : ℕ) :
    (pairSurvivorFinset degree R p s t).card =
      (deathSurvivorFinset degree R p s t).card := by
  classical
  apply Finset.card_bij
    (fun i hi => deathOfPivot R i ((Finset.mem_filter.mp hi).2.choose))
  · intro i hi
    have hpair := (Finset.mem_filter.mp hi).2
    obtain ⟨hp, hdeg, hbirth, hdeath⟩ := hpair
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, i, deathOfPivot_spec R i hp,
      hdeg, hbirth, hdeath⟩
  · intro i hi q hq heq
    let hip : IsPivot R i := (Finset.mem_filter.mp hi).2.choose
    let hqp : IsPivot R q := (Finset.mem_filter.mp hq).2.choose
    have hi' := deathOfPivot_spec R i hip
    have hq' := deathOfPivot_spec R q hqp
    have hp : some i = some q := by
      calc
        some i = columnPivot (R.col (deathOfPivot R i hip)) := hi'.symm
        _ = columnPivot (R.col (deathOfPivot R q hqp)) := by
          rw [heq]
        _ = some q := hq'
    exact Option.some.inj hp
  · intro j hj
    obtain ⟨i, hji, hdeg, hbirth, hdeath⟩ :=
      (Finset.mem_filter.mp hj).2
    have hi : IsPivot R i := ⟨j, hji⟩
    have hj' := deathOfPivot_unique R hpiv i j hi hji
    have himem : i ∈ pairSurvivorFinset degree R p s t := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hi, hdeg, hbirth, by rwa [hj']⟩
    refine ⟨i, himem, ?_⟩
    exact deathOfPivot_unique R hpiv i j
      (Finset.mem_filter.mp himem).2.choose hji

/-- Rank count in the issue's death-column/essential-column indexing.
The two sums count occurrences, so identical endpoint values retain multiplicity.
@isnad1 id=eq.2h7v.s12.a12c2fd1063d from=translated src=- shape=0a68397e vocab=7092d64b
-/
theorem aliveSpaceMap_rank_formula (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hpiv : DistinctPivots R)
    (p s t : ℕ) (hst : s ≤ t) :
    Module.finrank k (LinearMap.range (aliveSpaceMap degree R p s t)) =
      (deathSurvivorFinset degree R p s t).card +
        (essentialSurvivorFinset degree R p s).card := by
  rw [aliveSpaceMap_rank, survivorFinset_partition degree R p s t hst,
    Finset.card_union_of_disjoint (pair_essential_disjoint degree R p s t),
    pair_survivor_card_eq_death_card degree R hpiv p s t]

/--
@isnad1 id=eq.4h11v.s14.6490d43e5be4 from=translated src=- shape=40ac57e2 vocab=454b1761
-/
theorem normalHomologyMap_transport (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p s t : ℕ)
    (x : normalHomology degree R p s) :
    (normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p t)
      (normalHomologyMap degree D R V W hD2 hR hcert hpiv p s t x) =
    aliveSpaceMap degree R p s t
      ((normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p s) x) := by
  simp [normalHomologyMap]

noncomputable def normalHomologyMap_rangeEquiv (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p s t : ℕ) :
    LinearMap.range (normalHomologyMap degree D R V W hD2 hR hcert hpiv p s t) ≃ₗ[k]
      LinearMap.range (aliveSpaceMap degree R p s t) where
  toFun y := ⟨(normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p t) y.1,
    by
      obtain ⟨x, hx⟩ := y.2
      refine ⟨(normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p s) x, ?_⟩
      rw [← hx]
      exact (normalHomologyMap_transport degree D R V W hD2 hR hcert hpiv p s t x).symm⟩
  invFun y := ⟨(normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p t).symm y.1,
    by
      obtain ⟨x, hx⟩ := y.2
      refine ⟨(normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p s).symm x, ?_⟩
      apply (normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p t).injective
      rw [normalHomologyMap_transport, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
      exact hx⟩
  left_inv := by
    intro y
    apply Subtype.ext
    exact LinearEquiv.symm_apply_apply _ _
  right_inv := by
    intro y
    apply Subtype.ext
    exact LinearEquiv.apply_symm_apply _ _
  map_add' := by
    intro x y
    apply Subtype.ext
    simp
  map_smul' := by
    intro c x
    apply Subtype.ext
    simp

/-- Structure-map rank on the quotient homology spaces.
@isnad1 id=eq.5h10v.s14.97ccaff71202 from=translated src=- shape=f18f515d vocab=9b1a55d5
-/
theorem normalHomologyMap_rank_formula (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p s t : ℕ) (hst : s ≤ t) :
    Module.finrank k (LinearMap.range
      (normalHomologyMap degree D R V W hD2 hR hcert hpiv p s t)) =
      (deathSurvivorFinset degree R p s t).card +
        (essentialSurvivorFinset degree R p s).card := by
  rw [(normalHomologyMap_rangeEquiv degree D R V W hD2 hR hcert hpiv p s t).finrank_eq]
  exact aliveSpaceMap_rank_formula degree R hpiv p s t hst

end TDA.Persistence.Reduction
