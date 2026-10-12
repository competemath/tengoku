/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2024, Problem 3

Let a₁, a₂, a₃, ... be an infinite sequence of positive integers,
and let N be a positive integer. Suppose that, for each n > N,
aₙ is equal to the number of times aₙ₋₁ appears in the list
a₁, a₂, ..., aₙ₋₁.

Prove that at least one of the sequences a₁, a₃, a₅, ... and
a₂, a₄, a₆, ... is eventually periodic.
-/

namespace Imo2024P3

open scoped Finset

def Condition (a : ℕ → ℕ) (N : ℕ) : Prop :=
  (∀ i, 0 < a i) ∧ ∀ n, N < n → a n = #{i ∈ Finset.range n | a i = a (n - 1)}

def EventuallyPeriodic (b : ℕ → ℕ) : Prop :=
  ∃ p M, 0 < p ∧ ∀ m, M ≤ m → b (m + p) = b m

/-! ### Definitions and lemmas about the sequence that do not actually need the condition of
the problem -/

/-- A number greater than any of the initial terms `a 0` through `a N` (otherwise arbitrary). -/
def M (a : ℕ → ℕ) (N : ℕ) : ℕ := (Finset.range (N + 1)).sup a + 1

/--
@isnad1 id=lt.0h2v.s4.169223daaf40 from=translated src=- shape=d51b80ee vocab=ec86c7fd
-/
lemma M_pos (a : ℕ → ℕ) (N : ℕ) : 0 < M a N :=
  Nat.add_one_pos _

/--
@isnad1 id=le.0h2v.s4.08bec9a1a49c from=translated src=- shape=d51b80ee vocab=ecf73b6f
-/
lemma one_le_M (a : ℕ → ℕ) (N : ℕ) : 1 ≤ M a N :=
  Nat.lt_iff_add_one_le.1 (M_pos a N)

/--
@isnad1 id=lt.1h3v.s4.08e728720d95 from=translated src=- shape=d13332bb vocab=5a10b50b
-/
lemma apply_lt_M_of_le_N (a : ℕ → ℕ) {N i : ℕ} (h : i ≤ N) : a i < M a N :=
  Nat.lt_add_one_iff.2 (Finset.le_sup (Finset.mem_range_succ_iff.2 h))

/--
@isnad1 id=lt.1h3v.s4.a2311d71eb3d from=translated src=- shape=2c97bfec vocab=5a10b50b
-/
lemma N_lt_of_M_le_apply {a : ℕ → ℕ} {N i : ℕ} (h : M a N ≤ a i) : N < i := by
  by_contra! hi
  exact Nat.not_succ_le_self _ (h.trans (Finset.le_sup (Finset.mem_range_succ_iff.2 hi)))

/--
@isnad1 id=ne.1h3v.s4.337f219937fa from=translated src=- shape=0c5a61fe vocab=ecf73b6f
-/
lemma ne_zero_of_M_le_apply {a : ℕ → ℕ} {N i : ℕ} (h : M a N ≤ a i) : i ≠ 0 :=
  Nat.ne_zero_of_lt (N_lt_of_M_le_apply h)

/--
@isnad1 id=lt.2h4v.s5.c9e69deea069 from=translated src=- shape=2dbfe36e vocab=5a10b50b
-/
lemma apply_lt_of_M_le_apply {a : ℕ → ℕ} {N i j : ℕ} (hi : M a N ≤ a i) (hj : j ≤ N) :
    a j < a i :=
  (apply_lt_M_of_le_N a hj).trans_le hi

/--
@isnad1 id=ne.2h4v.s5.97c4e849f4ce from=translated src=- shape=2dbfe36e vocab=ecf73b6f
-/
lemma apply_ne_of_M_le_apply {a : ℕ → ℕ} {N i j : ℕ} (hi : M a N ≤ a i) (hj : j ≤ N) :
    a j ≠ a i :=
  (apply_lt_of_M_le_apply hi hj).ne

/--
@isnad1 id=lt.1h2v.s5.353fbd5c5699 from=translated src=- shape=ad179e26 vocab=c3417733
-/
lemma toFinset_card_pos {a : ℕ → ℕ} {i : ℕ} (hf : {j | a j = a i}.Finite) : 0 < #hf.toFinset :=
  Finset.card_pos.mpr ((Set.Finite.toFinset_nonempty _).mpr ⟨i, rfl⟩)

/--
@isnad1 id=eq.0h2v.s4.9277aa62b343 from=translated src=- shape=55484119 vocab=45a1bdab
-/
lemma apply_nth_zero (a : ℕ → ℕ) (i : ℕ) : a (Nat.nth (a · = a i) 0) = a i :=
  Nat.nth_mem (p := (a · = a i)) 0 toFinset_card_pos

/--
@isnad1 id=eq.1h2v.s6.5493506801cf from=translated src=- shape=c2b759c5 vocab=2e410a46
-/
lemma map_add_one_range (p : ℕ → Prop) [DecidablePred p] (n : ℕ) (h0 : ¬ p 0) :
    {x ∈ Finset.range n | p (x + 1)}.map ⟨(· + 1), add_left_injective 1⟩ =
     {x ∈ Finset.range (n + 1) | p x } := by
  ext x
  simp only [Finset.mem_map]
  constructor
  · aesop
  · intro hx
    use x - 1
    cases x <;> simp_all

namespace Condition

/-! ### The basic structure of the sequence, eventually alternating small and large numbers -/

variable {a : ℕ → ℕ} {N : ℕ} (hc : Condition a N)
include hc

/--
@isnad1 id=lt.1h3v.s4.263ae75122bc from=translated src=- shape=3c76f64e vocab=ff690c56
-/
protected lemma pos (n : ℕ) : 0 < a n := hc.1 n

/--
@isnad1 id=ne.1h3v.s4.3400feed417a from=translated src=- shape=4f66c6d9 vocab=0c6e3e4d
-/
@[simp] lemma apply_ne_zero (n : ℕ) : a n ≠ 0 :=
  (hc.pos _).ne'

/--
@isnad1 id=le.1h3v.s4.d1e474170cef from=translated src=- shape=3c76f64e vocab=23e66d68
-/
lemma one_le_apply (n : ℕ) : 1 ≤ a n :=
  Nat.one_le_iff_ne_zero.2 (hc.apply_ne_zero n)

/--
@isnad1 id=eq.2h3v.s6.7a26ce98aa15 from=translated src=- shape=85571d3e vocab=832efc86
-/
lemma apply_eq_card {n : ℕ} (h : N < n) : a n = #{i ∈ Finset.range n | a i = a (n - 1)} :=
  hc.2 n h

/--
@isnad1 id=eq.2h3v.s6.95cef0cada9d from=translated src=- shape=ee745b0f vocab=898df4b2
-/
lemma apply_add_one_eq_card {n : ℕ} (h : N ≤ n) :
    a (n + 1) = #{i ∈ Finset.range (n + 1) | a i = a n} := by
  rw [hc.apply_eq_card (Nat.lt_add_one_of_le h)]
  simp

/--
@isnad1 id=eq.1h3v.s5.5ea72e6e84ab from=translated src=- shape=da282c43 vocab=b3656cef
-/
@[simp] lemma nth_apply_eq_zero (n : ℕ) : Nat.nth (a · = 0) n = 0 := by
  convert Nat.nth_false _ with i
  simp only [(hc.pos i).ne']

/--
@isnad1 id=eq.2h3v.s5.ff4d923e403a from=translated src=- shape=24d36ffd vocab=5d9e897b
-/
lemma nth_apply_add_one_eq {n : ℕ} (h : N ≤ n) : Nat.nth (a · = a n) (a (n + 1) - 1) = n := by
  rw [hc.apply_add_one_eq_card h]
  nth_rw 5 [← Nat.nth_count (p := (a · = a n)) rfl]
  simp [Finset.range_add_one, Finset.filter_insert, Nat.count_eq_card_filter_range]

/--
@isnad1 id=eq.3h4v.s6.6792211d7e83 from=translated src=- shape=6534cf5b vocab=38ef3336
-/
lemma apply_nth_add_one_eq {m n : ℕ} (hfc : ∀ hf : {i | a i = m}.Finite, n < #hf.toFinset)
    (hn : N ≤ Nat.nth (a · = m) n) : a (Nat.nth (a · = m) n + 1) = n + 1 := by
  rw [hc.apply_eq_card (Nat.lt_add_one_of_le hn), add_tsub_cancel_right,
    ← Nat.count_eq_card_filter_range, Nat.nth_mem n hfc, Nat.count_nth_succ hfc]

/--
@isnad1 id=eq.3h4v.s6.9f26d1ff117e from=translated src=- shape=b8bad1f0 vocab=6c86f240
-/
lemma apply_nth_add_one_eq_of_infinite {m n : ℕ} (hi : {i | a i = m}.Infinite)
    (hn : N ≤ Nat.nth (a · = m) n) : a (Nat.nth (a · = m) n + 1) = n + 1 :=
  hc.apply_nth_add_one_eq (fun hf ↦ absurd hf hi) hn

/--
@isnad1 id=eq.2h4v.s6.25b0b6811e39 from=translated src=- shape=744217d3 vocab=b1c8a690
-/
lemma apply_nth_add_one_eq_of_lt {m n : ℕ} (hn : N < Nat.nth (a · = m) n) :
    a (Nat.nth (a · = m) n + 1) = n + 1 := by
  refine hc.apply_nth_add_one_eq ?_ hn.le
  by_contra! hf
  have := Nat.nth_eq_zero.2 (.inr hf)
  lia

/--
@isnad1 id=lt.3h3v.s6.44f57781f39a from=translated src=- shape=4d9cc6ee vocab=6f5cbeca
-/
lemma lt_toFinset_card {j : ℕ} (h : M a N ≤ a (j + 1)) (hf : {i | a i = a j}.Finite) :
    M a N - 1 < #hf.toFinset := by
  rw [Nat.sub_lt_iff_lt_add' (M_pos _ _), Nat.lt_one_add_iff]
  exact (hc.apply_eq_card (N_lt_of_M_le_apply h) ▸ h).trans (Finset.card_le_card (by simp))

/--
@isnad1 id=ne.3h4v.s5.f205db000e3c from=translated src=- shape=a0de31bf vocab=385c6318
-/
lemma nth_ne_zero_of_M_le_of_lt {i k : ℕ} (hi : M a N ≤ a i) (hk : k < a (i + 1)) :
    Nat.nth (a · = a i) k ≠ 0 :=
  Nat.nth_ne_zero_anti (apply_ne_of_M_le_apply hi (Nat.zero_le _)) (by lia)
    (hc.nth_apply_add_one_eq (N_lt_of_M_le_apply hi).le ▸ ne_zero_of_M_le_apply hi)

/--
@isnad1 id=lt.4h4v.s6.e9e5065cd6ad from=translated src=- shape=7e35b0e5 vocab=d8982bde
-/
lemma apply_add_one_lt_of_apply_eq {i j : ℕ} (hi : N ≤ i) (hij : i < j) (ha : a i = a j) :
    a (i + 1) < a (j + 1) := by
  rw [hc.apply_add_one_eq_card hi, hc.apply_add_one_eq_card (by lia), ha]
  refine Finset.card_lt_card (Finset.ssubset_def.mp ⟨Finset.filter_subset_filter _
    (by simp [hij.le]), Finset.not_subset.mpr ⟨j, ?_⟩⟩)
  simpa using Order.add_one_le_iff.mpr hij

/--
@isnad1 id=ne.5h4v.s6.b90f5523d0a9 from=translated src=- shape=993ff745 vocab=2d38ffbe
-/
lemma apply_add_one_ne_of_apply_eq {i j : ℕ} (hi : N ≤ i) (hj : N ≤ j) (hij : i ≠ j)
    (ha : a i = a j) : a (i + 1) ≠ a (j + 1) :=
  hij.lt_or_gt.elim (fun h ↦ (hc.apply_add_one_lt_of_apply_eq hi h ha).ne) fun h ↦
    (hc.apply_add_one_lt_of_apply_eq hj h ha.symm).ne'

/--
@isnad1 id=ex.1h2v.s4.3ef79aabde04 from=translated src=- shape=28561f33 vocab=a97b136e
-/
lemma exists_infinite_setOf_apply_eq : ∃ m, {i | a i = m}.Infinite := by
  by_contra hi
  have hr : (Set.range a).Infinite := by
    contrapose! hi with hr
    rw [← Set.finite_coe_iff] at hr
    obtain ⟨n, hn⟩ := Finite.exists_infinite_fiber (Set.rangeFactorization a)
    rw [Set.infinite_coe_iff, Set.preimage] at hn
    simp only [Set.mem_singleton_iff, Set.rangeFactorization, Subtype.ext_iff] at hn
    exact ⟨↑n, hn⟩
  simp only [not_exists, Set.not_infinite] at hi
  have hinj : Set.InjOn (fun i ↦ Nat.nth (a · = i) 0 + 1) (Set.range a \ Set.Ico 0 (M a N)) := by
    rintro _ ⟨⟨_, rfl⟩, hi⟩ _ ⟨⟨_, rfl⟩, hj⟩ h
    simp only [Set.mem_Ico, zero_le, true_and, not_lt] at hi hj
    simp only [add_left_inj] at h
    convert congr(a $h) using 1 <;> simp [apply_nth_zero]
  refine Set.not_infinite.2 (hi 1) (Set.infinite_of_injOn_mapsTo hinj (fun i hi ↦ ?_)
    (hr.sdiff (Set.finite_Ico _ _)))
  simp only [Set.mem_sdiff, Set.mem_range, Set.mem_Ico, zero_le, true_and, not_lt] at hi
  rcases hi with ⟨⟨_, rfl⟩, hi⟩
  exact hc.apply_nth_add_one_eq toFinset_card_pos
    (N_lt_of_M_le_apply (a := a) (by simp only [apply_nth_zero, hi])).le

/--
@isnad1 id=nonempty.1h2v.s4.1909d0e74932 from=translated src=- shape=1013f498 vocab=5450948b
-/
lemma nonempty_setOf_infinite_setOf_apply_eq : {m | {i | a i = m}.Infinite}.Nonempty :=
  hc.exists_infinite_setOf_apply_eq

/--
@isnad1 id=injon.2h3v.s5.56ab27c15772 from=translated src=- shape=1459a4c1 vocab=af26dbd1
-/
lemma injOn_setOf_apply_add_one_eq_of_M_le {n : ℕ} (h : M a N ≤ n) :
    Set.InjOn a {i | a (i + 1) = n} := by
  intro i hi j hj hij
  have hi' := hi ▸ hc.nth_apply_add_one_eq (Nat.lt_add_one_iff.mp (N_lt_of_M_le_apply (hi ▸ h)))
  have hj' := hj ▸ hc.nth_apply_add_one_eq (Nat.lt_add_one_iff.mp (N_lt_of_M_le_apply (hj ▸ h)))
  rw [← hi', ← hj', hij]

/--
@isnad1 id=eq.1h2v.s5.dcd70de227c1 from=translated src=- shape=4841320d vocab=b1bc284a
-/
lemma empty_consecutive_apply_ge_M : {i | M a N ≤ a i ∧ M a N ≤ a (i + 1)} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro i
  induction i using Nat.strong_induction_on with | h i ih =>
  -- Let i be the first index where both `a i` and `a (i + 1)` are at least M.
  rintro ⟨hi1, hi2⟩
  have hi : ∀ j < i, M a N ≤ a j → a (j + 1) < M a N := by simp_all
  -- t is the set of indices before an appearance of the integer (a i).  For each j ∈ t, (a j)
  -- is the (a i)th appearance of that value, so each such value before index i appears at least
  -- M times before that index; since (a i) is the (at least) Mth appearance of that value, there
  -- are at least M positive integers appearing M times before (a i), a contradiction because one of
  -- those must be at least M.
  let t : Finset ℕ := {j ∈ Finset.range i | a (j + 1) = a i}
  let t' : Finset ℕ := {j ∈ Finset.range (i + 1) | a j = a i}
  have t_map_eq_t' : t.map ⟨(· + 1), add_left_injective 1⟩ = t' := by
    refine map_add_one_range (a · = a i) i ?_
    intro H
    rw [← H, M] at hi1
    have a0_le : a 0 ≤ (Finset.range (N + 1)).sup a := Finset.le_sup (by simp)
    lia
  have card_t_eq_card_t' : #t = #t' := by simp [← t_map_eq_t', t]
  have htM : ∀ j ∈ t, a j < M a N := by
    intro j hj
    simp only [t, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hj, hji⟩ := hj
    by_contra! hjM
    exact (lt_self_iff_false _).mp ((hji ▸ hi j hj hjM).trans_le hi1)
  have N_le_i : N ≤ i := by
    unfold M at hi1
    by_contra! HH
    have i_in_range : i ∈ Finset.range (N + 1) := by rw [Finset.mem_range]; lia
    have ai_le_sup : a i ≤ (Finset.range (N + 1)).sup a := Finset.le_sup i_in_range
    lia
  have ht' : a (i + 1) = #t' := hc.apply_add_one_eq_card N_le_i
  rw [← card_t_eq_card_t'] at ht'
  have ht'inj : Set.InjOn a t := by
    refine (hc.injOn_setOf_apply_add_one_eq_of_M_le hi1).mono ?_
    simp_all [t, t']
  have card_image_eq_card_t : #(Finset.image a t) = #t := Finset.card_image_of_injOn ht'inj
  have card_image_lt_M : #(Finset.image a t) < M a N := by
    refine (Finset.card_le_card (t := Finset.Ico 1 (M a N)) ?_).trans_lt ?_
    · simp only [Finset.subset_iff, Finset.mem_image, Finset.mem_Ico, forall_exists_index, and_imp,
                 forall_apply_eq_imp_iff₂]
      exact fun j hj ↦ ⟨hc.pos _, htM j hj⟩
    · simpa using M_pos a N
  lia

/--
@isnad1 id=ex.2h3v.s6.7521dc69c29c from=translated src=- shape=8512cf3e vocab=aa81b1da
-/
lemma card_lt_M_of_M_le {n : ℕ} (h : M a N ≤ n) :
    ∃ hf : {i | a i = n}.Finite, #hf.toFinset < M a N := by
  have := empty_consecutive_apply_ge_M hc
  contrapose! this with hin
  use Nat.nth (a · = n) (M a N - 1)
  have hin' := fun hf ↦ Nat.sub_one_lt_of_le (M_pos a N) (hin hf)
  have ha : M a N ≤ a (Nat.nth (a · = n) (M a N - 1)) := (Nat.nth_mem _ hin').symm ▸ h
  refine ⟨ha, ?_⟩
  suffices H : a (Nat.nth (fun x ↦ a x = n) (M a N - 1) + 1) = M a N from Nat.le_of_eq H.symm
  convert! hc.apply_nth_add_one_eq hin' (N_lt_of_M_le_apply ha).le using 1

/--
@isnad1 id=bddabove.1h2v.s4.1ba6b868f739 from=translated src=- shape=1013f498 vocab=795ad8c7
-/
lemma bddAbove_setOf_infinite_setOf_apply_eq : BddAbove {m | {i | a i = m}.Infinite} := by
  refine ⟨M a N, fun x hi ↦ ?_⟩
  by_contra hx
  exact hi (hc.card_lt_M_of_M_le (not_le.mp hx).le).1

/--
@isnad1 id=infinite.4h4v.s5.b6c8888f0d6b from=translated src=- shape=944365a1 vocab=8fbcc4c1
-/
lemma infinite_setOf_apply_eq_anti {j k : ℕ} (hj : 0 < j) (hk : {i | a i = k}.Infinite)
    (hjk : j ≤ k) : {i | a i = j}.Infinite := by
  have hk' : {i | a (i + 1) = k}.Infinite := by
    have hinj : Set.InjOn (· + 1) {i | a (i + 1) = k} := (add_left_injective _).injOn
    rw [← Set.infinite_image_iff hinj]
    have hk0 : ({i | a i = k} \ {0}).Infinite := hk.sdiff (Set.finite_singleton _)
    convert hk0 using 1
    ext i
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨j, rfl, rfl⟩
      simp
    · rintro ⟨rfl, h⟩
      exact ⟨i - 1, by simp [(by lia : i - 1 + 1 = i)]⟩
  have hinj : Set.InjOn (fun x ↦ Nat.nth (a · = a x) (j - 1) + 1)
      ({i | a (i + 1) = k} \ Set.Ico 0 N) := by
    intro x hx y hy h
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_Ico, zero_le, true_and, not_lt] at hx hy
    rcases hx with ⟨hxk, hNx⟩
    rcases hy with ⟨hyk, hNy⟩
    simp only [add_left_inj] at h
    have hxk' : Nat.nth (a · = a x) (k - 1) = x := by rw [← hxk, hc.nth_apply_add_one_eq hNx]
    have hyk' : Nat.nth (a · = a y) (k - 1) = y := by rw [← hyk, hc.nth_apply_add_one_eq hNy]
    have hjk' : j - 1 ≤ k - 1 := by lia
    apply_fun a at hxk' hyk'
    have hyj : a (Nat.nth (a · = a y) (j - 1)) = a y :=
      Nat.nth_mem_anti (p := (a · = a y)) hjk' hyk'
    rw [← h, Nat.nth_mem_anti (p := (a · = a x)) hjk' hxk'] at hyj
    by_contra hxy
    exact hc.apply_add_one_ne_of_apply_eq hNx hNy hxy hyj (hyk ▸ hxk)
  have hk'' : (_ \ Set.Ico 0 (N + 2)).Infinite :=
    ((Set.infinite_image_iff hinj).mpr (hk'.sdiff (Set.finite_Ico _ _))).sdiff (Set.finite_Ico _ _)
  refine hk''.mono fun _ hi ↦ ?_
  simp only [Set.mem_image, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_Ico, zero_le, true_and,
    not_lt] at hi
  rcases hi with ⟨⟨x, -, rfl⟩, _⟩
  rw [Set.mem_ofPred_eq, hc.apply_nth_add_one_eq_of_lt (by lia), Nat.sub_add_cancel hj]

/-! ### The definitions of small, medium and big numbers and the eventual alternation -/

variable (a)

/-- The largest number to appear infinitely often. -/
noncomputable def k : ℕ := sSup {m | {i | a i = m}.Infinite}

/-- Small numbers are those that are at most `k` (that is, those that appear infinitely often). -/
def Small (j : ℕ) : Prop := j ≤ k a

variable {a}

/--
@isnad1 id=infinite.1h2v.s4.21f079bc31fa from=translated src=- shape=fdde02c6 vocab=57e5a09e
-/
lemma infinite_setOf_apply_eq_k : {i | a i = k a}.Infinite :=
  Nat.sSup_mem hc.nonempty_setOf_infinite_setOf_apply_eq hc.bddAbove_setOf_infinite_setOf_apply_eq

/--
@isnad1 id=iff.2h3v.s5.3b8553f398b8 from=translated src=- shape=72790064 vocab=4e08130f
-/
lemma infinite_setOf_apply_eq_iff_small {j : ℕ} (hj : 0 < j) :
    {i | a i = j}.Infinite ↔ Small a j :=
  ⟨fun h ↦ le_csSup hc.bddAbove_setOf_infinite_setOf_apply_eq h,
   fun h ↦ hc.infinite_setOf_apply_eq_anti hj hc.infinite_setOf_apply_eq_k h⟩

/--
@isnad1 id=iff.2h3v.s5.c8f3f4db78ac from=translated src=- shape=c2be8b28 vocab=99cbcbb2
-/
lemma finite_setOf_apply_eq_iff_not_small {j : ℕ} (hj : 0 < j) :
    {i | a i = j}.Finite ↔ ¬Small a j := by
  simpa only [Set.not_infinite] using (hc.infinite_setOf_apply_eq_iff_small hj).not

/--
@isnad1 id=finite.1h2v.s5.686363bb2576 from=translated src=- shape=d483c667 vocab=bff7b788
-/
lemma finite_setOf_apply_eq_k_add_one : {i | a i = k a + 1}.Finite := by
  rw [hc.finite_setOf_apply_eq_iff_not_small (by lia), Small]
  lia

/-- There are only finitely many `m` that appear more than `k` times.
@isnad1 id=finite.1h2v.s5.b6eea142ce48 from=translated src=- shape=5facaca7 vocab=5b370887
-/
lemma finite_setOf_k_lt_card : {m | ∀ hf : {i | a i = m}.Finite, k a < #hf.toFinset}.Finite := by
  rw [← Set.finite_image_iff]
  · refine Set.Finite.of_sdiff (hc.finite_setOf_apply_eq_k_add_one.subset fun i hi ↦ ?_)
      (Set.finite_Iic N)
    simp only [Set.mem_sdiff, Set.mem_image, Set.mem_ofPred_eq, Set.mem_Iic, not_le] at hi
    rcases hi with ⟨⟨j, hjf, rfl⟩, hNi⟩
    rw [Set.mem_ofPred_eq, hc.apply_nth_add_one_eq hjf (by lia)]
  · intro i hi j hj hij
    simp only [add_left_inj] at hij
    apply_fun a at hij
    rwa [Nat.nth_mem _ hi, Nat.nth_mem _ hj] at hij

/--
@isnad1 id=bddabove.1h2v.s5.37eb283a1b22 from=translated src=- shape=7d451e20 vocab=1144d6bf
-/
lemma bddAbove_setOf_k_lt_card : BddAbove {m | ∀ hf : {i | a i = m}.Finite, k a < #hf.toFinset} :=
  hc.finite_setOf_k_lt_card.bddAbove

/--
@isnad1 id=lt.1h2v.s4.47f2138eae08 from=translated src=- shape=d7920ff2 vocab=ad5e6afd
-/
lemma k_pos : 0 < k a := by
  by_contra! hn
  apply nonpos_iff_eq_zero.mp hn ▸ hc.infinite_setOf_apply_eq_k
  convert Set.finite_empty
  ext i
  simp [(hc.pos i).ne']

/--
@isnad1 id=small.1h2v.s4.b5b71d185290 from=translated src=- shape=83f8c837 vocab=8e079455
-/
lemma small_one : Small a 1 := by
  by_contra hns
  simp only [Small, not_le, Nat.lt_one_iff, hc.k_pos.ne'] at hns

/--
@isnad1 id=infinite.1h2v.s4.5fdb46de54cf from=translated src=- shape=89db2a4f vocab=a97b136e
-/
lemma infinite_setOf_apply_eq_one : {i | a i = 1}.Infinite :=
  (hc.infinite_setOf_apply_eq_iff_small (by decide)).mpr hc.small_one

variable (a)

/-- The largest number to appear more than `k` times. -/
noncomputable def l : ℕ := sSup {m | ∀ hf : {i | a i = m}.Finite, k a < #hf.toFinset}

/-- Medium numbers are those that are more than `k` but at most `l` (and include all numbers
appearing finitely often but more than `k` times). -/
def Medium (j : ℕ) : Prop := k a < j ∧ j ≤ l a

/-- Big numbers are those greater than `l` (thus, appear at most `k` times). -/
def Big (j : ℕ) : Prop := l a < j

variable {a}

/--
@isnad1 id=le.1h2v.s4.55180f66fef9 from=translated src=- shape=89a217f6 vocab=aa6c8fb0
-/
lemma k_le_l : k a ≤ l a :=
  le_csSup hc.bddAbove_setOf_k_lt_card (fun hf ↦ absurd hf hc.infinite_setOf_apply_eq_k)

/--
@isnad1 id=lt.2h3v.s4.ca5c87b53c12 from=translated src=- shape=d528616e vocab=734419e3
-/
lemma k_lt_of_big {j : ℕ} (h : Big a j) : k a < j :=
  hc.k_le_l.trans_lt h

/--
@isnad1 id=lt.2h3v.s4.84703052323d from=translated src=- shape=78b57720 vocab=e0c729cc
-/
lemma pos_of_big {j : ℕ} (h : Big a j) : 0 < j :=
  (Nat.zero_le _).trans_lt (hc.k_lt_of_big h)

/--
@isnad1 id=not.2h3v.s4.ebcd93323e98 from=translated src=- shape=c6c53ca4 vocab=c6e4f47a
-/
lemma not_small_of_big {j : ℕ} (h : Big a j) : ¬Small a j := by simp [Small, hc.k_lt_of_big h]

/--
@isnad1 id=ex.2h3v.s5.390df307f42a from=translated src=- shape=3c9fc4ba vocab=172864bc
-/
lemma exists_card_le_of_big {j : ℕ} (h : Big a j) :
    ∃ hf : {i | a i = j}.Finite, #hf.toFinset ≤ k a := by
  have hns := hc.not_small_of_big h
  rw [← hc.finite_setOf_apply_eq_iff_not_small (hc.pos_of_big h)] at hns
  use hns
  by_contra! hlt
  exact notMem_of_csSup_lt h hc.bddAbove_setOf_k_lt_card fun _ ↦ hlt

variable (a N)

/-- `N'aux` is such that, by position `N'aux`, every medium number has made all its appearances
and every small number has appeared more than max(k, N+1) times. -/
noncomputable def N'aux : ℕ :=
  sSup {i | Medium a (a i)} ⊔ sSup ((fun i ↦ Nat.nth (a · = i) (k a ⊔ (N + 1))) '' Set.Iic (k a))

/-- `N'` is such that, by position `N'`, every medium number has made all its appearances
and every small number has appeared more than max(k, N+1) times; furthermore, `a N'` is small
(which means that every subsequent big number is preceded by a small number). -/
noncomputable def N' : ℕ := by
  classical
  exact N'aux a N + (if Small a (a (N'aux a N + 1)) then 1 else 2)

variable {a N}

/--
@isnad1 id=not.2h3v.s4.3f0ada1c68aa from=translated src=- shape=63f34ff2 vocab=d050cffd
-/
lemma not_medium_of_N'aux_lt {j : ℕ} (h : N'aux a N < j) : ¬Medium a (a j) := by
  let s : Set ℕ := ⋃ i ∈ Set.Ioc (k a) (l a), {j | a j = i}
  have hf : s.Finite := by
    refine (Set.finite_Ioc _ _).biUnion ?_
    rintro i ⟨hk, -⟩
    rwa [hc.finite_setOf_apply_eq_iff_not_small (by lia), Small, not_le]
  exact fun hm ↦ notMem_of_csSup_lt (le_sup_left.trans_lt h)
    (hf.subset fun i hi ↦ (by simpa [s, Medium] using hi)).bddAbove hm

/--
@isnad1 id=or.2h3v.s4.f9573710d9b2 from=translated src=- shape=fd3deb16 vocab=931ac5b9
-/
lemma small_or_big_of_N'aux_lt {j : ℕ} (h : N'aux a N < j) : Small a (a j) ∨ Big a (a j) := by
  have _ := hc.not_medium_of_N'aux_lt h
  rw [Small, Medium, Big] at *
  lia

/--
@isnad1 id=or.2h3v.s4.39273e3b2981 from=translated src=- shape=fd3deb16 vocab=d5c9098c
-/
lemma small_or_big_of_N'_le {j : ℕ} (h : N' a N ≤ j) : Small a (a j) ∨ Big a (a j) := by
  refine hc.small_or_big_of_N'aux_lt ?_
  rw [N'] at h
  lia

omit hc

/--
@isnad1 id=le.1h3v.s5.9017fa5e3484 from=translated src=- shape=45d4eb7d vocab=64b34685
-/
lemma nth_sup_k_N_add_one_le_N'aux_of_small {j : ℕ} (h : Small a j) :
    Nat.nth (a · = j) (k a ⊔ (N + 1)) ≤ N'aux a N := by
  by_contra! hn
  exact notMem_of_csSup_lt (le_sup_right.trans_lt hn) ((Set.finite_Iic _).image _).bddAbove
    ⟨j, h, rfl⟩

include hc

/--
@isnad1 id=le.2h3v.s5.51c6eaee1ae0 from=translated src=- shape=453ba082 vocab=7e6d43cc
-/
lemma nth_sup_k_le_N'aux_of_small {j : ℕ} (h : Small a j) :
    Nat.nth (a · = j) (k a) ≤ N'aux a N :=
  match j with
  | 0 => by simp only [hc.nth_apply_eq_zero, zero_le]
  | j + 1 => ((Nat.nth_le_nth ((hc.infinite_setOf_apply_eq_iff_small (Nat.zero_lt_succ j)).mpr h)).2
      le_sup_left).trans (nth_sup_k_N_add_one_le_N'aux_of_small h)

/--
@isnad1 id=le.2h3v.s5.8156d05c2c89 from=translated src=- shape=b74adc6d vocab=b55c85b9
-/
lemma nth_sup_N_add_one_le_N'aux_of_small {j : ℕ} (h : Small a j) :
    Nat.nth (a · = j) (N + 1) ≤ N'aux a N :=
  match j with
  | 0 => by simp only [hc.nth_apply_eq_zero, zero_le]
  | j + 1 => ((Nat.nth_le_nth ((hc.infinite_setOf_apply_eq_iff_small (Nat.zero_lt_succ j)).mpr h)).2
      le_sup_right).trans (nth_sup_k_N_add_one_le_N'aux_of_small h)

/--
@isnad1 id=lt.1h2v.s4.805d671b24c1 from=translated src=- shape=9ac2ba53 vocab=04531b48
-/
lemma N_lt_N'aux : N < N'aux a N :=
  Nat.add_one_le_iff.mp ((Nat.le_nth fun hf ↦ absurd hf hc.infinite_setOf_apply_eq_one).trans
    (hc.nth_sup_N_add_one_le_N'aux_of_small hc.small_one))

/-- `N` is less than `N'`.
@isnad1 id=lt.1h2v.s4.ede1bbb92713 from=translated src=- shape=9ac2ba53 vocab=e29cb692
-/
lemma N_lt_N' : N < N' a N := hc.N_lt_N'aux.trans_le (Nat.le_add_right _ _)

/--
@isnad1 id=lt.4h5v.s6.fd3a8b8336c1 from=translated src=- shape=c0829a5b vocab=6fc79f32
-/
lemma lt_card_filter_eq_of_small_nth_lt {i j t : ℕ} (hj0 : 0 < j) (h : Small a j)
    (ht : Nat.nth (a · = j) t < i) : t < #{m ∈ Finset.range i | a m = j} := by
  rw [← hc.infinite_setOf_apply_eq_iff_small hj0] at h
  rw [← Nat.count_eq_card_filter_range]
  exact (Nat.nth_lt_nth h).mp (ht.trans_le (Nat.le_nth_count h _))

/--
@isnad1 id=lt.4h4v.s5.fd49ae5f95e1 from=translated src=- shape=c467ee4a vocab=52799883
-/
lemma k_lt_card_filter_eq_of_small_of_N'aux_le {i j : ℕ} (hj0 : 0 < j) (h : Small a j)
    (hN'aux : N'aux a N < i) : k a < #{m ∈ Finset.range i | a m = j} :=
  hc.lt_card_filter_eq_of_small_nth_lt hj0 h ((hc.nth_sup_k_le_N'aux_of_small h).trans_lt hN'aux)

/--
@isnad1 id=lt.4h4v.s6.e7ef20c0fe76 from=translated src=- shape=ee1c9e78 vocab=c523c8d8
-/
lemma N_add_one_lt_card_filter_eq_of_small_of_N'aux_le {i j : ℕ} (hj0 : 0 < j) (h : Small a j)
    (hN'aux : N'aux a N < i) : N + 1 < #{m ∈ Finset.range i | a m = j} :=
  hc.lt_card_filter_eq_of_small_nth_lt hj0 h
    ((hc.nth_sup_N_add_one_le_N'aux_of_small h).trans_lt hN'aux)

/--
@isnad1 id=lt.4h4v.s6.e5476e4149d6 from=translated src=- shape=ee1c9e78 vocab=bf29c2fe
-/
lemma N_add_one_lt_card_filter_eq_of_small_of_N'_le {i j : ℕ} (hj0 : 0 < j) (h : Small a j)
    (hN' : N' a N < i) : N + 1 < #{m ∈ Finset.range i | a m = j} := by
  refine hc.N_add_one_lt_card_filter_eq_of_small_of_N'aux_le hj0 h ?_
  rw [N'] at hN'
  exact Nat.lt_of_add_right_lt hN'

/--
@isnad1 id=big.3h3v.s5.e9c893f99be0 from=translated src=- shape=cdce9e0f vocab=1333dd07
-/
lemma apply_add_one_big_of_apply_small_of_N'aux_le {i : ℕ} (h : Small a (a i))
    (hN'aux : N'aux a N ≤ i) : Big a (a (i + 1)) := by
  have hN'' : N'aux a N < i + 1 := by lia
  suffices ¬Small a (a (i + 1)) by simpa [this] using hc.small_or_big_of_N'aux_lt hN''
  rw [hc.apply_add_one_eq_card (hc.N_lt_N'aux.le.trans hN'aux), Small, not_le]
  exact hc.k_lt_card_filter_eq_of_small_of_N'aux_le (hc.pos _) h hN''

/--
@isnad1 id=big.3h3v.s5.2bac898529e9 from=translated src=- shape=cdce9e0f vocab=003603ff
-/
lemma apply_add_one_big_of_apply_small_of_N'_le {i : ℕ} (h : Small a (a i)) (hN' : N' a N ≤ i) :
    Big a (a (i + 1)) :=
  hc.apply_add_one_big_of_apply_small_of_N'aux_le h ((Nat.le_add_right _ _).trans hN')

/--
@isnad1 id=small.3h3v.s5.7d7deedc58d7 from=translated src=- shape=cdce9e0f vocab=1333dd07
-/
lemma apply_add_one_small_of_apply_big_of_N'aux_le {i : ℕ} (h : Big a (a i))
    (hN'aux : N'aux a N ≤ i) : Small a (a (i + 1)) := by
  obtain ⟨hf, hfc⟩ := hc.exists_card_le_of_big h
  rw [hc.apply_add_one_eq_card (hc.N_lt_N'aux.le.trans hN'aux)]
  exact (Finset.card_le_card (by simp)).trans hfc

/--
@isnad1 id=small.3h3v.s5.5f767df0bf56 from=translated src=- shape=cdce9e0f vocab=003603ff
-/
lemma apply_add_one_small_of_apply_big_of_N'_le {i : ℕ} (h : Big a (a i)) (hN' : N' a N ≤ i) :
    Small a (a (i + 1)) :=
  hc.apply_add_one_small_of_apply_big_of_N'aux_le h ((Nat.le_add_right _ _).trans hN')

/--
@isnad1 id=small.3h3v.s5.71a7997af04d from=translated src=- shape=d3d82a81 vocab=c2c217f6
-/
lemma apply_add_two_small_of_apply_small_of_N'_le {i : ℕ} (h : Small a (a i)) (hN' : N' a N ≤ i) :
    Small a (a (i + 2)) :=
  hc.apply_add_one_small_of_apply_big_of_N'_le (hc.apply_add_one_big_of_apply_small_of_N'_le h hN')
    (by lia)

/-- `a (N' a N)` is a small number.
@isnad1 id=small.1h2v.s4.149e934aab37 from=translated src=- shape=f4a0a801 vocab=fb5d0fb0
-/
lemma small_apply_N' : Small a (a (N' a N)) := by
  rw [N']
  split_ifs with hi
  · exact hi
  · have hb : Big a (a (N'aux a N + 1)) := by
      simpa [hi] using hc.small_or_big_of_N'aux_lt (Nat.lt_add_one (N'aux a N))
    exact hc.apply_add_one_small_of_apply_big_of_N'aux_le hb (by lia)

/--
@isnad1 id=iff.1h3v.s5.4fe5dda3e78a from=translated src=- shape=f95c6019 vocab=e4519fe7
-/
lemma small_apply_N'_add_iff_even {n : ℕ} : Small a (a (N' a N + n)) ↔ Even n := by
  induction n with
  | zero => simpa using hc.small_apply_N'
  | succ n ih =>
    by_cases he : Even n <;> rw [← add_assoc] <;> simp only [he, iff_true, iff_false] at ih
    · have hne : ¬ Even (n + 1) := by simp [Nat.not_even_iff_odd, he]
      simp only [hne, iff_false]
      exact hc.not_small_of_big (hc.apply_add_one_big_of_apply_small_of_N'_le ih (by grind))
    · have hb : Big a (a (N' a N + n)) := by
        simpa [ih] using hc.small_or_big_of_N'_le (j := N' a N + n) (by lia)
      simp [hc.apply_add_one_small_of_apply_big_of_N'_le hb (by lia), Nat.not_even_iff_odd.mp he]

/--
@isnad1 id=iff.2h4v.s5.5069aff41813 from=translated src=- shape=fb78ae81 vocab=d0e50555
-/
lemma small_apply_add_two_mul_iff_small {n : ℕ} (m : ℕ) (hN' : N' a N ≤ n) :
    Small a (a (n + 2 * m)) ↔ Small a (a n) := by
  rw [show n = N' a N + (n - N' a N) by lia, add_assoc, hc.small_apply_N'_add_iff_even,
    hc.small_apply_N'_add_iff_even]
  simp [Nat.even_add]

/--
@isnad1 id=small.3h3v.s5.ad5d5f77dc48 from=translated src=- shape=cdce9e0f vocab=13b75738
-/
lemma apply_sub_one_small_of_apply_big_of_N'_le {i : ℕ} (h : Big a (a i)) (hN' : N' a N ≤ i) :
    Small a (a (i - 1)) := by
  have h0i : 1 ≤ i := by
    have := hc.N_lt_N'
    lia
  have h' : N' a N ≤ i - 1 := by
    by_contra hi
    have hi' : i = N' a N := by lia
    exact hc.not_small_of_big (hi' ▸ h) hc.small_apply_N'
  exact (hc.small_or_big_of_N'_le h').elim id fun hb ↦
    False.elim (hc.not_small_of_big h (Nat.sub_add_cancel h0i ▸
      (hc.apply_add_one_small_of_apply_big_of_N'_le hb h')))

/--
@isnad1 id=big.3h3v.s5.0421e9ddd791 from=translated src=- shape=cdce9e0f vocab=7c6e7534
-/
lemma apply_sub_one_big_of_apply_small_of_N'_lt {i : ℕ} (h : Small a (a i)) (hN' : N' a N < i) :
    Big a (a (i - 1)) := by
  have h0i : 1 ≤ i := by lia
  have h' : N' a N ≤ i - 1 := by lia
  exact (hc.small_or_big_of_N'_le h').elim (fun hs ↦ False.elim (hc.not_small_of_big
    (Nat.sub_add_cancel h0i ▸ hc.apply_add_one_big_of_apply_small_of_N'_le hs h') h)) id

/--
@isnad1 id=small.3h3v.s5.440fad51be17 from=translated src=- shape=d3d82a81 vocab=cfa38705
-/
lemma apply_sub_two_small_of_apply_small_of_N'_lt {i : ℕ} (h : Small a (a i)) (hN' : N' a N < i) :
    Small a (a (i - 2)) := by
  convert! hc.apply_sub_one_small_of_apply_big_of_N'_le
    (hc.apply_sub_one_big_of_apply_small_of_N'_lt h hN') (by lia) using 1

/--
@isnad1 id=lt.3h3v.s5.505a4d4acf00 from=translated src=- shape=4e4f01f5 vocab=2b506b66
-/
lemma N_add_one_lt_apply_of_apply_big_of_N'_le {i : ℕ} (h : Big a (a i)) (hN' : N' a N ≤ i) :
    N + 1 < a i := by
  refine hc.apply_eq_card (hc.N_lt_N'.trans_le hN') ▸
    hc.N_add_one_lt_card_filter_eq_of_small_of_N'_le (hc.pos _)
      (hc.apply_sub_one_small_of_apply_big_of_N'_le h hN') ?_
  by_contra
  exact hc.not_small_of_big ((by lia : i = N' a N) ▸ h) hc.small_apply_N'

/--
@isnad1 id=eq.3h3v.s6.98979a904913 from=translated src=- shape=19e6ff3c vocab=ef7cdd7e
-/
lemma setOf_apply_eq_of_apply_big_of_N'_le {i : ℕ} (h : Big a (a i)) (hN' : N' a N ≤ i) :
    {j | a j = a i} = {j | N < j ∧ Small a (a (j - 1)) ∧
      a i = #{t ∈ Finset.range j | a t = a (j - 1)}} := by
  have hs : {j | N < j ∧ Small a (a (j - 1)) ∧ a i = #{t ∈ Finset.range j | a t = a (j - 1)}} ⊆
      {j | a j = a i} := by
    rintro _ ⟨hNj, -, hj⟩
    exact hj ▸ hc.apply_eq_card hNj
  rcases hc.exists_card_le_of_big h with ⟨hf, hck⟩
  have hf' : {j | N < j ∧ Small a (a (j - 1)) ∧
    a i = #{t ∈ Finset.range j | a t = a (j - 1)}}.Finite := hf.subset hs
  suffices hf.toFinset = hf'.toFinset by simpa using this
  rw [← Set.Finite.toFinset_subset_toFinset (hs := hf') (ht := hf)] at hs
  refine (Finset.eq_of_subset_of_card_le hs (hck.trans ?_)).symm
  have hs : #((Finset.Icc 1 (k a)).image (fun t ↦ Nat.nth (a · = t) (a i - 1) + 1)) = k a := by
    convert Finset.card_image_of_injOn fun t ht u hu htu ↦ ?_
    · simp only [Nat.card_Icc, add_tsub_cancel_right]
    · simp only [add_left_inj] at htu
      simp only [Finset.coe_Icc, Set.mem_Icc] at ht hu
      rw [← Small, ← hc.infinite_setOf_apply_eq_iff_small (by lia)] at ht hu
      apply_fun a at htu
      rwa [Nat.nth_mem_of_infinite ht.2, Nat.nth_mem_of_infinite hu.2] at htu
  refine hs ▸ Finset.card_le_card (Finset.subset_iff.2 fun j hj ↦ ?_)
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  simp only [Finset.mem_image, Finset.mem_Icc] at hj
  rcases hj with ⟨t, ⟨ht1, htk⟩, rfl⟩
  have hN1 : N < a i - 1 := by
    have := hc.N_add_one_lt_apply_of_apply_big_of_N'_le h hN'
    lia
  simp only [add_tsub_cancel_right]
  rw [← Small] at htk
  have htki := htk
  rw [← hc.infinite_setOf_apply_eq_iff_small (by lia)] at htki
  rw [Nat.nth_mem_of_infinite htki]
  simp only [htk, true_and]
  refine ⟨Nat.lt_add_one_iff.mpr ((Nat.le_nth (fun hf ↦ absurd hf htki)).trans
    ((Nat.nth_le_nth htki).2 hN1.le)), ?_⟩
  rw [← Nat.count_eq_card_filter_range, Nat.count_nth_succ_of_infinite htki]
  lia

/--
@isnad1 id=lt.4h4v.s5.61b684e870ea from=translated src=- shape=2163d9ed vocab=18d34a2b
-/
lemma N_lt_of_apply_eq_of_apply_big_of_N'_le {i j : ℕ} (hj : a j = a i) (h : Big a (a i))
    (hN' : N' a N ≤ i) : N < j :=
  have hj' : j ∈ {t | a t = a i} := by simpa using hj
  (hc.setOf_apply_eq_of_apply_big_of_N'_le h hN' ▸ hj').1

/--
@isnad1 id=small.4h4v.s5.bfb136540d29 from=translated src=- shape=a9ba2dda vocab=13b75738
-/
lemma small_apply_sub_one_of_apply_eq_of_apply_big_of_N'_le {i j : ℕ} (hj : a j = a i)
    (h : Big a (a i)) (hN' : N' a N ≤ i) : Small a (a (j - 1)) :=
  have hj' : j ∈ {t | a t = a i} := by simpa using hj
  (hc.setOf_apply_eq_of_apply_big_of_N'_le h hN' ▸ hj').2.1

/-! ### The main lemmas leading to the required result -/

/-- Lemma 1 from the informal solution.
@isnad1 id=eq.3h3v.s6.e5633c702df3 from=translated src=- shape=3076aa64 vocab=3abc9e32
-/
lemma apply_add_one_eq_card_small_le_card_eq {i : ℕ} (hi : N' a N < i) (hib : Big a (a i)) :
    a (i + 1) = #{m ∈ Finset.range (k a + 1) | a i ≤ #{j ∈ Finset.range i | a j = m}} := by
  rw [hc.apply_add_one_eq_card (hc.N_lt_N'.trans hi).le]
  convert Finset.card_image_of_injOn (f := fun j ↦ Nat.nth (a · = j) (a i - 1) + 1) ?_ using 1
  · congr
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    refine ⟨fun ⟨hj, hji⟩ ↦ ⟨a (j - 1), hji ▸ ?_⟩, fun ⟨t, ⟨hts, htr⟩, ht⟩ ↦ ?_⟩
    · have hjN : N < j := hc.N_lt_of_apply_eq_of_apply_big_of_N'_le hji hib hi.le
      refine ⟨⟨Nat.lt_add_one_iff.mpr (hc.small_apply_sub_one_of_apply_eq_of_apply_big_of_N'_le
        hji hib hi.le), ?_⟩, ?_⟩
      · rw [hc.apply_eq_card hjN]
        have : j ≤ i := by lia
        gcongr
      · have hj1 : j = j - 1 + 1 := by lia
        nth_rw 2 [hj1]
        rw [hc.nth_apply_add_one_eq (by lia), hj1.symm]
    · subst ht
      rw [Nat.lt_add_one_iff, ← Small] at hts
      have ht0 : 0 < t := by
        by_contra! h0
        simp [nonpos_iff_eq_zero.mp h0, hc.apply_ne_zero] at htr
      rw [← hc.infinite_setOf_apply_eq_iff_small ht0] at hts
      rw [← Nat.count_eq_card_filter_range] at htr
      constructor
      · rwa [add_lt_add_iff_right, ← Nat.lt_nth_iff_count_lt hts,
          Nat.sub_lt_iff_lt_add' (hc.one_le_apply _), Nat.lt_one_add_iff]
      · rw [hc.apply_nth_add_one_eq_of_infinite hts]
        · exact Nat.sub_add_cancel (hc.one_le_apply _)
        · refine (Nat.le_nth fun hf ↦ absurd hf hts).trans ((Nat.nth_le_nth hts).2 ?_)
          have := hc.N_add_one_lt_apply_of_apply_big_of_N'_le hib hi.le
          lia
  · intro t ht u hu htu
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Nat.lt_add_one_iff] at ht hu
    rw [← Small] at ht hu
    have ht0 : 0 < t := by
      by_contra! h0
      simp only [nonpos_iff_eq_zero] at h0
      simp [h0, hc.apply_ne_zero] at ht
    have hu0 : 0 < u := by
      by_contra! h0
      simp only [nonpos_iff_eq_zero] at h0
      simp [h0, hc.apply_ne_zero] at hu
    rw [← hc.infinite_setOf_apply_eq_iff_small ht0] at ht
    rw [← hc.infinite_setOf_apply_eq_iff_small hu0] at hu
    simp only [add_left_inj] at htu
    apply_fun a at htu
    rwa [Nat.nth_mem_of_infinite ht.1, Nat.nth_mem_of_infinite hu.1] at htu

/-- Similar to Lemma 1 from the informal solution, but with a `Small` hypothesis instead of `Big`
and considering a range one larger (the form needed for Lemma 2).
@isnad1 id=eq.3h3v.s7.82c38535e31c from=translated src=- shape=68debcc9 vocab=6881346d
-/
lemma apply_eq_card_small_le_card_eq_of_small {i : ℕ} (hi : N' a N + 1 < i)
    (his : Small a (a i)) :
    a i = #{m ∈ Finset.range (k a + 1) | a (i - 1) ≤ #{j ∈ Finset.range i | a j = m}} := by
  have hib : Big a (a (i - 1)) := hc.apply_sub_one_big_of_apply_small_of_N'_lt his (by lia)
  nth_rw 1 [show i = i - 1 + 1 by lia]
  rw [hc.apply_add_one_eq_card_small_le_card_eq (by lia) hib]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
  intro hj
  convert Iff.rfl using 2
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_range]
  refine ⟨fun ⟨hti, rfl⟩ ↦ ⟨?_, rfl⟩, fun ⟨_, rfl⟩ ↦ ⟨by lia, rfl⟩⟩
  by_contra hti1
  have htieq : t = i - 1 := by lia
  subst htieq
  exact hc.not_small_of_big hib (Nat.lt_add_one_iff.mp hj)

/-- Lemma 2 from the informal solution.
@isnad1 id=ex.6h4v.s7.d4b54330e320 from=translated src=- shape=eb328cba vocab=29c2c7bf
-/
lemma exists_apply_sub_two_eq_of_apply_eq {i j : ℕ} (hi : N' a N + 2 < i) (hijlt : i < j)
    (his : Small a (a i)) (hijeq : a i = a j)
    (hij1 : ∀ t, Small a t → #{x ∈ Finset.Ico i j | a x = t} ≤ 1) :
    ∃ t, t ∈ Finset.Ico i j ∧ a (i - 2) = a t := by
  let I : Finset ℕ := {t ∈ Finset.range (k a + 1) | a (i - 1) ≤ #{u ∈ Finset.range i | a u = t}}
  let J : Finset ℕ := {t ∈ Finset.range (k a + 1) | a (j - 1) ≤ #{u ∈ Finset.range j | a u = t}}
  have hIc : a i = #I := hc.apply_eq_card_small_le_card_eq_of_small (by lia) his
  have hJc : a j = #J := hc.apply_eq_card_small_le_card_eq_of_small (by lia) (hijeq ▸ his)
  have hIJc : #I = #J := hIc ▸ hJc ▸ hijeq
  have := hc.N_lt_N'
  have hiju : Finset.range i ∪ Finset.Ico i j = Finset.range j := by
    rw [Finset.range_eq_Ico, Finset.Ico_union_Ico' (by lia) (by lia)]
    simp [hijlt.le]
  have hi2s : a (i - 2) < k a + 1 :=
    Nat.lt_add_one_iff.mpr (hc.apply_sub_two_small_of_apply_small_of_N'_lt his (by lia))
  have hiI : a (i - 2) ∈ I := by
    simp only [I, Finset.mem_filter, Finset.mem_range, hi2s, true_and]
    rw [hc.apply_eq_card (by lia), show i - 1 - 1 = i - 2 by lia]
    exact Finset.card_le_card (Finset.filter_subset_filter _  (by simp))
  have hj2s : a (j - 2) < k a + 1 :=
    Nat.lt_add_one_iff.mpr (hc.apply_sub_two_small_of_apply_small_of_N'_lt (hijeq ▸ his) (by lia))
  have hjJ : a (j - 2) ∈ J := by
    simp only [J, Finset.mem_filter, Finset.mem_range, hj2s, true_and]
    rw [hc.apply_eq_card (by lia), show j - 1 - 1 = j - 2 by lia]
    exact Finset.card_le_card (Finset.filter_subset_filter _  (by simp))
  have hjI : a (j - 2) ∈ I := by
    by_contra hjI
    have hjIf := hjI
    simp only [Finset.mem_filter, Finset.mem_range, hj2s, true_and, not_le, I,
      Nat.lt_iff_add_one_le] at hjIf
    have hjI' : a (j - 1) ≤ a (i - 1) := by
      calc a (j - 1) ≤ #{u ∈ Finset.range j | a u = a (j - 2)} :=
            (Finset.mem_filter.mp hjJ).2
        _ = #{u ∈ Finset.range i ∪ Finset.Ico i j | a u = a (j - 2)} := by rw [hiju]
        _ ≤ #{u ∈ Finset.range i | a u = a (j - 2)} + #{u ∈ Finset.Ico i j | a u = a (j - 2)} := by
            rw [Finset.filter_union]
            exact Finset.card_union_le _ _
        _ ≤ #{u ∈ Finset.range i | a u = a (j - 2)} + 1 := by
            gcongr
            exact hij1 _ (by rwa [Nat.lt_add_one_iff, ← Small] at hj2s)
        _ ≤ a (i - 1) := hjIf
    refine hjI (Finset.eq_of_subset_of_card_le (fun x hxI ↦ ?_) hIJc.symm.le ▸ hjJ)
    simp only [Finset.mem_filter, I, J] at *
    refine ⟨hxI.1, ?_⟩
    calc a (j - 1) ≤ a (i - 1) := hjI'
      _ ≤ #{u ∈ Finset.range i | a u = x} := hxI.2
      _ ≤ #{u ∈ Finset.range j | a u = x} :=
        Finset.card_le_card (Finset.filter_subset_filter _ (by simp [hijlt.le]))
  have hi1j1 : a (i - 1) + 1 ≤ a (j - 1) := by
    calc a (i - 1) + 1 ≤ #{u ∈ Finset.range i | a u = a (j - 2)} + 1 := by
          gcongr
          simp only [Finset.mem_filter, I] at hjI
          exact hjI.2
      _ ≤ #{u ∈ Finset.range i | a u = a (j - 2)} + #{u ∈ Finset.Ico i j | a u = a (j - 2)} := by
          gcongr
          simp only [Finset.one_le_card]
          refine ⟨j - 2, ?_⟩
          simp only [Finset.mem_filter, Finset.mem_Ico, and_true]
          refine ⟨?_, by lia⟩
          by_contra hj
          have hj' : j = i + 1 := by lia
          subst hj'
          exact hc.not_small_of_big (hc.apply_add_one_big_of_apply_small_of_N'_le his (by lia))
            (hijeq ▸ his)
      _ = #({u ∈ Finset.range i | a u = a (j - 2)} ∪ {u ∈ Finset.Ico i j | a u = a (j - 2)}) := by
          refine (Finset.card_union_of_disjoint ?_).symm
          simp only [Finset.disjoint_iff_ne, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
            and_imp]
          rintro t hti - u hiu - -
          lia
      _ = #{u ∈ Finset.range j | a u = a (j - 2)} := by
          rw [← Finset.filter_union, hiju]
      _ = a (j - 1) := by
          rw [hc.apply_eq_card (show N < j - 1 by lia)]
          congr 1
          ext t
          simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨fun ⟨htj, htj'⟩ ↦ ⟨?_, by convert! htj' using 1⟩,
            fun ⟨htj, htj'⟩ ↦ ⟨by lia, by convert! htj' using 1⟩⟩
          by_contra htj''
          have ht1 : t = j - 1 := by lia
          subst ht1
          exact hc.not_small_of_big (htj' ▸ hc.apply_sub_one_big_of_apply_small_of_N'_lt
            (hijeq ▸ his) (by lia)) (hc.apply_sub_two_small_of_apply_small_of_N'_lt
            (hijeq ▸ his) (by lia))
  have hIJ : I = J := by
    refine (Finset.eq_of_subset_of_card_le (Finset.subset_iff.mp fun x hxJ ↦ ?_) hIJc.le).symm
    simp only [Finset.mem_filter, Finset.mem_range, I, J, Nat.lt_add_one_iff] at *
    refine ⟨hxJ.1, (add_le_add_iff_right 1).mp ?_⟩
    calc a (i - 1) + 1 ≤ a (j - 1) := hi1j1
       _ ≤ #{u ∈ Finset.range j | a u = x} := hxJ.2
       _ = #({u ∈ Finset.range i | a u = x} ∪ {u ∈ Finset.Ico i j | a u = x}) := by
           rw [← Finset.filter_union, hiju]
       _ ≤ #{u ∈ Finset.range i | a u = x} + #{u ∈ Finset.Ico i j | a u = x} :=
           Finset.card_union_le _ _
       _ ≤ #{u ∈ Finset.range i | a u = x} + 1 := by
           gcongr
           exact hij1 _ hxJ.1
  simp only [hIJ, J, Finset.mem_filter] at hiI
  have hiI' := hi1j1.trans hiI.2
  rw [hc.apply_eq_card (by lia), show i - 1 - 1 = i - 2 by lia, Nat.add_one_le_iff,
     ← not_le] at hiI'
  rcases Finset.not_subset.mp (mt Finset.card_le_card hiI') with ⟨t, htj, hti⟩
  simp only [Finset.mem_filter, Finset.mem_range] at htj hti
  simp only [htj.2, and_true, not_lt, tsub_le_iff_right] at hti
  refine ⟨t, Finset.mem_Ico.mpr ⟨?_, htj.1⟩, htj.2.symm⟩
  by_contra
  have hti' : t = i - 1 := by lia
  subst hti'
  exact hc.not_small_of_big (hc.apply_sub_one_big_of_apply_small_of_N'_lt his (by lia)) (htj.2 ▸
    (hc.apply_sub_two_small_of_apply_small_of_N'_lt his (by lia)))

variable (a)

/-- The indices, minus `n`, of small numbers appearing for the second or subsequent time at or
after `a n`. -/
def pSet (n : ℕ) : Set ℕ := {t | ∃ i ∈ Finset.Ico n (n + t), Small a (a i) ∧ a (n + t) = a i}

/-- The index, minus `n`, of the second appearance of the first small number to appear twice at
or after `a n`. This is only used for small `a n` with `N' a N + 2 < n`. -/
noncomputable def p (n : ℕ) : ℕ := sInf (pSet a n)

variable {a}

/--
@isnad1 id=nonempty.1h3v.s4.da56435b9fab from=translated src=- shape=a5f1461f vocab=512f3d1f
-/
lemma nonempty_pSet (n : ℕ) : (pSet a n).Nonempty := by
  rcases hc.infinite_setOf_apply_eq_one.exists_gt n with ⟨i, hi1, hni⟩
  rcases hc.infinite_setOf_apply_eq_one.exists_gt i with ⟨j, hj1, hij⟩
  refine ⟨j - n, ?_⟩
  simp only [pSet, Finset.mem_Ico, Set.mem_ofPred_eq]
  exact ⟨i, ⟨hni.le, by lia⟩, hi1 ▸ ⟨hc.small_one, hj1 ▸ (by congr; lia)⟩⟩

/--
@isnad1 id=ex.1h3v.s6.79fb86fe660e from=translated src=- shape=a7b72452 vocab=c3fd2b16
-/
lemma exists_mem_Ico_small_and_apply_add_p_eq (n : ℕ) :
    ∃ i ∈ Finset.Ico n (n + p a n), Small a (a i) ∧ a (n + p a n) = a i :=
  csInf_mem (hc.nonempty_pSet _)

/--
@isnad1 id=lt.1h3v.s4.5275be5ef55a from=translated src=- shape=c383f3db vocab=8c241e58
-/
lemma p_pos (n : ℕ) : 0 < p a n := by
  by_contra! h
  have hn := hc.exists_mem_Ico_small_and_apply_add_p_eq n
  simp [h] at hn

/--
@isnad1 id=le.2h4v.s5.cd13f462780b from=translated src=- shape=131f38fd vocab=7396a501
-/
lemma card_filter_apply_eq_Ico_add_p_le_one (n : ℕ) {j : ℕ} (hjs : Small a j) :
    #{i ∈ Finset.Ico n (n + p a n) | a i = j} ≤ 1 := by
  have h : IsLeast (pSet a n) (p a n) := isLeast_csInf (hc.nonempty_pSet n)
  simp only [IsLeast, pSet, Set.mem_ofPred_eq, mem_lowerBounds, forall_exists_index, and_imp,
    Finset.mem_Ico] at h
  rw [Finset.card_le_one_iff]
  intro x y hx hy
  simp only [Finset.mem_filter, Finset.mem_Ico] at hx hy
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · replace h := h.2 (y - n) x hx.1.1 (by lia) (hx.2 ▸ hjs)
    have hny : n + (y - n) = y := by lia
    rw [hny, hy.2, hx.2] at h
    exact absurd (h rfl) (by lia)
  · rfl
  · replace h := h.2 (x - n) y hy.1.1 (by lia) (hy.2 ▸ hjs)
    have hnx : n + (x - n) = x := by lia
    rw [hnx, hx.2, hy.2] at h
    exact absurd (h rfl) (by lia)

/--
@isnad1 id=eq.3h3v.s5.ba0336f0a4b5 from=translated src=- shape=1b2c0faa vocab=bbe83a80
-/
lemma apply_add_p_eq {n : ℕ} (hn : N' a N + 2 < n) (hs : Small a (a n)) : a (n + p a n) = a n := by
  rcases hc.exists_mem_Ico_small_and_apply_add_p_eq n with ⟨i, hiIco, his, hin⟩
  suffices i = n by rw [hin, this]
  simp only [Finset.mem_Ico] at hiIco
  by_contra hin'
  have hf (t : ℕ) (hts : Small a t) : #{x ∈ Finset.Ico i (n + p a n) | a x = t} ≤ 1 :=
    calc #{x ∈ Finset.Ico i (n + p a n) | a x = t} ≤ #{x ∈ Finset.Ico n (n + p a n) | a x = t} :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Ico_subset_Ico hiIco.1 le_rfl))
      _ ≤ 1 := hc.card_filter_apply_eq_Ico_add_p_le_one _ hts
  obtain ⟨t, hti, hi2t⟩ := hc.exists_apply_sub_two_eq_of_apply_eq (j := n + p a n) (by lia)
    (by lia) his hin.symm hf
  have h1 := hc.card_filter_apply_eq_Ico_add_p_le_one n
    (hi2t ▸ hc.apply_sub_two_small_of_apply_small_of_N'_lt his (by lia))
  revert h1
  simp only [imp_false, not_le, Finset.one_lt_card_iff, Finset.mem_filter, Finset.mem_Ico, ne_eq,
    exists_and_left]
  simp only [Finset.mem_Ico] at hti
  refine ⟨i - 2, ⟨⟨?_, by lia⟩, hi2t⟩, t, by lia⟩
  by_contra hi2
  have hi1 : n = i - 1 := by lia
  subst hi1
  exact hc.not_small_of_big (hc.apply_sub_one_big_of_apply_small_of_N'_lt his (by lia)) hs

/--
@isnad1 id=even.3h3v.s5.d3fc636a9760 from=translated src=- shape=41518c92 vocab=3bdd795b
-/
lemma even_p {n : ℕ} (hn : N' a N + 2 < n) (hs : Small a (a n)) : Even (p a n) := by
  have hna : n = N' a N + (n - (N' a N)) := by lia
  have hs' := hc.apply_add_p_eq hn hs ▸ hs
  rw [hna, hc.small_apply_N'_add_iff_even] at hs
  nth_rw 1 [hna] at hs'
  rw [add_assoc, hc.small_apply_N'_add_iff_even] at hs'
  simpa [Nat.even_add, hs] using hs'

/--
@isnad1 id=le.3h3v.s5.81f40a028ed4 from=translated src=- shape=b363b812 vocab=8b5c59c6
-/
lemma p_le_two_mul_k {n : ℕ} (hn : N' a N + 2 < n) (hs : Small a (a n)) : p a n ≤ 2 * k a := by
  by_contra hlt
  obtain ⟨x, hx, y, hy, hxyne, hxy⟩ : ∃ x ∈ Finset.range (k a + 1), ∃ y ∈ Finset.range (k a + 1),
      x ≠ y ∧ a (n + 2 * x) = a (n + 2 * y) := by
    convert Finset.exists_ne_map_eq_of_card_lt_of_maps_to (t := Finset.Icc 1 (k a)) ?_ ?_
    · simp
    · rintro i -
      simp only [Finset.coe_Icc, Set.mem_Icc]
      rw [← Small, hc.small_apply_add_two_mul_iff_small i (by lia)]
      simp [hs, hc.one_le_apply]
  have hs' : Small a (a (n + 2 * x)) := by rwa [hc.small_apply_add_two_mul_iff_small x (by lia)]
  have hj := hc.card_filter_apply_eq_Ico_add_p_le_one n hs'
  revert hj
  simp only [imp_false, not_le, Finset.one_lt_card_iff, Finset.mem_filter, Finset.mem_Ico, ne_eq,
    exists_and_left]
  simp only [Finset.mem_range] at hx hy
  exact ⟨n + 2 * x, by lia, n + 2 * y, by lia⟩

/--
@isnad1 id=le.3h3v.s5.f829180c0ced from=translated src=- shape=7694ef2a vocab=7c96a97c
-/
lemma p_apply_sub_two_le_p_apply {n : ℕ} (hn : N' a N + 4 < n) (hs : Small a (a n)) :
    p a (n - 2) ≤ p a n := by
  obtain ⟨t, hti, _⟩ := hc.exists_apply_sub_two_eq_of_apply_eq (j := n + p a n) (by lia)
    ((lt_add_iff_pos_right n).mpr (hc.p_pos n)) hs
    (hc.apply_add_p_eq (by lia) hs).symm (fun _ ↦ hc.card_filter_apply_eq_Ico_add_p_le_one _)
  by_contra
  have hn2 := (hc.apply_sub_two_small_of_apply_small_of_N'_lt hs (by lia))
  have : p a n ≤ p a (n - 2) - 2 := by
    obtain ⟨_, _⟩ := hc.even_p (by lia) hs
    obtain ⟨_, _⟩ := hc.even_p (by lia) hn2
    lia
  have h := hc.card_filter_apply_eq_Ico_add_p_le_one (n - 2) hn2
  revert h
  simp only [imp_false, not_le, Finset.one_lt_card_iff, Finset.mem_filter, Finset.mem_Ico,
    ne_eq, exists_and_left]
  simp only [Finset.mem_Ico] at hti
  exact ⟨n - 2, ⟨⟨le_rfl, by lia⟩, rfl⟩, t, by lia⟩

/--
@isnad1 id=le.3h3v.s5.3e4568e40c5e from=translated src=- shape=2a87038f vocab=2ccfa262
-/
lemma p_apply_le_p_apply_add_two {n : ℕ} (hn : N' a N + 2 < n) (hs : Small a (a n)) :
    p a n ≤ p a (n + 2) :=
  hc.p_apply_sub_two_le_p_apply (n := n + 2) (by lia)
    (hc.apply_add_two_small_of_apply_small_of_N'_le hs (by lia))

variable (a N)

/--
@isnad1 id=ex.1h2v.s5.2f61a8fc9051 from=translated src=- shape=b046d900 vocab=4af1348c
-/
lemma exists_p_eq : ∃ b c, ∀ n, b < n → p a (N' a N + 2 * n) = c := by
  let c : ℕ := sSup (Set.range (fun i ↦ p a (N' a N + 2 * (2 + i))))
  have hk : 2 * k a ∈ upperBounds (Set.range (fun i ↦ p a (N' a N + 2 * (2 + i)))) := by
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact fun i ↦ hc.p_le_two_mul_k (by lia) (hc.small_apply_N'_add_iff_even.mpr (by simp))
  have hlec : ∀ j ∈ Set.range (fun i ↦ p a (N' a N + 2 * (2 + i))), j ≤ c :=
    fun _ hj ↦ le_csSup ⟨_, hk⟩ hj
  obtain ⟨t, ht⟩ := Set.Nonempty.csSup_mem (Set.range_nonempty _) (BddAbove.finite ⟨2 * k a, hk⟩)
  have heqc (u : ℕ) : p a (N' a N + 2 * (2 + t + u)) = c := by
    induction u with
    | zero => simpa using ht
    | succ u ih =>
      refine le_antisymm ?_ (ih ▸ ?_)
      · simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hlec
        exact add_assoc _ _ (u + 1) ▸ hlec (t + (u + 1))
      · have hs : Small a (a (N' a N + 2 * (2 + t + u))) := by
          rw [hc.small_apply_N'_add_iff_even]
          simp
        convert! hc.p_apply_le_p_apply_add_two (by lia) hs using 1
  refine ⟨1 + t, c, fun n hn ↦ ?_⟩
  rw [show n = 2 + t + (n - (2 + t)) by lia]
  exact heqc _

/--
@isnad1 id=ex.1h2v.s6.b440d430e974 from=translated src=- shape=0e1e9cbb vocab=50d4a940
-/
lemma exists_a_apply_add_eq : ∃ b c, 0 < c ∧ ∀ n, b < n →
    a (N' a N + 2 * n + 2 * c) = a (N' a N + 2 * n) := by
  obtain ⟨b, c', hbc'⟩ := hc.exists_p_eq a N
  have hs (n : ℕ) : Small a (a (N' a N + 2 * n)) := hc.small_apply_N'_add_iff_even.mpr (by simp)
  refine ⟨b + 2, c' / 2, ?_, fun n hbn ↦ hbc' n (by lia) ▸ ?_⟩
  · have := hbc' (b + 2) (by lia)
    have := hc.p_pos (N' a N + 2 * (b + 2))
    rcases hc.even_p (by lia) (hs (b + 2)) with ⟨_, _⟩
    lia
  · convert hc.apply_add_p_eq (by lia) (hs n) using 3
    rcases hc.even_p (by lia) (hs n) with ⟨_, ht⟩
    simp [ht, ← two_mul]

variable {a N}

end Condition

end Imo2024P3
