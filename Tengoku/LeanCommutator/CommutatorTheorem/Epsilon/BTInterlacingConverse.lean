import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTInterlacing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite converse infrastructure for common interlacing

Fell's converse says that a finite family of same-degree real-rooted
polynomials has a common interlacer when all its convex combinations are
real-rooted.  The analytic two-polynomial implication is the difficult core.

This file first closes the finite Helly step: pairwise common interlacing is
already enough for a single interlacer for the whole finite family.  The proof
is constructive.  At each root gap it takes the largest lower endpoint among
the family; pairwise common interlacing says that this endpoint lies below
every upper endpoint.  We first prove the statement for sorted root lists and
then package it for polynomials.
-/

open scoped BigOperators Polynomial

namespace CommutatorTheorem.BTInterlacingConverse

open Polynomial
open CommutatorTheorem

/-! ## Finite maximizers -/

/-- A selected point at which a real-valued function on a nonempty finset is
maximal.-/
noncomputable def maximizingIndex {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) : ι :=
  Classical.choose (Finset.exists_max_image s f hs)

theorem maximizingIndex_mem {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) :
    maximizingIndex s hs f ∈ s :=
  (Classical.choose_spec (Finset.exists_max_image s f hs)).1

theorem le_maximizingIndex {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ)
    {i : ι} (hi : i ∈ s) :
    f i ≤ f (maximizingIndex s hs f) :=
  (Classical.choose_spec (Finset.exists_max_image s f hs)).2 i hi

/-! ## The interval-Helly step for root lists -/

/-- The `k`-th entry of an equal-length family of lists.-/
noncomputable def listEntry {ι : Type*} (upper : ι → List ℝ)
    (d : ℕ) (hlen : ∀ i, (upper i).length = d)
    (i : ι) (k : Fin d) : ℝ :=
  (upper i).get ⟨k, by simp [hlen i]⟩

@[simp] theorem listEntry_eq_get {ι : Type*} (upper : ι → List ℝ)
    (d : ℕ) (hlen : ∀ i, (upper i).length = d)
    (i : ι) (k : Fin d) :
    listEntry upper d hlen i k =
      (upper i).get ⟨k, by simp [hlen i]⟩ := rfl

/-- At gap `k`, choose a member whose lower endpoint is largest.-/
noncomputable def gapMaximizer {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (upper : ι → List ℝ)
    (d : ℕ) (hlen : ∀ i, (upper i).length = d)
    (k : Fin (d - 1)) : ι :=
  maximizingIndex s hs (fun i ↦
    listEntry upper d hlen i ⟨k, by omega⟩)

/-- The candidate common interlacer list: largest lower endpoint in every
root gap.-/
noncomputable def commonGapList {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (upper : ι → List ℝ)
    (d : ℕ) (hlen : ∀ i, (upper i).length = d) : List ℝ :=
  List.ofFn (fun k : Fin (d - 1) ↦
    listEntry upper d hlen (gapMaximizer s hs upper d hlen k)
      ⟨k, by omega⟩)

@[simp] theorem commonGapList_length {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (upper : ι → List ℝ)
    (d : ℕ) (hlen : ∀ i, (upper i).length = d) :
    (commonGapList s hs upper d hlen).length = d - 1 := by
  simp [commonGapList]

/-- Pairwise interlacing supplies the cross-gap inequality: the lower
endpoint from any member is below the upper endpoint from any other member.-/
theorem cross_gap_le_of_pairwise_listsInterlace
    {ι : Type*}
    {s : Finset ι} {upper : ι → List ℝ} {d : ℕ}
    (hlen : ∀ i ∈ s, (upper i).length = d)
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      ∃ lower : List ℝ,
        ListsInterlace lower (upper i) ∧ ListsInterlace lower (upper j))
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (k : ℕ) (hk : k + 1 < d) :
    (upper i).get ⟨k, by rw [hlen i hi]; omega⟩ ≤
      (upper j).get ⟨k + 1, by rw [hlen j hj]; omega⟩ := by
  obtain ⟨lower, hil, hjl⟩ := hpair i hi j hj
  obtain ⟨hilen, hiEntries⟩ := hil
  obtain ⟨hjlen, hjEntries⟩ := hjl
  have hlower : lower.length = d - 1 := by
    rw [hlen i hi] at hilen
    omega
  have hkLower : k < lower.length := by omega
  exact (hiEntries k hkLower).1.trans (hjEntries k hkLower).2

/-! ## Pairwise common interlacing implies finite common interlacing -/

/-! ## The degree-one Fell base case -/

/-- Every finite family of monic real-rooted linear polynomials has the
constant polynomial `1` as a common interlacer.-/
theorem hasCommonInterlacer_of_natDegree_one
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ[X])
    (hmonic : ∀ i ∈ s, (p i).Monic)
    (hsplits : ∀ i ∈ s, RealRooted (p i))
    (hdegree : ∀ i ∈ s, (p i).natDegree = 1) :
    HasCommonInterlacer s p := by
  refine ⟨1, ?_⟩
  intro i hi
  have hp0 : p i ≠ 0 := (hmonic i hi).ne_zero
  have hrootsLen : ((p i).roots.sort (· ≤ ·)).length = 1 := by
    calc
      ((p i).roots.sort (· ≤ ·)).length = (p i).roots.card := by simp
      _ = (p i).natDegree := (hsplits i hi).natDegree_eq_card_roots.symm
      _ = 1 := hdegree i hi
  refine ⟨one_ne_zero, hp0, monic_one, hmonic i hi,
    Splits.one, hsplits i hi, ?_⟩
  have honeRoots : ((1 : ℝ[X]).roots.sort (· ≤ ·)) = [] := by simp
  rw [honeRoots]
  refine ⟨by simpa using hrootsLen, ?_⟩
  intro k hk
  simp at hk

/-- In particular, the analytic pair Fell converse is completely settled in
degree one.-/
theorem pair_fell_natDegree_one
    (p q : ℝ[X])
    (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpsplits : RealRooted p) (hqsplits : RealRooted q)
    (hpdegree : p.natDegree = 1) (hqdegree : q.natDegree = 1)
    (_hall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p + (1 - t) • q)) :
    HasCommonInterlacer ({false, true} : Finset Bool)
      (fun b ↦ if b then p else q) := by
  apply hasCommonInterlacer_of_natDegree_one
  · intro b hb
    cases b <;> simp [hpmonic, hqmonic]
  · intro b hb
    cases b <;> simp [hpsplits, hqsplits]
  · intro b hb
    cases b <;> simp [hpdegree, hqdegree]

end CommutatorTheorem.BTInterlacingConverse
