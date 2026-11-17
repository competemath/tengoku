import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Algebra.InfiniteRamsey
import Tengoku.Seed.Data.Finset.Sort
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Order-pattern homogeneity

A finite coloring of `N`-tuples of natural numbers is constant on each order pattern
after restriction to some infinite subset of `ℕ` (Lemma B.10). The proof colors each
`N`-element set by the colors of all tuples drawn from it and applies the infinite
Ramsey theorem.
-/

namespace OrderPattern

/-- Two tuples have the same order pattern when all strict-order and equality
comparisons between their coordinates agree.-/
def sameOrderPattern {N : ℕ} (z z' : Fin N → ℕ) : Prop :=
  ∀ i j, (z i < z j ↔ z' i < z' j) ∧ (z i = z j ↔ z' i = z' j)

/-- The distinct coordinate values of a tuple.-/
def tupleValues {N : ℕ} (z : Fin N → ℕ) : Finset ℕ := Finset.univ.image z

/--
@isnad1 id=mem.0h3v.s4.733000696a98 from=translated src=- shape=d8126424 vocab=29403fc7
-/
theorem mem_tupleValues {N : ℕ} (z : Fin N → ℕ) (i : Fin N) :
    z i ∈ tupleValues z := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- The inverse increasing enumeration counts the elements strictly below its argument.
@isnad1 id=eq.2h3v.s8.726e36d2a759 from=translated src=- shape=aa9eaf6e vocab=3bfaf114
-/
theorem orderIsoOfFin_symm_val {s : Finset ℕ} {N : ℕ} (hs : s.card = N)
    (x : ℕ) (hx : x ∈ s) :
    ((s.orderIsoOfFin hs).symm ⟨x, hx⟩).val = (s.filter (· < x)).card := by
  classical
  let e := s.orderIsoOfFin hs
  let j := e.symm ⟨x, hx⟩
  have hcard : (s.filter (· < x)).card = (Finset.range j.val).card := by
    apply Finset.card_bij (fun y hy => (e.symm ⟨y, (Finset.mem_filter.mp hy).1⟩).val)
    · intro y hy
      apply Finset.mem_range.mpr
      change e.symm ⟨y, (Finset.mem_filter.mp hy).1⟩ < e.symm ⟨x, hx⟩
      exact e.symm.strictMono (Finset.mem_filter.mp hy).2
    · intro y hy y' hy' heq
      have hfin : e.symm ⟨y, (Finset.mem_filter.mp hy).1⟩ =
          e.symm ⟨y', (Finset.mem_filter.mp hy').1⟩ := Fin.ext heq
      exact congrArg Subtype.val (e.symm.injective hfin)
    · intro l hl
      have hlj : l < j.val := Finset.mem_range.mp hl
      let l' : Fin N := ⟨l, lt_trans hlj j.isLt⟩
      have he : (e l' : ℕ) < x := by
        have h := e.strictMono (show l' < j from hlj)
        change (e l' : ℕ) < (e j : ℕ) at h
        simpa only [j, e.apply_symm_apply] using h
      refine ⟨e l', Finset.mem_filter.mpr ⟨(e l').property, he⟩, ?_⟩
      simp [l']
  simpa only [Finset.card_range] using hcard.symm

/-- Equal order patterns give equal numbers of distinct values below each coordinate.
@isnad1 id=eq.1h4v.s6.5c79ea9fc823 from=translated src=- shape=b42d05de vocab=f5ddf8ae
-/
theorem card_values_below_eq {N : ℕ} {z z' : Fin N → ℕ}
    (h : sameOrderPattern z z') (i : Fin N) :
    ((tupleValues z).filter (· < z i)).card =
      ((tupleValues z').filter (· < z' i)).card := by
  classical
  have hpick : ∀ x ∈ tupleValues z, ∃ j : Fin N, z j = x := by
    intro x hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
    exact ⟨j, hj⟩
  choose pick hpick using hpick
  apply Finset.card_bij
    (fun x hx => z' (pick x (Finset.mem_filter.mp hx).1))
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨mem_tupleValues z' _, ?_⟩
    exact (h _ i).1.mp (by simpa only [hpick] using hx'.2)
  · intro x hx y hy heq
    have hxy := (h (pick x (Finset.mem_filter.mp hx).1)
      (pick y (Finset.mem_filter.mp hy).1)).2.mpr heq
    simpa only [hpick] using hxy
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy'.1
    have hx : z j ∈ (tupleValues z).filter (· < z i) := by
      refine Finset.mem_filter.mpr ⟨mem_tupleValues z j, ?_⟩
      exact (h j i).1.mpr (by simpa only [hj] using hy'.2)
    refine ⟨z j, hx, ?_⟩
    exact ((h _ j).2.mp (hpick (z j) (Finset.mem_filter.mp hx).1)).trans hj

/-- Pad the distinct values of a tuple to an `N`-element subset of `H` using points above all
of them.
@isnad1 id=ex.2h3v.s6.bc1920f5e95a from=translated src=- shape=66a95fba vocab=4ce572ad
-/
theorem exists_padded_finset {N : ℕ} (H : Set ℕ) (hH : H.Infinite)
    (z : Fin N → ℕ) (hz : ∀ i, z i ∈ H) :
    ∃ s : Finset ℕ, (↑s : Set ℕ) ⊆ H ∧ s.card = N ∧
      (∀ i, z i ∈ s) ∧
      ∀ i, s.filter (· < z i) = (tupleValues z).filter (· < z i) := by
  classical
  let v := tupleValues z
  have hv : v.card ≤ N := by
    calc v.card ≤ Finset.univ.card := Finset.card_image_le
         _ = N := Finset.card_fin N
  have hvH : (↑v : Set ℕ) ⊆ H := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hz i
  let M := v.sup id
  have hvM : ∀ x ∈ v, x ≤ M := fun x hx => Finset.le_sup (f := id) hx
  have htail : (H \ (Finset.range (M + 1) : Set ℕ)).Infinite :=
    hH.sdiff (Finset.finite_toSet _)
  obtain ⟨t, ht, htcard⟩ := htail.exists_subset_card_eq (N - v.card)
  have htM : ∀ x ∈ t, M < x := by
    intro x hx
    have hxnot := (ht hx).2
    simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hxnot
    omega
  have hdisj : Disjoint v t := by
    apply Finset.disjoint_left.mpr
    intro x hxv hxt
    exact (not_lt_of_ge (hvM x hxv)) (htM x hxt)
  refine ⟨v ∪ t, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hvH hx
    · exact (ht hx).1
  · rw [Finset.card_union_of_disjoint hdisj, htcard]
    omega
  · intro i
    exact Finset.mem_union_left t (mem_tupleValues z i)
  · intro i
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hxv | hxt, hxi⟩
      · exact ⟨hxv, hxi⟩
      · have hiM := hvM (z i) (mem_tupleValues z i)
        have hxM := htM x hxt
        omega
    · rintro ⟨hx, hxi⟩
      exact ⟨Or.inl hx, hxi⟩

/-- A finite coloring of tuples is constant on each order pattern on some infinite set.
@isnad1 id=ex.0h3v.s6.1f32e21941a1 from=translated src=- shape=00158405 vocab=e8924515
-/
theorem exists_infinite_order_homogeneous {C : Type*} [Finite C] (N : ℕ)
    (T : (Fin N → ℕ) → C) :
    ∃ H : Set ℕ, H.Infinite ∧
      ∀ z z' : Fin N → ℕ, (∀ i, z i ∈ H) → (∀ i, z' i ∈ H) →
        sameOrderPattern z z' → T z = T z' := by
  classical
  let color : Finset ℕ → ((Fin N → Fin N) → C) := fun s =>
    if hs : s.card = N then fun β => T (fun i => s.orderEmbOfFin hs (β i))
    else fun _ => T (fun _ => 0)
  obtain ⟨H, hH, c, hc⟩ := InfiniteRamsey.exists_infinite_homogeneous N color
  refine ⟨H, hH, ?_⟩
  intro z z' hz hz' hpat
  obtain ⟨s, hsH, hs, hsz, hfilter⟩ := exists_padded_finset H hH z hz
  obtain ⟨s', hsH', hs', hsz', hfilter'⟩ := exists_padded_finset H hH z' hz'
  let β : Fin N → Fin N := fun i => (s.orderIsoOfFin hs).symm ⟨z i, hsz i⟩
  let β' : Fin N → Fin N := fun i => (s'.orderIsoOfFin hs').symm ⟨z' i, hsz' i⟩
  have hβ : β = β' := by
    funext i
    apply Fin.ext
    change ((s.orderIsoOfFin hs).symm ⟨z i, hsz i⟩).val =
      ((s'.orderIsoOfFin hs').symm ⟨z' i, hsz' i⟩).val
    rw [orderIsoOfFin_symm_val hs, orderIsoOfFin_symm_val hs', hfilter, hfilter']
    exact card_values_below_eq hpat i
  have hzrepr : (fun i => s.orderEmbOfFin hs (β i)) = z := by
    funext i
    exact congrArg Subtype.val ((s.orderIsoOfFin hs).apply_symm_apply ⟨z i, hsz i⟩)
  have hzrepr' : (fun i => s'.orderEmbOfFin hs' (β' i)) = z' := by
    funext i
    exact congrArg Subtype.val ((s'.orderIsoOfFin hs').apply_symm_apply ⟨z' i, hsz' i⟩)
  have hsame : color s β = color s' β' := by
    rw [hc s hsH hs, hc s' hsH' hs', hβ]
  simpa only [color, dite_eq_left hs, dite_eq_left hs', hzrepr, hzrepr'] using hsame

end OrderPattern
