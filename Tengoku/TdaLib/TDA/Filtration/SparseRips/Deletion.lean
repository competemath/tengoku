import Tengoku.TdaLib.TDA.Filtration.SparseRips.GreedyNet
import Tengoku.TdaLib.TDA.Filtration.SparseRips.Weight

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometric deletion maps for greedy sparse Rips complexes

Deletion time is the insertion radius divided by `η * (1 - 2 * η)`. The initial
vertex survives forever. A vertex deleted at scale `r` is sent to the greedy net
at threshold `η * r`, whose points have zero weight and survive strictly past `r`.
Active vertices are fixed. This gives the domination inequality used by simplicial
contiguity without assuming a net tree or a topological equivalence.
-/

namespace TDA.Filtration.SparseRips

open GreedyNet

noncomputable section

variable {V : Type*} [MetricSpace V] [Fintype V]

/-- Finite deletion times, with `none` for the initial vertex.-/
def deletionTime (seed : V) (η : ℝ) (x : V) : Option ℝ :=
  (insertionRadius seed x).map (fun ρ => ρ / (η * (1 - 2 * η)))

/-- The open active set uses a strict inequality at deletion-time ties.-/
def OpenActive (time : Option ℝ) (r : ℝ) : Prop :=
  time.elim True (fun t => r < t)

/-- The closed active set retains a vertex at its deletion time.-/
def ClosedActive (time : Option ℝ) (r : ℝ) : Prop :=
  time.elim True (fun t => r ≤ t)

/--
@isnad1 id=eq.0h3v.s4.235db173b5c1 from=translated src=- shape=5ee8af76 vocab=89364a3b
-/
@[simp] theorem deletionTime_seed (seed : V) (η : ℝ) : deletionTime seed η seed = none := by
  simp [deletionTime]

/--
@isnad1 id=openacti.0h1v.s2.c14360fd5d11 from=translated src=- shape=1bfdc32f vocab=81c7674a
-/
@[simp] theorem openActive_none (r : ℝ) : OpenActive none r := trivial

/--
@isnad1 id=closedac.0h1v.s2.dde803552a8c from=translated src=- shape=1bfdc32f vocab=38d6fabf
-/
@[simp] theorem closedActive_none (r : ℝ) : ClosedActive none r := trivial

/--
@isnad1 id=eq.1h4v.s6.f91b2c7bf083 from=translated src=- shape=351153eb vocab=d01a0a1b
-/
theorem deletionTime_of_ne (seed : V) (η : ℝ) {x : V} (hx : x ≠ seed) :
    deletionTime seed η x = some
      (radius seed (insertionIndex seed x - 1) / (η * (1 - 2 * η))) := by
  simp [deletionTime, insertionRadius, (insertionIndex_eq_zero_iff seed x).not.mpr hx]

private theorem parameter_pos {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3) :
    0 < η * (1 - 2 * η) := mul_pos hη (by linarith)

/--
@isnad1 id=le.3h5v.s6.e40944e50a38 from=translated src=- shape=00762bb9 vocab=132408ee
-/
theorem deletionTime_nonneg (seed : V) {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3)
    (x : V) : ∀ t ∈ deletionTime seed η x, 0 ≤ t := by
  intro t ht
  by_cases hx : x = seed
  · simp [hx] at ht
  · rw [deletionTime_of_ne seed η hx] at ht
    have heq : t = radius seed (insertionIndex seed x - 1) / (η * (1 - 2 * η)) := by
      simpa [eq_comm] using ht
    rw [heq]
    exact div_nonneg (radius_nonneg seed _) (parameter_pos hη hη').le

/-- The geometric witness lies beyond the deletion boundary and has weight zero.
@isnad1 id=other.3h5v.s6.e3ad0ff73f58 from=translated src=- shape=af34ec82 vocab=0e412374
-/
theorem netPoint_active_weight_zero (seed : V) {η r : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (x : V) :
    let q := netPoint seed (η * r) (mul_nonneg hη.le hr) x
    OpenActive (deletionTime seed η q) r ∧ weight η (deletionTime seed η q) r = 0 := by
  dsimp only
  let q := netPoint seed (η * r) (mul_nonneg hη.le hr) x
  change OpenActive (deletionTime seed η q) r ∧ weight η (deletionTime seed η q) r = 0
  have hq := (mem_threshold_iff seed q (η * r) (mul_nonneg hη.le hr)).mp
    (netPoint_mem seed (η * r) (mul_nonneg hη.le hr) x)
  rcases hq with hq | hq
  · rw [hq, deletionTime_seed]
    simp [OpenActive]
  · by_cases hqs : q = seed
    · rw [hqs, deletionTime_seed]
      simp [OpenActive]
    · rw [deletionTime_of_ne seed η hqs]
      simp only [OpenActive, Option.elim_some, weight_some]
      have hp := parameter_pos hη hη'
      have hfactor : 0 < 1 - 2 * η := by linarith
      have hηr := mul_nonneg hη.le hr
      have htime : r < radius seed (insertionIndex seed q - 1) / (η * (1 - 2 * η)) := by
        apply (lt_div_iff₀ hp).mpr
        have hprod := mul_nonneg hη.le hηr
        have hbound : η * (1 - 2 * η) * r ≤ η * r := by nlinarith
        nlinarith
      refine ⟨htime, finiteWeight_of_le ?_⟩
      have hcancel : (1 - 2 * η) *
          (radius seed (insertionIndex seed q - 1) / (η * (1 - 2 * η))) =
          radius seed (insertionIndex seed q - 1) / η := by
        field_simp [ne_of_gt hη, ne_of_gt hfactor]
      rw [hcancel]
      exact (le_div_iff₀ hη).mpr (by nlinarith)

/-- Fix active vertices and send removed vertices to the proved greedy covering net.-/
def deletionMap (seed : V) (η r : ℝ) (hη : 0 ≤ η) (hr : 0 ≤ r) (x : V) : V := by
  classical
  exact if OpenActive (deletionTime seed η x) r then x
    else netPoint seed (η * r) (mul_nonneg hη hr) x

/--
@isnad1 id=eq.3h5v.s5.a0a278693984 from=translated src=- shape=7f18009c vocab=6efb95d0
-/
@[simp] theorem deletionMap_of_active (seed : V) {η r : ℝ} (hη : 0 ≤ η) (hr : 0 ≤ r)
    {x : V} (hx : OpenActive (deletionTime seed η x) r) :
    deletionMap seed η r hη hr x = x := by
  simp [deletionMap, hx]

/--
@isnad1 id=openacti.3h5v.s6.1ac138e488f4 from=translated src=- shape=7812b499 vocab=a6f753b0
-/
theorem deletionMap_active (seed : V) {η r : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (x : V) :
    OpenActive (deletionTime seed η (deletionMap seed η r hη.le hr x)) r := by
  classical
  by_cases hx : OpenActive (deletionTime seed η x) r
  · simp [deletionMap, hx]
  · simpa [deletionMap, hx] using (netPoint_active_weight_zero seed hη hη' hr x).1

/-- The deletion projection satisfies the precise weighted domination inequality.
@isnad1 id=le.3h5v.s6.bc82ad462b4c from=translated src=- shape=077da3ca vocab=934ca0b1
-/
theorem deletionMap_domination (seed : V) {η r : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (x : V) :
    dist x (deletionMap seed η r hη.le hr x) ≤
      weight η (deletionTime seed η x) r -
        weight η (deletionTime seed η (deletionMap seed η r hη.le hr x)) r := by
  classical
  by_cases hx : OpenActive (deletionTime seed η x) r
  · simp [deletionMap, hx]
  · have hxs : x ≠ seed := by
      intro h
      apply hx
      simp [h]
    have htime := deletionTime_of_ne seed η hxs
    have hfinite : 0 ≤ radius seed (insertionIndex seed x - 1) / (η * (1 - 2 * η)) :=
      div_nonneg (radius_nonneg seed _) (parameter_pos hη hη').le
    have hremoved : radius seed (insertionIndex seed x - 1) / (η * (1 - 2 * η)) ≤ r := by
      simpa [htime, OpenActive] using hx
    have hw : weight η (deletionTime seed η x) r = η * r := by
      rw [htime, weight_some]
      exact finiteWeight_of_time_le hη.le hfinite hremoved
    simp only [deletionMap, ite_eq_right hx, hw]
    rw [(netPoint_active_weight_zero seed hη hη' hr x).2, sub_zero]
    exact dist_netPoint_le seed (η * r) (mul_nonneg hη.le hr) x

end

end TDA.Filtration.SparseRips
