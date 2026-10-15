/-
Copyright (c) 2026 Dirk Kunert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dirk Kunert
-/
module

public import Tengoku

/-!
# The Three-Gap (Steinhaus) theorem

A self-contained Lean 4 / Mathlib formalization of the three-gap theorem,
depending only on Mathlib.  It works in `[0,1)` through `Int.fract` (NOT
`AddCircle`), via the first-return (Slater / van Ravenstein) route.

## Status

**Complete and machine-checked** — `three_gap_card_le_three` (for every `a : ℝ`
and `N : ℕ`, the `N`-point orbit `{i·a mod 1 : i < N}` partitions `[0,1)` into at
most three distinct gap lengths) is proved with no `sorry`, no warnings, and only
the standard axioms `propext / Classical.choice / Quot.sound`.  Uniform in `a`
(rational and irrational alike).

The development, in order:

* `orbit`, `gaps`, `gaps_sum_eq_one` — construction; the gaps sum to `1`;
* `sortedVal` and its order theory (`sortedVal_strictMono`, `_zero`, `_last`, …);
* the two first returns `etaPos = η⁺`, `etaNeg = η⁻`, with minimality;
* `three_gap_card_le_three_of_subset` — the reduction "gap values lie in a
  three-element set `⇒` at most three distinct gap lengths";
* the multiplier layer (`canMul`, `mPlus`, `mMinus`) with the index-shift
  identities (`fract_index_shift`) and the `noPointBetween` lemmas;
* cases A (`gap_eq_etaPos`) and B (`gap_eq_etaNeg`) of the first-return
  classification, with the index-bridge infrastructure;
* the **corner case** `η⁺ + η⁻` (`corner_gap`), via the M-circle (L1/L3) and an
  induction-free closure of L2 — see the "corner case" section below;
* the full classification `neighbour_gap_in_returns` and the bound
  `three_gap_card_le_three`.

## Design

`gaps` enumerates the sorted distinct points through `Finset.orderEmbOfFin`
(`Fin k ↪o ℝ`, `k = (orbit a N).card`), extended to a total `sortedVal : ℕ → ℝ`;
the gaps are the adjacent differences over `Finset.range (k - 1)` plus the
wrap-around `(min + 1) - max`, and `gaps_sum_eq_one` is a `Finset` telescoping sum.

Note on `noncomputable`: on `ℝ`, `DecidableEq` and the order are noncomputable, so
`orbit`, `orbitCard`, `orbitEmb`, `sortedVal`, `gaps`, `canMul`, … are all
`noncomputable`.
-/

@[expose] public section

namespace SteinhausThreeGap

/-- The (finite, distinct) orbit `{ Int.fract (i * a) | i < N }` in `[0,1)`.

    `noncomputable`, since `Finset.image` on `ℝ` uses the (noncomputable)
    `DecidableEq ℝ` instance. -/
noncomputable def orbit (a : ℝ) (N : ℕ) : Finset ℝ :=
  (Finset.range N).image (fun i : ℕ => Int.fract ((i : ℝ) * a))

/-- The orbit is nonempty as soon as there is at least one index, i.e. `0 < N`.
    Ties the hypothesis `0 < N` of `gaps_sum_eq_one` to the orbit.
@isnad1 id=nonempty.1h2v.s4.13e15cdc790c from=translated src=- shape=0f4a3c96 vocab=04b899cd
-/
theorem orbit_nonempty (a : ℝ) {N : ℕ} (hN : 0 < N) : (orbit a N).Nonempty := by
  simp only [orbit, Finset.image_nonempty, Finset.nonempty_range_iff]
  exact hN.ne'

/-- Every orbit point is a fractional part, hence lies in `[0,1)`.
@isnad1 id=le.0h2v.s5.7897b5e94ee4 from=translated src=- shape=5b1deab3 vocab=7b1240cc
-/
theorem orbit_subset_Ico (a : ℝ) (N : ℕ) :
    ↑(orbit a N) ⊆ Set.Ico (0 : ℝ) 1 := by
  intro x hx
  simp only [Finset.mem_coe, orbit, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact Set.mem_Ico.mpr ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The number of distinct orbit points.  `noncomputable`, as it depends on the
    noncomputable `orbit`. -/
noncomputable def orbitCard (a : ℝ) (N : ℕ) : ℕ := (orbit a N).card

/-- The increasing enumeration `Fin k ↪o ℝ` of the distinct orbit points, where
    `k = orbitCard a N`.  Element `i` is the `i`-th smallest point. -/
noncomputable def orbitEmb (a : ℝ) (N : ℕ) :
    Fin (orbitCard a N) ↪o ℝ :=
  (orbit a N).orderEmbOfFin rfl

/-- The sorted distinct orbit points as a *total* index function `ℕ → ℝ`:
    `sortedVal a N i` is the `i`-th smallest point when `i < orbitCard a N`,
    and a junk value `0` otherwise.  Only indices `0, …, orbitCard a N - 1`
    matter; the telescoping below is purely formal in `sortedVal`. -/
noncomputable def sortedVal (a : ℝ) (N : ℕ) (i : ℕ) : ℝ :=
  if h : i < orbitCard a N then orbitEmb a N ⟨i, h⟩ else 0

/-- The multiset of consecutive gaps of the sorted distinct orbit points, plus
    the single wrap-around gap `(min + 1) - max`.

    With `k = orbitCard a N` and `g = sortedVal a N`:
    * the `k - 1` adjacent gaps `g (i+1) - g i`, `i = 0, …, k - 2`, by mapping
      over `Finset.range (k - 1)`;
    * the wrap-around gap `g 0 + 1 - g (k - 1)` (i.e. `min + 1 - max`), added as a
      singleton. -/
noncomputable def gaps (a : ℝ) (N : ℕ) : Multiset ℝ :=
  ((Finset.range (orbitCard a N - 1)).val.map
      (fun i => sortedVal a N (i + 1) - sortedVal a N i)) +
    {sortedVal a N 0 + 1 - sortedVal a N (orbitCard a N - 1)}

/-- **The gaps sum to one.**  Telescoping of the adjacent differences gives
    `max - min`; adding the wrap-around gap `(min + 1) - max` yields `1`.

    The proof is a pure `Finset` telescoping sum (`Finset.sum_range_sub`) followed
    by `ring`.
@isnad1 id=eq.1h2v.s4.ce321b6c13db from=translated src=- shape=0baba646 vocab=54804e7b
-/
theorem gaps_sum_eq_one (a : ℝ) (N : ℕ) (hN : 0 < N) : (gaps a N).sum = 1 := by
  have _hne : (orbit a N).Nonempty := orbit_nonempty a hN
  simp only [gaps, Multiset.sum_add, Multiset.sum_singleton, Finset.sum_map_val]
  rw [Finset.sum_range_sub (sortedVal a N) (orbitCard a N - 1)]
  ring

/-! ## Phase 1 — orbit membership and the sorted enumeration -/

/-- **Membership in the orbit.**  `x` is an orbit point iff it is `Int.fract (i * a)`
    for some index `i < N`.
@isnad1 id=iff.0h3v.s5.df164678d7c1 from=translated src=- shape=2057547a vocab=71b6489a
-/
theorem mem_orbit_iff (a : ℝ) (N : ℕ) (x : ℝ) :
    x ∈ orbit a N ↔ ∃ i, i < N ∧ Int.fract ((i : ℝ) * a) = x := by
  simp only [orbit, Finset.mem_image, Finset.mem_range]

/-- **`0` lies in every nonempty orbit** (index `i = 0` gives `Int.fract 0 = 0`).
@isnad1 id=mem.1h2v.s5.c0f99b42d118 from=translated src=- shape=c0c8c869 vocab=5c3e1b81
-/
theorem zero_mem_orbit (a : ℝ) {N : ℕ} (hN : 0 < N) : (0 : ℝ) ∈ orbit a N := by
  rw [mem_orbit_iff]
  exact ⟨0, hN, by rw [Nat.cast_zero, zero_mul, Int.fract_zero]⟩

/-- **The sorted enumeration is strictly increasing** on the valid index range:
    for `i < j` with `j < orbitCard a N`, `sortedVal a N i < sortedVal a N j`.
@isnad1 id=lt.2h4v.s5.63e86f27839d from=translated src=- shape=a62ccde9 vocab=349295a8
-/
theorem sortedVal_strictMono (a : ℝ) (N : ℕ) {i j : ℕ}
    (hij : i < j) (hj : j < orbitCard a N) :
    sortedVal a N i < sortedVal a N j := by
  have hi : i < orbitCard a N := lt_trans hij hj
  simp only [sortedVal, dite_eq_left hi, dite_eq_left hj]
  exact (orbitEmb a N).strictMono (by simpa using hij)

/-- **The first sorted value is the minimum.**
@isnad1 id=eq.1h2v.s4.64d33d36c137 from=translated src=- shape=be63f0f7 vocab=60476a57
-/
theorem sortedVal_zero (a : ℝ) {N : ℕ} (hN : 0 < N) :
    sortedVal a N 0 = (orbit a N).min' (orbit_nonempty a hN) := by
  have hpos : 0 < orbitCard a N := Finset.card_pos.mpr (orbit_nonempty a hN)
  simp only [sortedVal, dite_eq_left hpos]
  exact Finset.orderEmbOfFin_zero rfl hpos

/-- **The last sorted value is the maximum.**
@isnad1 id=eq.1h2v.s5.dd5414547310 from=translated src=- shape=1ceb1de2 vocab=aad908f4
-/
theorem sortedVal_last (a : ℝ) {N : ℕ} (hN : 0 < N) :
    sortedVal a N (orbitCard a N - 1) = (orbit a N).max' (orbit_nonempty a hN) := by
  have hpos : 0 < orbitCard a N := Finset.card_pos.mpr (orbit_nonempty a hN)
  have hlast : orbitCard a N - 1 < orbitCard a N := Nat.sub_lt hpos Nat.one_pos
  simp only [sortedVal, dite_eq_left hlast]
  exact Finset.orderEmbOfFin_last rfl hpos

/-- **Every sorted value (below the count) is an orbit point.**
@isnad1 id=mem.1h3v.s4.a1ca34a6a606 from=translated src=- shape=04485467 vocab=ec2a6057
-/
theorem sortedVal_mem (a : ℝ) {N : ℕ} {i : ℕ} (h : i < orbitCard a N) :
    sortedVal a N i ∈ orbit a N := by
  simp only [sortedVal, dite_eq_left h]
  exact Finset.orderEmbOfFin_mem (orbit a N) rfl ⟨i, h⟩

/-! ## Phase 2 — gap infrastructure and the distinct-gap-count reduction -/

/-- The `i`-th adjacent gap of the sorted enumeration. -/
noncomputable def gapAt (a : ℝ) (N : ℕ) (i : ℕ) : ℝ :=
  sortedVal a N (i + 1) - sortedVal a N i

/-- `gaps` written through `gapAt` (definitional).
@isnad1 id=eq.0h2v.s6.31729127576d from=translated src=- shape=65b5e00a vocab=072b9ef1
-/
theorem gaps_eq (a : ℝ) (N : ℕ) :
    gaps a N =
      ((Finset.range (orbitCard a N - 1)).val.map (gapAt a N)) +
        {sortedVal a N 0 + 1 - sortedVal a N (orbitCard a N - 1)} := rfl

/-- Internal (non-wrap-around) gaps are positive.
@isnad1 id=lt.1h3v.s5.87fafa9bec26 from=translated src=- shape=9874a929 vocab=d8c2440a
-/
theorem gapAt_pos (a : ℝ) (N : ℕ) {i : ℕ} (h : i + 1 < orbitCard a N) :
    0 < gapAt a N i := by
  unfold gapAt
  exact sub_pos.mpr (sortedVal_strictMono a N (Nat.lt_succ_self i) h)

/-- Membership in `gaps`, unpacked into the internal gaps and the wrap-around gap.
@isnad1 id=iff.0h3v.s6.ef09f4a38c0b from=translated src=- shape=76ec1649 vocab=276bff6f
-/
theorem mem_gaps_iff (a : ℝ) (N : ℕ) (x : ℝ) :
    x ∈ gaps a N ↔
      (∃ i, i < orbitCard a N - 1 ∧ gapAt a N i = x) ∨
      x = sortedVal a N 0 + 1 - sortedVal a N (orbitCard a N - 1) := by
  rw [gaps_eq]
  simp only [Multiset.mem_add, Multiset.mem_map, Finset.range_val,
    Multiset.mem_range, Multiset.mem_singleton]

/-- A loose bound: the number of distinct gap values is at most the number of gaps.
@isnad1 id=le.0h2v.s4.8371342b952e from=translated src=- shape=5ff653b3 vocab=55980f65
-/
theorem gaps_toFinset_card_le (a : ℝ) (N : ℕ) :
    (gaps a N).toFinset.card ≤ Multiset.card (gaps a N) :=
  Multiset.toFinset_card_le (gaps a N)

/-- **Reduction lemma for the three-gap bound.** If every distinct gap value lies in
    a fixed three-element set, then there are at most three distinct gap lengths.
    The Phase 2 core supplies the hypothesis with `{η⁺, η⁻, η⁺+η⁻}`.
@isnad1 id=le.1h5v.s6.58fa8ecdd48c from=translated src=- shape=2eed1816 vocab=39c5bad6
-/
theorem three_gap_card_le_three_of_subset (a : ℝ) (N : ℕ) {x y z : ℝ}
    (hsub : (gaps a N).toFinset ⊆ ({x, y, z} : Finset ℝ)) :
    (gaps a N).toFinset.card ≤ 3 :=
  (Finset.card_le_card hsub).trans Finset.card_le_three

/-! ## Phase 2 core — the two first returns `η⁺`, `η⁻` (self-contained infrastructure)

The *positive return* `η⁺` is the smallest **positive** orbit point; the *negative
return* `η⁻` is `1 - max(orbit)`.  We package the positive orbit points as
`posOrbit a N := (orbit a N).erase 0`.  Everything below is proved unconditionally
(no surjectivity of the sorted enumeration is needed); the genuinely combinatorial
crux and the lemmas that depend on the enumeration-onto bridge are organized in the
Phase 2 core sections below. -/

/-- The **positive orbit points** `(orbit a N) \ {0}`.  Each lies in `(0,1)`. -/
noncomputable def posOrbit (a : ℝ) (N : ℕ) : Finset ℝ := (orbit a N).erase 0

/--
@isnad1 id=iff.0h3v.s5.817b1ac97a52 from=translated src=- shape=81edb25a vocab=2ac38b25
-/
theorem mem_posOrbit_iff (a : ℝ) (N : ℕ) (x : ℝ) :
    x ∈ posOrbit a N ↔ x ≠ 0 ∧ x ∈ orbit a N := by
  simp only [posOrbit, Finset.mem_erase]

/--
@isnad1 id=le.0h2v.s4.bdc4646140d5 from=translated src=- shape=74d6d0d6 vocab=cdec680a
-/
theorem posOrbit_subset_orbit (a : ℝ) (N : ℕ) : posOrbit a N ⊆ orbit a N :=
  Finset.erase_subset _ _

/--
@isnad1 id=lt.1h3v.s4.cae97e4a7ea6 from=translated src=- shape=d553b3cb vocab=b42f5b88
-/
theorem posOrbit_pos (a : ℝ) (N : ℕ) {x : ℝ} (hx : x ∈ posOrbit a N) : 0 < x := by
  rw [mem_posOrbit_iff] at hx
  obtain ⟨hx0, hxo⟩ := hx
  have hmem : x ∈ Set.Ico (0 : ℝ) 1 := orbit_subset_Ico a N (by simpa using hxo)
  exact lt_of_le_of_ne hmem.1 (Ne.symm hx0)

/--
@isnad1 id=lt.1h3v.s4.5acb2f017445 from=translated src=- shape=b3d46774 vocab=b42f5b88
-/
theorem posOrbit_lt_one (a : ℝ) (N : ℕ) {x : ℝ} (hx : x ∈ posOrbit a N) : x < 1 := by
  rw [mem_posOrbit_iff] at hx
  have hmem : x ∈ Set.Ico (0 : ℝ) 1 := orbit_subset_Ico a N (by simpa using hx.2)
  exact hmem.2

/--
@isnad1 id=nonempty.1h2v.s4.add464ca1c71 from=translated src=- shape=78649951 vocab=e80becf4
-/
theorem posOrbit_nonempty (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    (posOrbit a N).Nonempty := by
  have hntriv : (orbit a N).Nontrivial := by
    rw [← Finset.one_lt_card_iff_nontrivial]
    exact lt_of_lt_of_le one_lt_two h2
  obtain ⟨x, hx, hx0⟩ := hntriv.exists_ne (0 : ℝ)
  exact ⟨x, by rw [mem_posOrbit_iff]; exact ⟨hx0, hx⟩⟩

/-- `orbitCard a N ≤ N` (the orbit is the image of `range N`).
@isnad1 id=le.0h2v.s3.1e6a90f2525a from=translated src=- shape=be8b5c95 vocab=961fe64a
-/
theorem orbitCard_le (a : ℝ) (N : ℕ) : orbitCard a N ≤ N := by
  unfold orbitCard orbit
  calc ((Finset.range N).image (fun i : ℕ => Int.fract ((i : ℝ) * a))).card
      ≤ (Finset.range N).card := Finset.card_image_le
    _ = N := Finset.card_range N

/-- A nondegenerate orbit (`2 ≤ orbitCard`) forces `0 < N`.
@isnad1 id=lt.1h2v.s4.a1d19d3196d1 from=translated src=- shape=f85d87e2 vocab=71fb7cfd
-/
theorem pos_of_two_le_orbitCard (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) : 0 < N := by
  have hle := orbitCard_le a N
  omega

/-- The **positive return** `η⁺`: the smallest positive orbit point. Junk `1` in the
    degenerate regime. -/
noncomputable def etaPos (a : ℝ) (N : ℕ) : ℝ :=
  if h : (posOrbit a N).Nonempty then (posOrbit a N).min' h else 1

/-- The **negative return** `η⁻ = 1 - (largest positive orbit point)`. Junk `1` in
    the degenerate regime. -/
noncomputable def etaNeg (a : ℝ) (N : ℕ) : ℝ :=
  if h : (posOrbit a N).Nonempty then 1 - (posOrbit a N).max' h else 1

/-- `η⁺` is achieved by an actual positive orbit point: it lies in `posOrbit`.
@isnad1 id=mem.1h2v.s5.87987547f737 from=translated src=- shape=053b8350 vocab=94dd1bac
-/
theorem etaPos_mem (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    etaPos a N ∈ posOrbit a N := by
  have h := posOrbit_nonempty a h2
  simp only [etaPos, dite_eq_left h]
  exact (posOrbit a N).min'_mem h

/-- `η⁺ > 0`.
@isnad1 id=lt.1h2v.s4.08491fd41d6d from=translated src=- shape=013ebb13 vocab=1f6ff308
-/
theorem etaPos_pos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) : 0 < etaPos a N :=
  posOrbit_pos a N (etaPos_mem a h2)

/-- `η⁺` is minimal among positive orbit points.
@isnad1 id=le.2h3v.s5.07f5942f2192 from=translated src=- shape=3f9d593a vocab=94dd1bac
-/
theorem etaPos_le (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N)
    {x : ℝ} (hx : x ∈ posOrbit a N) : etaPos a N ≤ x := by
  have h := posOrbit_nonempty a h2
  simp only [etaPos, dite_eq_left h]
  exact (posOrbit a N).min'_le x hx

/-- `η⁺` is the smallest *positive* orbit point.
@isnad1 id=le.3h3v.s5.a8f95e5ddc24 from=translated src=- shape=7e4b9a7d vocab=e3117a58
-/
theorem no_orbit_below_etaPos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N)
    {x : ℝ} (hx : x ∈ orbit a N) (hx0 : 0 < x) : etaPos a N ≤ x :=
  etaPos_le a h2 (by rw [mem_posOrbit_iff]; exact ⟨hx0.ne', hx⟩)

/-- `1 - η⁻` (the largest positive orbit point) is achieved.
@isnad1 id=mem.1h2v.s5.956eb698632c from=translated src=- shape=c9f9c63d vocab=4b596d47
-/
theorem max_posOrbit_mem (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    (1 : ℝ) - etaNeg a N ∈ posOrbit a N := by
  have h := posOrbit_nonempty a h2
  simp only [etaNeg, dite_eq_left h, sub_sub_self]
  exact (posOrbit a N).max'_mem h

/-- `η⁻ > 0`.
@isnad1 id=lt.1h2v.s4.5c852902a33f from=translated src=- shape=013ebb13 vocab=8610dd5a
-/
theorem etaNeg_pos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) : 0 < etaNeg a N := by
  have hmem := max_posOrbit_mem a h2
  have hlt1 : (1 : ℝ) - etaNeg a N < 1 := posOrbit_lt_one a N hmem
  linarith

/-- Every positive orbit point is `≤ 1 - η⁻`.
@isnad1 id=le.2h3v.s5.b865f77d47dc from=translated src=- shape=fa60f9d3 vocab=4b596d47
-/
theorem le_one_sub_etaNeg (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N)
    {x : ℝ} (hx : x ∈ posOrbit a N) : x ≤ 1 - etaNeg a N := by
  have h := posOrbit_nonempty a h2
  simp only [etaNeg, dite_eq_left h, sub_sub_self]
  exact (posOrbit a N).le_max' x hx

/-- With at least one orbit point, the smallest sorted value is `0`.
@isnad1 id=eq.1h2v.s4.7d629e04ff6a from=translated src=- shape=49af02a5 vocab=51ea763b
-/
theorem sortedVal_zero_eq_zero (a : ℝ) {N : ℕ} (hN : 0 < N) :
    sortedVal a N 0 = 0 := by
  rw [sortedVal_zero a hN]
  refine le_antisymm ?_ ?_
  · exact (orbit a N).min'_le 0 (zero_mem_orbit a hN)
  · rw [Finset.le_min'_iff]
    intro y hy
    have : y ∈ Set.Ico (0 : ℝ) 1 := orbit_subset_Ico a N (by simpa using hy)
    exact this.1

/-- `sortedVal` is monotone (non-strict) on the valid index range.
@isnad1 id=le.2h4v.s5.65f4de3d3ec4 from=translated src=- shape=27721f2b vocab=40e0ff02
-/
theorem sortedVal_monotone (a : ℝ) (N : ℕ) {i j : ℕ}
    (hij : i ≤ j) (hj : j < orbitCard a N) :
    sortedVal a N i ≤ sortedVal a N j := by
  rcases eq_or_lt_of_le hij with h | h
  · exact le_of_eq (by rw [h])
  · exact le_of_lt (sortedVal_strictMono a N h hj)

/-- `sortedVal` reflects strict order on valid indices.
@isnad1 id=lt.2h4v.s5.5346cfdeb143 from=translated src=- shape=1cb8c834 vocab=349295a8
-/
theorem lt_of_sortedVal_lt (a : ℝ) (N : ℕ) {i m : ℕ}
    (hi : i < orbitCard a N) (h : sortedVal a N i < sortedVal a N m) : i < m := by
  by_contra hcon
  push Not at hcon
  exact absurd (sortedVal_monotone a N hcon hi) (not_le.mpr h)

/-- In the degenerate regime `orbitCard a N ≤ 1`, `gaps a N` has a single element.
@isnad1 id=eq.1h2v.s4.913381f5efaa from=translated src=- shape=ba507385 vocab=880ce9b0
-/
theorem gaps_card_eq_one_of_degenerate (a : ℝ) {N : ℕ} (h1 : orbitCard a N ≤ 1) :
    Multiset.card (gaps a N) = 1 := by
  rw [gaps_eq]
  have hz : orbitCard a N - 1 = 0 := by omega
  rw [hz]
  simp

/-! ## Phase 2 core — enumeration-onto bridge and the two returns as gap values

The bridge from the sorted enumeration back to the orbit, the no-orbit-point-between
lemma, and the identification of the first internal gap with `η⁺` and the wrap-around
gap with `η⁻`.  Together with `three_gap_card_le_three_of_subset` these reduce the
three-gap bound to the single first-return classification lemma
(`neighbour_gap_in_returns`, the genuine combinatorial core, proved below). -/

/-- **The sorted enumeration is onto the orbit.**  Every orbit point is `sortedVal j`
    for some valid index `j`.
@isnad1 id=ex.1h3v.s5.91f4131f20f5 from=translated src=- shape=1074dffa vocab=ec2a6057
-/
theorem exists_index_of_mem_orbit (a : ℝ) (N : ℕ) {y : ℝ} (hy : y ∈ orbit a N) :
    ∃ j, j < orbitCard a N ∧ sortedVal a N j = y := by
  have hrange : Set.range (orbitEmb a N) = ↑(orbit a N) :=
    Finset.range_orderEmbOfFin (orbit a N) (k := orbitCard a N) rfl
  have hyr : y ∈ Set.range (orbitEmb a N) := by
    rw [hrange]; exact Finset.mem_coe.mpr hy
  obtain ⟨j, hj⟩ := hyr
  refine ⟨j.1, j.2, ?_⟩
  simp only [sortedVal, dite_eq_left j.2, Fin.eta]
  exact hj

/-- No orbit point lies strictly between two consecutive sorted points.
@isnad1 id=false.4h4v.s6.4827191104db from=translated src=- shape=fe9b758a vocab=dd87410d
-/
theorem no_orbit_strictly_between (a : ℝ) (N : ℕ) {i : ℕ} (hi : i + 1 < orbitCard a N)
    {z : ℝ} (hz : z ∈ orbit a N)
    (hlo : sortedVal a N i < z) (hhi : z < sortedVal a N (i + 1)) : False := by
  obtain ⟨m, hm, hmval⟩ := exists_index_of_mem_orbit a N hz
  have hi' : i < orbitCard a N := lt_trans (Nat.lt_succ_self i) hi
  have him : i < m := lt_of_sortedVal_lt a N hi' (by rwa [hmval])
  have hmi : m < i + 1 := lt_of_sortedVal_lt a N hm (by rwa [hmval])
  omega

/-- `sortedVal a N 1 = η⁺`.
@isnad1 id=eq.1h2v.s4.800b06154648 from=translated src=- shape=e2fab632 vocab=b10fd751
-/
theorem sortedVal_one_eq_etaPos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    sortedVal a N 1 = etaPos a N := by
  have hN : 0 < N := pos_of_two_le_orbitCard a h2
  have h1 : (1 : ℕ) < orbitCard a N := lt_of_lt_of_le one_lt_two h2
  have hpos : 0 < sortedVal a N 1 := by
    have := sortedVal_strictMono a N (i := 0) (j := 1) Nat.zero_lt_one h1
    rwa [sortedVal_zero_eq_zero a hN] at this
  have hmem : sortedVal a N 1 ∈ orbit a N := sortedVal_mem a (i := 1) h1
  refine le_antisymm ?_ ?_
  · have hetaMem : etaPos a N ∈ orbit a N := posOrbit_subset_orbit a N (etaPos_mem a h2)
    have hetaPos : 0 < etaPos a N := etaPos_pos a h2
    obtain ⟨j, hj, hjval⟩ := exists_index_of_mem_orbit a N hetaMem
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · rw [sortedVal_zero_eq_zero a hN] at hjval
        exact absurd hjval.symm hetaPos.ne'
      · exact hjpos
    rw [← hjval]
    rcases eq_or_lt_of_le hj1 with hje | hjlt
    · exact le_of_eq (by rw [← hje])
    · exact le_of_lt (sortedVal_strictMono a N hjlt hj)
  · exact no_orbit_below_etaPos a h2 hmem hpos

/-- The wrap-around gap equals `η⁻`.
@isnad1 id=eq.1h2v.s6.58c08ed5cada from=translated src=- shape=b04f8e9c vocab=965245d2
-/
theorem wraparound_eq_etaNeg (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    sortedVal a N 0 + 1 - sortedVal a N (orbitCard a N - 1) = etaNeg a N := by
  have hN : 0 < N := pos_of_two_le_orbitCard a h2
  rw [sortedVal_zero_eq_zero a hN, sortedVal_last a hN]
  have hmem : (1 : ℝ) - etaNeg a N ∈ orbit a N :=
    posOrbit_subset_orbit a N (max_posOrbit_mem a h2)
  have hmax : (orbit a N).max' (orbit_nonempty a hN) = 1 - etaNeg a N := by
    refine le_antisymm ?_ ?_
    · rw [Finset.max'_le_iff]
      intro y hy
      rcases eq_or_ne y 0 with rfl | hy0
      · have hmm : (1 : ℝ) - etaNeg a N ∈ Set.Ico (0 : ℝ) 1 :=
          orbit_subset_Ico a N (by simpa using hmem)
        exact hmm.1
      · exact le_one_sub_etaNeg a h2 (by rw [mem_posOrbit_iff]; exact ⟨hy0, hy⟩)
    · exact (orbit a N).le_max' _ hmem
  rw [hmax]; ring

/-- The first internal gap is `η⁺`.
@isnad1 id=eq.1h2v.s4.00ff883fef0f from=translated src=- shape=e2fab632 vocab=6f914228
-/
theorem gapAt_zero_eq_etaPos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    gapAt a N 0 = etaPos a N := by
  have hN : 0 < N := pos_of_two_le_orbitCard a h2
  unfold gapAt
  rw [sortedVal_zero_eq_zero a hN, sortedVal_one_eq_etaPos a h2, sub_zero]

/-- `η⁺` occurs as a gap value.  (API extra; not used by the main chain.)
@isnad1 id=mem.1h2v.s4.781a7b56ebde from=translated src=- shape=053b8350 vocab=96a9a4b2
-/
theorem etaPos_is_gap (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    etaPos a N ∈ gaps a N := by
  rw [mem_gaps_iff]
  left
  refine ⟨0, ?_, gapAt_zero_eq_etaPos a h2⟩
  omega

/-- `η⁻` occurs as a gap value.  (API extra; not used by the main chain.)
@isnad1 id=mem.1h2v.s4.9ce7517438ad from=translated src=- shape=053b8350 vocab=8eb12317
-/
theorem etaNeg_is_gap (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    etaNeg a N ∈ gaps a N := by
  rw [mem_gaps_iff]
  right
  exact (wraparound_eq_etaNeg a h2).symm

/-! ## Phase 2 core — fractional-part rotation helpers (toward the first-return lemma) -/

/-- **Fractional-part index-shift identity.**  Reducing the two summands mod 1
    first does not change the fractional part of a sum:
    `Int.fract (Int.fract x + Int.fract y) = Int.fract (x + y)`.  With `x = u*a`,
    `y = m*a` this is the value form of the multiplier shift `u, m ↦ u + m`.
@isnad1 id=eq.0h2v.s5.f4e944a37117 from=translated src=- shape=00234d03 vocab=19981c94
-/
theorem fract_add_fract_eq (x y : ℝ) :
    Int.fract (Int.fract x + Int.fract y) = Int.fract (x + y) := by
  rw [Int.fract_eq_fract]
  refine ⟨-⌊x⌋ - ⌊y⌋, ?_⟩
  have hx : Int.fract x = x - ⌊x⌋ := (Int.self_sub_floor x).symm
  have hy : Int.fract y = y - ⌊y⌋ := (Int.self_sub_floor y).symm
  rw [hx, hy]; push_cast; ring

/-- **Forward rotation closure (multiplier in range).**  If `u + m < N`, the
    rotated value `Int.fract (Int.fract (u*a) + Int.fract (m*a))` is again an orbit
    point.  This is the half of the Slater closure that does not wrap past index
    `N`; the values that fall off the end (`u + m ≥ N`) are where the negative
    return appears.  (API extra; not used by the main chain.)
@isnad1 id=mem.1h4v.s6.4c63cc477ef0 from=translated src=- shape=81a9c2a1 vocab=3bee4100
-/
theorem fract_rotate_mem (a : ℝ) (N : ℕ) {u m : ℕ} (hum : u + m < N) :
    Int.fract (Int.fract ((u : ℝ) * a) + Int.fract ((m : ℝ) * a)) ∈ orbit a N := by
  rw [fract_add_fract_eq]
  have hcast : (u : ℝ) * a + (m : ℝ) * a = ((u + m : ℕ) : ℝ) * a := by push_cast; ring
  rw [hcast]
  exact (mem_orbit_iff a N _).mpr ⟨u + m, hum, rfl⟩

/-! ## Multiplier-indexed infrastructure (toward the first-return dichotomy)

The value-Finset `orbit` hides the index ("multiplier") behind each point.
We recover a canonical multiplier and the forward value-shift; the discriminant
of the three-gap dichotomy is the *Nat* condition `canMul + mp < N`.
-/

/-- The finset of indices `< N` whose rotation value equals `p`. -/
noncomputable def mulFiber (a : ℝ) (N : ℕ) (p : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun k => Int.fract ((k : ℝ) * a) = p)

/--
@isnad1 id=iff.0h4v.s5.1b32b02c568f from=translated src=- shape=6acd73a4 vocab=49bdce36
-/
theorem mem_mulFiber_iff (a : ℝ) (N : ℕ) (p : ℝ) (k : ℕ) :
    k ∈ mulFiber a N p ↔ k < N ∧ Int.fract ((k : ℝ) * a) = p := by
  simp only [mulFiber, Finset.mem_filter, Finset.mem_range]

/--
@isnad1 id=nonempty.1h3v.s4.b6b90d1ba00a from=translated src=- shape=6fc360c5 vocab=c444a3fb
-/
theorem mulFiber_nonempty (a : ℝ) (N : ℕ) {p : ℝ} (hp : p ∈ orbit a N) :
    (mulFiber a N p).Nonempty := by
  obtain ⟨i, hi, hival⟩ := (mem_orbit_iff a N p).mp hp
  exact ⟨i, (mem_mulFiber_iff a N p i).mpr ⟨hi, hival⟩⟩

/-- **Canonical (least) multiplier** of an orbit point `p`. -/
noncomputable def canMul (a : ℝ) (N : ℕ) (p : ℝ) (hp : p ∈ orbit a N) : ℕ :=
  (mulFiber a N p).min' (mulFiber_nonempty a N hp)

/--
@isnad1 id=mem.1h3v.s5.a5082d7b06ed from=translated src=- shape=bdf32c9c vocab=877f0aec
-/
theorem canMul_mem_fiber (a : ℝ) (N : ℕ) {p : ℝ} (hp : p ∈ orbit a N) :
    canMul a N p hp ∈ mulFiber a N p := by
  unfold canMul
  exact (mulFiber a N p).min'_mem (mulFiber_nonempty a N hp)

/--
@isnad1 id=lt.1h3v.s4.1f1063d18ff9 from=translated src=- shape=223b60b2 vocab=48e93bc9
-/
theorem canMul_lt (a : ℝ) (N : ℕ) {p : ℝ} (hp : p ∈ orbit a N) :
    canMul a N p hp < N :=
  ((mem_mulFiber_iff a N p _).mp (canMul_mem_fiber a N hp)).1

/--
@isnad1 id=eq.1h3v.s5.82f02882dbd9 from=translated src=- shape=0ebedfce vocab=a130bb1e
-/
theorem fract_canMul (a : ℝ) (N : ℕ) {p : ℝ} (hp : p ∈ orbit a N) :
    Int.fract ((canMul a N p hp : ℝ) * a) = p :=
  ((mem_mulFiber_iff a N p _).mp (canMul_mem_fiber a N hp)).2

/-- **Return-multiplier existence** for `η⁺` (the smallest positive orbit point):
    some `mp < N` rotates to `η⁺`.
@isnad1 id=ex.1h2v.s5.779a18310860 from=translated src=- shape=f2523cd8 vocab=6b85362c
-/
theorem exists_return_multiplier (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    ∃ mp, mp < N ∧ Int.fract ((mp : ℝ) * a) = etaPos a N := by
  have hmem : etaPos a N ∈ orbit a N := posOrbit_subset_orbit a N (etaPos_mem a h2)
  obtain ⟨mp, hmp, hmpval⟩ := (mem_orbit_iff a N _).mp hmem
  exact ⟨mp, hmp, hmpval⟩

/-- **Backward return-multiplier existence** for `1 - η⁻` (the largest positive
    orbit point): some `mn < N` rotates to `1 - η⁻`.
@isnad1 id=ex.1h2v.s5.31069b76f6e1 from=translated src=- shape=7201c51a vocab=a51a789e
-/
theorem exists_back_return_multiplier (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    ∃ mn, mn < N ∧ Int.fract ((mn : ℝ) * a) = 1 - etaNeg a N := by
  have hmem : (1 : ℝ) - etaNeg a N ∈ orbit a N :=
    posOrbit_subset_orbit a N (max_posOrbit_mem a h2)
  obtain ⟨mn, hmn, hmnval⟩ := (mem_orbit_iff a N _).mp hmem
  exact ⟨mn, hmn, hmnval⟩

/-- **Value-shift identity.**  Rotating an orbit point `p` (canonical multiplier
    `u = canMul p`) by a return multiplier `mp` for `η⁺` lands on
    `Int.fract (p + η⁺)`.  (API extra; the main chain uses `fract_index_shift`.)
@isnad1 id=eq.2h4v.s6.796c3c77d1eb from=translated src=- shape=c5e339d6 vocab=8df28a34
-/
theorem fract_shift_eq (a : ℝ) (N : ℕ) {p : ℝ} (hp : p ∈ orbit a N)
    {mp : ℕ} (hmpval : Int.fract ((mp : ℝ) * a) = etaPos a N) :
    Int.fract (((canMul a N p hp + mp : ℕ)) * a) = Int.fract (p + etaPos a N) := by
  have hcast : ((canMul a N p hp + mp : ℕ) : ℝ) * a
      = (canMul a N p hp : ℝ) * a + (mp : ℝ) * a := by push_cast; ring
  rw [hcast, ← fract_add_fract_eq, fract_canMul a N hp, hmpval]

/-- **Forward shift lands in the orbit** when the multiplier stays in range
    (`canMul p + mp < N`) and `p + η⁺ < 1` (no wrap).  (API extra; unused.)
@isnad1 id=mem.6h4v.s7.e79827ee8985 from=translated src=- shape=91e35a2d vocab=ae94a2f5
-/
theorem shift_mem_orbit (a : ℝ) (N : ℕ) {p : ℝ} (hp : p ∈ orbit a N)
    {mp : ℕ} (hmpval : Int.fract ((mp : ℝ) * a) = etaPos a N)
    (hrange : canMul a N p hp + mp < N)
    (hlt1 : p + etaPos a N < 1)
    (hp0 : 0 ≤ p) (heta0 : 0 ≤ etaPos a N) :
    p + etaPos a N ∈ orbit a N := by
  have hval : Int.fract (((canMul a N p hp + mp : ℕ)) * a) = p + etaPos a N := by
    rw [fract_shift_eq a N hp hmpval, Int.fract_eq_self.mpr ⟨by linarith, hlt1⟩]
  exact (mem_orbit_iff a N _).mpr ⟨_, hrange, hval⟩

/-! ### Forward-neighbour upper bound (API extra — superseded by Case A below) -/

/-- **Forward-neighbour upper bound.**  Under the forward hypothesis `hfwd`, the
    gap is at MOST `η⁺`: the orbit point `q := sortedVal i + η⁺` lies strictly above
    `sortedVal i` and `< 1`, so by `no_orbit_strictly_between` it cannot sit strictly
    below `sortedVal (i+1)`.  (API extra; superseded by `gap_eq_etaPos`.)
@isnad1 id=le.3h3v.s6.d5321354b0b2 from=translated src=- shape=fd0cc590 vocab=dc1af9ed
-/
theorem gap_le_etaPos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N)
    {i : ℕ} (hi : i + 1 < orbitCard a N)
    (hfwd : sortedVal a N i + etaPos a N < 1 ∧ sortedVal a N i + etaPos a N ∈ orbit a N) :
    gapAt a N i ≤ etaPos a N := by
  obtain ⟨_, hmem⟩ := hfwd
  have heta0 : 0 < etaPos a N := etaPos_pos a h2
  by_contra hcon
  push Not at hcon
  have hlo : sortedVal a N i < sortedVal a N i + etaPos a N := by linarith
  have hhi : sortedVal a N i + etaPos a N < sortedVal a N (i + 1) := by
    unfold gapAt at hcon; linarith
  exact no_orbit_strictly_between a N hi hmem hlo hhi

/-! ## Index-bridge infrastructure (multiplier indices and difference extraction)

Toward the first-return classification, recovering the index structure behind the
orbit values.  The decisive discriminant is the index condition `j + m⁺ < N`, NOT
the value condition `xⱼ + η⁺ ∈ orbit`: those differ (e.g. `α = 4/5, N = 4`, point
`2/5` has `2/5 + η⁺ = 4/5 ∈ orbit` yet gap `= η⁻`, since its index is off-end).
-/

/-- Fractional-part subtraction identity (companion of `fract_add_fract_eq`).
@isnad1 id=eq.0h2v.s5.6eccfff17826 from=translated src=- shape=00234d03 vocab=5b2435c4
-/
theorem fract_sub_fract_eq (x y : ℝ) :
    Int.fract (Int.fract x - Int.fract y) = Int.fract (x - y) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊y⌋ - ⌊x⌋, ?_⟩
  have hx : Int.fract x = x - ⌊x⌋ := (Int.self_sub_floor x).symm
  have hy : Int.fract y = y - ⌊y⌋ := (Int.self_sub_floor y).symm
  rw [hx, hy]; push_cast; ring

/-- Pure `Nat`/`Finset` counting seed: exactly `N - mp` indices keep their forward
    `+mp` shift in range, so exactly `mp` fall off the end.  (API extra; unused.)
@isnad1 id=eq.1h2v.s5.7942108eebcb from=translated src=- shape=725a6976 vocab=a80f5427
-/
theorem forward_inRange_card {N mp : ℕ} (h : mp ≤ N) :
    (Finset.filter (fun j => j + mp < N) (Finset.range N)).card = N - mp := by
  have hset : Finset.filter (fun j => j + mp < N) (Finset.range N)
      = Finset.range (N - mp) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset, Finset.card_range]

/-- Forward return multiplier as an index: the canonical (least) index whose
    rotation value is `η⁺`. -/
noncomputable def mPlus (a : ℝ) (N : ℕ) (h2 : 2 ≤ orbitCard a N) : ℕ :=
  canMul a N (etaPos a N) (posOrbit_subset_orbit a N (etaPos_mem a h2))

/--
@isnad1 id=lt.1h2v.s4.882fd1c6daff from=translated src=- shape=ff179860 vocab=5493b24b
-/
theorem mPlus_lt (a : ℝ) (N : ℕ) (h2 : 2 ≤ orbitCard a N) : mPlus a N h2 < N := by
  unfold mPlus; exact canMul_lt a N _

/--
@isnad1 id=eq.1h2v.s5.bb6860635da5 from=translated src=- shape=5c559e22 vocab=cb2e01eb
-/
theorem fract_mPlus (a : ℝ) (N : ℕ) (h2 : 2 ≤ orbitCard a N) :
    Int.fract ((mPlus a N h2 : ℝ) * a) = etaPos a N := by
  unfold mPlus; exact fract_canMul a N _

/--
@isnad1 id=lt.1h2v.s4.45a0d90d2fe9 from=translated src=- shape=7dd7ae36 vocab=5493b24b
-/
theorem mPlus_pos (a : ℝ) (N : ℕ) (h2 : 2 ≤ orbitCard a N) : 0 < mPlus a N h2 := by
  rcases Nat.eq_zero_or_pos (mPlus a N h2) with h0 | hpos
  · exfalso
    have hf := fract_mPlus a N h2
    rw [h0] at hf
    simp only [Nat.cast_zero, zero_mul, Int.fract_zero] at hf
    exact (etaPos_pos a h2).ne hf
  · exact hpos

/-- **Difference extraction, `w ≥ j`.**  If two orbit points have non-decreasing
    indices `j ≤ w < N` and increasing values, their difference is an orbit point.
    Combined with `no_orbit_below_etaPos` this rules out a between-point reachable
    from a higher index.
@isnad1 id=mem.3h4v.s6.575106ffa781 from=translated src=- shape=f5315149 vocab=1b8d65e1
-/
theorem sub_mem_orbit_of_index_le (a : ℝ) (N : ℕ) {j w : ℕ} (hjw : j ≤ w) (hw : w < N)
    (hlt : Int.fract ((j : ℝ) * a) < Int.fract ((w : ℝ) * a)) :
    Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a) ∈ orbit a N := by
  set d : ℝ := Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a) with hd
  have hpos : 0 < d := by rw [hd]; linarith
  have hlt1 : d < 1 := by
    rw [hd]
    have h1 := Int.fract_lt_one ((w : ℝ) * a)
    have h2 := Int.fract_nonneg ((j : ℝ) * a)
    linarith
  have hself : Int.fract d = d := Int.fract_eq_self.mpr ⟨le_of_lt hpos, hlt1⟩
  have hcast : ((w - j : ℕ) : ℝ) * a = (w : ℝ) * a - (j : ℝ) * a := by
    rw [Nat.cast_sub hjw]; ring
  have hkey : Int.fract (((w - j : ℕ) : ℝ) * a) = d := by
    rw [hcast, ← fract_sub_fract_eq]; exact hself
  have hwj : w - j < N := lt_of_le_of_lt (Nat.sub_le w j) hw
  rw [← hkey]
  exact (mem_orbit_iff a N _).mpr ⟨w - j, hwj, rfl⟩

/-- **Difference extraction, `w < j` (dual).**  If the larger value `{w·a}` has the
    *smaller* index `w < j`, the complement `1 - ({w·a} - {j·a})` is an orbit point
    (`{(j-w)·a}`) in the top band `(1 - η⁺, 1)`.  Via `le_one_sub_etaNeg` this gives
    `{w·a} - {j·a} ≥ η⁻`; used in the backward index-bridge toward Case B.
@isnad1 id=mem.3h4v.s6.124cdccefd41 from=translated src=- shape=ed7a32c7 vocab=bc3a282f
-/
theorem compl_mem_orbit_of_index_gt (a : ℝ) (N : ℕ) {j w : ℕ} (hwj : w < j) (hj : j < N)
    (hlt : Int.fract ((j : ℝ) * a) < Int.fract ((w : ℝ) * a)) :
    1 - (Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a)) ∈ orbit a N := by
  set z : ℝ := Int.fract ((w : ℝ) * a) with hz
  set v : ℝ := Int.fract ((j : ℝ) * a) with hv
  have hpos : 0 < z - v := by linarith
  have hlt1 : z - v < 1 := by
    rw [hz, hv]
    have h1 := Int.fract_lt_one ((w : ℝ) * a)
    have h2 := Int.fract_nonneg ((j : ℝ) * a)
    linarith
  have hmem01 : (0 : ℝ) ≤ 1 - (z - v) ∧ 1 - (z - v) < 1 := ⟨by linarith, by linarith⟩
  have hcast : ((j - w : ℕ) : ℝ) * a = (j : ℝ) * a - (w : ℝ) * a := by
    rw [Nat.cast_sub (le_of_lt hwj)]; ring
  have hfr : Int.fract (((j - w : ℕ) : ℝ) * a) = 1 - (z - v) := by
    rw [hcast, ← fract_sub_fract_eq, ← hz, ← hv]
    have heq : v - z = (1 - (z - v)) + ((-1 : ℤ) : ℝ) := by push_cast; ring
    rw [heq, Int.fract_add_intCast, Int.fract_eq_self.mpr hmem01]
  have hjw : j - w < N := lt_of_le_of_lt (Nat.sub_le j w) hj
  rw [← hfr]
  exact (mem_orbit_iff a N _).mpr ⟨j - w, hjw, rfl⟩

/-! ## The forward (η⁺) case -/

/-- Shifting an index by `m⁺` realises the rotation by `η⁺` at the value level:
    `{(j+m⁺)·a} = {{j·a} + η⁺}`.
@isnad1 id=eq.1h3v.s6.f5a33e310ede from=translated src=- shape=db6cbc78 vocab=40a5b05f
-/
theorem fract_index_shift (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) (j : ℕ) :
    Int.fract (((j + mPlus a N h2 : ℕ) : ℝ) * a)
      = Int.fract (Int.fract ((j : ℝ) * a) + etaPos a N) := by
  have hcast : ((j + mPlus a N h2 : ℕ) : ℝ) * a
      = (j : ℝ) * a + (mPlus a N h2 : ℝ) * a := by push_cast; ring
  rw [hcast, ← fract_add_fract_eq, fract_mPlus]

/-- No-wrap specialisation: when `{j·a} + η⁺ < 1`, the `m⁺`-shifted index lands on
    exactly `{j·a} + η⁺`.
@isnad1 id=eq.2h3v.s6.5172e89d5fd8 from=translated src=- shape=3f742c55 vocab=33cef43d
-/
theorem fract_index_shift_noWrap (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) (j : ℕ)
    (hlt1 : Int.fract ((j : ℝ) * a) + etaPos a N < 1) :
    Int.fract (((j + mPlus a N h2 : ℕ) : ℝ) * a) = Int.fract ((j : ℝ) * a) + etaPos a N := by
  rw [fract_index_shift a h2 j]
  have hnn : (0 : ℝ) ≤ Int.fract ((j : ℝ) * a) + etaPos a N := by
    have h1 := Int.fract_nonneg ((j : ℝ) * a)
    have h2' := etaPos_pos a h2
    linarith
  exact Int.fract_eq_self.mpr ⟨hnn, hlt1⟩

/-- **D1 — an in-range index is not in the top band.**  If `d + m⁺ < N` then
    `{d·a} + η⁺ ≤ 1`.  (If not, `{(d+m⁺)·a} = {d·a}+η⁺-1` is a positive orbit value
    `< η⁺`, contradicting minimality.)
@isnad1 id=le.2h3v.s6.9014047b3bec from=translated src=- shape=5ce491ac vocab=33cef43d
-/
theorem fract_add_etaPos_le_one (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {d : ℕ}
    (hd : d + mPlus a N h2 < N) :
    Int.fract ((d : ℝ) * a) + etaPos a N ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have hfr_lt1 := Int.fract_lt_one ((d : ℝ) * a)
  have heta_lt1 : etaPos a N < 1 := posOrbit_lt_one a N (etaPos_mem a h2)
  have hval : Int.fract (Int.fract ((d : ℝ) * a) + etaPos a N)
      = Int.fract ((d : ℝ) * a) + etaPos a N - 1 := by
    have h1 : (0 : ℝ) ≤ Int.fract ((d : ℝ) * a) + etaPos a N - 1 := by linarith
    have h2'' : Int.fract ((d : ℝ) * a) + etaPos a N - 1 < 1 := by linarith
    conv_lhs => rw [show Int.fract ((d : ℝ) * a) + etaPos a N
          = (Int.fract ((d : ℝ) * a) + etaPos a N - 1) + ((1 : ℤ) : ℝ) by push_cast; ring]
    rw [Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨h1, h2''⟩
  have hmem : Int.fract (((d + mPlus a N h2 : ℕ) : ℝ) * a) ∈ orbit a N :=
    (mem_orbit_iff a N _).mpr ⟨d + mPlus a N h2, hd, rfl⟩
  rw [fract_index_shift a h2 d, hval] at hmem
  have hpos : 0 < Int.fract ((d : ℝ) * a) + etaPos a N - 1 := by linarith
  have hmin := no_orbit_below_etaPos a h2 hmem hpos
  linarith

/-- **No orbit point lies in `(xⱼ, xⱼ + η⁺)` when `j + m⁺ < N`.**  `w ≥ j`: the
    difference is a positive orbit value `< η⁺` (minimality).  `w < j`: the
    complementary index `j - w` would be in the top band, contradicting D1.
@isnad1 id=false.5h4v.s6.4e3d4637e320 from=translated src=- shape=c637a796 vocab=b01e9e0f
-/
theorem noPointBetween (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {j : ℕ}
    (hj : j + mPlus a N h2 < N)
    {z : ℝ} (hz : z ∈ orbit a N)
    (hlo : Int.fract ((j : ℝ) * a) < z)
    (hhi : z < Int.fract ((j : ℝ) * a) + etaPos a N) : False := by
  obtain ⟨w, hwN, hwval⟩ := (mem_orbit_iff a N z).mp hz
  have hjN : j < N := lt_of_le_of_lt (Nat.le_add_right j _) hj
  have hlt' : Int.fract ((j : ℝ) * a) < Int.fract ((w : ℝ) * a) := by rw [hwval]; exact hlo
  rcases Nat.lt_or_ge w j with hwlt | hwge
  · have hdN : (j - w) + mPlus a N h2 < N := by omega
    have hD1 := fract_add_etaPos_le_one a h2 hdN
    have hcast : ((j - w : ℕ) : ℝ) * a = (j : ℝ) * a - (w : ℝ) * a := by
      rw [Nat.cast_sub (le_of_lt hwlt)]; ring
    have hzv1 : Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a) < 1 := by
      have h1 := Int.fract_lt_one ((w : ℝ) * a)
      have h2' := Int.fract_nonneg ((j : ℝ) * a)
      linarith
    have hzvpos : 0 < Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a) := by linarith
    have hmem01 : (0 : ℝ) ≤ 1 - (Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a)) ∧
        1 - (Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a)) < 1 := ⟨by linarith, by linarith⟩
    have hfr : Int.fract (((j - w : ℕ) : ℝ) * a)
        = 1 - (Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a)) := by
      rw [hcast, ← fract_sub_fract_eq]
      have heq : Int.fract ((j : ℝ) * a) - Int.fract ((w : ℝ) * a)
          = (1 - (Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a))) + ((-1 : ℤ) : ℝ) := by
        push_cast; ring
      rw [heq, Int.fract_add_intCast, Int.fract_eq_self.mpr hmem01]
    rw [hfr, hwval] at hD1
    linarith
  · have hd := sub_mem_orbit_of_index_le a N hwge hwN hlt'
    have hdpos : 0 < Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a) := by
      rw [hwval]; linarith
    have hmin := no_orbit_below_etaPos a h2 hd hdpos
    rw [hwval] at hmin
    linarith

/-- **Case A (forward): an index `j` of `v = sortedVal i` with `j + m⁺ < N` forces
    gap `= η⁺`.**
@isnad1 id=eq.4h4v.s6.883e673c2456 from=translated src=- shape=9e84261a vocab=3d237cc7
-/
theorem gap_eq_etaPos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {i : ℕ}
    (hi : i + 1 < orbitCard a N)
    {j : ℕ} (hjfr : Int.fract ((j : ℝ) * a) = sortedVal a N i)
    (hjN : j + mPlus a N h2 < N) :
    gapAt a N i = etaPos a N := by
  set v := sortedVal a N i with hv
  set v' := sortedVal a N (i + 1) with hv'
  have hv'mem : v' ∈ orbit a N := sortedVal_mem a hi
  have hvv' : v < v' := sortedVal_strictMono a N (Nat.lt_succ_self i) hi
  have hv'lt1 : v' < 1 := (orbit_subset_Ico a N (Finset.mem_coe.mpr hv'mem)).2
  have hetapos : 0 < etaPos a N := etaPos_pos a h2
  have hge : v + etaPos a N ≤ v' := by
    by_contra hc
    push Not at hc
    exact noPointBetween a h2 hjN hv'mem (by rw [hjfr]; exact hvv') (by rw [hjfr]; exact hc)
  have hvlt1 : v + etaPos a N < 1 := by
    by_contra hc
    push Not at hc
    exact noPointBetween a h2 hjN hv'mem (by rw [hjfr]; exact hvv') (by rw [hjfr]; linarith)
  have hmem : v + etaPos a N ∈ orbit a N := by
    have hms : Int.fract (((j + mPlus a N h2 : ℕ) : ℝ) * a) ∈ orbit a N :=
      (mem_orbit_iff a N _).mpr ⟨j + mPlus a N h2, hjN, rfl⟩
    rw [fract_index_shift_noWrap a h2 j (by rw [hjfr]; exact hvlt1), hjfr] at hms
    exact hms
  have hle : v' ≤ v + etaPos a N := by
    by_contra hc
    push Not at hc
    exact no_orbit_strictly_between a N hi hmem (by linarith) hc
  have heq : v' = v + etaPos a N := le_antisymm hle hge
  unfold gapAt
  rw [← hv, ← hv', heq]; ring

/-! ### Backward (η⁻) machinery — mirror of the forward case -/

/-- Backward return multiplier: the canonical index of the MAX orbit value `1-η⁻`. -/
noncomputable def mMinus (a : ℝ) (N : ℕ) (h2 : 2 ≤ orbitCard a N) : ℕ :=
  canMul a N (1 - etaNeg a N) (posOrbit_subset_orbit a N (max_posOrbit_mem a h2))

/--
@isnad1 id=lt.1h2v.s4.55cbe770a63d from=translated src=- shape=ff179860 vocab=72153a80
-/
theorem mMinus_lt (a : ℝ) (N : ℕ) (h2 : 2 ≤ orbitCard a N) : mMinus a N h2 < N := by
  unfold mMinus; exact canMul_lt a N _

/--
@isnad1 id=eq.1h2v.s5.e71f539538bb from=translated src=- shape=8671d1c5 vocab=52443ab4
-/
theorem fract_mMinus (a : ℝ) (N : ℕ) (h2 : 2 ≤ orbitCard a N) :
    Int.fract ((mMinus a N h2 : ℝ) * a) = 1 - etaNeg a N := by
  unfold mMinus; exact fract_canMul a N _

/-- Index shift by `m⁻` realises rotation by `1-η⁻` (i.e. by `-η⁻`) at value level.
@isnad1 id=eq.1h3v.s6.9454d6103d76 from=translated src=- shape=701763e8 vocab=747ceb73
-/
theorem fract_index_shift_neg (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) (j : ℕ) :
    Int.fract (((j + mMinus a N h2 : ℕ) : ℝ) * a)
      = Int.fract (Int.fract ((j : ℝ) * a) + (1 - etaNeg a N)) := by
  have hcast : ((j + mMinus a N h2 : ℕ) : ℝ) * a
      = (j : ℝ) * a + (mMinus a N h2 : ℝ) * a := by push_cast; ring
  rw [hcast, ← fract_add_fract_eq, fract_mMinus]

/-- **D1' (mirror): an in-range index is not in the bottom band.**  If
    `d + m⁻ < N` and `{d·a} > 0` then `η⁻ ≤ {d·a}`.
@isnad1 id=le.3h3v.s6.152022bd25e4 from=translated src=- shape=dc332d4b vocab=e57aee15
-/
theorem fract_sub_etaNeg_ge (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {d : ℕ}
    (hd : d + mMinus a N h2 < N) (h0 : 0 < Int.fract ((d : ℝ) * a)) :
    etaNeg a N ≤ Int.fract ((d : ℝ) * a) := by
  by_contra hcon
  push Not at hcon
  have h1mη : 0 < 1 - etaNeg a N := posOrbit_pos a N (max_posOrbit_mem a h2)
  have hval : Int.fract (Int.fract ((d : ℝ) * a) + (1 - etaNeg a N))
      = Int.fract ((d : ℝ) * a) + (1 - etaNeg a N) :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hmemorb : Int.fract (((d + mMinus a N h2 : ℕ) : ℝ) * a) ∈ orbit a N :=
    (mem_orbit_iff a N _).mpr ⟨_, hd, rfl⟩
  rw [fract_index_shift_neg a h2 d, hval] at hmemorb
  have hpos2 : 0 < Int.fract ((d : ℝ) * a) + (1 - etaNeg a N) := by linarith
  have hposorb : Int.fract ((d : ℝ) * a) + (1 - etaNeg a N) ∈ posOrbit a N := by
    rw [mem_posOrbit_iff]; exact ⟨ne_of_gt hpos2, hmemorb⟩
  have hle := le_one_sub_etaNeg a h2 hposorb
  linarith

/-- **No orbit point lies in `(xⱼ - η⁻, xⱼ)` when `j + m⁻ < N`** (backward mirror
    of `noPointBetween`).
@isnad1 id=false.5h4v.s6.315e0d63190d from=translated src=- shape=23e85392 vocab=777b7a7a
-/
theorem noPointBetween_neg (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {j : ℕ}
    (hj : j + mMinus a N h2 < N)
    {z : ℝ} (hz : z ∈ orbit a N)
    (hlo : Int.fract ((j : ℝ) * a) - etaNeg a N < z)
    (hhi : z < Int.fract ((j : ℝ) * a)) : False := by
  obtain ⟨w, hwN, hwval⟩ := (mem_orbit_iff a N z).mp hz
  have hlt' : Int.fract ((w : ℝ) * a) < Int.fract ((j : ℝ) * a) := by rw [hwval]; exact hhi
  rcases Nat.lt_or_ge w j with hwlt | hwge
  · have hdN : (j - w) + mMinus a N h2 < N := by omega
    have hcast : ((j - w : ℕ) : ℝ) * a = (j : ℝ) * a - (w : ℝ) * a := by
      rw [Nat.cast_sub (le_of_lt hwlt)]; ring
    have hdpos : 0 < Int.fract ((j : ℝ) * a) - Int.fract ((w : ℝ) * a) := by linarith
    have hdlt1 : Int.fract ((j : ℝ) * a) - Int.fract ((w : ℝ) * a) < 1 := by
      have h1 := Int.fract_lt_one ((j : ℝ) * a)
      have h2' := Int.fract_nonneg ((w : ℝ) * a)
      linarith
    have hself : Int.fract (Int.fract ((j : ℝ) * a) - Int.fract ((w : ℝ) * a))
        = Int.fract ((j : ℝ) * a) - Int.fract ((w : ℝ) * a) :=
      Int.fract_eq_self.mpr ⟨le_of_lt hdpos, hdlt1⟩
    have hfrac : Int.fract (((j - w : ℕ) : ℝ) * a)
        = Int.fract ((j : ℝ) * a) - Int.fract ((w : ℝ) * a) := by
      rw [hcast, ← fract_sub_fract_eq]; exact hself
    have hval_pos : 0 < Int.fract (((j - w : ℕ) : ℝ) * a) := by rw [hfrac]; exact hdpos
    have hD1' := fract_sub_etaNeg_ge a h2 hdN hval_pos
    rw [hfrac, hwval] at hD1'
    linarith
  · have hwgt : j < w := by
      rcases eq_or_lt_of_le hwge with he | hgt
      · exfalso; rw [he, hwval] at hhi; exact lt_irrefl z hhi
      · exact hgt
    have hcm := compl_mem_orbit_of_index_gt a N hwgt hwN hlt'
    rw [hwval] at hcm
    have h1mη : 0 < 1 - etaNeg a N := posOrbit_pos a N (max_posOrbit_mem a h2)
    have hgt1mη : 1 - etaNeg a N < 1 - (Int.fract ((j : ℝ) * a) - z) := by linarith
    have hpos : 0 < 1 - (Int.fract ((j : ℝ) * a) - z) := by linarith
    have hposorb : 1 - (Int.fract ((j : ℝ) * a) - z) ∈ posOrbit a N := by
      rw [mem_posOrbit_iff]; exact ⟨ne_of_gt hpos, hcm⟩
    have hle := le_one_sub_etaNeg a h2 hposorb
    linarith

/-- **Case B (backward): an index `j'` of `v' = sortedVal (i+1)` with `j' + m⁻ < N`
    forces gap `= η⁻`.**
@isnad1 id=eq.4h4v.s6.78ac59369ba8 from=translated src=- shape=bcf9ac2f vocab=33be0aea
-/
theorem gap_eq_etaNeg (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {i : ℕ}
    (hi : i + 1 < orbitCard a N)
    {j' : ℕ} (hjfr : Int.fract ((j' : ℝ) * a) = sortedVal a N (i + 1))
    (hjN : j' + mMinus a N h2 < N) :
    gapAt a N i = etaNeg a N := by
  set v := sortedVal a N i with hv
  set v' := sortedVal a N (i + 1) with hv'
  have hvmem : v ∈ orbit a N := sortedVal_mem a (by omega : i < orbitCard a N)
  have hvv' : v < v' := sortedVal_strictMono a N (Nat.lt_succ_self i) hi
  have hetaneg : 0 < etaNeg a N := etaNeg_pos a h2
  have hvpos : 0 ≤ v := (orbit_subset_Ico a N (Finset.mem_coe.mpr hvmem)).1
  have hv'lt1 : v' < 1 := (orbit_subset_Ico a N (Finset.mem_coe.mpr (sortedVal_mem a hi))).2
  have hge : v ≤ v' - etaNeg a N := by
    by_contra hc
    push Not at hc
    exact noPointBetween_neg a h2 hjN hvmem (by rw [hjfr]; exact hc) (by rw [hjfr]; exact hvv')
  have hge0 : etaNeg a N ≤ v' := by
    by_contra hc
    push Not at hc
    exact noPointBetween_neg a h2 hjN hvmem (by rw [hjfr]; linarith) (by rw [hjfr]; exact hvv')
  have hmem : v' - etaNeg a N ∈ orbit a N := by
    have hms : Int.fract (((j' + mMinus a N h2 : ℕ) : ℝ) * a) ∈ orbit a N :=
      (mem_orbit_iff a N _).mpr ⟨_, hjN, rfl⟩
    rw [fract_index_shift_neg a h2 j', hjfr] at hms
    have hcompute : Int.fract (v' + (1 - etaNeg a N)) = v' - etaNeg a N := by
      rw [show v' + (1 - etaNeg a N) = (v' - etaNeg a N) + ((1 : ℤ) : ℝ) by push_cast; ring,
        Int.fract_add_intCast]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hcompute] at hms
    exact hms
  have hle : v' - etaNeg a N ≤ v := by
    by_contra hc
    push Not at hc
    exact no_orbit_strictly_between a N hi hmem hc (by linarith)
  have heq : v = v' - etaNeg a N := le_antisymm hge hle
  unfold gapAt
  rw [← hv, ← hv', heq]; ring

/-! ## The corner case `η⁺ + η⁻` — completing the classification

The remaining case of the three-gap bound: the *corner*, where both first returns
fall off the end (`canMul v + m⁺ ≥ N` and `canMul v' + m⁻ ≥ N`).  Then the gap is
`η⁺ + η⁻` (`corner_gap`).  The argument:

* `corner_canMul_lt_mMinus` (`hP1 : canMul v < m⁻`): if `j ≥ m⁻` then `v+η⁻` would
  be the successor `v'`, forcing `canMul v' + m⁻ < N`, contradicting `hB`.
* upper bound `v' ≤ v+η⁺+η⁻`: realise `q := v+η⁺+η⁻` as `{(canMul v + m⁺ - m⁻)·a}`
  (index `< N` by `hP1`).
* lower bound: no orbit point in `(v, v+η⁺+η⁻)`, split as L1 `(v, v+η⁺)`,
  L2 `v+η⁺ ∉ orbit a N`, L3 `(v+η⁺, q)`.

L1/L3 (`corner_noPoint_lo` / `corner_noPoint_hi`) use the *M-circle* `M := m⁺ + m⁻`:
`orbit a N ⊆ orbit a M`, the returns are unchanged (`no_new_below_etaPos`,
`no_new_above_etaNeg`, `etaPos_eq_extend`, `etaNeg_eq_extend`), and `hP1` keeps the
shifted indices `< M`.

L2 is closed WITHOUT induction (uniform in `a`, rational or irrational): if
`v+η⁺ = {k·a}` with `k ≥ j` then `m⁺ ≤ k-j`, so `k ≥ j+m⁺ ≥ N`, impossible; if
`k < j` then `d := j+m⁺-k` is a period (`{d·a}=0`) with `m⁺ < d < m⁺+m⁻`,
contradicting minimality of `m⁻` (the max `1-η⁻` at index `m⁻-d`) or of `m⁺`
(`η⁺=η⁻`, then at index `d-m⁻`).  This replaces van Ravenstein / Mayero's
induction-on-`N` and avoids their irrational-only restriction. -/

/-- **Backward index shift by `m⁻`.**  For `m⁻ ≤ k`, subtracting the canonical
    `m⁻` from the index `k` rotates the value by `-(1-η⁻)` mod 1.
@isnad1 id=eq.2h3v.s6.b5d4f1ccb466 from=translated src=- shape=b777659c vocab=52443ab4
-/
theorem fract_sub_mMinus (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {k : ℕ}
    (hk : mMinus a N h2 ≤ k) :
    Int.fract (((k - mMinus a N h2 : ℕ) : ℝ) * a)
      = Int.fract (Int.fract ((k : ℝ) * a) - (1 - etaNeg a N)) := by
  have hcast : ((k - mMinus a N h2 : ℕ) : ℝ) * a
      = (k : ℝ) * a - (mMinus a N h2 : ℝ) * a := by
    rw [Nat.cast_sub hk]; ring
  rw [hcast, ← fract_sub_fract_eq, fract_mMinus a N h2]

/-- **Minimality of the canonical multiplier.**  Any in-range index `c < N` whose
    rotation value is `p` is at least `canMul a N p`.
@isnad1 id=le.3h4v.s5.6f4f792ed35b from=translated src=- shape=908131e9 vocab=c2005305
-/
theorem canMul_le (a : ℝ) (N : ℕ) {p : ℝ} (hp : p ∈ orbit a N) {c : ℕ}
    (hc : c < N) (hcval : Int.fract ((c : ℝ) * a) = p) : canMul a N p hp ≤ c := by
  unfold canMul
  exact Finset.min'_le _ _ ((mem_mulFiber_iff a N p c).mpr ⟨hc, hcval⟩)

/-- **Forward index shift by `m⁺`.**  For `m⁺ ≤ k`, subtracting the canonical `m⁺`
    from the index `k` rotates the value by `-η⁺` mod 1.
@isnad1 id=eq.2h3v.s6.072f295064e4 from=translated src=- shape=2c379561 vocab=bdbae934
-/
theorem fract_sub_mPlus (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {k : ℕ}
    (hk : mPlus a N h2 ≤ k) :
    Int.fract (((k - mPlus a N h2 : ℕ) : ℝ) * a)
      = Int.fract (Int.fract ((k : ℝ) * a) - etaPos a N) := by
  have hcast : ((k - mPlus a N h2 : ℕ) : ℝ) * a
      = (k : ℝ) * a - (mPlus a N h2 : ℝ) * a := by
    rw [Nat.cast_sub hk]; ring
  rw [hcast, ← fract_sub_fract_eq, fract_mPlus a N h2]

/-- **Returns are preserved when extending the orbit to `M = m⁺ + m⁻` indices
    (positive return).**  No new index `k ∈ [N, m⁺+m⁻)` produces a positive value
    below `η⁺`.  (Key step of the M-circle route to the corner bound: a value
    `s = {k·a} ∈ (0, η⁺)` would force `{(k-m⁻)·a} = η⁺`, hence `m⁺ ≤ k-m⁻` by
    minimality, i.e. `k ≥ m⁺+m⁻`, contradiction.)
@isnad1 id=le.4h3v.s6.c25f143ffc96 from=translated src=- shape=c72431bc vocab=3baf573e
-/
theorem no_new_below_etaPos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N)
    {k : ℕ} (hkN : N ≤ k) (hkM : k < mPlus a N h2 + mMinus a N h2)
    (hpos : 0 < Int.fract ((k : ℝ) * a)) :
    etaPos a N ≤ Int.fract ((k : ℝ) * a) := by
  by_contra hcon
  push Not at hcon
  set s := Int.fract ((k : ℝ) * a) with hs
  have hep : 0 < etaPos a N := etaPos_pos a h2
  have hep1 : etaPos a N < 1 := posOrbit_lt_one a N (etaPos_mem a h2)
  have hen : 0 < etaNeg a N := etaNeg_pos a h2
  have hmPlt : mPlus a N h2 < N := mPlus_lt a N h2
  have hmMlt : mMinus a N h2 < N := mMinus_lt a N h2
  have hsum : etaPos a N + etaNeg a N ≤ 1 := by
    have := le_one_sub_etaNeg a h2 (etaPos_mem a h2); linarith
  -- s + η⁻ = {(k - m⁻)·a} ∈ orbit, hence ≥ η⁺
  have hval1 : Int.fract (((k - mMinus a N h2 : ℕ) : ℝ) * a) = s + etaNeg a N := by
    rw [fract_sub_mMinus a h2 (by omega : mMinus a N h2 ≤ k), ← hs,
      show s - (1 - etaNeg a N) = (s + etaNeg a N) + ((-1 : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hmem1 : s + etaNeg a N ∈ orbit a N :=
    hval1 ▸ (mem_orbit_iff a N _).mpr ⟨k - mMinus a N h2, by omega, rfl⟩
  have hge1 : etaPos a N ≤ s + etaNeg a N :=
    no_orbit_below_etaPos a h2 hmem1 (by linarith)
  -- 1-(η⁺-s) = {(k - m⁺)·a} ∈ orbit, hence ≤ 1-η⁻, giving s ≤ η⁺-η⁻
  have hval2 : Int.fract (((k - mPlus a N h2 : ℕ) : ℝ) * a) = 1 - (etaPos a N - s) := by
    rw [fract_sub_mPlus a h2 (by omega : mPlus a N h2 ≤ k), ← hs,
      show s - etaPos a N = (1 - (etaPos a N - s)) + ((-1 : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hmem2 : 1 - (etaPos a N - s) ∈ orbit a N :=
    hval2 ▸ (mem_orbit_iff a N _).mpr ⟨k - mPlus a N h2, by omega, rfl⟩
  have hle2 : 1 - (etaPos a N - s) ≤ 1 - etaNeg a N :=
    le_one_sub_etaNeg a h2 (by rw [mem_posOrbit_iff]; exact ⟨ne_of_gt (by linarith), hmem2⟩)
  -- combine: s + η⁻ = η⁺, so {(k-m⁻)·a} = η⁺, so m⁺ ≤ k-m⁻, i.e. k ≥ m⁺+m⁻
  have hs_eq : s + etaNeg a N = etaPos a N := by linarith
  have hmin : mPlus a N h2 ≤ k - mMinus a N h2 := by
    have h := canMul_le a N (posOrbit_subset_orbit a N (etaPos_mem a h2))
      (show k - mMinus a N h2 < N by omega) (by rw [hval1, hs_eq])
    simpa only [mPlus] using h
  omega

/-- **Returns are preserved when extending the orbit to `M = m⁺ + m⁻` indices
    (negative return).**  No new index `k ∈ [N, m⁺+m⁻)` produces a value in the top
    band `(1-η⁻, 1)`.  Mirror of `no_new_below_etaPos`.
@isnad1 id=le.3h3v.s6.9491f4beea9c from=translated src=- shape=ff3947d1 vocab=228efe4d
-/
theorem no_new_above_etaNeg (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N)
    {k : ℕ} (hkN : N ≤ k) (hkM : k < mPlus a N h2 + mMinus a N h2) :
    Int.fract ((k : ℝ) * a) ≤ 1 - etaNeg a N := by
  by_contra hcon
  push Not at hcon
  set s := Int.fract ((k : ℝ) * a) with hs
  have hs1 : s < 1 := Int.fract_lt_one _
  have hep : 0 < etaPos a N := etaPos_pos a h2
  have hep1 : etaPos a N < 1 := posOrbit_lt_one a N (etaPos_mem a h2)
  have hen : 0 < etaNeg a N := etaNeg_pos a h2
  have hmPlt : mPlus a N h2 < N := mPlus_lt a N h2
  have hmMlt : mMinus a N h2 < N := mMinus_lt a N h2
  have hsum : etaPos a N + etaNeg a N ≤ 1 := by
    have := le_one_sub_etaNeg a h2 (etaPos_mem a h2); linarith
  -- s - η⁺ = {(k - m⁺)·a} ∈ orbit, hence ≤ 1-η⁻
  have hval1 : Int.fract (((k - mPlus a N h2 : ℕ) : ℝ) * a) = s - etaPos a N := by
    rw [fract_sub_mPlus a h2 (by omega : mPlus a N h2 ≤ k), ← hs]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hmem1 : s - etaPos a N ∈ orbit a N :=
    hval1 ▸ (mem_orbit_iff a N _).mpr ⟨k - mPlus a N h2, by omega, rfl⟩
  have hle1 : s - etaPos a N ≤ 1 - etaNeg a N :=
    le_one_sub_etaNeg a h2 (by rw [mem_posOrbit_iff]; exact ⟨ne_of_gt (by linarith), hmem1⟩)
  -- s - (1-η⁻) = {(k - m⁻)·a} ∈ orbit, positive, hence ≥ η⁺
  have hval2 : Int.fract (((k - mMinus a N h2 : ℕ) : ℝ) * a) = s - (1 - etaNeg a N) := by
    rw [fract_sub_mMinus a h2 (by omega : mMinus a N h2 ≤ k), ← hs]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hmem2 : s - (1 - etaNeg a N) ∈ orbit a N :=
    hval2 ▸ (mem_orbit_iff a N _).mpr ⟨k - mMinus a N h2, by omega, rfl⟩
  have hge2 : etaPos a N ≤ s - (1 - etaNeg a N) :=
    no_orbit_below_etaPos a h2 hmem2 (by linarith)
  -- combine: s - η⁺ = 1-η⁻, so {(k-m⁺)·a} = 1-η⁻ (= max), so m⁻ ≤ k-m⁺, k ≥ m⁺+m⁻
  have hs_eq : s - etaPos a N = 1 - etaNeg a N := by linarith
  have hmin : mMinus a N h2 ≤ k - mPlus a N h2 := by
    have h := canMul_le a N (posOrbit_subset_orbit a N (max_posOrbit_mem a h2))
      (show k - mPlus a N h2 < N by omega) (by rw [hval1, hs_eq])
    simpa only [mMinus] using h
  omega

/-! ## M-circle infrastructure (orbit extension `N ↦ M = m⁺ + m⁻`)

Monotonicity of the orbit in the index count, and the fact that the two returns
`η⁺, η⁻` are *unchanged* when the orbit is extended from `N` to `M = m⁺ + m⁻`
(no new index in `[N, M)` produces a smaller positive value or a larger value).
These let the corner "no point in the big gap" arguments (`corner_noPoint_lo/hi`)
borrow the in-range first-return machinery in the larger circle. -/

/-- The orbit grows with the index count.
@isnad1 id=le.1h3v.s4.350f9ca44b96 from=translated src=- shape=9a6dd29f vocab=9da35000
-/
theorem orbit_mono (a : ℝ) {N M : ℕ} (h : N ≤ M) : orbit a N ⊆ orbit a M := by
  intro x hx
  rw [mem_orbit_iff] at hx ⊢
  obtain ⟨k, hk, hkval⟩ := hx
  exact ⟨k, lt_of_lt_of_le hk h, hkval⟩

/--
@isnad1 id=le.1h3v.s4.9da9a22a6be1 from=translated src=- shape=008790cb vocab=961fe64a
-/
theorem orbitCard_mono (a : ℝ) {N M : ℕ} (h : N ≤ M) : orbitCard a N ≤ orbitCard a M :=
  Finset.card_le_card (orbit_mono a h)

/--
@isnad1 id=le.1h3v.s4.2243b3417b8f from=translated src=- shape=9a6dd29f vocab=9feb747e
-/
theorem posOrbit_mono (a : ℝ) {N M : ℕ} (h : N ≤ M) : posOrbit a N ⊆ posOrbit a M := by
  intro x hx
  rw [mem_posOrbit_iff] at hx ⊢
  exact ⟨hx.1, orbit_mono a h hx.2⟩

/-- **Positive return preserved under extension.**  If every new index `k ∈ [N, M)`
    avoids the band `(0, η⁺)`, then `η⁺` is unchanged from `N` to `M`.
@isnad1 id=eq.4h3v.s6.479212139ff6 from=translated src=- shape=751dfa60 vocab=6b85362c
-/
theorem etaPos_eq_extend (a : ℝ) {N M : ℕ} (h2 : 2 ≤ orbitCard a N) (hNM : N ≤ M)
    (hM2 : 2 ≤ orbitCard a M)
    (hnew : ∀ k, N ≤ k → k < M → 0 < Int.fract ((k : ℝ) * a) →
      etaPos a N ≤ Int.fract ((k : ℝ) * a)) :
    etaPos a M = etaPos a N := by
  refine le_antisymm ?_ ?_
  · exact etaPos_le a hM2 (posOrbit_mono a hNM (etaPos_mem a h2))
  · have hmem := etaPos_mem a hM2
    have hpos : 0 < etaPos a M := posOrbit_pos a M hmem
    have horb : etaPos a M ∈ orbit a M := posOrbit_subset_orbit a M hmem
    obtain ⟨k, hk, hkval⟩ := (mem_orbit_iff a M _).mp horb
    rcases Nat.lt_or_ge k N with hkN | hkN
    · exact no_orbit_below_etaPos a h2 ((mem_orbit_iff a N _).mpr ⟨k, hkN, hkval⟩) hpos
    · have := hnew k hkN hk (by rw [hkval]; exact hpos); rwa [hkval] at this

/-- **Negative return preserved under extension.**  If every new index `k ∈ [N, M)`
    avoids the top band `(1 - η⁻, 1)`, then `η⁻` is unchanged from `N` to `M`.
@isnad1 id=eq.4h3v.s6.5a2c0070c919 from=translated src=- shape=f6222571 vocab=a51a789e
-/
theorem etaNeg_eq_extend (a : ℝ) {N M : ℕ} (h2 : 2 ≤ orbitCard a N) (hNM : N ≤ M)
    (hM2 : 2 ≤ orbitCard a M)
    (hnew : ∀ k, N ≤ k → k < M → Int.fract ((k : ℝ) * a) ≤ 1 - etaNeg a N) :
    etaNeg a M = etaNeg a N := by
  refine le_antisymm ?_ ?_
  · have : (1 : ℝ) - etaNeg a N ≤ 1 - etaNeg a M :=
      le_one_sub_etaNeg a hM2 (posOrbit_mono a hNM (max_posOrbit_mem a h2))
    linarith
  · have hmem := max_posOrbit_mem a hM2
    have hpos : 0 < 1 - etaNeg a M := posOrbit_pos a M hmem
    have horb : (1 - etaNeg a M) ∈ orbit a M := posOrbit_subset_orbit a M hmem
    obtain ⟨k, hk, hkval⟩ := (mem_orbit_iff a M _).mp horb
    have hle : (1 : ℝ) - etaNeg a M ≤ 1 - etaNeg a N := by
      rcases Nat.lt_or_ge k N with hkN | hkN
      · refine le_one_sub_etaNeg a h2 ?_
        rw [mem_posOrbit_iff]
        exact ⟨ne_of_gt hpos, (mem_orbit_iff a N _).mpr ⟨k, hkN, hkval⟩⟩
      · have := hnew k hkN hk; rwa [hkval] at this
    linarith

/-- **Corner discriminant `hP1` (independent of the lower bound).**  In the corner,
    the canonical index `j = canMul v` of the left point satisfies `j < m⁻`.

    Proof: if `j ≥ m⁻`, then `w := v + η⁻ = {(j-m⁻)·a} ∈ orbit a N` (a valid index
    `< N`).  As `w` lies in range with `canMul w + m⁻ ≤ j < N`, case B
    (`gap_eq_etaNeg`) shows the predecessor of `w` is `w - η⁻ = v`; hence `w` is the
    successor `v'` of `v`, so `v' = v + η⁻` and `canMul v' ≤ j - m⁻`, giving
    `canMul v' + m⁻ ≤ j < N` — contradicting the corner hypothesis `hB`.
@isnad1 id=lt.5h3v.s7.8f511b2f81d4 from=translated src=- shape=f9f421e1 vocab=ea0d3295
-/
theorem corner_canMul_lt_mMinus (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {i : ℕ}
    (hi : i + 1 < orbitCard a N)
    (hvmem : sortedVal a N i ∈ orbit a N)
    (hv'mem : sortedVal a N (i + 1) ∈ orbit a N)
    (hB : ¬ (canMul a N (sortedVal a N (i + 1)) hv'mem + mMinus a N h2 < N)) :
    canMul a N (sortedVal a N i) hvmem < mMinus a N h2 := by
  have hN : 0 < N := pos_of_two_le_orbitCard a h2
  set v := sortedVal a N i with hv
  set j := canMul a N v hvmem with hj
  by_contra hcon
  push Not at hcon
  have hjfr : Int.fract ((j : ℝ) * a) = v := fract_canMul a N hvmem
  have hjN : j < N := canMul_lt a N hvmem
  have hen : 0 < etaNeg a N := etaNeg_pos a h2
  have hvv' : v < sortedVal a N (i + 1) := sortedVal_strictMono a N (Nat.lt_succ_self i) hi
  have hv0 : 0 ≤ v := (orbit_subset_Ico a N (Finset.mem_coe.mpr hvmem)).1
  have hv'pos : 0 < sortedVal a N (i + 1) := lt_of_le_of_lt hv0 hvv'
  have hv'le : sortedVal a N (i + 1) ≤ 1 - etaNeg a N :=
    le_one_sub_etaNeg a h2 (by rw [mem_posOrbit_iff]; exact ⟨ne_of_gt hv'pos, hv'mem⟩)
  have hvmax : v < 1 - etaNeg a N := lt_of_lt_of_le hvv' hv'le
  -- w := v + η⁻ realised at index j - m⁻
  have hwval : Int.fract (((j - mMinus a N h2 : ℕ) : ℝ) * a) = v + etaNeg a N := by
    rw [fract_sub_mMinus a h2 hcon, hjfr,
      show v - (1 - etaNeg a N) = (v + etaNeg a N) + ((-1 : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hwmem : v + etaNeg a N ∈ orbit a N :=
    hwval ▸ (mem_orbit_iff a N _).mpr ⟨j - mMinus a N h2, by omega, rfl⟩
  obtain ⟨s, hs, hsval⟩ := exists_index_of_mem_orbit a N hwmem
  -- s ≥ 1 since sortedVal 0 = 0 < v + η⁻
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with rfl | hsp
    · rw [sortedVal_zero_eq_zero a hN] at hsval; linarith
    · exact hsp
  -- canMul w is in range: canMul w + m⁻ ≤ j < N
  set jw := canMul a N (v + etaNeg a N) hwmem with hjw
  have hjwle : jw ≤ j - mMinus a N h2 := canMul_le a N hwmem (by omega) hwval
  have hjwN : jw + mMinus a N h2 < N := by omega
  -- case B at index s-1: gap to the left of w (= sortedVal s) is η⁻
  have hsval' : Int.fract ((jw : ℝ) * a) = sortedVal a N ((s - 1) + 1) := by
    rw [show (s - 1) + 1 = s by omega, hsval]; exact fract_canMul a N hwmem
  have hgap := gap_eq_etaNeg a h2 (by omega : (s - 1) + 1 < orbitCard a N) hsval' hjwN
  -- so sortedVal (s-1) = w - η⁻ = v
  have hpred : sortedVal a N (s - 1) = v := by
    unfold gapAt at hgap
    rw [show (s - 1) + 1 = s by omega, hsval] at hgap
    linarith
  -- hence s - 1 = i (sortedVal injective on valid indices)
  have hsi : s - 1 = i := by
    by_contra hne
    rcases Nat.lt_or_ge (s - 1) i with h | h
    · have := sortedVal_strictMono a N h (show i < orbitCard a N by omega)
      rw [hpred] at this; exact (lt_irrefl v) this
    · have h' : i < s - 1 := lt_of_le_of_ne h (Ne.symm hne)
      have := sortedVal_strictMono a N h' (show s - 1 < orbitCard a N by omega)
      rw [hpred] at this; exact (lt_irrefl v) this
  -- so sortedVal (i+1) = w = v + η⁻, and canMul (sortedVal (i+1)) ≤ j - m⁻,
  -- contradicting hB
  have hv'idx : Int.fract (((j - mMinus a N h2 : ℕ) : ℝ) * a) = sortedVal a N (i + 1) := by
    rw [hwval, ← (show s = i + 1 by omega)]; exact hsval.symm
  have hle : canMul a N (sortedVal a N (i + 1)) hv'mem ≤ j - mMinus a N h2 :=
    canMul_le a N hv'mem (by omega) hv'idx
  exact hB (by omega)

/-- **L1 — no orbit point in `(v, v + η⁺)` (corner).**  Direct difference
    extraction: a point `z = {w·a}` with `v < z < v + η⁺` gives, when `w ≥ j`, a
    positive value `z - v < η⁺` in `orbit a N` (contra `η⁺` minimal); and when
    `w < j`, a positive value `η⁺ - (z-v) < η⁺` in the *extended* orbit `orbit a M`
    (`M = m⁺ + m⁻`) at index `(j-w) + m⁺ < M`, contradicting minimality of
    `etaPos a M = etaPos a N`.  The discriminant `hP1 : j < m⁻` makes the shifted
    index stay in range `< M`.
@isnad1 id=false.7h4v.s6.ba3f31540ee9 from=translated src=- shape=35b55e47 vocab=8a088415
-/
theorem corner_noPoint_lo (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {i : ℕ}
    (hvmem : sortedVal a N i ∈ orbit a N)
    (hP1 : canMul a N (sortedVal a N i) hvmem < mMinus a N h2)
    (hA : N ≤ canMul a N (sortedVal a N i) hvmem + mPlus a N h2)
    {z : ℝ} (hz : z ∈ orbit a N)
    (hlo : sortedVal a N i < z) (hhi : z < sortedVal a N i + etaPos a N) : False := by
  set v := sortedVal a N i with hv
  set j := canMul a N v hvmem with hj
  have hjfr : Int.fract ((j : ℝ) * a) = v := fract_canMul a N hvmem
  have hjN : j < N := canMul_lt a N hvmem
  have hep : 0 < etaPos a N := etaPos_pos a h2
  have hep1 : etaPos a N < 1 := posOrbit_lt_one a N (etaPos_mem a h2)
  have hmP : mPlus a N h2 < N := mPlus_lt a N h2
  have hmM : mMinus a N h2 < N := mMinus_lt a N h2
  set M := mPlus a N h2 + mMinus a N h2 with hMdef
  have hNM : N ≤ M := by omega
  have hM2 : 2 ≤ orbitCard a M := le_trans h2 (orbitCard_mono a hNM)
  have hetaPosM : etaPos a M = etaPos a N :=
    etaPos_eq_extend a h2 hNM hM2 (fun k hk1 hk2 hk3 => no_new_below_etaPos a h2 hk1 hk2 hk3)
  obtain ⟨w, hwN, hwval⟩ := (mem_orbit_iff a N z).mp hz
  rcases Nat.lt_or_ge w j with hwlt | hwge
  · -- w < j : η⁺ - (z-v) ∈ orbit a M, positive and < η⁺
    have hfracjw : Int.fract (((j - w : ℕ) : ℝ) * a) = 1 - (z - v) := by
      have hcast : ((j - w : ℕ) : ℝ) * a = (j : ℝ) * a - (w : ℝ) * a := by
        rw [Nat.cast_sub (le_of_lt hwlt)]; ring
      rw [hcast, ← fract_sub_fract_eq, hjfr, hwval,
        show v - z = (1 - (z - v)) + ((-1 : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hidxval : Int.fract ((((j - w) + mPlus a N h2 : ℕ) : ℝ) * a) = etaPos a N - (z - v) := by
      rw [fract_index_shift a h2 (j - w), hfracjw,
        show (1 - (z - v)) + etaPos a N = (etaPos a N - (z - v)) + ((1 : ℤ) : ℝ) by push_cast; ring,
        Int.fract_add_intCast]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hmemM : etaPos a N - (z - v) ∈ orbit a M := by
      rw [← hidxval]
      exact (mem_orbit_iff a M _).mpr ⟨(j - w) + mPlus a N h2, by omega, rfl⟩
    have := no_orbit_below_etaPos a hM2 hmemM (by linarith)
    rw [hetaPosM] at this; linarith
  · -- w ≥ j : z - v ∈ orbit a N, positive and < η⁺
    have hlt' : Int.fract ((j : ℝ) * a) < Int.fract ((w : ℝ) * a) := by rw [hjfr, hwval]; linarith
    have hdmem := sub_mem_orbit_of_index_le a N hwge hwN hlt'
    rw [hwval, hjfr] at hdmem
    have := no_orbit_below_etaPos a h2 hdmem (by linarith)
    linarith

/-- **L3 — no orbit point in `(v + η⁺, v + η⁺ + η⁻)` (corner).**  Mirror of `L1`:
    the point `p₁ = v + η⁺ = {(j+m⁺)·a} ∈ orbit a M`.  A point `z` with
    `p₁ < z < p₁ + η⁻` has every index `w < N ≤ j + m⁺`, so `{((j+m⁺)-w)·a} = 1 -
    (z - p₁)` lies in `(1 - η⁻, 1) ∩ orbit a M`, exceeding the maximum `1 - η⁻` of
    `orbit a M` — contradiction.
@isnad1 id=false.7h4v.s7.e0aafdcf55fd from=translated src=- shape=1cd75592 vocab=83127ba2
-/
theorem corner_noPoint_hi (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {i : ℕ}
    (hvmem : sortedVal a N i ∈ orbit a N)
    (hP1 : canMul a N (sortedVal a N i) hvmem < mMinus a N h2)
    (hA : N ≤ canMul a N (sortedVal a N i) hvmem + mPlus a N h2)
    {z : ℝ} (hz : z ∈ orbit a N)
    (hlo : sortedVal a N i + etaPos a N < z)
    (hhi : z < sortedVal a N i + etaPos a N + etaNeg a N) : False := by
  set v := sortedVal a N i with hv
  set j := canMul a N v hvmem with hj
  have hjfr : Int.fract ((j : ℝ) * a) = v := fract_canMul a N hvmem
  have hjN : j < N := canMul_lt a N hvmem
  have hv0 : 0 ≤ v := (orbit_subset_Ico a N (Finset.mem_coe.mpr hvmem)).1
  have hep : 0 < etaPos a N := etaPos_pos a h2
  have hen : 0 < etaNeg a N := etaNeg_pos a h2
  have hmP : mPlus a N h2 < N := mPlus_lt a N h2
  have hmM : mMinus a N h2 < N := mMinus_lt a N h2
  set M := mPlus a N h2 + mMinus a N h2 with hMdef
  have hNM : N ≤ M := by omega
  have hM2 : 2 ≤ orbitCard a M := le_trans h2 (orbitCard_mono a hNM)
  have hetaNegM : etaNeg a M = etaNeg a N :=
    etaNeg_eq_extend a h2 hNM hM2 (fun k hk1 hk2 => no_new_above_etaNeg a h2 hk1 hk2)
  obtain ⟨w, hwN, hwval⟩ := (mem_orbit_iff a N z).mp hz
  have hz1 : z < 1 := (orbit_subset_Ico a N (Finset.mem_coe.mpr hz)).2
  have hvep1 : v + etaPos a N < 1 := lt_trans hlo hz1
  have hp1val : Int.fract (((j + mPlus a N h2 : ℕ) : ℝ) * a) = v + etaPos a N := by
    rw [fract_index_shift a h2 j, hjfr]
    exact Int.fract_eq_self.mpr ⟨by linarith, hvep1⟩
  have hwlt : w < j + mPlus a N h2 := by omega
  have hfrac : Int.fract ((((j + mPlus a N h2) - w : ℕ) : ℝ) * a) = 1 - (z - (v + etaPos a N)) := by
    have hcast : (((j + mPlus a N h2) - w : ℕ) : ℝ) * a
        = ((j + mPlus a N h2 : ℕ) : ℝ) * a - (w : ℝ) * a := by
      rw [Nat.cast_sub (le_of_lt hwlt)]; ring
    rw [hcast, ← fract_sub_fract_eq, hp1val, hwval,
      show (v + etaPos a N) - z = (1 - (z - (v + etaPos a N))) + ((-1 : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hmemM : 1 - (z - (v + etaPos a N)) ∈ orbit a M := by
    rw [← hfrac]
    exact (mem_orbit_iff a M _).mpr ⟨(j + mPlus a N h2) - w, by omega, rfl⟩
  have hpos : 0 < 1 - (z - (v + etaPos a N)) := by linarith
  have hle := le_one_sub_etaNeg a hM2 (by rw [mem_posOrbit_iff]; exact ⟨ne_of_gt hpos, hmemM⟩)
  rw [hetaNegM] at hle; linarith

/-- **The corner case.**  When both first returns fall off the end
    (`canMul v + m⁺ ≥ N` and `canMul v' + m⁻ ≥ N`), the internal gap is `η⁺ + η⁻`.
    The lower bound `hLower` (no orbit point lies strictly in `(v, v + η⁺ + η⁻)`)
    is proved inline below; the proof is self-contained, with no external input.
@isnad1 id=eq.6h3v.s7.070b8afbf514 from=translated src=- shape=c8810775 vocab=db4ff3c8
-/
theorem corner_gap (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {i : ℕ}
    (hi : i + 1 < orbitCard a N)
    (hvmem : sortedVal a N i ∈ orbit a N)
    (hv'mem : sortedVal a N (i + 1) ∈ orbit a N)
    (hA : ¬ (canMul a N (sortedVal a N i) hvmem + mPlus a N h2 < N))
    (hB : ¬ (canMul a N (sortedVal a N (i + 1)) hv'mem + mMinus a N h2 < N)) :
    gapAt a N i = etaPos a N + etaNeg a N := by
  have hN : 0 < N := pos_of_two_le_orbitCard a h2
  set v := sortedVal a N i with hv
  set v' := sortedVal a N (i + 1) with hv'
  set j := canMul a N v hvmem with hj
  have hjfr : Int.fract ((j : ℝ) * a) = v := by rw [hj]; exact fract_canMul a N hvmem
  have hjN : j < N := by rw [hj]; exact canMul_lt a N hvmem
  have hep : 0 < etaPos a N := etaPos_pos a h2
  have hen : 0 < etaNeg a N := etaNeg_pos a h2
  have hmMlt : mMinus a N h2 < N := mMinus_lt a N h2
  have hmPlt : mPlus a N h2 < N := mPlus_lt a N h2
  have hvv' : v < v' := sortedVal_strictMono a N (Nat.lt_succ_self i) hi
  have hv0 : 0 ≤ v := (orbit_subset_Ico a N (Finset.mem_coe.mpr hvmem)).1
  have hv'lt1 : v' < 1 := (orbit_subset_Ico a N (Finset.mem_coe.mpr hv'mem)).2
  have hv'pos : 0 < v' := lt_of_le_of_lt hv0 hvv'
  have hv'le : v' ≤ 1 - etaNeg a N :=
    le_one_sub_etaNeg a h2 (by rw [mem_posOrbit_iff]; exact ⟨ne_of_gt hv'pos, hv'mem⟩)
  have hv_lt_max : v < 1 - etaNeg a N := lt_of_lt_of_le hvv' hv'le
  -- corner index fact: canMul v + m⁺ ≥ N
  have hAge : N ≤ j + mPlus a N h2 := by omega
  -- hP1 : j < m⁻ — the corner discriminant, proved independently (no circularity).
  have hP1 : j < mMinus a N h2 := corner_canMul_lt_mMinus a h2 hi hvmem hv'mem hB
  -- THE LOWER BOUND, reduced to L2.  No orbit point lies strictly in
  -- `(v, v + η⁺ + η⁻)`: by L1 none in `(v, v+η⁺)`, by L3 none in `(v+η⁺, q)`, so the
  -- successor `v'` (which is `> v` and, if `hLower` failed, `< q`) would have to be
  -- exactly `v + η⁺` — but `v + η⁺ ∉ orbit a N` (L2).  L1/L3 (the M-circle lemmas
  -- above) and L2 (the period argument below) are all proved here, no `sorry`.
  have hLower : v + etaPos a N + etaNeg a N ≤ v' := by
    by_contra hcon
    push Not at hcon
    have hge : v + etaPos a N ≤ v' := by
      by_contra hc
      push Not at hc
      exact corner_noPoint_lo a h2 hvmem hP1 hAge hv'mem hvv' hc
    have hle : v' ≤ v + etaPos a N := by
      by_contra hc
      push Not at hc
      exact corner_noPoint_hi a h2 hvmem hP1 hAge hv'mem hc hcon
    have hv'eq : v' = v + etaPos a N := le_antisymm hle hge
    -- L2: `v + η⁺ ∉ orbit a N` in the corner.
    have hL2 : v + etaPos a N ∉ orbit a N := by
      intro hmem
      obtain ⟨k, hkN, hkval⟩ := (mem_orbit_iff a N _).mp hmem
      rcases Nat.lt_or_ge k j with hkj | hkj
      · -- k < j : `{k·a} = v+η⁺ = {(j+m⁺)·a}` with `k ≠ j+m⁺` forces `d := j+m⁺-k`
        -- to be a PERIOD (`{d·a}=0`), with `m⁺ < d < m⁺+m⁻`.  That contradicts
        -- minimality of `m⁻` (if `d < m⁻`, the max `1-η⁻` appears at index `m⁻-d`)
        -- or of `m⁺` (if `d > m⁻`, then `η⁻ ∈ orbit` and `1-η⁺ ∈ orbit` force
        -- `η⁺ = η⁻`, which then appears at index `d-m⁻ < m⁺`).  Induction-free.
        have hvep1 : v + etaPos a N < 1 := by rw [← hkval]; exact Int.fract_lt_one _
        have hep1 : etaPos a N < 1 := posOrbit_lt_one a N (etaPos_mem a h2)
        have hen1 : etaNeg a N < 1 := by
          have := posOrbit_pos a N (max_posOrbit_mem a h2); linarith
        have hmaxpos : 0 < 1 - etaNeg a N := posOrbit_pos a N (max_posOrbit_mem a h2)
        have hjmp : Int.fract (((j + mPlus a N h2 : ℕ) : ℝ) * a) = v + etaPos a N := by
          rw [fract_index_shift_noWrap a h2 j (by rw [hjfr]; exact hvep1), hjfr]
        set d : ℕ := (j + mPlus a N h2) - k with hd
        have hdpos : 0 < d := by omega
        have hdcast : ((d : ℕ) : ℝ) * a = ((j + mPlus a N h2 : ℕ) : ℝ) * a - (k : ℝ) * a := by
          rw [hd, Nat.cast_sub (by omega)]; ring
        have hd0 : Int.fract ((d : ℝ) * a) = 0 := by
          rw [hdcast, ← fract_sub_fract_eq, hjmp, hkval, sub_self, Int.fract_zero]
        have hdlo : mPlus a N h2 < d := by omega
        have hdhi : d < mPlus a N h2 + mMinus a N h2 := by omega
        -- 1 - η⁺ ∈ orbit a N (index d - m⁺ < m⁻), hence η⁻ ≤ η⁺
        have h1mp : Int.fract (((d - mPlus a N h2 : ℕ) : ℝ) * a) = 1 - etaPos a N := by
          rw [fract_sub_mPlus a h2 (by omega : mPlus a N h2 ≤ d), hd0,
            show (0 : ℝ) - etaPos a N = (1 - etaPos a N) + ((-1 : ℤ) : ℝ) by push_cast; ring,
            Int.fract_add_intCast]
          exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
        have h1mp_mem : 1 - etaPos a N ∈ orbit a N :=
          h1mp ▸ (mem_orbit_iff a N _).mpr ⟨d - mPlus a N h2, by omega, rfl⟩
        have hηle : etaNeg a N ≤ etaPos a N := by
          have := le_one_sub_etaNeg a h2 (by
            rw [mem_posOrbit_iff]; exact ⟨ne_of_gt (by linarith), h1mp_mem⟩)
          linarith
        rcases Nat.lt_trichotomy d (mMinus a N h2) with hdm | hdm | hdm
        · -- d < m⁻ : the max `1-η⁻` occurs at index m⁻-d < m⁻, contra `canMul = m⁻`
          have hmax : Int.fract (((mMinus a N h2 - d : ℕ) : ℝ) * a) = 1 - etaNeg a N := by
            have hcast : ((mMinus a N h2 - d : ℕ) : ℝ) * a
                = (mMinus a N h2 : ℝ) * a - (d : ℝ) * a := by
              rw [Nat.cast_sub (le_of_lt hdm)]; ring
            rw [hcast, ← fract_sub_fract_eq, fract_mMinus a N h2, hd0, sub_zero]
            exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
          have hmaxmem : (1 - etaNeg a N) ∈ orbit a N :=
            hmax ▸ (mem_orbit_iff a N _).mpr ⟨mMinus a N h2 - d, by omega, rfl⟩
          have hb : mMinus a N h2 ≤ mMinus a N h2 - d :=
            canMul_le a N hmaxmem (by omega) hmax
          omega
        · -- d = m⁻ : but {m⁻·a} = 1-η⁻ > 0, contradicting {d·a} = 0
          rw [hdm, fract_mMinus a N h2] at hd0; linarith
        · -- d > m⁻ : η⁻ ∈ orbit (index d-m⁻ < m⁺); with η⁻ ≤ η⁺ get η⁺ = η⁻, contra `canMul = m⁺`
          have hηm : Int.fract (((d - mMinus a N h2 : ℕ) : ℝ) * a) = etaNeg a N := by
            rw [fract_sub_mMinus a h2 (le_of_lt hdm), hd0,
              show (0 : ℝ) - (1 - etaNeg a N) = etaNeg a N + ((-1 : ℤ) : ℝ) by push_cast; ring,
              Int.fract_add_intCast]
            exact Int.fract_eq_self.mpr ⟨le_of_lt hen, by linarith⟩
          have hηmem : etaNeg a N ∈ orbit a N :=
            hηm ▸ (mem_orbit_iff a N _).mpr ⟨d - mMinus a N h2, by omega, rfl⟩
          have heq : etaPos a N = etaNeg a N :=
            le_antisymm (no_orbit_below_etaPos a h2 hηmem hen) hηle
          have hηm' : Int.fract (((d - mMinus a N h2 : ℕ) : ℝ) * a) = etaPos a N := by
            rw [hηm, heq]
          have hb : mPlus a N h2 ≤ d - mMinus a N h2 :=
            canMul_le a N (posOrbit_subset_orbit a N (etaPos_mem a h2)) (by omega) hηm'
          omega
      · -- k ≥ j : `{(k-j)·a} = η⁺`, so `m⁺ ≤ k - j`, i.e. `k ≥ j + m⁺ ≥ N` — but
        -- `k < N`.  (This is exactly where `hA` bites.)
        have hep1 : etaPos a N < 1 := posOrbit_lt_one a N (etaPos_mem a h2)
        have hfr : Int.fract (((k - j : ℕ) : ℝ) * a) = etaPos a N := by
          have hcast : ((k - j : ℕ) : ℝ) * a = (k : ℝ) * a - (j : ℝ) * a := by
            rw [Nat.cast_sub hkj]; ring
          rw [hcast, ← fract_sub_fract_eq, hkval, hjfr,
            show (v + etaPos a N) - v = etaPos a N by ring]
          exact Int.fract_eq_self.mpr ⟨le_of_lt hep, hep1⟩
        have hmem' : etaPos a N ∈ orbit a N := posOrbit_subset_orbit a N (etaPos_mem a h2)
        have hle : mPlus a N h2 ≤ k - j := by
          have := canMul_le a N hmem' (show k - j < N by omega) hfr
          simpa only [mPlus] using this
        omega
    exact hL2 (hv'eq ▸ hv'mem)
  have hP2 : v + etaPos a N + etaNeg a N < 1 := lt_of_le_of_lt hLower hv'lt1
  have hvep1 : v + etaPos a N < 1 := by linarith
  -- construct q = v + η⁺ + η⁻ ∈ orbit, via index (j + m⁺) - m⁻ < N
  have hkcN : (j + mPlus a N h2) - mMinus a N h2 < N := by omega
  have hqval : Int.fract ((((j + mPlus a N h2) - mMinus a N h2 : ℕ) : ℝ) * a)
      = v + etaPos a N + etaNeg a N := by
    rw [fract_sub_mMinus a h2 (by omega : mMinus a N h2 ≤ j + mPlus a N h2),
      fract_index_shift a h2 j, hjfr, Int.fract_eq_self.mpr ⟨by linarith, hvep1⟩,
      show v + etaPos a N - (1 - etaNeg a N)
          = (v + etaPos a N + etaNeg a N) + ((-1 : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, hP2⟩
  have hq : v + etaPos a N + etaNeg a N ∈ orbit a N := by
    rw [← hqval]
    exact (mem_orbit_iff a N _).mpr ⟨_, hkcN, rfl⟩
  -- upper bound: v' ≤ q (else q is strictly between the consecutive v, v')
  have hUpper : v' ≤ v + etaPos a N + etaNeg a N := by
    by_contra hcon
    push Not at hcon
    exact no_orbit_strictly_between a N hi hq (by linarith) hcon
  have heq : v' = v + etaPos a N + etaNeg a N := le_antisymm hUpper hLower
  unfold gapAt
  rw [← hv, ← hv', heq]; ring

/-- **The first-return classification.**  Every internal gap is `η⁺`, `η⁻`, or
    `η⁺ + η⁻`: case A (`gap_eq_etaPos`) when `canMul v + m⁺ < N`, case B
    (`gap_eq_etaNeg`) when `canMul v' + m⁻ < N`, and the corner (`corner_gap`)
    otherwise.  (No `i = 0` special case is needed: there `canMul v = 0` and
    `m⁺ < N`, so case A always fires.)
@isnad1 id=mem.2h3v.s6.5ba0360c4c32 from=translated src=- shape=ce40807e vocab=9f65af1a
-/
theorem neighbour_gap_in_returns (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N)
    {i : ℕ} (hi : i + 1 < orbitCard a N) :
    gapAt a N i ∈ ({etaPos a N, etaNeg a N, etaPos a N + etaNeg a N} : Finset ℝ) := by
  have hvmem : sortedVal a N i ∈ orbit a N := sortedVal_mem a (by omega : i < orbitCard a N)
  have hv'mem : sortedVal a N (i + 1) ∈ orbit a N := sortedVal_mem a hi
  have hjvfr : Int.fract ((canMul a N (sortedVal a N i) hvmem : ℝ) * a) = sortedVal a N i :=
    fract_canMul a N hvmem
  have hjv'fr : Int.fract ((canMul a N (sortedVal a N (i + 1)) hv'mem : ℝ) * a)
      = sortedVal a N (i + 1) := fract_canMul a N hv'mem
  by_cases hA : canMul a N (sortedVal a N i) hvmem + mPlus a N h2 < N
  · rw [gap_eq_etaPos a h2 hi hjvfr hA]
    exact Finset.mem_insert_self _ _
  · by_cases hB : canMul a N (sortedVal a N (i + 1)) hv'mem + mMinus a N h2 < N
    · rw [gap_eq_etaNeg a h2 hi hjv'fr hB]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [corner_gap a h2 hi hvmem hv'mem hA hB]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- All distinct gap values lie in `{η⁺, η⁻, η⁺ + η⁻}` (non-degenerate regime).
@isnad1 id=le.1h2v.s6.4e71f474a891 from=translated src=- shape=ac174eb8 vocab=1dbbd228
-/
theorem gaps_subset_returns (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    (gaps a N).toFinset ⊆
      ({etaPos a N, etaNeg a N, etaPos a N + etaNeg a N} : Finset ℝ) := by
  intro x hx
  rw [Multiset.mem_toFinset, mem_gaps_iff] at hx
  rcases hx with ⟨i, hi, hgap⟩ | hwrap
  · rw [← hgap]
    have hi' : i + 1 < orbitCard a N := by omega
    exact neighbour_gap_in_returns a h2 hi'
  · rw [hwrap, wraparound_eq_etaNeg a h2]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

/-- **The three-gap (Steinhaus) theorem, distinct-gap-count form.**  Every gap of
    `{i·a mod 1 : i < N}` is `η⁺`, `η⁻`, or `η⁺ + η⁻`, so at most three lengths.
@isnad1 id=le.0h2v.s4.ba9444765f19 from=translated src=- shape=7dd9e545 vocab=ec55e339
-/
theorem three_gap_card_le_three (a : ℝ) (N : ℕ) :
    (gaps a N).toFinset.card ≤ 3 := by
  by_cases h2 : 2 ≤ orbitCard a N
  · exact three_gap_card_le_three_of_subset a N (gaps_subset_returns a h2)
  · have h1 : orbitCard a N ≤ 1 := by omega
    calc (gaps a N).toFinset.card
        ≤ Multiset.card (gaps a N) := gaps_toFinset_card_le a N
      _ = 1 := gaps_card_eq_one_of_degenerate a h1
      _ ≤ 3 := by norm_num

/-- **The sum relation.**  When the gaps take exactly three distinct lengths, those
    lengths are precisely `η⁺`, `η⁻`, and `η⁺ + η⁻`; in particular the largest,
    `η⁺ + η⁻`, is the sum of the other two (they are positive: `etaPos_pos`,
    `etaNeg_pos`).  The nondegeneracy `2 ≤ orbitCard` is derived from `h3`.
@isnad1 id=eq.1h2v.s6.6e18f3dcf609 from=translated src=- shape=e45190ae vocab=7b7ce3b0
-/
theorem three_gap_lengths_eq (a : ℝ) {N : ℕ}
    (h3 : (gaps a N).toFinset.card = 3) :
    (gaps a N).toFinset = ({etaPos a N, etaNeg a N, etaPos a N + etaNeg a N} : Finset ℝ) := by
  have h2 : 2 ≤ orbitCard a N := by
    by_contra h
    have hle := gaps_toFinset_card_le a N
    rw [gaps_card_eq_one_of_degenerate a (by omega)] at hle
    omega
  refine Finset.eq_of_subset_of_card_le (gaps_subset_returns a h2) ?_
  rw [h3]; exact Finset.card_le_three

end SteinhausThreeGap
