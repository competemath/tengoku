/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku.LeanPool.LeanPool.ACMax.Counting.Incidence
public import Tengoku
public import Tengoku.LeanPool.LeanPool.ACMax.Counting.FarPair
public import Tengoku.LeanPool.LeanPool.ACMax.Counting.CompactCell
public import Tengoku.LeanPool.LeanPool.ACMax.Counting.CompactLedgers

/-!
# The hub-cross firing law and the big-clean-twin structure

The spectral closer for the hub–hub mediation channel of the m-bound, together
with the rigidity of the twin population it controls.

## Main results

* `algConn_le_two_of_hub_cross_pair` — the **hub-cross firing law**: two
  non-adjacent degree-3 vertices `u ≠ v` with no common neighbour, partners all
  of degree `≤ 4` (hub degrees `D, D' ≥ 4` unbounded), and whose only possible
  `N(u)`–`N(v)` edge is the hub–hub edge `g ~ g'`, force `algConn G ≤ 2`. It
  strictly extends the cross-free usable far-pair law: instantiating the
  weighted double-star master with `au = av = 1`, hub weights `s = 1/(D−1)` and a
  balance-shifted partner weight makes the hub leak-identity
  `(1−s)² + (D−2)s² = 1 − s` yield worst-case slack `−(s+s')` (the hub–hub cross
  is spectrally cheap).
* `usable_twin_partners_deg_le_four` — σ-rigidity: a usable degree-3 twin of a
  degree-`≥ 9` hub has both other partners of degree `≤ 4`
  (`σ(9) + σ(5) + σ(4) > 2`). So the firing law applies to every cross-cloud twin
  pair mediated only by a hub–hub edge.
* `bigCleanTwins` and its structure lemmas `bigCleanTwins_nbr_deg` (neighbours
  have degree `4` or `≥ 9`), `bigCleanTwins_unique_big` (exactly one big
  neighbour, two degree-4 partners), `sum_big_inc_le`, `sum_small_inc_le` — the
  bipartite incidence counts feeding the hub-cross coverage argument.
-/

@[expose] public section

namespace ACMax

open Finset

variable {V : Type*} [Fintype V]

open Classical in
/-- **σ-rigidity of big-hub twins.**  A usable degree-3 vertex `t` (`sigS ≤ 2`)
adjacent to a hub `g` of degree `≥ 9` has both partners of degree `≤ 4`,
provided neither partner is degree-3 (i.e. off the `M`-cluster):
`σ(9) + σ(5) + σ(4) = 6/7 + 2/3 + 1/2 = 85/42 > 2`. -/
theorem usable_twin_partners_deg_le_four (G : SimpleGraph V) (t g w w' : V)
    (ht3 : G.degree t = 3) (htg : G.Adj t g) (htw : G.Adj t w) (htw' : G.Adj t w')
    (hgw : w ≠ g) (hgw' : w' ≠ g) (hww' : w ≠ w')
    (hD : 9 ≤ G.degree g) (husable : sigS G t ≤ 2)
    (hw4 : 4 ≤ G.degree w) (hw'4 : 4 ≤ G.degree w') :
    G.degree w ≤ 4 ∧ G.degree w' ≤ 4 := by
  classical
  -- `N(t) = {g, w, w'}`.
  have hgt : g ∈ G.neighborFinset t := (G.mem_neighborFinset t g).mpr htg
  have hwt : w ∈ G.neighborFinset t := (G.mem_neighborFinset t w).mpr htw
  have hw't : w' ∈ G.neighborFinset t := (G.mem_neighborFinset t w').mpr htw'
  have hcard : (G.neighborFinset t).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact ht3
  have hsub : ({g, w, w'} : Finset V) ⊆ G.neighborFinset t := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have hset : G.neighborFinset t = ({g, w, w'} : Finset V) := by
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [hcard]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp [hww']
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hgw h.symm, fun h => hgw' h.symm⟩
  -- Decompose `sigS`.
  have hsig : sigS G t = sigma (G.degree g) + sigma (G.degree w)
      + sigma (G.degree w') := by
    unfold sigS
    rw [hset]
    rw [Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hgw h.symm, fun h => hgw' h.symm⟩)]
    rw [Finset.sum_insert (by simp [hww'])]
    rw [Finset.sum_singleton]
    ring
  -- σ lower bounds.
  have hσg : sigma 9 ≤ sigma (G.degree g) := sigma_mono (by norm_num) hD
  have h9 : sigma 9 = 6 / 7 := by norm_num [sigma]
  constructor
  · -- If `deg w ≥ 5`, then `σ ≥ 6/7 + 2/3 + 1/2 > 2`.
    by_contra hcon
    have hw5 : 5 ≤ G.degree w := by omega
    have hσw : sigma 5 ≤ sigma (G.degree w) := sigma_mono (by norm_num) hw5
    have hσw' : sigma 4 ≤ sigma (G.degree w') := sigma_mono (by norm_num) hw'4
    have h5 : sigma 5 = 2 / 3 := sigma_five
    have h4 : sigma 4 = 1 / 2 := sigma_four
    rw [hsig] at husable
    rw [h9] at hσg; rw [h5] at hσw; rw [h4] at hσw'
    linarith
  · by_contra hcon
    have hw5 : 5 ≤ G.degree w' := by omega
    have hσw : sigma 4 ≤ sigma (G.degree w) := sigma_mono (by norm_num) hw4
    have hσw' : sigma 5 ≤ sigma (G.degree w') := sigma_mono (by norm_num) hw5
    have h5 : sigma 5 = 2 / 3 := sigma_five
    have h4 : sigma 4 = 1 / 2 := sigma_four
    rw [hsig] at husable
    rw [h9] at hσg; rw [h4] at hσw; rw [h5] at hσw'
    linarith

end ACMax

/-! ## Big clean twins

The *big clean twins* `bigCleanTwins G = {u : deg u = 3 ∧ sigS u ≤ 2 ∧
(∃ x ~ u, deg x ≥ 9) ∧ (∀ x ~ u, deg x ≠ 3)}` are the usable degree-3 vertices
with a big neighbour and no degree-3 neighbour. By σ-rigidity their
neighbourhoods are completely determined (`bigCleanTwins_nbr_deg`,
`bigCleanTwins_unique_big`), and the bipartite incidence counts `sum_big_inc_le`
/ `sum_small_inc_le` feed the hub-cross pair-coverage count. -/

namespace ACMax

open Finset

open Classical in
/-- The **big clean twins**: usable degree-3 vertices with a degree-`≥ 9`
neighbour and no degree-3 neighbour. -/
noncomputable def bigCleanTwins {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun u : Fin n =>
    G.degree u = 3 ∧ sigS G u ≤ 2 ∧
    (∃ x ∈ G.neighborFinset u, 9 ≤ G.degree x) ∧
    (∀ x ∈ G.neighborFinset u, G.degree x ≠ 3))

open Classical in
theorem mem_bigCleanTwins {n : ℕ} {G : SimpleGraph (Fin n)} {u : Fin n} :
    u ∈ bigCleanTwins G ↔
      G.degree u = 3 ∧ sigS G u ≤ 2 ∧
      (∃ x ∈ G.neighborFinset u, 9 ≤ G.degree x) ∧
      (∀ x ∈ G.neighborFinset u, G.degree x ≠ 3) := by
  unfold bigCleanTwins
  simp

open Classical in
/-- **Neighbourhood rigidity.**  Every neighbour of a big clean twin has degree
`4` or degree `≥ 9`. -/
theorem bigCleanTwins_nbr_deg {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    {u : Fin n} (hu : u ∈ bigCleanTwins G) {x : Fin n}
    (hx : x ∈ G.neighborFinset u) :
    G.degree x = 4 ∨ 9 ≤ G.degree x := by
  classical
  obtain ⟨hdeg, hsig, ⟨gbig, hgmem, hgbig⟩, hno3⟩ := mem_bigCleanTwins.mp hu
  by_cases hxg : x = gbig
  · exact Or.inr (hxg ▸ hgbig)
  -- `x ≠ gbig`: `x` is a partner.  Get the third neighbour.
  have hxne3 : G.degree x ≠ 3 := hno3 x hx
  have hx4 : 4 ≤ G.degree x := by
    have := h3 x
    omega
  -- the third neighbour `y`: `N(u) = {gbig, x, y}`
  have hcard : (G.neighborFinset u).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg
  have hcard2 : (((G.neighborFinset u).erase gbig).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem hgmem, hcard]
    exact Finset.mem_erase.mpr ⟨hxg, hx⟩
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard2
  have hymem : y ∈ ((G.neighborFinset u).erase gbig).erase x := by
    rw [hy]; exact Finset.mem_singleton_self y
  have hyx : y ≠ x := (Finset.mem_erase.mp hymem).1
  have hyg : y ≠ gbig := (Finset.mem_erase.mp (Finset.mem_erase.mp hymem).2).1
  have hyN : y ∈ G.neighborFinset u := (Finset.mem_erase.mp (Finset.mem_erase.mp hymem).2).2
  have hy4 : 4 ≤ G.degree y := by
    have h1 := hno3 y hyN
    have h2 := h3 y
    omega
  -- σ-rigidity: partners of a `≥ 9` hub are degree `≤ 4`
  have hle := usable_twin_partners_deg_le_four G u gbig x y hdeg
    ((G.mem_neighborFinset u gbig).mp hgmem)
    ((G.mem_neighborFinset u x).mp hx)
    ((G.mem_neighborFinset u y).mp hyN)
    hxg hyg hyx.symm hgbig hsig hx4 hy4
  exact Or.inl (le_antisymm hle.1 hx4)

open Classical in
/-- **Unique big neighbour.**  A big clean twin has exactly one big neighbour:
there is a big neighbour `g`, and every other neighbour has degree `≤ 4`. -/
theorem bigCleanTwins_unique_big {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    {u : Fin n} (hu : u ∈ bigCleanTwins G) :
    ∃ g ∈ G.neighborFinset u, 9 ≤ G.degree g ∧
      ∀ x ∈ G.neighborFinset u, x ≠ g → G.degree x = 4 := by
  classical
  obtain ⟨hdeg, hsig, ⟨gbig, hgmem, hgbig⟩, hno3⟩ := mem_bigCleanTwins.mp hu
  refine ⟨gbig, hgmem, hgbig, ?_⟩
  intro x hx hxg
  rcases bigCleanTwins_nbr_deg G h3 hu hx with h4 | h9
  · exact h4
  -- two big neighbours: contradiction via σ-rigidity (`x` would be a partner of
  -- degree `≥ 9 > 4`).
  exfalso
  -- third neighbour `y` of `u` besides `gbig, x`
  have hcard : (G.neighborFinset u).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg
  have hcard2 : (((G.neighborFinset u).erase gbig).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem hgmem, hcard]
    exact Finset.mem_erase.mpr ⟨hxg, hx⟩
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard2
  have hymem : y ∈ ((G.neighborFinset u).erase gbig).erase x := by
    rw [hy]; exact Finset.mem_singleton_self y
  have hyx : y ≠ x := (Finset.mem_erase.mp hymem).1
  have hyg : y ≠ gbig := (Finset.mem_erase.mp (Finset.mem_erase.mp hymem).2).1
  have hyN : y ∈ G.neighborFinset u := (Finset.mem_erase.mp (Finset.mem_erase.mp hymem).2).2
  have hy4 : 4 ≤ G.degree y := by
    have h1 := hno3 y hyN
    have h2 := h3 y
    omega
  have hle := usable_twin_partners_deg_le_four G u gbig x y hdeg
    ((G.mem_neighborFinset u gbig).mp hgmem)
    ((G.mem_neighborFinset u x).mp hx)
    ((G.mem_neighborFinset u y).mp hyN)
    hxg hyg hyx.symm hgbig hsig (by omega) hy4
  omega

open Classical in
/-- **Bipartite incidence exchange** (indicator double count):
`Σ_{w ∈ s} |N(w) ∩ t| = Σ_{u ∈ t} |N(u) ∩ s|`. -/
theorem sum_nbr_inter_comm {n : ℕ} (G : SimpleGraph (Fin n))
    (s t : Finset (Fin n)) :
    ∑ w ∈ s, (G.neighborFinset w ∩ t).card
      = ∑ u ∈ t, (G.neighborFinset u ∩ s).card := by
  classical
  have hleft : ∀ w : Fin n, (G.neighborFinset w ∩ t).card
      = ∑ u ∈ t, (if G.Adj w u then 1 else 0) := by
    intro w
    have hset : G.neighborFinset w ∩ t = t.filter (fun u => G.Adj w u) := by
      ext u
      simp [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
        and_comm]
    rw [hset, Finset.card_filter]
  have hright : ∀ u : Fin n, (G.neighborFinset u ∩ s).card
      = ∑ w ∈ s, (if G.Adj w u then 1 else 0) := by
    intro u
    have hset : G.neighborFinset u ∩ s = s.filter (fun w => G.Adj w u) := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hu, hw⟩
        exact ⟨hw, hu.symm⟩
      · rintro ⟨hw, hu⟩
        exact ⟨hu.symm, hw⟩
    rw [hset, Finset.card_filter]
  simp_rw [hleft, hright]
  exact Finset.sum_comm

open Classical in
/-- **Big-incidence exchange.**  The incidences between big vertices and big
clean twins number at most `|bigCleanTwins|` — each twin has exactly one big
neighbour. -/
theorem sum_big_inc_le {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w),
        (G.neighborFinset w ∩ bigCleanTwins G).card
      ≤ (bigCleanTwins G).card := by
  classical
  rw [sum_nbr_inter_comm]
  calc ∑ u ∈ bigCleanTwins G,
      (G.neighborFinset u ∩ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w)).card
      ≤ ∑ _u ∈ bigCleanTwins G, 1 := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        obtain ⟨g, hgmem, hgbig, hrest⟩ := bigCleanTwins_unique_big G h3 hu
        refine Finset.card_le_one.mpr (fun x hx y hy => ?_)
        rw [Finset.mem_inter, Finset.mem_filter] at hx hy
        have hxg : x = g := by
          by_contra hne
          have := hrest x hx.1 hne
          have := hx.2.2
          omega
        have hyg : y = g := by
          by_contra hne
          have := hrest y hy.1 hne
          have := hy.2.2
          omega
        rw [hxg, hyg]
    _ = (bigCleanTwins G).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]

open Classical in
/-- **Small-incidence exchange.**  The incidences between degree-`≤ 8` vertices
and big clean twins number at most `2·|bigCleanTwins|` — each twin has exactly
two degree-4 partners. -/
theorem sum_small_inc_le {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w ≤ 8),
        (G.neighborFinset w ∩ bigCleanTwins G).card
      ≤ 2 * (bigCleanTwins G).card := by
  classical
  rw [sum_nbr_inter_comm]
  calc ∑ u ∈ bigCleanTwins G,
      (G.neighborFinset u ∩ Finset.univ.filter (fun w : Fin n => G.degree w ≤ 8)).card
      ≤ ∑ _u ∈ bigCleanTwins G, 2 := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        obtain ⟨g, hgmem, hgbig, hrest⟩ := bigCleanTwins_unique_big G h3 hu
        -- the small neighbours avoid `g`, and `N(u) \ {g}` has two elements
        have hsub : G.neighborFinset u ∩
            Finset.univ.filter (fun w : Fin n => G.degree w ≤ 8)
            ⊆ (G.neighborFinset u).erase g := by
          intro x hx
          rw [Finset.mem_inter, Finset.mem_filter] at hx
          refine Finset.mem_erase.mpr ⟨?_, hx.1⟩
          intro hxg
          have h8 : G.degree x ≤ 8 := hx.2.2
          rw [hxg] at h8
          omega
        have hcard : (G.neighborFinset u).card = 3 := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          exact (mem_bigCleanTwins.mp hu).1
        calc (G.neighborFinset u ∩
              Finset.univ.filter (fun w : Fin n => G.degree w ≤ 8)).card
            ≤ ((G.neighborFinset u).erase g).card := Finset.card_le_card hsub
          _ = 2 := by rw [Finset.card_erase_of_mem hgmem, hcard]
    _ = 2 * (bigCleanTwins G).card := by
        rw [Finset.sum_const, smul_eq_mul]
        ring

open Classical in
/-- The `M`-population under the dichotomy: at most `2` degree-3 vertices
have a degree-3 neighbour. -/
theorem deg3_with_deg3_nbr_card_le_two {n : ℕ} (G : SimpleGraph (Fin n))
    (huniq : ∀ t₁ t₂ t₃ t₄ : Fin n, G.Adj t₁ t₂ → G.Adj t₃ t₄ →
      G.degree t₁ = 3 → G.degree t₂ = 3 → G.degree t₃ = 3 →
      G.degree t₄ = 3 →
      ({t₁, t₂} : Finset (Fin n)) = ({t₃, t₄} : Finset (Fin n))) :
    (Finset.univ.filter (fun u : Fin n =>
      G.degree u = 3 ∧ ∃ x ∈ G.neighborFinset u, G.degree x = 3)).card ≤ 2 := by
  classical
  have hsub : Finset.univ.filter (fun u : Fin n =>
        G.degree u = 3 ∧ ∃ x ∈ G.neighborFinset u, G.degree x = 3)
      ⊆ (deg3Set G).filter
        (fun t => ∃ t' : Fin n, G.Adj t t' ∧ G.degree t' = 3) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨-, hu3, x, hxm, hx3⟩ := hu
    rw [Finset.mem_filter]
    exact ⟨mem_deg3Set.mpr hu3, x, (G.mem_neighborFinset u x).mp hxm, hx3⟩
  exact (Finset.card_le_card hsub).trans
    (medge_endpoint_card_le_two n G huniq)

end ACMax
