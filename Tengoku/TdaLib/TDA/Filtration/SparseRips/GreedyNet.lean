import Tengoku.Seed.Topology.MetricSpace.Basic
import Tengoku.Seed.Data.Finset.Max
import Tengoku.Seed.Data.Fintype.EquivFin
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Farthest-first nets in a finite metric space

Starting from a chosen vertex, each greedyPrefix grows by a vertex maximizing its distance
to that greedyPrefix. The construction stabilizes at the whole space. The next insertion
radius bounds the covering radius of the current greedyPrefix and separates all vertices
already inserted. The initial vertex is supplied separately: it has no finite
insertion radius.
-/

namespace TDA.Filtration.SparseRips.GreedyNet

noncomputable section

variable {V : Type*} [MetricSpace V]

local instance greedyNetDecidableEq : DecidableEq V := Classical.decEq V

/-- Distance to a finite set, with auxiliary value zero at the empty set.-/
def nearestDistance (s : Finset V) (x : V) : ℝ :=
  by
    classical
    exact if h : s.Nonempty then s.inf' h (dist x) else 0

/--
@isnad1 id=le.1h4v.s5.81acfdb96255 from=translated src=- shape=42b47cdb vocab=0a09a1ac
-/
theorem nearestDistance_le {s : Finset V} {x y : V} (hy : y ∈ s) :
    nearestDistance s x ≤ dist x y := by
  classical
  rw [nearestDistance, dite_eq_left (show s.Nonempty from ⟨y, hy⟩)]
  exact Finset.inf'_le _ hy

/--
@isnad1 id=ex.1h3v.s5.d4a84d3bd13f from=translated src=- shape=2eff4a75 vocab=75886027
-/
theorem exists_nearest {s : Finset V} (hs : s.Nonempty) (x : V) :
    ∃ y ∈ s, dist x y = nearestDistance s x := by
  classical
  obtain ⟨y, hy, hmin⟩ := s.exists_min_image (dist x) hs
  refine ⟨y, hy, le_antisymm ?_ (nearestDistance_le hy)⟩
  simp only [nearestDistance, dite_eq_left hs]
  exact Finset.le_inf' hs (dist x) (fun z hz => hmin z hz)

/--
@isnad1 id=le.0h3v.s4.d53fde98bdf5 from=translated src=- shape=95d29364 vocab=26ff91bb
-/
theorem nearestDistance_nonneg (s : Finset V) (x : V) :
    0 ≤ nearestDistance s x := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨y, _, hy⟩ := exists_nearest hs x
    rw [← hy]
    exact dist_nonneg
  · simp [nearestDistance, hs]

/--
@isnad1 id=eq.1h3v.s5.d4e7ca43574a from=translated src=- shape=e9db3f57 vocab=09440411
-/
@[simp] theorem nearestDistance_of_mem {s : Finset V} {x : V} (hx : x ∈ s) :
    nearestDistance s x = 0 :=
  le_antisymm (by simpa using nearestDistance_le (x := x) hx)
    (nearestDistance_nonneg s x)

/--
@isnad1 id=lt.2h3v.s5.89c245b1a1ab from=translated src=- shape=c45c46e4 vocab=fbfe4733
-/
theorem nearestDistance_pos {s : Finset V} (hs : s.Nonempty) {x : V} (hx : x ∉ s) :
    0 < nearestDistance s x := by
  obtain ⟨y, hy, heq⟩ := exists_nearest hs x
  rw [← heq]
  exact dist_pos.mpr (fun h => hx (h ▸ hy))

/--
@isnad1 id=le.2h4v.s5.32ac90d38ff8 from=translated src=- shape=1925ff1c vocab=10768c26
-/
theorem nearestDistance_antitone {s t : Finset V} (hs : s.Nonempty) (hst : s ⊆ t)
    (x : V) : nearestDistance t x ≤ nearestDistance s x := by
  obtain ⟨y, hy, heq⟩ := exists_nearest hs x
  rw [← heq]
  exact nearestDistance_le (hst hy)

variable [Fintype V]

/-- A farthest vertex, selected using finiteness. Ties may be resolved arbitrarily.-/
def next (seed : V) (s : Finset V) : V :=
  Classical.choose (Finset.univ.exists_max_image (nearestDistance s)
    ⟨seed, Finset.mem_univ seed⟩)

/--
@isnad1 id=le.0h4v.s5.be76e966a053 from=translated src=- shape=5a71d2e7 vocab=e9929c80
-/
theorem le_next (seed : V) (s : Finset V) (x : V) :
    nearestDistance s x ≤ nearestDistance s (next seed s) := by
  classical
  exact (Classical.choose_spec (Finset.univ.exists_max_image (nearestDistance s)
    ⟨seed, Finset.mem_univ seed⟩)).2 x (Finset.mem_univ x)

/-- Prefix zero contains just the immortal initial vertex.-/
def greedyPrefix (seed : V) : ℕ → Finset V
  | 0 => {seed}
  | n + 1 => insert (next seed (greedyPrefix seed n)) (greedyPrefix seed n)

/--
@isnad1 id=eq.0h2v.s4.3fd5c1da4a19 from=translated src=- shape=4a5f5e46 vocab=16d7caaf
-/
@[simp] theorem prefix_zero (seed : V) : greedyPrefix seed 0 = {seed} := rfl

/--
@isnad1 id=eq.0h3v.s5.fd86e9b56c60 from=translated src=- shape=816d86d3 vocab=b2c249dc
-/
@[simp] theorem prefix_succ (seed : V) (n : ℕ) :
    greedyPrefix seed (n + 1) = insert (next seed (greedyPrefix seed n)) (greedyPrefix seed n) := rfl

/--
@isnad1 id=le.0h3v.s5.91173501bf14 from=translated src=- shape=82968730 vocab=91065c21
-/
theorem prefix_step (seed : V) (n : ℕ) : greedyPrefix seed n ⊆ greedyPrefix seed (n + 1) := by
  classical
  exact Finset.subset_insert _ _

/--
@isnad1 id=monotone.0h2v.s4.e3edb1164ea1 from=translated src=- shape=64b85bae vocab=da5c0921
-/
theorem prefix_mono (seed : V) : Monotone (greedyPrefix seed) :=
  monotone_nat_of_le_succ (prefix_step seed)

/--
@isnad1 id=mem.0h3v.s4.0b31492d2e65 from=translated src=- shape=ee40918f vocab=7aab456d
-/
theorem seed_mem_prefix (seed : V) (n : ℕ) : seed ∈ greedyPrefix seed n :=
  prefix_mono seed (Nat.zero_le n) (by simp)

/--
@isnad1 id=nonempty.0h3v.s4.61d861336052 from=translated src=- shape=c8e2b1b7 vocab=f0bd3c84
-/
theorem prefix_nonempty (seed : V) (n : ℕ) : (greedyPrefix seed n).Nonempty :=
  ⟨seed, seed_mem_prefix seed n⟩

/-- The farthest-first sequence starts with `seed`. Its meaningful indices are
strictly below the cardinality of the space.-/
def vertex (seed : V) : ℕ → V
  | 0 => seed
  | n + 1 => next seed (greedyPrefix seed n)

/--
@isnad1 id=eq.0h2v.s4.da60398c4254 from=translated src=- shape=ef057593 vocab=5ad21fc3
-/
@[simp] theorem vertex_zero (seed : V) : vertex seed 0 = seed := rfl

/--
@isnad1 id=eq.0h3v.s5.ce7a62c90ef6 from=translated src=- shape=5f4dcaef vocab=c4eb81b8
-/
@[simp] theorem vertex_succ (seed : V) (n : ℕ) :
    vertex seed (n + 1) = next seed (greedyPrefix seed n) := rfl

/--
@isnad1 id=iff.0h4v.s5.af6436b06f74 from=translated src=- shape=f88b042c vocab=9976df58
-/
theorem mem_prefix_iff (seed : V) (n : ℕ) (x : V) :
    x ∈ greedyPrefix seed n ↔ ∃ i ≤ n, vertex seed i = x := by
  classical
  induction n with
  | zero => simp [eq_comm]
  | succ n ih =>
    rw [prefix_succ, Finset.mem_insert, ih]
    constructor
    · rintro (h | ⟨i, hi, rfl⟩)
      · exact ⟨n + 1, le_rfl, h.symm⟩
      · exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, heq⟩
      by_cases hin : i ≤ n
      · exact Or.inr ⟨i, hin, heq⟩
      · have hindex : i = n + 1 := by omega
        exact Or.inl (by simpa [hindex] using heq.symm)

/-- The next insertion radius is finite; the initial vertex has no such radius.-/
def radius (seed : V) (n : ℕ) : ℝ :=
  nearestDistance (greedyPrefix seed n) (next seed (greedyPrefix seed n))

/--
@isnad1 id=le.0h3v.s4.c98cfd0d6f67 from=translated src=- shape=35874182 vocab=6799a076
-/
theorem radius_nonneg (seed : V) (n : ℕ) : 0 ≤ radius seed n :=
  nearestDistance_nonneg _ _

/--
@isnad1 id=ex.0h4v.s5.d3fedd769b01 from=translated src=- shape=5b2577b6 vocab=c73d2d7a
-/
theorem covering (seed : V) (n : ℕ) (x : V) :
    ∃ y ∈ greedyPrefix seed n, dist x y ≤ radius seed n := by
  obtain ⟨y, hy, heq⟩ := exists_nearest (prefix_nonempty seed n) x
  exact ⟨y, hy, heq.trans_le (le_next seed _ x)⟩

/--
@isnad1 id=not.1h3v.s5.d9ef874fdcaa from=translated src=- shape=5ed725aa vocab=381160fa
-/
theorem next_not_mem (seed : V) {n : ℕ} (h : greedyPrefix seed n ≠ Finset.univ) :
    next seed (greedyPrefix seed n) ∉ greedyPrefix seed n := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, x ∉ greedyPrefix seed n := by
    by_contra! hall
    exact h (Finset.eq_univ_of_forall hall)
  have hpos := (nearestDistance_pos (prefix_nonempty seed n) hx).trans_le
    (le_next seed (greedyPrefix seed n) x)
  intro hn
  rw [nearestDistance_of_mem hn] at hpos
  exact (lt_irrefl 0) hpos

/-- Insertion radii decrease, including the terminal zero radii after exhaustion.
@isnad1 id=antitone.0h2v.s4.19cd485ac140 from=translated src=- shape=46e5bbee vocab=9ce73123
-/
theorem radius_antitone (seed : V) : Antitone (radius seed) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (nearestDistance_antitone (prefix_nonempty seed n) (prefix_step seed n) _).trans
    (le_next seed _ _)

/-- Every greedyPrefix has the expected cardinality until all vertices have been inserted.
@isnad1 id=eq.0h3v.s5.1c55a8bee9aa from=translated src=- shape=198dfb00 vocab=e112ff17
-/
theorem card_prefix (seed : V) (n : ℕ) :
    (greedyPrefix seed n).card = min (n + 1) (Fintype.card V) := by
  classical
  have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨seed⟩
  induction n with
  | zero => simp; omega
  | succ n ih =>
    by_cases h : greedyPrefix seed n = Finset.univ
    · have hle : Fintype.card V ≤ n + 1 := by
        rw [h, Finset.card_univ] at ih
        omega
      simp [prefix_succ, h]
      omega
    · have hlt : (greedyPrefix seed n).card < Fintype.card V := by
        exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr h)
      rw [prefix_succ, Finset.card_insert_of_notMem (next_not_mem seed h), ih]
      omega

/-- Finiteness proves completion; no net structure is assumed as input.
@isnad1 id=eq.1h3v.s5.2ecf70e420d7 from=translated src=- shape=6e02a97d vocab=ae437345
-/
theorem prefix_eq_univ (seed : V) {n : ℕ} (hn : Fintype.card V ≤ n + 1) :
    greedyPrefix seed n = Finset.univ := by
  classical
  apply (Finset.card_eq_iff_eq_univ _).mp
  rw [card_prefix]
  omega

/-- The constructed finite farthest-first sequence enumerates every vertex exactly once.
@isnad1 id=bijectiv.0h2v.s4.f8490d0e360d from=translated src=- shape=7cde3823 vocab=5c28c069
-/
theorem vertex_bijective (seed : V) :
    Function.Bijective (fun i : Fin (Fintype.card V) => vertex seed i.val) := by
  classical
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, by simp⟩
  intro x
  have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨seed⟩
  have hx : x ∈ greedyPrefix seed (Fintype.card V - 1) := by
    rw [prefix_eq_univ seed (by omega)]
    exact Finset.mem_univ x
  obtain ⟨i, hi, hix⟩ := (mem_prefix_iff seed _ x).mp hx
  exact ⟨⟨i, by omega⟩, hix⟩

/-- A greedy permutation obtained solely from the finite metric space and its initial vertex.-/
def enumeration (seed : V) : Fin (Fintype.card V) ≃ V :=
  Equiv.ofBijective _ (vertex_bijective seed)

/--
@isnad1 id=eq.0h3v.s6.0074bc79e9ae from=translated src=- shape=5976e37d vocab=5f26f6a9
-/
@[simp] theorem enumeration_apply (seed : V) (i : Fin (Fintype.card V)) :
    enumeration seed i = vertex seed i.val := rfl

/-- All distinct vertices of a greedyPrefix are separated by the next insertion radius.
@isnad1 id=le.3h5v.s6.4b796fe6dbad from=translated src=- shape=713c5415 vocab=c73d2d7a
-/
theorem separation (seed : V) (n : ℕ) {x y : V}
    (hx : x ∈ greedyPrefix seed n) (hy : y ∈ greedyPrefix seed n) (hne : x ≠ y) :
    radius seed n ≤ dist x y := by
  classical
  induction n with
  | zero => simp only [prefix_zero, Finset.mem_singleton] at hx hy; exact (hne (hx.trans hy.symm)).elim
  | succ n ih =>
    simp only [prefix_succ, Finset.mem_insert] at hx hy
    have hrad := radius_antitone seed (Nat.le_succ n)
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hne rfl).elim
    · exact hrad.trans (nearestDistance_le hy)
    · rw [dist_comm]
      exact hrad.trans (nearestDistance_le hx)
    · exact hrad.trans (ih hx hy)

/-- The radius of the last inserted vertex separates the enlarged greedyPrefix.
@isnad1 id=le.3h5v.s6.34d8a070c5d7 from=translated src=- shape=a9ef8aab vocab=553e600e
-/
theorem separation_succ (seed : V) (n : ℕ) {x y : V}
    (hx : x ∈ greedyPrefix seed (n + 1)) (hy : y ∈ greedyPrefix seed (n + 1)) (hne : x ≠ y) :
    radius seed n ≤ dist x y := by
  classical
  simp only [prefix_succ, Finset.mem_insert] at hx hy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact (hne rfl).elim
  · exact nearestDistance_le hy
  · rw [dist_comm]; exact nearestDistance_le hx
  · exact separation seed n hx hy hne

/--
@isnad1 id=eq.1h3v.s5.a37db302543f from=translated src=- shape=fbe05894 vocab=8d55db8d
-/
@[simp] theorem radius_eq_zero_of_full (seed : V) {n : ℕ}
    (hn : greedyPrefix seed n = Finset.univ) : radius seed n = 0 := by
  classical
  unfold radius
  exact nearestDistance_of_mem (hn ▸ Finset.mem_univ _)

/-- A finite threshold greedyPrefix exists even at threshold zero.
@isnad1 id=ex.1h3v.s5.68b5fdedc725 from=translated src=- shape=3066a285 vocab=6799a076
-/
theorem exists_radius_le (seed : V) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ n, radius seed n ≤ δ := by
  refine ⟨Fintype.card V, ?_⟩
  rw [radius_eq_zero_of_full seed (prefix_eq_univ seed (by omega))]
  exact hδ

/-- Stop immediately before the next insertion would have radius at most `δ`.-/
def cutoff (seed : V) (δ : ℝ) (hδ : 0 ≤ δ) : ℕ :=
  Nat.find (exists_radius_le seed hδ)

/--
@isnad1 id=le.1h3v.s5.dee08a2692d2 from=translated src=- shape=30a2712d vocab=2c2f1b7e
-/
theorem radius_cutoff_le (seed : V) (δ : ℝ) (hδ : 0 ≤ δ) :
    radius seed (cutoff seed δ hδ) ≤ δ :=
  Nat.find_spec (exists_radius_le seed hδ)

/--
@isnad1 id=lt.2h4v.s5.4278a712255c from=translated src=- shape=7c63b4e4 vocab=ed80970e
-/
theorem lt_radius_before_cutoff (seed : V) (δ : ℝ) (hδ : 0 ≤ δ) {n : ℕ}
    (hn : n < cutoff seed δ hδ) : δ < radius seed n :=
  lt_of_not_ge (Nat.find_min (exists_radius_le seed hδ) hn)

/-- The threshold net has closed covering radius `δ` and strict separation `δ`.
The strict inequality handles simultaneous deletion times without choosing a tie order.
@isnad1 id=and.1h3v.s7.eadc7fc9205d from=translated src=- shape=956a0d93 vocab=e770f4e8
-/
theorem threshold_net (seed : V) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ x, ∃ y ∈ greedyPrefix seed (cutoff seed δ hδ), dist x y ≤ δ) ∧
    (∀ x ∈ greedyPrefix seed (cutoff seed δ hδ),
      ∀ y ∈ greedyPrefix seed (cutoff seed δ hδ), x ≠ y → δ < dist x y) := by
  constructor
  · intro x
    obtain ⟨y, hy, hxy⟩ := covering seed (cutoff seed δ hδ) x
    exact ⟨y, hy, hxy.trans (radius_cutoff_le seed δ hδ)⟩
  · intro x hx y hy hne
    generalize hk : cutoff seed δ hδ = k at hx hy
    cases k with
    | zero =>
      simp only [prefix_zero, Finset.mem_singleton] at hx hy
      exact (hne (hx.trans hy.symm)).elim
    | succ n =>
      exact (lt_radius_before_cutoff seed δ hδ (by omega)).trans_le
        (separation_succ seed n hx hy hne)

/-- The first index at which a vertex occurs. This is zero exactly for `seed`.-/
def insertionIndex (seed x : V) : ℕ :=
  Nat.find (show ∃ n, x ∈ greedyPrefix seed n from
    ⟨Fintype.card V, by rw [prefix_eq_univ seed (by omega)]; exact Finset.mem_univ x⟩)

/--
@isnad1 id=mem.0h3v.s5.851c2e5f3dbf from=translated src=- shape=316b8b99 vocab=deb4591d
-/
theorem mem_insertionIndex (seed x : V) : x ∈ greedyPrefix seed (insertionIndex seed x) :=
  by
    unfold insertionIndex
    exact Nat.find_spec (p := fun n => x ∈ greedyPrefix seed n) _

/--
@isnad1 id=not.1h4v.s5.7344c0d52e94 from=translated src=- shape=e10b2f18 vocab=b44d6e6c
-/
theorem not_mem_before_insertionIndex (seed x : V) {n : ℕ}
    (hn : n < insertionIndex seed x) : x ∉ greedyPrefix seed n :=
  Nat.find_min _ hn

/--
@isnad1 id=eq.0h2v.s4.f99c93524fa2 from=translated src=- shape=ec54b993 vocab=0d30615f
-/
@[simp] theorem insertionIndex_seed (seed : V) : insertionIndex seed seed = 0 := by
  unfold insertionIndex
  exact (Nat.find_eq_zero _).mpr (by simp)

/-- The insertion radius of the first vertex is `none`, interpreted as infinity.
All other vertices receive their actual positive finite insertion radius.-/
def insertionRadius (seed x : V) : Option ℝ :=
  if insertionIndex seed x = 0 then none
  else some (radius seed (insertionIndex seed x - 1))

/--
@isnad1 id=eq.0h2v.s4.9a9000464488 from=translated src=- shape=c5a5df1d vocab=b293f439
-/
@[simp] theorem insertionRadius_seed (seed : V) : insertionRadius seed seed = none := by
  simp [insertionRadius]

/--
@isnad1 id=iff.0h3v.s4.068c16b44762 from=translated src=- shape=6d74731b vocab=0d30615f
-/
theorem insertionIndex_eq_zero_iff (seed x : V) : insertionIndex seed x = 0 ↔ x = seed := by
  constructor
  · intro h
    have hx := mem_insertionIndex seed x
    simpa [h] using hx
  · intro h; subst x; exact insertionIndex_seed seed

/-- Every point kept by the threshold net is either the initial vertex or was inserted
at radius strictly greater than the threshold.
@isnad1 id=iff.1h4v.s6.660e26478b64 from=translated src=- shape=5619a3e1 vocab=b99c4d82
-/
theorem mem_threshold_iff (seed x : V) (δ : ℝ) (hδ : 0 ≤ δ) :
    x ∈ greedyPrefix seed (cutoff seed δ hδ) ↔
      x = seed ∨ δ < radius seed (insertionIndex seed x - 1) := by
  constructor
  · intro hx
    by_cases hxs : x = seed
    · exact Or.inl hxs
    · right
      have hindex : 0 < insertionIndex seed x := by
        have := (insertionIndex_eq_zero_iff seed x).not.mpr hxs
        omega
      have hle : insertionIndex seed x ≤ cutoff seed δ hδ := by
        by_contra! hn
        exact not_mem_before_insertionIndex seed x hn hx
      exact lt_radius_before_cutoff seed δ hδ (by omega)
  · rintro (hxs | hrad)
    · subst x; exact seed_mem_prefix seed _
    · by_cases hi : insertionIndex seed x ≤ cutoff seed δ hδ
      · exact prefix_mono seed hi (mem_insertionIndex seed x)
      · have hle : cutoff seed δ hδ ≤ insertionIndex seed x - 1 := by omega
        have hmono := radius_antitone seed hle
        have hcut := radius_cutoff_le seed δ hδ
        linarith

/-- The first occurrence of a vertex is its actual greedy enumeration entry.
@isnad1 id=eq.0h3v.s4.935ce96bf8bf from=translated src=- shape=1e8ad55d vocab=7cc7b121
-/
theorem vertex_insertionIndex (seed x : V) : vertex seed (insertionIndex seed x) = x := by
  by_cases hx : x = seed
  · subst x; simp
  · have hi : 0 < insertionIndex seed x := by
      have := (insertionIndex_eq_zero_iff seed x).not.mpr hx
      omega
    have hnot := not_mem_before_insertionIndex seed x
      (show insertionIndex seed x - 1 < insertionIndex seed x by omega)
    have hmem := mem_insertionIndex seed x
    have heq : insertionIndex seed x = (insertionIndex seed x - 1) + 1 := by omega
    rw [heq, prefix_succ, Finset.mem_insert] at hmem
    rw [heq, vertex_succ]
    exact (hmem.resolve_right hnot).symm

/--
@isnad1 id=injectiv.0h2v.s4.286253b3ccad from=translated src=- shape=14a77580 vocab=8ac0e314
-/
theorem insertionIndex_injective (seed : V) : Function.Injective (insertionIndex seed) := by
  intro x y hxy
  rw [← vertex_insertionIndex seed x, ← vertex_insertionIndex seed y, hxy]

/-- Noninitial vertices have strictly positive insertion radii.
@isnad1 id=lt.1h3v.s5.6fedd7f83fe0 from=translated src=- shape=3521e292 vocab=44100763
-/
theorem insertionRadius_pos (seed x : V) (hxs : x ≠ seed) :
    0 < radius seed (insertionIndex seed x - 1) := by
  have hi : 0 < insertionIndex seed x := by
    have := (insertionIndex_eq_zero_iff seed x).not.mpr hxs
    omega
  have hnot := not_mem_before_insertionIndex seed x (show insertionIndex seed x - 1 <
    insertionIndex seed x by omega)
  have hx := mem_insertionIndex seed x
  have heq : insertionIndex seed x = (insertionIndex seed x - 1) + 1 := by omega
  rw [heq, prefix_succ, Finset.mem_insert] at hx
  have hxnext : x = next seed (greedyPrefix seed (insertionIndex seed x - 1)) :=
    hx.resolve_right hnot
  unfold radius
  rw [← hxnext]
  exact nearestDistance_pos (prefix_nonempty seed _) hnot

/-- Choose a point of the threshold net within its proved covering radius.-/
def netPoint (seed : V) (δ : ℝ) (hδ : 0 ≤ δ) (x : V) : V :=
  Classical.choose ((threshold_net seed δ hδ).1 x)

/--
@isnad1 id=mem.1h4v.s5.2764927332eb from=translated src=- shape=812a5663 vocab=595092d5
-/
theorem netPoint_mem (seed : V) (δ : ℝ) (hδ : 0 ≤ δ) (x : V) :
    netPoint seed δ hδ x ∈ greedyPrefix seed (cutoff seed δ hδ) :=
  (Classical.choose_spec ((threshold_net seed δ hδ).1 x)).1

/--
@isnad1 id=le.1h4v.s5.4facf2b9b123 from=translated src=- shape=dab65948 vocab=41b6d265
-/
theorem dist_netPoint_le (seed : V) (δ : ℝ) (hδ : 0 ≤ δ) (x : V) :
    dist x (netPoint seed δ hδ x) ≤ δ :=
  (Classical.choose_spec ((threshold_net seed δ hδ).1 x)).2

end

end TDA.Filtration.SparseRips.GreedyNet
