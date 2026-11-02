import Tengoku.Seed.Analysis.Convex.Segment
import Tengoku.Seed.Analysis.Convex.Basic
import Tengoku.Seed.Analysis.Normed.Module.Convex
import Tengoku.Seed.Analysis.Convex.Topology
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Topology.MetricSpace.Pseudo.Lemmas
import Tengoku.Seed.Analysis.SpecificLimits.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # A ℚ-valued Čech–Goursat coboundary theorem on open convex covers of ℂ

Wall Leg B closing wave, the pure chain-calculus core: **a ℚ-valued Čech
`1`-cocycle on an open convex cover of `ℂ` is a coboundary**
(`exists_coboundary`).  This is the abstract input that turns kernel-valued
difference sections on a ball-image chart cover into a correcting `0`-cochain
— the `core` slot of `HodgePilot.AnalyticWallB` — and it is proved here from
first principles, with no sheaf, no cohomology group, and no integration
anywhere.

## Route

* **Walk sums on uniform segment subdivisions.**  For a chain `l : List ι` of
  cover indices, `Valid U z w l` says the `k`-th piece of the uniform
  `l.length`-piece subdivision of the segment `[z, w]` lies in `U l[k]`;
  `wSum q i l i'` is the telescoping sum of cocycle values along the walk.
  `wSum_indep` (two valid chains of the same length have the same walk sum),
  `wSum_blowup`/`Valid.blowup` (uniform refinement leaves the walk sum
  unchanged) and `wSum_welldef` (any two valid chains agree, by blowing each
  up to the common refinement) make the **chain integral**
  `beta U q hop hcov z w i i'` well-defined via a Lebesgue-number choice of
  chain (`exists_valid_chain`).
* **Chain calculus.**  `beta_split_mid` (midpoint splitting), `beta_rev`
  (orientation reversal), `beta_swap_right` (endpoint-index swap), and the
  four-child **Goursat subdivision identity** `tri_subdiv`.
* **The Goursat triangle lemma** (`beta_triangle`): the closed chain integral
  around any triangle vanishes — the classical bisection: a quarter-child
  with at least a quarter of the parent's boundary integral is chosen at
  every stage (`exists_goursat_child`), perimeters decay geometrically, the
  first vertices form a Cauchy sequence, and at the limit point one cover
  element absorbs a small stage triangle (`tri_eq_zero_of_segments_subset`,
  the one-element base case), forcing the original boundary integral to
  vanish.
* **The coboundary theorem** (`exists_coboundary`): anchoring every index at
  a base point with `beta` produces the correcting `0`-cochain; convexity of
  the cover elements enters only through the base case of the slide from the
  anchor to a common point of an overlap.

## Claim discipline

Everything here is elementary metric topology and rational bookkeeping over
`ℂ` — no sheaf, no site, no cohomology group, no comparison with any
cohomology theory, and no claim of any Čech-to-derived-functor statement in
any generality: `exists_coboundary` is exactly the quantifier-explicit
coboundary statement printed above, for ℚ-valued functions on index pairs of
an open convex cover of the plane, and nothing more.  Nothing here makes the
Hodge conjecture statable.

## Credits

The bisection argument is Goursat's classical proof of the triangle lemma
(as in Cauchy–Goursat); the chain-subdivision bookkeeping replacing the
integral is this project's.  The Lebesgue number lemma, the convexity API
(`segment`, `convex_ball`, `Convex.segment_subset`), the geometric-series
Cauchy criterion (`cauchySeq_of_le_geometric`) and completeness of `ℂ` are
Mathlib's.
-/

noncomputable section

namespace HodgePilot

namespace CechGoursat

open Set

variable {ι : Type} (U : ι → Set ℂ) (q : ι → ι → ℚ)

/-! ## The cocycle condition and its degenerate consequences -/

/-- The Čech 1-cocycle condition on nonempty triple overlaps.-/
def Coc : Prop := ∀ i j k : ι, (U i ∩ U j ∩ U k).Nonempty → q i j + q j k = q i k

theorem Coc.self_eq_zero {U : ι → Set ℂ} {q : ι → ι → ℚ} (h : Coc U q) {i : ι}
    (hi : (U i).Nonempty) : q i i = 0 := by
  obtain ⟨x, hx⟩ := hi
  have := h i i i ⟨x, ⟨⟨hx, hx⟩, hx⟩⟩
  linarith

theorem Coc.antisymm {U : ι → Set ℂ} {q : ι → ι → ℚ} (h : Coc U q) {i j : ι}
    (hij : (U i ∩ U j).Nonempty) : q j i = - q i j := by
  obtain ⟨x, hx⟩ := hij
  have h1 := h i j i ⟨x, ⟨⟨hx.1, hx.2⟩, hx.1⟩⟩
  have h2 := h.self_eq_zero ⟨x, hx.1⟩
  linarith

/-! ## Uniform subdivision points -/

/-- The `k`-th uniform subdivision point of the segment from `z` to `w`
in `N` pieces.-/
def pt (z w : ℂ) (N k : ℕ) : ℂ := z + ((k : ℂ) / (N : ℂ)) * (w - z)

@[simp] theorem pt_zero (z w : ℂ) (N : ℕ) : pt z w N 0 = z := by
  simp [pt]

theorem pt_last (z w : ℂ) {N : ℕ} (hN : N ≠ 0) : pt z w N N = w := by
  have h : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [pt]
  rw [div_self h, one_mul]
  ring

/-- Shifting: the level-`n` subdivision points of `[pt z w (n+1) 1, w]` are the
tail of the level-`(n+1)` subdivision points of `[z, w]`.-/
theorem pt_shift (z w : ℂ) {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    pt (pt z w (n + 1) 1) w n k = pt z w (n + 1) (k + 1) := by
  have h1 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h2 : ((n : ℂ) + 1) ≠ 0 := by
    have h3 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    push_cast at h3
    exact h3
  simp only [pt]
  push_cast
  field_simp
  ring

/-! ## Valid chains for a uniform subdivision -/

/-- `l` is a valid chain for the uniform `l.length`-piece subdivision of
`[z, w]`: the `k`-th piece lies in `U l[k]`.-/
def Valid (z w : ℂ) (l : List ι) : Prop :=
  ∀ (k : ℕ) (hk : k < l.length),
    segment ℝ (pt z w l.length k) (pt z w l.length (k + 1)) ⊆ U (l[k]'hk)

theorem Valid.mem_left {U : ι → Set ℂ} {z w : ℂ} {l : List ι} (h : Valid U z w l)
    {k : ℕ} (hk : k < l.length) : pt z w l.length k ∈ U (l[k]'hk) :=
  h k hk (left_mem_segment ℝ _ _)

theorem Valid.mem_right {U : ι → Set ℂ} {z w : ℂ} {l : List ι} (h : Valid U z w l)
    {k : ℕ} (hk : k < l.length) : pt z w l.length (k + 1) ∈ U (l[k]'hk) :=
  h k hk (right_mem_segment ℝ _ _)

theorem Valid.head_mem_z {U : ι → Set ℂ} {z w : ℂ} {a : ι} {l : List ι}
    (h : Valid U z w (a :: l)) : z ∈ U a := by
  have h0 := h.mem_left (k := 0) (by simp)
  simpa using h0

theorem Valid.head_mem_pt1 {U : ι → Set ℂ} {z w : ℂ} {a : ι} {l : List ι}
    (h : Valid U z w (a :: l)) : pt z w (l.length + 1) 1 ∈ U a := by
  have h0 := h.mem_right (k := 0) (by simp)
  simpa using h0

theorem Valid.second_mem_pt1 {U : ι → Set ℂ} {z w : ℂ} {a b : ι} {l : List ι}
    (h : Valid U z w (a :: b :: l)) : pt z w (l.length + 2) 1 ∈ U b := by
  have h0 := h.mem_left (k := 1) (by simp)
  simpa using h0

theorem Valid.singleton_mem_w {U : ι → Set ℂ} {z w : ℂ} {a : ι}
    (h : Valid U z w [a]) : w ∈ U a := by
  have e : pt z w 1 1 = w := pt_last z w one_ne_zero
  have h0 := h.mem_right (k := 0) (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
    Nat.zero_add] at h0
  rwa [e] at h0

theorem Valid.used_nonempty {U : ι → Set ℂ} {z w : ℂ} {l : List ι}
    (h : Valid U z w l) {a : ι} (ha : a ∈ l) : (U a).Nonempty := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
  exact ⟨_, h.mem_left hk⟩

/-- Tail of a valid chain is valid for the shifted segment.-/
theorem Valid.tail {U : ι → Set ℂ} {z w : ℂ} {a : ι} {l : List ι}
    (h : Valid U z w (a :: l)) : Valid U (pt z w (l.length + 1) 1) w l := by
  intro k hk
  have hn : l.length ≠ 0 := by omega
  have e1 : pt (pt z w (l.length + 1) 1) w l.length k =
      pt z w (l.length + 1) (k + 1) := pt_shift z w hn k
  have e2 : pt (pt z w (l.length + 1) 1) w l.length (k + 1) =
      pt z w (l.length + 1) (k + 2) := pt_shift z w hn (k + 1)
  rw [e1, e2]
  have h1 := h (k + 1) (by simpa using Nat.succ_lt_succ hk)
  simpa using h1

/-- The one-piece chain through a single element containing the segment.-/
theorem valid_singleton {U : ι → Set ℂ} {z w : ℂ} {j : ι}
    (h : segment ℝ z w ⊆ U j) : Valid U z w [j] := by
  intro k hk
  have hk0 : k = 0 := by simpa using hk
  subst hk0
  have e : pt z w 1 1 = w := pt_last z w one_ne_zero
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
    Nat.zero_add, pt_zero]
  rwa [e]

/-! ## Walk sums -/

/-- The walk sum: transitions from `i` through the entries of `l` to `i'`.-/
def wSum (q : ι → ι → ℚ) : ι → List ι → ι → ℚ
  | i, [], i' => q i i'
  | i, a :: l, i' => q i a + wSum q a l i'

@[simp] theorem wSum_nil (i i' : ι) : wSum q i [] i' = q i i' := rfl

@[simp] theorem wSum_cons (i a i' : ι) (l : List ι) :
    wSum q i (a :: l) i' = q i a + wSum q a l i' := rfl

theorem wSum_append (i i' a : ι) (l₁ l₂ : List ι) :
    wSum q i (l₁ ++ a :: l₂) i' = wSum q i l₁ a + wSum q a l₂ i' := by
  induction l₁ generalizing i with
  | nil => simp
  | cons b l₁ ih => simp [ih, add_assoc]

/-! ## KILL-GATE 1: index-independence at a fixed level

Two valid chains of the same length for the same segment have the same walk
sum, whatever their indices — head recursion, two cocycle applications per
step, no ordering combinatorics. -/

theorem wSum_indep (hcoc : Coc U q) :
    ∀ (t t' : List ι) (a a' : ι) (z w : ℂ) (i i' : ι),
      t.length = t'.length →
      Valid U z w (a :: t) → Valid U z w (a' :: t') →
      z ∈ U i → w ∈ U i' →
      wSum q i (a :: t) i' = wSum q i (a' :: t') i' := by
  intro t
  induction t with
  | nil =>
    intro t' a a' z w i i' hlen hv hv' hz hw
    have ht' : t' = [] := by
      cases t' with
      | nil => rfl
      | cons b l => simp at hlen
    subst ht'
    have hza : z ∈ U a := hv.head_mem_z
    have hza' : z ∈ U a' := hv'.head_mem_z
    have hwa : w ∈ U a := hv.singleton_mem_w
    have hwa' : w ∈ U a' := hv'.singleton_mem_w
    have c1 : q i a + q a a' = q i a' := hcoc i a a' ⟨z, ⟨⟨hz, hza⟩, hza'⟩⟩
    have c2 : q a a' + q a' i' = q a i' := hcoc a a' i' ⟨w, ⟨⟨hwa, hwa'⟩, hw⟩⟩
    simp only [wSum_cons, wSum_nil]
    linarith
  | cons b t ih =>
    intro t' a a' z w i i' hlen hv hv' hz hw
    obtain ⟨b', t'', rfl⟩ : ∃ b' t'', t' = b' :: t'' := by
      cases t' with
      | nil => simp at hlen
      | cons b' t'' => exact ⟨b', t'', rfl⟩
    have hlen2 : t.length = t''.length := by simpa using hlen
    -- the common second subdivision point
    have hza : z ∈ U a := hv.head_mem_z
    have hza' : z ∈ U a' := hv'.head_mem_z
    have hz1a : pt z w (t.length + 2) 1 ∈ U a := by
      have h0 := hv.head_mem_pt1
      simpa using h0
    have hz1a' : pt z w (t.length + 2) 1 ∈ U a' := by
      have h0 := hv'.head_mem_pt1
      simp only [List.length_cons] at h0
      rwa [show t''.length + 1 + 1 = t.length + 2 by omega] at h0
    have hz1b' : pt z w (t.length + 2) 1 ∈ U b' := by
      have h0 := hv'.second_mem_pt1
      rwa [show t''.length + 2 = t.length + 2 by omega] at h0
    -- Step A: the tails are valid chains from the common point pt1
    have hta : Valid U (pt z w (t.length + 2) 1) w (b :: t) := by
      have h0 := hv.tail
      simpa using h0
    have hta' : Valid U (pt z w (t.length + 2) 1) w (b' :: t'') := by
      have h0 := hv'.tail
      simp only [List.length_cons] at h0
      rwa [show t''.length + 1 + 1 = t.length + 2 by omega] at h0
    have hIH : wSum q a (b :: t) i' = wSum q a (b' :: t'') i' :=
      ih t'' b b' (pt z w (t.length + 2) 1) w a i' hlen2 hta hta' hz1a hw
    -- Step B: head swap through two cocycles
    have c1 : q i a + q a a' = q i a' := hcoc i a a' ⟨z, ⟨⟨hz, hza⟩, hza'⟩⟩
    have c2 : q a a' + q a' b' = q a b' :=
      hcoc a a' b' ⟨pt z w (t.length + 2) 1, ⟨⟨hz1a, hz1a'⟩, hz1b'⟩⟩
    simp only [wSum_cons] at hIH ⊢
    linarith

/-! ## KILL-GATE 2: uniform refinement (blow-up) -/

/-- Uniform blow-up of a chain: replace each entry by `M` copies.-/
def blowup (M : ℕ) (l : List ι) : List ι := l.flatMap fun a => List.replicate M a

@[simp] theorem blowup_nil (M : ℕ) : blowup M ([] : List ι) = [] := rfl

@[simp] theorem blowup_cons (M : ℕ) (a : ι) (l : List ι) :
    blowup M (a :: l) = List.replicate M a ++ blowup M l := rfl

theorem blowup_length (M : ℕ) (l : List ι) :
    (blowup M l).length = l.length * M := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [blowup_cons, List.length_append, List.length_replicate, ih,
      List.length_cons]
    ring

theorem wSum_replicate_append (m : ℕ) (a i' : ι) (r : List ι) :
    wSum q a (List.replicate m a ++ r) i' = m * q a a + wSum q a r i' := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, wSum_cons, ih]
    push_cast
    ring

/-- Blowing up a chain does not change the walk sum (self-transitions vanish).-/
theorem wSum_blowup {M : ℕ} (hM : M ≠ 0) (i i' : ι) (l : List ι)
    (hq0 : ∀ a ∈ l, q a a = 0) :
    wSum q i (blowup M l) i' = wSum q i l i' := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    have h0 : q a a = 0 := hq0 a (List.mem_cons_self ..)
    rw [blowup_cons, List.replicate_succ, List.cons_append, wSum_cons,
      wSum_replicate_append, h0,
      ih a fun x hx => hq0 x (List.mem_cons_of_mem a hx)]
    simp

/-- Entry lookup in a blow-up.-/
theorem blowup_getElem {M : ℕ} (hM : M ≠ 0) (l : List ι) (k : ℕ)
    (hk : k < (blowup M l).length) (hk' : k / M < l.length) :
    (blowup M l)[k]'hk = l[k / M]'hk' := by
  induction l generalizing k with
  | nil => simp at hk'
  | cons a l ih =>
    by_cases h : k < M
    · have hd : k / M = 0 := Nat.div_eq_of_lt h
      have hlt : k < (List.replicate M a).length := by
        simpa [List.length_replicate] using h
      have hk2 : k < (List.replicate M a ++ blowup M l).length := by
        rw [blowup_cons] at hk; exact hk
      show (List.replicate M a ++ blowup M l)[k]'hk2 = (a :: l)[k / M]'hk'
      rw [List.getElem_append_left hlt]
      simp [hd]
    · have h : M ≤ k := Nat.le_of_not_lt h
      have hpos : 0 < M := Nat.pos_of_ne_zero hM
      have hd : k / M = (k - M) / M + 1 := Nat.div_eq_sub_div hpos h
      have hge : (List.replicate M a).length ≤ k := by
        simpa [List.length_replicate] using h
      have hkA : k < (List.replicate M a ++ blowup M l).length := by
        rw [blowup_cons] at hk; exact hk
      show (List.replicate M a ++ blowup M l)[k]'hkA = (a :: l)[k / M]'hk'
      rw [List.getElem_append_right hge]
      have hk2 : k - (List.replicate M a).length < (blowup M l).length := by
        simp only [List.length_replicate]
        rw [blowup_length] at hk ⊢
        simp only [List.length_cons, Nat.add_mul, one_mul] at hk
        omega
      have hk2' : (k - M) / M < l.length := by
        have h5 := hk'
        rw [hd] at h5
        simp only [List.length_cons] at h5
        omega
      have hrec := ih (k - M) (by simpa [List.length_replicate] using hk2) hk2'
      simp only [List.length_replicate]
      rw [hrec]
      have : l[(k - M) / M]'hk2' = (a :: l)[(k - M) / M + 1]'(by
        simp only [List.length_cons]; omega) := by
        rw [List.getElem_cons_succ]
      rw [this]
      congr 1
      omega

/-- The convex-combination core: a refined subdivision point lies on the
segment between the enclosing coarse subdivision points.-/
theorem pt_mem_segment_block {z w : ℂ} {n M a k : ℕ} (hn : n ≠ 0) (hM : M ≠ 0)
    (h1 : a * M ≤ k) (h2 : k ≤ (a + 1) * M) :
    pt z w (n * M) k ∈ segment ℝ (pt z w n a) (pt z w n (a + 1)) := by
  have hMR : (0 : ℝ) < (M : ℝ) := by
    have := Nat.pos_of_ne_zero hM
    exact_mod_cast this
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  set θ : ℝ := (k : ℝ) / (M : ℝ) - (a : ℝ) with hθ
  have hθ0 : 0 ≤ θ := by
    rw [hθ, sub_nonneg, le_div_iff₀ hMR]
    exact_mod_cast h1
  have hθ1 : θ ≤ 1 := by
    rw [hθ, sub_le_iff_le_add, div_le_iff₀ hMR]
    calc (k : ℝ) ≤ ((a + 1) * M : ℕ) := by exact_mod_cast h2
      _ = (1 + (a : ℝ)) * (M : ℝ) := by push_cast; ring
  refine ⟨1 - θ, θ, by linarith, hθ0, by ring, ?_⟩
  have hsmul : ∀ (r : ℝ) (c : ℂ), r • c = (r : ℂ) * c := fun r c =>
    Complex.real_smul
  rw [hsmul, hsmul]
  simp only [pt, hθ]
  push_cast
  field_simp
  ring

/-- Blowing up preserves validity.-/
theorem Valid.blowup {U : ι → Set ℂ} {z w : ℂ} {l : List ι}
    (h : Valid U z w l) {M : ℕ} (hM : M ≠ 0) : Valid U z w (CechGoursat.blowup M l) := by
  intro k hk
  have hkL : k < l.length * M := by rwa [blowup_length] at hk
  have hn : l.length ≠ 0 := by
    intro h0
    rw [h0] at hkL
    omega
  have hpos : 0 < M := Nat.pos_of_ne_zero hM
  have hdiv : k / M < l.length := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    omega
  rw [blowup_getElem hM l k hk hdiv]
  -- bounds for the block
  have hmod := Nat.div_add_mod k M
  have hmlt := Nat.mod_lt k hpos
  have hb1 : (k / M) * M ≤ k := Nat.div_mul_le_self k M
  have hb2 : k + 1 ≤ (k / M + 1) * M := by
    have : k < (k / M + 1) * M := by
      have h3 : (k / M + 1) * M = M * (k / M) + M := by ring
      omega
    omega
  have hsub : segment ℝ (pt z w ((CechGoursat.blowup M l).length) k)
      (pt z w ((CechGoursat.blowup M l).length) (k + 1)) ⊆
      segment ℝ (pt z w l.length (k / M)) (pt z w l.length (k / M + 1)) := by
    rw [blowup_length]
    exact (convex_segment _ _).segment_subset
      (pt_mem_segment_block hn hM hb1 (by omega))
      (pt_mem_segment_block hn hM (by omega) hb2)
  exact hsub.trans (h (k / M) hdiv)

/-! ## Well-definedness across levels: the walk sum depends only on the
segment and the endpoint indices -/

theorem wSum_welldef (hcoc : Coc U q) {z w : ℂ} {l l' : List ι}
    (hl : l ≠ []) (hl' : l' ≠ [])
    (hv : Valid U z w l) (hv' : Valid U z w l')
    {i i' : ι} (hz : z ∈ U i) (hw : w ∈ U i') :
    wSum q i l i' = wSum q i l' i' := by
  have hL : l.length ≠ 0 := fun h0 => hl (List.length_eq_zero_iff.mp h0)
  have hL' : l'.length ≠ 0 := fun h0 => hl' (List.length_eq_zero_iff.mp h0)
  have e1 : wSum q i (blowup l'.length l) i' = wSum q i l i' :=
    wSum_blowup q hL' i i' l fun x hx => hcoc.self_eq_zero (hv.used_nonempty hx)
  have e2 : wSum q i (blowup l.length l') i' = wSum q i l' i' :=
    wSum_blowup q hL i i' l' fun x hx => hcoc.self_eq_zero (hv'.used_nonempty hx)
  have hbv : Valid U z w (blowup l'.length l) := hv.blowup hL'
  have hbv' : Valid U z w (blowup l.length l') := hv'.blowup hL
  have hne : blowup l'.length l ≠ [] := by
    intro h0
    have h1 := blowup_length l'.length l
    rw [h0] at h1
    simp only [List.length_nil] at h1
    rcases Nat.mul_eq_zero.mp h1.symm with h2 | h2
    · exact hL h2
    · exact hL' h2
  have hne' : blowup l.length l' ≠ [] := by
    intro h0
    have h1 := blowup_length l.length l'
    rw [h0] at h1
    simp only [List.length_nil] at h1
    rcases Nat.mul_eq_zero.mp h1.symm with h2 | h2
    · exact hL' h2
    · exact hL h2
  obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨a', t', hat'⟩ := List.exists_cons_of_ne_nil hne'
  have hlen : t.length = t'.length := by
    have h1 : (a :: t).length = (a' :: t').length := by
      rw [← hat, ← hat', blowup_length, blowup_length]
      ring
    simpa using h1
  rw [← e1, ← e2, hat, hat']
  exact wSum_indep U q hcoc t t' a a' z w i i' hlen (hat ▸ hbv) (hat' ▸ hbv')
    hz hw

/-! ## Existence of valid chains (Lebesgue number on the segment) -/

/-- Subdivision points lie on the segment.-/
theorem pt_mem_segment {z w : ℂ} {N k : ℕ} (hN : N ≠ 0) (hk : k ≤ N) :
    pt z w N k ∈ segment ℝ z w := by
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have := Nat.pos_of_ne_zero hN
    exact_mod_cast this
  set θ : ℝ := (k : ℝ) / (N : ℝ) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hNR]
    exact_mod_cast hk
  refine ⟨1 - θ, θ, by linarith, hθ0, by ring, ?_⟩
  have hsmul : ∀ (r : ℝ) (c : ℂ), r • c = (r : ℂ) * c := fun r c =>
    Complex.real_smul
  rw [hsmul, hsmul]
  simp only [pt, hθ]
  push_cast
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp
  ring

/-- Adjacent subdivision points are `dist z w / N` apart.-/
theorem dist_pt_succ (z w : ℂ) {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    dist (pt z w N (k + 1)) (pt z w N k) = dist z w / N := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [dist_eq_norm]
  have e : pt z w N (k + 1) - pt z w N k = (1 / (N : ℂ)) * (w - z) := by
    simp only [pt]
    push_cast
    field_simp
    ring
  rw [e, norm_mul, dist_eq_norm]
  simp only [one_div, norm_inv, Complex.norm_natCast]
  rw [norm_sub_rev]
  ring

theorem exists_valid_chain (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (z w : ℂ) : ∃ l : List ι, l ≠ [] ∧ Valid U z w l := by
  have hcpt : IsCompact (segment ℝ z w) := by
    rw [segment_eq_image ℝ z w]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric hcpt hop
    (by rw [hcov]; exact subset_univ _)
  obtain ⟨N, hN⟩ := exists_nat_gt (dist z w / δ)
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0] at hN
    simp only [Nat.cast_zero] at hN
    have : 0 ≤ dist z w / δ := div_nonneg dist_nonneg hδ.le
    linarith
  have hstep : dist z w / N < δ := by
    rw [div_lt_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hN0)]
    rw [div_lt_iff₀ hδ] at hN
    linarith [mul_comm δ (N : ℝ)]
  have hmem : ∀ k : ℕ, k < N → pt z w N k ∈ segment ℝ z w :=
    fun k hk => pt_mem_segment hN0 hk.le
  choose f hf using fun k : Fin N =>
    hball (pt z w N k.1) (hmem k.1 k.2)
  refine ⟨List.ofFn f, ?_, ?_⟩
  · intro h0
    have := congrArg List.length h0
    simp only [List.length_ofFn, List.length_nil] at this
    exact hN0 this
  · intro k hk
    have hkN : k < N := by simpa using hk
    have hsub : segment ℝ (pt z w (List.ofFn f).length k)
        (pt z w (List.ofFn f).length (k + 1)) ⊆
        Metric.ball (pt z w N k) δ := by
      simp only [List.length_ofFn]
      have hcb : segment ℝ (pt z w N k) (pt z w N (k + 1)) ⊆
          Metric.closedBall (pt z w N k) (dist z w / N) := by
        apply (convex_closedBall _ _).segment_subset
        · simp [Metric.mem_closedBall, div_nonneg dist_nonneg (Nat.cast_nonneg N)]
        · rw [Metric.mem_closedBall]
          rw [dist_pt_succ z w hN0 k]
      exact hcb.trans (Metric.closedBall_subset_ball hstep)
    have hgoal := hsub.trans (hf ⟨k, hkN⟩)
    have hgetElem : (List.ofFn f)[k]'hk = f ⟨k, hkN⟩ := by
      simp
    rw [hgetElem]
    exact hgoal

/-- The chain integral between two points with endpoint indices: well-defined
by `wSum_welldef`.-/
def beta (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (z w : ℂ) (i i' : ι) : ℚ :=
  wSum q i (exists_valid_chain U hop hcov z w).choose i'

theorem beta_spec (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (hcoc : Coc U q) {z w : ℂ} {l : List ι} (hl : l ≠ []) (hv : Valid U z w l)
    {i i' : ι} (hz : z ∈ U i) (hw : w ∈ U i') :
    beta U q hop hcov z w i i' = wSum q i l i' :=
  wSum_welldef U q hcoc (exists_valid_chain U hop hcov z w).choose_spec.1 hl
    (exists_valid_chain U hop hcov z w).choose_spec.2 hv hz hw

/-- One-element evaluation: through a single element containing the segment.-/
theorem beta_of_segment_subset (hop : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = univ) (hcoc : Coc U q) {z w : ℂ} {j : ι}
    (hseg : segment ℝ z w ⊆ U j) {i i' : ι} (hz : z ∈ U i) (hw : w ∈ U i') :
    beta U q hop hcov z w i i' = q i j + q j i' := by
  rw [beta_spec U q hop hcov hcoc (by simp) (valid_singleton hseg) hz hw]
  rfl

/-! ## The Goursat layer: midpoint splitting, orientation reversal, the
subdivision identity, and the bisection -/

/-! ### Midpoint splitting (proved) -/

theorem pt_concat_left (z w : ℂ) {N : ℕ} (hN : N ≠ 0) (j : ℕ) :
    pt z w (N + N) j = pt z ((z + w) / 2) N j := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have h2N : (N : ℂ) + (N : ℂ) ≠ 0 := by
    rw [← two_mul]
    exact mul_ne_zero two_ne_zero hNC
  simp only [pt]
  push_cast
  field_simp
  ring

theorem pt_concat_right (z w : ℂ) {N : ℕ} (hN : N ≠ 0) (j : ℕ) :
    pt z w (N + N) (N + j) = pt ((z + w) / 2) w N j := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have h2N : (N : ℂ) + (N : ℂ) ≠ 0 := by
    rw [← two_mul]
    exact mul_ne_zero two_ne_zero hNC
  simp only [pt]
  push_cast
  field_simp
  ring

/-- Two equal-length valid chains on the two halves concatenate to a valid
chain on the whole segment (the level-`2N` subdivision restricts to the
level-`N` subdivisions of the halves).-/
theorem Valid.append_halves {U : ι → Set ℂ} {z w : ℂ} {l₁ l₂ : List ι}
    (h₁ : Valid U z ((z + w) / 2) l₁) (h₂ : Valid U ((z + w) / 2) w l₂)
    (hlen : l₁.length = l₂.length) : Valid U z w (l₁ ++ l₂) := by
  intro k hk
  have hLL : (l₁ ++ l₂).length = l₁.length + l₁.length := by
    rw [List.length_append, hlen]
  have hk2 : k < l₁.length + l₁.length := by rwa [hLL] at hk
  have hN : l₁.length ≠ 0 := by omega
  by_cases hcase : k < l₁.length
  · have e1 : pt z w ((l₁ ++ l₂).length) k = pt z ((z + w) / 2) l₁.length k := by
      rw [hLL]
      exact pt_concat_left z w hN k
    have e2 : pt z w ((l₁ ++ l₂).length) (k + 1) =
        pt z ((z + w) / 2) l₁.length (k + 1) := by
      rw [hLL]
      exact pt_concat_left z w hN (k + 1)
    have hidx : (l₁ ++ l₂)[k]'hk = l₁[k]'hcase := List.getElem_append_left hcase
    rw [e1, e2, hidx]
    exact h₁ k hcase
  · obtain ⟨j, rfl⟩ : ∃ j, k = l₁.length + j := ⟨k - l₁.length, by omega⟩
    have hj : j < l₂.length := by omega
    have e1 : pt z w ((l₁ ++ l₂).length) (l₁.length + j) =
        pt ((z + w) / 2) w l₂.length j := by
      rw [hLL, pt_concat_right z w hN j, hlen]
    have e2 : pt z w ((l₁ ++ l₂).length) (l₁.length + j + 1) =
        pt ((z + w) / 2) w l₂.length (j + 1) := by
      rw [hLL]
      have : l₁.length + j + 1 = l₁.length + (j + 1) := by omega
      rw [this, pt_concat_right z w hN (j + 1), hlen]
    have hle : l₁.length ≤ l₁.length + j := by omega
    have hidx : (l₁ ++ l₂)[l₁.length + j]'hk =
        l₂[l₁.length + j - l₁.length]'(by omega) :=
      List.getElem_append_right hle
    have hidx2 : l₂[l₁.length + j - l₁.length]'(by omega) = l₂[j]'hj := by
      congr 1
      omega
    rw [e1, e2, hidx, hidx2]
    exact h₂ j hj

/-- The last element of a valid chain contains the right endpoint.-/
theorem Valid.getLast_mem_w {U : ι → Set ℂ} {w : ℂ} :
    ∀ (l : List ι) {z : ℂ} (hne : l ≠ []) (_ : Valid U z w l),
      w ∈ U (l.getLast hne) := by
  intro l
  induction l with
  | nil => intro z h; exact absurd rfl h
  | cons a t ih =>
    intro z _ hv
    cases t with
    | nil => simpa using hv.singleton_mem_w
    | cons b t₂ =>
      have h1 := ih (z := pt z w ((b :: t₂).length + 1) 1) (by simp) hv.tail
      simpa [List.getLast_cons] using h1

/-- Swapping the terminal index of a walk at a common point of the last
element (one cocycle application, by induction).-/
theorem wSum_swap_right (hcoc : Coc U q) :
    ∀ (l : List ι) (a : ι) {x : ℂ} {b b' i : ι},
      x ∈ U b → x ∈ U b' → x ∈ U ((a :: l).getLast (by simp)) →
      wSum q i (a :: l) b = wSum q i (a :: l) b' + q b' b := by
  intro l
  induction l with
  | nil =>
    intro a x b b' i hb hb' hlast
    have hlast' : x ∈ U a := by simpa using hlast
    have c1 : q a b' + q b' b = q a b := hcoc a b' b ⟨x, ⟨⟨hlast', hb'⟩, hb⟩⟩
    simp only [wSum_cons, wSum_nil]
    linarith
  | cons c t ih =>
    intro a x b b' i hb hb' hlast
    have hlast' : x ∈ U ((c :: t).getLast (by simp)) := by
      simpa [List.getLast_cons] using hlast
    have h1 := ih c hb hb' hlast' (i := a)
    simp only [wSum_cons] at h1 ⊢
    linarith

/-- **Midpoint splitting of the chain integral** (proved).-/
theorem beta_split_mid (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (hcoc : Coc U q) (z w : ℂ) (i i' im : ι)
    (hm : (z + w) / 2 ∈ U im) (hz : z ∈ U i) (hw : w ∈ U i') :
    beta U q hop hcov z w i i' =
      beta U q hop hcov z ((z + w) / 2) i im +
        beta U q hop hcov ((z + w) / 2) w im i' := by
  set m : ℂ := (z + w) / 2 with hmdef
  obtain ⟨l₁, hl₁, hv₁⟩ := exists_valid_chain U hop hcov z m
  obtain ⟨l₂, hl₂, hv₂⟩ := exists_valid_chain U hop hcov m w
  have hL1 : l₁.length ≠ 0 := fun h0 => hl₁ (List.length_eq_zero_iff.mp h0)
  have hL2 : l₂.length ≠ 0 := fun h0 => hl₂ (List.length_eq_zero_iff.mp h0)
  set L₁ : List ι := CechGoursat.blowup l₂.length l₁ with hL₁def
  set L₂ : List ι := CechGoursat.blowup l₁.length l₂ with hL₂def
  have hbv₁ : Valid U z m L₁ := hv₁.blowup hL2
  have hbv₂ : Valid U m w L₂ := hv₂.blowup hL1
  have hlen : L₁.length = L₂.length := by
    rw [hL₁def, hL₂def, blowup_length, blowup_length]
    ring
  have hL₁ne : L₁ ≠ [] := by
    intro h0
    have h1 := blowup_length l₂.length l₁
    rw [← hL₁def, h0] at h1
    simp only [List.length_nil] at h1
    rcases Nat.mul_eq_zero.mp h1.symm with h2 | h2
    · exact hL1 h2
    · exact hL2 h2
  have hL₂ne : L₂ ≠ [] := by
    intro h0
    have h1 := blowup_length l₁.length l₂
    rw [← hL₂def, h0] at h1
    simp only [List.length_nil] at h1
    rcases Nat.mul_eq_zero.mp h1.symm with h2 | h2
    · exact hL2 h2
    · exact hL1 h2
  obtain ⟨a₂, t₂, hat₂⟩ := List.exists_cons_of_ne_nil hL₂ne
  -- the appended chain computes beta z w
  have happ : Valid U z w (L₁ ++ L₂) := hbv₁.append_halves hbv₂ hlen
  have happne : L₁ ++ L₂ ≠ [] := fun h0 => hL₁ne (List.append_eq_nil_iff.mp h0).1
  have hbeta : beta U q hop hcov z w i i' = wSum q i (L₁ ++ L₂) i' :=
    beta_spec U q hop hcov hcoc happne happ hz hw
  -- the two halves compute the two betas
  have hbeta₁ : beta U q hop hcov z m i im = wSum q i L₁ im :=
    beta_spec U q hop hcov hcoc hL₁ne hbv₁ hz hm
  have hbeta₂ : beta U q hop hcov m w im i' = wSum q im L₂ i' :=
    beta_spec U q hop hcov hcoc hL₂ne hbv₂ hm hw
  -- memberships at the midpoint
  have hma₂ : m ∈ U a₂ := by
    have := hbv₂
    rw [hat₂] at this
    exact this.head_mem_z
  have hmlast : m ∈ U (L₁.getLast hL₁ne) := Valid.getLast_mem_w L₁ hL₁ne hbv₁
  -- assemble
  obtain ⟨a₁, t₁, hat₁⟩ := List.exists_cons_of_ne_nil hL₁ne
  have hbv₁' : Valid U z m (a₁ :: t₁) := hat₁ ▸ hbv₁
  have hswap : wSum q i L₁ a₂ = wSum q i L₁ im + q im a₂ := by
    rw [hat₁]
    exact wSum_swap_right U q hcoc t₁ a₁ hma₂ hm
      (Valid.getLast_mem_w (a₁ :: t₁) (by simp) hbv₁')
  calc beta U q hop hcov z w i i'
      = wSum q i (L₁ ++ a₂ :: t₂) i' := by rw [hbeta, hat₂]
    _ = wSum q i L₁ a₂ + wSum q a₂ t₂ i' := wSum_append q i i' a₂ L₁ t₂
    _ = wSum q i L₁ im + (q im a₂ + wSum q a₂ t₂ i') := by
        rw [hswap]; ring
    _ = wSum q i L₁ im + wSum q im (a₂ :: t₂) i' := by rw [wSum_cons]
    _ = beta U q hop hcov z m i im + beta U q hop hcov m w im i' := by
        rw [hbeta₁, hbeta₂, hat₂]

/-! ### Orientation reversal (proved) -/

theorem pt_rev (z w : ℂ) {N k : ℕ} (hN : N ≠ 0) (hk : k ≤ N) :
    pt w z N k = pt z w N (N - k) := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hcast : ((N - k : ℕ) : ℂ) = (N : ℂ) - (k : ℂ) := by
    rw [Nat.cast_sub hk]
  simp only [pt, hcast]
  field_simp
  ring

/-- Reversed chains are valid for the reversed segment.-/
theorem Valid.reverse {U : ι → Set ℂ} {z w : ℂ} {l : List ι}
    (h : Valid U z w l) : Valid U w z l.reverse := by
  intro k hk
  have hkl : k < l.length := by simpa using hk
  have hn : l.length ≠ 0 := by omega
  have e1' : pt w z l.length k = pt z w l.length (l.length - 1 - k + 1) := by
    rw [pt_rev z w hn hkl.le]
    congr 1
    omega
  have e2' : pt w z l.length (k + 1) = pt z w l.length (l.length - 1 - k) := by
    rw [pt_rev z w hn (by omega : k + 1 ≤ l.length)]
    congr 1
    omega
  simp only [List.length_reverse, List.getElem_reverse]
  rw [e1', e2', segment_symm]
  exact h (l.length - 1 - k) (by omega)

/-- Consecutive-overlap structure of a walk.-/
def Adj (U : ι → Set ℂ) : ι → List ι → ι → Prop
  | i, [], i' => (U i ∩ U i').Nonempty
  | i, a :: l, i' => (U i ∩ U a).Nonempty ∧ Adj U a l i'

theorem Valid.adj {U : ι → Set ℂ} {w : ℂ} :
    ∀ (l : List ι) {z : ℂ} (_ : l ≠ []) (_ : Valid U z w l) {i i' : ι}
      (_ : z ∈ U i) (_ : w ∈ U i'), Adj U i l i' := by
  intro l
  induction l with
  | nil => intro z h; exact absurd rfl h
  | cons a t ih =>
    intro z _ hv i i' hz hw
    refine ⟨⟨z, hz, hv.head_mem_z⟩, ?_⟩
    cases t with
    | nil => exact ⟨w, hv.singleton_mem_w, hw⟩
    | cons b t₂ =>
      exact ih (by simp) hv.tail hv.head_mem_pt1 hw

/-- Walk sums reverse to their negatives along adjacency.-/
theorem wSum_rev (hcoc : Coc U q) :
    ∀ (l : List ι) {i i' : ι} (_ : Adj U i l i'),
      wSum q i' l.reverse i = - wSum q i l i' := by
  intro l
  induction l with
  | nil =>
    intro i i' hadj
    simpa using hcoc.antisymm hadj
  | cons a t ih =>
    intro i i' hadj
    have h1 : (a :: t).reverse = t.reverse ++ a :: [] := by simp
    rw [h1, wSum_append]
    rw [ih hadj.2, wSum_nil, wSum_cons]
    have h2 : q a i = - q i a := hcoc.antisymm hadj.1
    linarith

/-- **Orientation reversal of the chain integral** (proved).-/
theorem beta_rev (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (hcoc : Coc U q) (z w : ℂ) (i i' : ι) (hz : z ∈ U i) (hw : w ∈ U i') :
    beta U q hop hcov w z i' i = - beta U q hop hcov z w i i' := by
  obtain ⟨l, hl, hv⟩ := exists_valid_chain U hop hcov z w
  have hrev : beta U q hop hcov w z i' i = wSum q i' l.reverse i :=
    beta_spec U q hop hcov hcoc (by simpa using hl) hv.reverse hw hz
  have hfwd : beta U q hop hcov z w i i' = wSum q i l i' :=
    beta_spec U q hop hcov hcoc hl hv hz hw
  rw [hrev, hfwd, wSum_rev U q hcoc l (Valid.adj l hl hv hz hw)]

/-- The boundary chain integral of a triangle with vertex indices.-/
def tri (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (a b c : ℂ) (ia ib ic : ι) : ℚ :=
  beta U q hop hcov a b ia ib + beta U q hop hcov b c ib ic +
    beta U q hop hcov c a ic ia

/-- **The Goursat subdivision identity** (proved): the boundary integral of a
triangle is the sum of the boundary integrals of its four midpoint children —
`beta_split_mid` on the three edges, the three interior edges cancel by
`beta_rev`.-/
theorem tri_subdiv (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (hcoc : Coc U q) (a b c : ℂ) (ia ib ic iab ibc ica : ι)
    (ha : a ∈ U ia) (hb : b ∈ U ib) (hc : c ∈ U ic)
    (hab : (a + b) / 2 ∈ U iab) (hbc : (b + c) / 2 ∈ U ibc)
    (hca : (c + a) / 2 ∈ U ica) :
    tri U q hop hcov a b c ia ib ic =
      tri U q hop hcov a ((a + b) / 2) ((c + a) / 2) ia iab ica +
      tri U q hop hcov ((a + b) / 2) b ((b + c) / 2) iab ib ibc +
      tri U q hop hcov ((c + a) / 2) ((b + c) / 2) c ica ibc ic +
      tri U q hop hcov ((a + b) / 2) ((b + c) / 2) ((c + a) / 2) iab ibc ica := by
  have s1 := beta_split_mid U q hop hcov hcoc a b ia ib iab hab ha hb
  have s2 := beta_split_mid U q hop hcov hcoc b c ib ic ibc hbc hb hc
  have s3 := beta_split_mid U q hop hcov hcoc c a ic ia ica hca hc ha
  have r1 := beta_rev U q hop hcov hcoc ((a + b) / 2) ((c + a) / 2) iab ica
    hab hca
  have r2 := beta_rev U q hop hcov hcoc ((a + b) / 2) ((b + c) / 2) iab ibc
    hab hbc
  have r3 := beta_rev U q hop hcov hcoc ((c + a) / 2) ((b + c) / 2) ica ibc
    hca hbc
  simp only [tri]
  linarith

/-! ### The bisection state and its invariants -/

/-- The state of the Goursat bisection: a triangle with vertex indices and
membership witnesses.-/
structure GTri where
  /-- The first vertex.-/
  a : ℂ
  /-- The second vertex.-/
  b : ℂ
  /-- The third vertex.-/
  c : ℂ
  /-- The cover index of the first vertex.-/
  ia : ι
  /-- The cover index of the second vertex.-/
  ib : ι
  /-- The cover index of the third vertex.-/
  ic : ι
  /-- The first vertex lies in its cover element.-/
  ha : a ∈ U ia
  /-- The second vertex lies in its cover element.-/
  hb : b ∈ U ib
  /-- The third vertex lies in its cover element.-/
  hc : c ∈ U ic

/-- The perimeter of a bisection state.-/
def GTri.perim (T : GTri U) : ℝ := dist T.a T.b + dist T.b T.c + dist T.c T.a

theorem GTri.perim_nonneg (T : GTri U) : 0 ≤ T.perim := by
  have h1 : (0 : ℝ) ≤ dist T.a T.b := dist_nonneg
  have h2 : (0 : ℝ) ≤ dist T.b T.c := dist_nonneg
  have h3 : (0 : ℝ) ≤ dist T.c T.a := dist_nonneg
  show (0 : ℝ) ≤ dist T.a T.b + dist T.b T.c + dist T.c T.a
  linarith

theorem GTri.dist_ba_le_perim (T : GTri U) : dist T.b T.a ≤ T.perim := by
  have h1 : (0 : ℝ) ≤ dist T.b T.c := dist_nonneg
  have h2 : (0 : ℝ) ≤ dist T.c T.a := dist_nonneg
  rw [dist_comm]
  show dist T.a T.b ≤ dist T.a T.b + dist T.b T.c + dist T.c T.a
  linarith

theorem GTri.dist_ca_le_perim (T : GTri U) : dist T.c T.a ≤ T.perim := by
  have h1 : (0 : ℝ) ≤ dist T.a T.b := dist_nonneg
  have h2 : (0 : ℝ) ≤ dist T.b T.c := dist_nonneg
  show dist T.c T.a ≤ dist T.a T.b + dist T.b T.c + dist T.c T.a
  linarith

/-- The boundary chain integral of a bisection state.-/
def triVal (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ) (T : GTri U) :
    ℚ :=
  tri U q hop hcov T.a T.b T.c T.ia T.ib T.ic

/-- Distance halving along an exhibited midpoint relation.-/
theorem dist_eq_half_of_sub_eq {x y u v : ℂ} (h : x - y = (u - v) / 2) :
    dist x y = dist u v / 2 := by
  rw [dist_eq_norm, dist_eq_norm, h, norm_div, Complex.norm_two]

/-- Some cover element contains any given point.-/
theorem exists_idx (hcov : ⋃ i, U i = univ) (z : ℂ) : ∃ i, z ∈ U i :=
  Set.mem_iUnion.mp (by rw [hcov]; trivial)

/-- A sum of four terms has a summand carrying at least a quarter of its
absolute value.-/
theorem abs_le_four_of_eq_sum {s t0 t1 t2 t3 : ℚ} (h : s = t0 + t1 + t2 + t3) :
    |s| ≤ 4 * |t0| ∨ |s| ≤ 4 * |t1| ∨ |s| ≤ 4 * |t2| ∨ |s| ≤ 4 * |t3| := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1, h2, h3⟩ := hcon
  have e1 : |t0 + t1| ≤ |t0| + |t1| := abs_add_le _ _
  have e2 : |t0 + t1 + t2| ≤ |t0 + t1| + |t2| := abs_add_le _ _
  have e3 : |s| ≤ |t0 + t1 + t2| + |t3| := by rw [h]; exact abs_add_le _ _
  linarith

/-- **Child selection**: every bisection state has a midpoint child carrying
at least a quarter of the boundary integral, half the perimeter, and a first
vertex within half the perimeter of the parent's.-/
theorem exists_goursat_child (hop : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = univ) (hcoc : Coc U q) (T : GTri U) :
    ∃ T' : GTri U,
      |triVal U q hop hcov T| ≤ 4 * |triVal U q hop hcov T'| ∧
        T'.perim = T.perim / 2 ∧ dist T'.a T.a ≤ T.perim / 2 := by
  obtain ⟨iab, hiab⟩ := exists_idx U hcov ((T.a + T.b) / 2)
  obtain ⟨ibc, hibc⟩ := exists_idx U hcov ((T.b + T.c) / 2)
  obtain ⟨ica, hica⟩ := exists_idx U hcov ((T.c + T.a) / 2)
  have hsub := tri_subdiv U q hop hcov hcoc T.a T.b T.c T.ia T.ib T.ic
    iab ibc ica T.ha T.hb T.hc hiab hibc hica
  rcases abs_le_four_of_eq_sum hsub with h | h | h | h
  · refine ⟨⟨T.a, (T.a + T.b) / 2, (T.c + T.a) / 2, T.ia, iab, ica,
      T.ha, hiab, hica⟩, h, ?_, ?_⟩
    · have e1 : dist T.a ((T.a + T.b) / 2) = dist T.a T.b / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      have e2 : dist ((T.a + T.b) / 2) ((T.c + T.a) / 2) = dist T.b T.c / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      have e3 : dist ((T.c + T.a) / 2) T.a = dist T.c T.a / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      show dist T.a ((T.a + T.b) / 2) + dist ((T.a + T.b) / 2) ((T.c + T.a) / 2) +
          dist ((T.c + T.a) / 2) T.a = T.perim / 2
      rw [e1, e2, e3]
      show dist T.a T.b / 2 + dist T.b T.c / 2 + dist T.c T.a / 2 =
        (dist T.a T.b + dist T.b T.c + dist T.c T.a) / 2
      ring
    · show dist T.a T.a ≤ T.perim / 2
      have h0 := T.perim_nonneg
      rw [dist_self]
      linarith
  · refine ⟨⟨(T.a + T.b) / 2, T.b, (T.b + T.c) / 2, iab, T.ib, ibc,
      hiab, T.hb, hibc⟩, h, ?_, ?_⟩
    · have e1 : dist ((T.a + T.b) / 2) T.b = dist T.a T.b / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      have e2 : dist T.b ((T.b + T.c) / 2) = dist T.b T.c / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      have e3 : dist ((T.b + T.c) / 2) ((T.a + T.b) / 2) = dist T.c T.a / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      show dist ((T.a + T.b) / 2) T.b + dist T.b ((T.b + T.c) / 2) +
          dist ((T.b + T.c) / 2) ((T.a + T.b) / 2) = T.perim / 2
      rw [e1, e2, e3]
      show dist T.a T.b / 2 + dist T.b T.c / 2 + dist T.c T.a / 2 =
        (dist T.a T.b + dist T.b T.c + dist T.c T.a) / 2
      ring
    · show dist ((T.a + T.b) / 2) T.a ≤ T.perim / 2
      have e1 : dist ((T.a + T.b) / 2) T.a = dist T.b T.a / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      have h0 := T.dist_ba_le_perim
      rw [e1]
      linarith
  · refine ⟨⟨(T.c + T.a) / 2, (T.b + T.c) / 2, T.c, ica, ibc, T.ic,
      hica, hibc, T.hc⟩, h, ?_, ?_⟩
    · have e1 : dist ((T.c + T.a) / 2) ((T.b + T.c) / 2) = dist T.a T.b / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      have e2 : dist ((T.b + T.c) / 2) T.c = dist T.b T.c / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      have e3 : dist T.c ((T.c + T.a) / 2) = dist T.c T.a / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      show dist ((T.c + T.a) / 2) ((T.b + T.c) / 2) + dist ((T.b + T.c) / 2) T.c +
          dist T.c ((T.c + T.a) / 2) = T.perim / 2
      rw [e1, e2, e3]
      show dist T.a T.b / 2 + dist T.b T.c / 2 + dist T.c T.a / 2 =
        (dist T.a T.b + dist T.b T.c + dist T.c T.a) / 2
      ring
    · show dist ((T.c + T.a) / 2) T.a ≤ T.perim / 2
      have e1 : dist ((T.c + T.a) / 2) T.a = dist T.c T.a / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      have h0 := T.dist_ca_le_perim
      rw [e1]
      linarith
  · refine ⟨⟨(T.a + T.b) / 2, (T.b + T.c) / 2, (T.c + T.a) / 2, iab, ibc, ica,
      hiab, hibc, hica⟩, h, ?_, ?_⟩
    · have e1 : dist ((T.a + T.b) / 2) ((T.b + T.c) / 2) = dist T.a T.c / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      have e2 : dist ((T.b + T.c) / 2) ((T.c + T.a) / 2) = dist T.b T.a / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      have e3 : dist ((T.c + T.a) / 2) ((T.a + T.b) / 2) = dist T.c T.b / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      show dist ((T.a + T.b) / 2) ((T.b + T.c) / 2) +
          dist ((T.b + T.c) / 2) ((T.c + T.a) / 2) +
          dist ((T.c + T.a) / 2) ((T.a + T.b) / 2) = T.perim / 2
      rw [e1, e2, e3, dist_comm T.a T.c, dist_comm T.b T.a, dist_comm T.c T.b]
      show dist T.c T.a / 2 + dist T.a T.b / 2 + dist T.b T.c / 2 =
        (dist T.a T.b + dist T.b T.c + dist T.c T.a) / 2
      ring
    · show dist ((T.a + T.b) / 2) T.a ≤ T.perim / 2
      have e1 : dist ((T.a + T.b) / 2) T.a = dist T.b T.a / 2 :=
        dist_eq_half_of_sub_eq (by ring)
      have h0 := T.dist_ba_le_perim
      rw [e1]
      linarith

/-- The Goursat bisection sequence: iterated choice of a quarter-carrying
midpoint child.-/
def gseq (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ) (hcoc : Coc U q)
    (T0 : GTri U) : ℕ → GTri U
  | 0 => T0
  | n + 1 => (exists_goursat_child U q hop hcov hcoc
      (gseq hop hcov hcoc T0 n)).choose

theorem gseq_zero (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (hcoc : Coc U q) (T0 : GTri U) : gseq U q hop hcov hcoc T0 0 = T0 := rfl

theorem gseq_succ (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (hcoc : Coc U q) (T0 : GTri U) (n : ℕ) :
    gseq U q hop hcov hcoc T0 (n + 1) =
      (exists_goursat_child U q hop hcov hcoc
        (gseq U q hop hcov hcoc T0 n)).choose := rfl

/-- The boundary integral decays at worst geometrically along the bisection.-/
theorem gseq_val_le (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (hcoc : Coc U q) (T0 : GTri U) (n : ℕ) :
    |triVal U q hop hcov T0| ≤
      4 ^ n * |triVal U q hop hcov (gseq U q hop hcov hcoc T0 n)| := by
  induction n with
  | zero =>
    rw [gseq_zero]
    norm_num
  | succ n ih =>
    have hstep := (exists_goursat_child U q hop hcov hcoc
      (gseq U q hop hcov hcoc T0 n)).choose_spec.1
    have h4 : (0 : ℚ) ≤ 4 ^ n := by positivity
    rw [gseq_succ]
    calc |triVal U q hop hcov T0|
        ≤ 4 ^ n * |triVal U q hop hcov (gseq U q hop hcov hcoc T0 n)| := ih
      _ ≤ 4 ^ n * (4 * |triVal U q hop hcov ((exists_goursat_child U q hop hcov
            hcoc (gseq U q hop hcov hcoc T0 n)).choose)|) :=
          mul_le_mul_of_nonneg_left hstep h4
      _ = 4 ^ (n + 1) * |triVal U q hop hcov ((exists_goursat_child U q hop hcov
            hcoc (gseq U q hop hcov hcoc T0 n)).choose)| := by ring

/-- The perimeter halves at every stage.-/
theorem gseq_perim (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (hcoc : Coc U q) (T0 : GTri U) (n : ℕ) :
    (gseq U q hop hcov hcoc T0 n).perim = T0.perim / 2 ^ n := by
  induction n with
  | zero =>
    rw [gseq_zero]
    norm_num
  | succ n ih =>
    have hstep := (exists_goursat_child U q hop hcov hcoc
      (gseq U q hop hcov hcoc T0 n)).choose_spec.2.1
    rw [gseq_succ, hstep, ih, div_div, ← pow_succ]

/-- The first vertices advance by at most a halving geometric step.-/
theorem gseq_dist (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (hcoc : Coc U q) (T0 : GTri U) (n : ℕ) :
    dist (gseq U q hop hcov hcoc T0 (n + 1)).a
      (gseq U q hop hcov hcoc T0 n).a ≤ T0.perim / 2 ^ (n + 1) := by
  have hstep := (exists_goursat_child U q hop hcov hcoc
    (gseq U q hop hcov hcoc T0 n)).choose_spec.2.2
  rw [gseq_succ]
  calc dist ((exists_goursat_child U q hop hcov hcoc
        (gseq U q hop hcov hcoc T0 n)).choose).a (gseq U q hop hcov hcoc T0 n).a
      ≤ (gseq U q hop hcov hcoc T0 n).perim / 2 := hstep
    _ = T0.perim / 2 ^ (n + 1) := by
        rw [gseq_perim U q hop hcov hcoc T0 n, div_div, ← pow_succ]

/-! ### The base case and the limit point -/

/-- **The one-element base case**: a triangle whose three edges lie in a
single cover element has vanishing boundary integral.-/
theorem tri_eq_zero_of_segments_subset (hop : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = univ) (hcoc : Coc U q) {a b c : ℂ} {j ia ib ic : ι}
    (hab : segment ℝ a b ⊆ U j) (hbc : segment ℝ b c ⊆ U j)
    (hca : segment ℝ c a ⊆ U j) (ha : a ∈ U ia) (hb : b ∈ U ib)
    (hc : c ∈ U ic) : tri U q hop hcov a b c ia ib ic = 0 := by
  have haj : a ∈ U j := hab (left_mem_segment ℝ a b)
  have hbj : b ∈ U j := hab (right_mem_segment ℝ a b)
  have hcj : c ∈ U j := hbc (right_mem_segment ℝ b c)
  have h1 : q ib j = - q j ib := hcoc.antisymm ⟨b, hbj, hb⟩
  have h2 : q ic j = - q j ic := hcoc.antisymm ⟨c, hcj, hc⟩
  have h3 : q j ia = - q ia j := hcoc.antisymm ⟨a, ha, haj⟩
  unfold tri
  rw [beta_of_segment_subset U q hop hcov hcoc hab ha hb,
    beta_of_segment_subset U q hop hcov hcoc hbc hb hc,
    beta_of_segment_subset U q hop hcov hcoc hca hc ha]
  linarith

/-- A bisection state whose vertices all lie in a ball inside one cover
element has vanishing boundary integral.-/
theorem triVal_eq_zero_of_close (hop : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = univ) (hcoc : Coc U q) (T : GTri U) {z : ℂ} {i0 : ι}
    {ε : ℝ} (hball : Metric.ball z ε ⊆ U i0) (ha : dist T.a z < ε)
    (hb : dist T.b z < ε) (hc : dist T.c z < ε) :
    triVal U q hop hcov T = 0 := by
  have hsub : ∀ {x y : ℂ}, dist x z < ε → dist y z < ε →
      segment ℝ x y ⊆ U i0 := fun {x y} hx hy =>
    Set.Subset.trans
      ((convex_ball z ε).segment_subset (Metric.mem_ball.mpr hx)
        (Metric.mem_ball.mpr hy)) hball
  exact tri_eq_zero_of_segments_subset U q hop hcov hcoc (hsub ha hb)
    (hsub hb hc) (hsub hc ha) T.ha T.hb T.hc

/-- **The bisection closes**: every bisection state has vanishing boundary
integral — the Goursat recursion, the Cauchy limit of the first vertices, and
the one-element base case at the limit point.-/
theorem triVal_eq_zero (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (hcoc : Coc U q) (T0 : GTri U) : triVal U q hop hcov T0 = 0 := by
  by_contra hne
  have hperim0 := T0.perim_nonneg
  -- the first-vertex sequence is Cauchy (geometric step decay)
  have hcauchy : CauchySeq (fun k => (gseq U q hop hcov hcoc T0 k).a) :=
    cauchySeq_of_le_geometric (1 / 2) T0.perim (by norm_num) fun n => by
      show dist (gseq U q hop hcov hcoc T0 n).a
        (gseq U q hop hcov hcoc T0 (n + 1)).a ≤ T0.perim * (1 / 2) ^ n
      rw [dist_comm]
      calc dist (gseq U q hop hcov hcoc T0 (n + 1)).a
            (gseq U q hop hcov hcoc T0 n).a
          ≤ T0.perim / 2 ^ (n + 1) := gseq_dist U q hop hcov hcoc T0 n
        _ ≤ T0.perim * (1 / 2) ^ n := by
            rw [div_eq_mul_inv, ← inv_pow, ← one_div]
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n))
              hperim0
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
  obtain ⟨i0, hi0⟩ := exists_idx U hcov z
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hop i0) z hi0
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hz (ε / 4) (by linarith)
  obtain ⟨N2, hN2⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < ε / 4 / (T0.perim + 1) by
      exact div_pos (by linarith) (by linarith))
    (show (1 : ℝ) / 2 < 1 by norm_num)
  -- at stage `max N1 N2` the whole triangle sits in `ball z ε ⊆ U i0`
  have hzero : triVal U q hop hcov
      (gseq U q hop hcov hcoc T0 (max N1 N2)) = 0 := by
    have haz : dist (gseq U q hop hcov hcoc T0 (max N1 N2)).a z < ε / 4 :=
      hN1 (max N1 N2) (le_max_left N1 N2)
    have hperim : (gseq U q hop hcov hcoc T0 (max N1 N2)).perim < ε / 4 := by
      rw [gseq_perim U q hop hcov hcoc T0 (max N1 N2)]
      have hmono : ((1 : ℝ) / 2) ^ max N1 N2 ≤ (1 / 2) ^ N2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right N1 N2)
      have hrw : T0.perim / 2 ^ max N1 N2 = T0.perim * (1 / 2) ^ max N1 N2 := by
        rw [div_eq_mul_inv, ← inv_pow, ← one_div]
      rw [hrw]
      have hne1 : T0.perim + 1 ≠ 0 := by linarith
      calc T0.perim * ((1 : ℝ) / 2) ^ max N1 N2
          ≤ (T0.perim + 1) * ((1 / 2) ^ N2) :=
            mul_le_mul (by linarith) hmono (by positivity) (by linarith)
        _ < (T0.perim + 1) * (ε / 4 / (T0.perim + 1)) :=
            mul_lt_mul_of_pos_left hN2 (by linarith)
        _ = ε / 4 := by field_simp
    have hba := (gseq U q hop hcov hcoc T0 (max N1 N2)).dist_ba_le_perim
    have hca := (gseq U q hop hcov hcoc T0 (max N1 N2)).dist_ca_le_perim
    refine triVal_eq_zero_of_close U q hop hcov hcoc _ hball (by linarith) ?_ ?_
    · calc dist (gseq U q hop hcov hcoc T0 (max N1 N2)).b z
          ≤ dist (gseq U q hop hcov hcoc T0 (max N1 N2)).b
              (gseq U q hop hcov hcoc T0 (max N1 N2)).a +
            dist (gseq U q hop hcov hcoc T0 (max N1 N2)).a z :=
            dist_triangle _ _ _
        _ < ε := by linarith
    · calc dist (gseq U q hop hcov hcoc T0 (max N1 N2)).c z
          ≤ dist (gseq U q hop hcov hcoc T0 (max N1 N2)).c
              (gseq U q hop hcov hcoc T0 (max N1 N2)).a +
            dist (gseq U q hop hcov hcoc T0 (max N1 N2)).a z :=
            dist_triangle _ _ _
        _ < ε := by linarith
  have hval := gseq_val_le U q hop hcov hcoc T0 (max N1 N2)
  rw [hzero] at hval
  simp only [abs_zero, mul_zero] at hval
  exact hne (abs_eq_zero.mp (le_antisymm hval (abs_nonneg _)))

/-- **The Goursat triangle lemma** (proved): the closed chain integral around
any triangle vanishes — `tri_subdiv` supplies the four-child subdivision,
`exists_goursat_child` selects a quarter-carrying child, the perimeters decay
geometrically, the first vertices converge by completeness of `ℂ`, and one
cover element absorbs a small stage triangle
(`tri_eq_zero_of_segments_subset`).-/
theorem beta_triangle (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (hcoc : Coc U q) (a b c : ℂ) (ia ib ic : ι)
    (ha : a ∈ U ia) (hb : b ∈ U ib) (hc : c ∈ U ic) :
    beta U q hop hcov a b ia ib + beta U q hop hcov b c ib ic +
      beta U q hop hcov c a ic ia = 0 :=
  triVal_eq_zero U q hop hcov hcoc ⟨a, b, c, ia, ib, ic, ha, hb, hc⟩

/-! ## The main coboundary theorem -/

/-- Swapping the terminal index of the chain integral at the endpoint.-/
theorem beta_swap_right (hop : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    (hcoc : Coc U q) {z w : ℂ} {i b b' : ι}
    (hz : z ∈ U i) (hwb : w ∈ U b) (hwb' : w ∈ U b') :
    beta U q hop hcov z w i b = beta U q hop hcov z w i b' + q b' b := by
  obtain ⟨l, hl, hv⟩ := exists_valid_chain U hop hcov z w
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
  rw [beta_spec U q hop hcov hcoc hl hv hz hwb,
    beta_spec U q hop hcov hcoc hl hv hz hwb']
  exact wSum_swap_right U q hcoc t a hwb hwb'
    (Valid.getLast_mem_w (a :: t) (by simp) hv)

/-- **The coboundary theorem**: a ℚ-valued Čech `1`-cocycle on an open convex
cover of `ℂ` is a coboundary — anchor every index at a base point with the
chain integral; `beta_triangle` slides the anchor to a common point of each
overlap.-/
theorem exists_coboundary (hop : ∀ i, IsOpen (U i)) (hconv : ∀ i, Convex ℝ (U i))
    (hcov : ⋃ i, U i = univ) (hcoc : Coc U q) :
    ∃ b : ι → ℚ, ∀ i j, (U i ∩ U j).Nonempty → q i j = b j - b i := by
  classical
  have h0mem : (0 : ℂ) ∈ ⋃ i, U i := by rw [hcov]; trivial
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp h0mem
  refine ⟨fun i => if h : (U i).Nonempty then
    beta U q hop hcov 0 h.choose i₀ i else 0, ?_⟩
  intro i j hij
  obtain ⟨x, hxi, hxj⟩ := hij
  have hUi : (U i).Nonempty := ⟨x, hxi⟩
  have hUj : (U j).Nonempty := ⟨x, hxj⟩
  show q i j =
    (if h : (U j).Nonempty then beta U q hop hcov 0 h.choose i₀ j else 0) -
      (if h : (U i).Nonempty then beta U q hop hcov 0 h.choose i₀ i else 0)
  rw [dite_eq_left hUj, dite_eq_left hUi]
  -- slide each witness point to the common point x inside its convex element
  have hslide : ∀ (k : ι) (hUk : (U k).Nonempty), x ∈ U k →
      beta U q hop hcov 0 hUk.choose i₀ k = beta U q hop hcov 0 x i₀ k := by
    intro k hUk hxk
    have hpk : hUk.choose ∈ U k := hUk.choose_spec
    have htr := beta_triangle U q hop hcov hcoc 0 hUk.choose x i₀ k k
      hi₀ hpk hxk
    have hseg : segment ℝ hUk.choose x ⊆ U k := (hconv k).segment_subset hpk hxk
    have hmid : beta U q hop hcov hUk.choose x k k = q k k + q k k :=
      beta_of_segment_subset U q hop hcov hcoc hseg hpk hxk
    have hqkk : q k k = 0 := hcoc.self_eq_zero hUk
    have hrev : beta U q hop hcov x 0 k i₀ =
        - beta U q hop hcov 0 x i₀ k :=
      beta_rev U q hop hcov hcoc 0 x i₀ k hi₀ hxk
    rw [hmid, hqkk, hrev] at htr
    linarith
  rw [hslide i hUi hxi, hslide j hUj hxj]
  have hswap : beta U q hop hcov 0 x i₀ j =
      beta U q hop hcov 0 x i₀ i + q i j :=
    beta_swap_right U q hop hcov hcoc hi₀ hxj hxi
  linarith

end CechGoursat

end HodgePilot

end
