import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Data.Fintype.Pigeonhole
import Tengoku.Seed.Order.Filter.AtTopBot.Finite
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The combinatorial part of manuscript Lemma `lem:scalar-finiteness`.
The geometric component and radius-tail hypotheses remain explicit. In particular,
this file does not assert that a Laurent polynomial satisfies those hypotheses. -/

open Filter
open scoped Topology

namespace DuistermaatVanDerKallen

/-- Points with nearby target values cannot share a component whose image has
small diameter. The three errors are kept separate for reuse.
@isnad1 id=ne.5h11v.s7.6bcb3a28eff9 from=translated src=- shape=3445e39d vocab=fe946dec
-/
theorem distinct_component_of_separation {X Y : Type*} [PseudoMetricSpace Y]
    {F : X → Y} {label : X → ℕ} {x y : X} {c d : Y} {η ε L : ℝ}
    (hsep : η ≤ dist c d) (hx : dist c (F x) < η / 8)
    (hy : dist (F y) d < η / 8) (hsmall : L * ε < η / 4)
    (hdiam : label x = label y → dist (F x) (F y) ≤ L * ε) :
    label x ≠ label y := by
  intro h
  have htri := dist_triangle4 c (F x) (F y) d
  have hb := hdiam h
  linarith [dist_nonneg (x := c) (y := F x)]

/-- At one common radius, `N+1` separated proposed values contradict `N`
component labels. Uniformity in both radius and epsilon is in the hypotheses.
@isnad1 id=false.5h10v.s8.4aa9b9ebaa67 from=translated src=- shape=b19ffa11 vocab=bc889e19
-/
theorem common_radius_contradiction {X Y : Type*} [PseudoMetricSpace Y]
    {N : ℕ} (F : X → Y) (A : ℝ → ℝ → Set X)
    (label : ℝ → ℝ → X → Fin N) (c : Fin (N + 1) → Y)
    {η ε L : ℝ} (hη : 0 < η) (hsmall : L * ε < η / 4)
    (hsep : ∀ i j, i ≠ j → η ≤ dist (c i) (c j))
    (hdiam : ∀ R x y, x ∈ A R ε → y ∈ A R ε →
      label R ε x = label R ε y → dist (F x) (F y) ≤ L * ε)
    (htail : ∀ i, ∀ᶠ R in atTop,
      ∃ x ∈ A R ε, dist (F x) (c i) < η / 8) : False := by
  classical
  have ht : ∀ᶠ R in atTop, ∀ i, ∃ x ∈ A R ε, dist (F x) (c i) < η / 8 :=
    (eventually_all).2 htail
  obtain ⟨R, hR⟩ := ht.exists
  choose x hx hclose using hR
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i => label R ε (x i)) (by simp)
  have hd := hdiam R (x i) (x j) (hx i) (hx j) heq
  have ht := dist_triangle4 (c i) (F (x i)) (F (x j)) (c j)
  rw [dist_comm (c i) (F (x i))] at ht
  have hs := hsep i j hij
  have hi := hclose i
  have hj := hclose j
  linarith

/-- Any finite list of distinct metric points has a uniform positive separation.
@isnad1 id=ex.1h3v.s6.4e595fb85fc1 from=translated src=- shape=b6c6d8fe vocab=3e6ba4d5
-/
theorem finite_uniform_separation {Y : Type*} [MetricSpace Y] {n : ℕ}
    (c : Fin (n + 1) → Y) (hc : Function.Injective c) :
    ∃ η > (0 : ℝ), ∀ i j, i ≠ j → η ≤ dist (c i) (c j) := by
  classical
  let f : Fin (n + 1) × Fin (n + 1) → ℝ :=
    fun p => if p.1 = p.2 then 1 else dist (c p.1) (c p.2)
  let s := Finset.univ.image f
  have hs : s.Nonempty := ⟨f (0, 0), Finset.mem_image.mpr ⟨(0, 0), by simp, rfl⟩⟩
  refine ⟨s.min' hs, ?_, ?_⟩
  · obtain ⟨⟨i, j⟩, _, heq⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
    rw [← heq]
    dsimp [f]
    split_ifs with h
    · exact zero_lt_one
    · exact dist_pos.mpr (hc.ne h)
  · intro i j hij
    have h := Finset.min'_le s (f (i, j)) (Finset.mem_image.mpr ⟨(i, j), by simp, rfl⟩)
    simpa [f, hij] using h

/-- Abstract common-radius finiteness. Its hypotheses isolate exactly the two
geometric inputs: uniformly small component images and a whole tail of radii
for every proposed limit value. No semialgebraic theorem is hidden here.
@isnad1 id=finite.3h8v.s7.4a0acb4a34c6 from=translated src=- shape=28da1f82 vocab=0093eda1
-/
theorem finite_of_common_radius {X Y : Type*} [MetricSpace Y]
    {N : ℕ} (F : X → Y) (A : ℝ → ℝ → Set X)
    (label : ℝ → ℝ → X → Fin N) (K : Set Y) {L : ℝ} (hL : 0 < L)
    (hdiam : ∀ ε > 0, ∀ R x y, x ∈ A R ε → y ∈ A R ε →
      label R ε x = label R ε y → dist (F x) (F y) ≤ L * ε)
    (htail : ∀ c ∈ K, ∀ ε > 0, ∀ δ > 0, ∀ᶠ R in atTop,
      ∃ x ∈ A R ε, dist (F x) c < δ) : K.Finite := by
  classical
  by_contra hinf
  let e := Set.Infinite.natEmbedding K hinf
  let c : Fin (N + 1) → Y := fun i => (e i).val
  have hc : Function.Injective c := fun i j h =>
    Fin.ext (e.injective (Subtype.ext h))
  obtain ⟨η, hη, hsep⟩ := finite_uniform_separation c hc
  have he : 0 < η / (8 * L) := div_pos hη (by positivity)
  have hsmall : L * (η / (8 * L)) < η / 4 := by
    have heq : L * (η / (8 * L)) = η / 8 := by field_simp
    rw [heq]
    linarith
  exact common_radius_contradiction F A label c hη hsmall hsep
    (hdiam _ he) (fun i => htail (c i) (e i).property _ he _ (by positivity))

end DuistermaatVanDerKallen
