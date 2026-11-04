import Tengoku.ErdosLean.ErdosLean.Erdos956.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős #956 — Part 4: `C = D/2` for a symmetric finite generating set

Generic facts about `C = (1/2) • conv S` for a finite set `S` closed under negation, plus the
specialisation to `gens k`.
-/

namespace Erdos956

open Pointwise

section generic

variable {S : Finset E}

/--
@isnad1 id=iscompac.0h1v.s8.3df8e76cbf9e from=translated src=- shape=9bc1127b vocab=d317a6ba
-/
lemma half_hull_isCompact : IsCompact ((1 / 2 : ℝ) • convexHull ℝ (S : Set E)) := by
  rw [← Set.image_smul]
  exact (S.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).image (continuous_const_smul _)

/--
@isnad1 id=convex.0h1v.s8.134b0254cf05 from=translated src=- shape=51500ecb vocab=1373f699
-/
lemma half_hull_convex : Convex ℝ ((1 / 2 : ℝ) • convexHull ℝ (S : Set E)) :=
  (convex_convexHull ℝ _).smul _

/--
@isnad1 id=nonempty.1h1v.s8.3a4a2e113bfe from=translated src=- shape=70a62194 vocab=92b1f88a
-/
lemma half_hull_nonempty (hne : S.Nonempty) :
    ((1 / 2 : ℝ) • convexHull ℝ (S : Set E)).Nonempty := by
  obtain ⟨z, hz⟩ := hne
  exact ⟨(1 / 2 : ℝ) • z, Set.smul_mem_smul_set (subset_convexHull ℝ _ (by simpa using hz))⟩

/-- `C - C ⊆ D` when `S = -S`.
@isnad1 id=mem.3h3v.s9.1ef7f8948515 from=translated src=- shape=4bcee283 vocab=5e78bc21
-/
lemma sub_mem_hull_of_mem_half (hS : ∀ z ∈ S, -z ∈ S) {c c' : E}
    (hc : c ∈ (1 / 2 : ℝ) • convexHull ℝ (S : Set E))
    (hc' : c' ∈ (1 / 2 : ℝ) • convexHull ℝ (S : Set E)) :
    c - c' ∈ convexHull ℝ (S : Set E) := by
  obtain ⟨x, hx, rfl⟩ := hc
  obtain ⟨y, hy, rfl⟩ := hc'
  have hneg : -y ∈ convexHull ℝ (S : Set E) := by
    have h1 : -y ∈ convexHull ℝ (-(S : Set E)) := by
      rw [convexHull_neg]; simpa [Set.mem_neg] using hy
    refine convexHull_mono ?_ h1
    intro z hz
    have := hS (-z) (by simpa [Set.mem_neg] using hz)
    simpa using this
  have := convex_convexHull ℝ (S : Set E) hx hneg (a := 1 / 2) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  convert this using 1
  simp [smul_neg, sub_eq_add_neg]

/--
@isnad1 id=mem.1h2v.s8.ebccb708b700 from=translated src=- shape=c998dd52 vocab=ebd21b7d
-/
lemma half_mem_half_hull {z : E} (hz : z ∈ S) :
    (1 / 2 : ℝ) • z ∈ (1 / 2 : ℝ) • convexHull ℝ (S : Set E) :=
  Set.smul_mem_smul_set (subset_convexHull ℝ _ (by simpa using hz))

end generic

/--
@isnad1 id=mem.1h2v.s6.5fda9cff51bf from=translated src=- shape=0bcc3979 vocab=7dab33aa
-/
lemma neg_mem_gens {k : ℕ} {z : E} (hz : z ∈ gens k) : -z ∈ gens k := by
  unfold gens at *
  simp only [Finset.mem_union, Finset.mem_image] at *
  rcases hz with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · exact Or.inr ⟨i, hi, rfl⟩
  · exact Or.inl ⟨i, hi, (neg_neg _).symm⟩

/--
@isnad1 id=mem.2h2v.s5.41f3689a5aba from=translated src=- shape=c5a099e6 vocab=e197fb60
-/
lemma pp_mem_gens {k i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) : pp (η k) (i * a k) ∈ gens k := by
  unfold gens
  exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_Icc.2 ⟨hi1, hik⟩, rfl⟩)

/--
@isnad1 id=nonempty.1h1v.s4.1ae12e3f4660 from=translated src=- shape=238e953f vocab=e06eebd8
-/
lemma gens_nonempty {k : ℕ} (hk : 1 ≤ k) : (gens k).Nonempty :=
  ⟨_, pp_mem_gens le_rfl hk⟩

/--
@isnad1 id=iscompac.0h1v.s5.8f6311de346c from=translated src=- shape=1a6c1393 vocab=c827bcc1
-/
lemma C_isCompact (k : ℕ) : IsCompact (C k) := half_hull_isCompact
/--
@isnad1 id=convex.0h1v.s6.2d9ade13953d from=translated src=- shape=7000f90d vocab=09c40166
-/
lemma C_convex (k : ℕ) : Convex ℝ (C k) := half_hull_convex
/--
@isnad1 id=nonempty.1h1v.s4.19f6be2eb450 from=translated src=- shape=238e953f vocab=8a14598c
-/
lemma C_nonempty {k : ℕ} (hk : 1 ≤ k) : (C k).Nonempty := half_hull_nonempty (gens_nonempty hk)

/--
@isnad1 id=mem.2h3v.s6.ec67435bdd4b from=translated src=- shape=afc775dc vocab=5e9b4776
-/
lemma sub_mem_D {k : ℕ} {c c' : E} (hc : c ∈ C k) (hc' : c' ∈ C k) : c - c' ∈ D k :=
  sub_mem_hull_of_mem_half (fun _ hz => neg_mem_gens hz) hc hc'

end Erdos956
