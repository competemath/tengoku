/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Pentagon.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import Tengoku.Jsp000198Lean.EmptyPentagon.Definitions
import Tengoku.Jsp000198Lean.EmptyPentagon.Certificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
namespace Horton

/-- The orientation is invariant under cyclic rotation of its arguments.
@isnad1 id=eq.0h3v.s4.fb6ac0e43daf from=translated src=- shape=8c14c8b7 vocab=289b8093
-/
theorem orient_cyc (a b c : Point) : orient a b c = orient b c a := by
  unfold orient; ring

/-- Swapping the last two arguments negates the orientation.
@isnad1 id=eq.0h3v.s4.d649bc266ec0 from=translated src=- shape=04d76633 vocab=d04c39b3
-/
theorem orient_swap (a b c : Point) : orient a c b = -orient a b c := by
  unfold orient; ring

/-- The orientation vanishes when the third point equals the first.
@isnad1 id=eq.0h2v.s4.2cb7dcd4cdba from=translated src=- shape=52ed7545 vocab=289b8093
-/
theorem orient_self_left (a b : Point) : orient a b a = 0 := by
  unfold orient; ring

/-- The orientation vanishes when the third point equals the second.
@isnad1 id=eq.0h2v.s4.59e0d3782358 from=translated src=- shape=f5a3d3ad vocab=289b8093
-/
theorem orient_self_right (a b : Point) : orient a b b = 0 := by
  unfold orient; ring

/-- The orientation vanishes when the first two points coincide.
@isnad1 id=eq.0h2v.s4.143ab1928fc0 from=translated src=- shape=bd2a8fb1 vocab=289b8093
-/
theorem orient_self_pair (a c : Point) : orient a a c = 0 := by
  unfold orient; ring

/-- A counterclockwise-labelled pentagon is convex independent.
@isnad1 id=convexin.2h1v.s8.f0fc92c3440f from=translated src=- shape=e33ad4ff vocab=0911311b
-/
theorem convexIndependent_of_ccw (P : Fin 5 → Point) (hinj : Function.Injective P)
    (hccw : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (P i) (P (i + 1)) (P j)) :
    ConvexIndependent ℝ (fun x : ((Finset.univ.image P : Finset Point) : Set Point) => (x : Point)) := by
  apply convexIndependent_of_separated
  intro v hv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨P (i - 1), Finset.mem_image_of_mem P (Finset.mem_univ _),
    P (i + 1), Finset.mem_image_of_mem P (Finset.mem_univ _), ?_, ?_, ?_⟩
  · intro h
    have h1 : ∀ i : Fin 5, i - 1 ≠ i + 1 := by decide
    exact h1 i (hinj h)
  · have h1 : ∀ i : Fin 5, i - 1 + 1 = i := by decide
    have h2 : ∀ i : Fin 5, i + 1 ≠ i - 1 := by decide
    have h3 : ∀ i : Fin 5, i + 1 ≠ i - 1 + 1 := by decide
    have h := hccw (i - 1) (i + 1) (h2 i) (h3 i)
    rw [h1 i] at h
    rw [orient_swap]
    linarith
  · intro x hx hne
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    have hji : j ≠ i := fun h => hne (by rw [h])
    have hcases : ∀ i j : Fin 5, j ≠ i →
        j = i - 1 ∨ j = i + 1 ∨ j = i + 2 ∨ j = i + 3 := by decide
    rcases hcases i j hji with rfl | rfl | rfl | rfl
    · rw [orient_self_left]
    · rw [orient_self_right]
    · have h1 : ∀ i : Fin 5, i + 1 + 1 = i + 2 := by decide
      have h2 : ∀ i : Fin 5, i - 1 ≠ i + 1 := by decide
      have h3 : ∀ i : Fin 5, i - 1 ≠ i + 1 + 1 := by decide
      have h := hccw (i + 1) (i - 1) (h2 i) (h3 i)
      rw [h1 i, orient_cyc, orient_cyc] at h
      exact h.le
    · have h1 : ∀ i : Fin 5, i + 3 + 1 = i - 1 := by decide
      have h2 : ∀ i : Fin 5, i + 1 ≠ i + 3 := by decide
      have h3 : ∀ i : Fin 5, i + 1 ≠ i + 3 + 1 := by decide
      have h := hccw (i + 3) (i + 1) (h2 i) (h3 i)
      rw [h1 i, orient_cyc] at h
      exact h.le

/-- A counterclockwise pentagon of `S` with no point of `S` strictly inside is an empty convex
polygon of `S`.
@isnad1 id=emptycon.4h2v.s8.d40d4595d60b from=translated src=- shape=033d3b43 vocab=d8aabdf0
-/
theorem emptyConvexPolygon_of_ccw (S : Finset Point) (P : Fin 5 → Point)
    (hinj : Function.Injective P) (hPS : ∀ i, P i ∈ S)
    (hccw : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (P i) (P (i + 1)) (P j))
    (hempty : ∀ q ∈ S, q ∉ Finset.univ.image P →
      q ∉ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point))) :
    EmptyConvexPolygon S (Finset.univ.image P) :=
  ⟨Finset.image_subset_iff.mpr fun i _ => hPS i, convexIndependent_of_ccw P hinj hccw, hempty⟩

/-- A point strictly inside a counterclockwise pentagon is strictly left of every edge.
@isnad1 id=lt.2h3v.s8.ac0855351950 from=translated src=- shape=a7d59ddb vocab=c7ab0a46
-/
theorem orient_edge_pos_of_mem_interior (P : Fin 5 → Point) (M : Point)
    (hM : M ∈ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point)))
    (hccw : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (P i) (P (i + 1)) (P j)) (i : Fin 5) :
    0 < orient (P i) (P (i + 1)) M := by
  by_contra hlt
  have hle := not_lt.mp hlt
  refine not_mem_interior_convexHull_of_halfplane _ (P i) (P (i + 1)) M ?_ ?_ hle hM
  · intro h
    have h2 : ∀ i : Fin 5, i + 2 ≠ i := by decide
    have h3 : ∀ i : Fin 5, i + 2 ≠ i + 1 := by decide
    have hpos := hccw i (i + 2) (h2 i) (h3 i)
    rw [h, orient_self_pair] at hpos
    exact lt_irrefl _ hpos
  · intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    by_cases hj : j = i
    · rw [hj, orient_self_left]
    by_cases hj' : j = i + 1
    · rw [hj', orient_self_right]
    exact (hccw i j hj hj').le

end Horton
