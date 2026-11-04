import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicLine
import Tengoku.Seed.Data.Set.Card
import Tengoku.Seed.Order.Interval.Set.Infinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniform bounds for polynomial-curve intersections and real line fibers.
The bound depends on the fixed semialgebraic description and the degree bound,
not on the varying curve coefficients or parameter values. Zero specialized
polynomials and drops in degree are included. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set

/--
@isnad1 id=ex.0h3v.s5.7533311273ef from=translated src=- shape=69785fd2 vocab=ccf060a6
-/
theorem polynomial_curve_uniform_degree_bound {ι : Type*} (p : MvPolynomial ι ℝ) (D : ℕ) :
    ∃ B : ℕ, ∀ g : ι → Polynomial ℝ, (∀ i, (g i).natDegree ≤ D) →
      (MvPolynomial.eval₂ Polynomial.C g p).natDegree ≤ B := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨0, fun g hg => by simp⟩
  | add p q hp hq =>
    obtain ⟨B, hB⟩ := hp
    obtain ⟨C, hC⟩ := hq
    refine ⟨max B C, fun g hg => ?_⟩
    rw [MvPolynomial.eval₂_add]
    exact Polynomial.natDegree_add_le_of_le (hB g hg) (hC g hg)
  | mul_X p i hp =>
    obtain ⟨B, hB⟩ := hp
    refine ⟨B + D, fun g hg => ?_⟩
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact Polynomial.natDegree_mul_le_of_le (hB g hg) (hg i)

/--
@isnad1 id=le.0h1v.s5.730e73f226eb from=translated src=- shape=318caf99 vocab=93e2a4f4
-/
theorem polynomial_nonneg_frontier_ncard_le (p : Polynomial ℝ) :
    (frontier {t : ℝ | 0 ≤ p.eval t}).ncard ≤ p.natDegree := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  · have hsub : frontier {t : ℝ | 0 ≤ p.eval t} ⊆ (p.roots.toFinset : Set ℝ) := by
      intro t ht
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hp).mpr
      exact (frontier_le_subset_eq continuous_const p.continuous ht).symm
    calc
      _ ≤ (p.roots.toFinset : Set ℝ).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = p.roots.toFinset.card := Set.ncard_coe_finset _
      _ ≤ p.roots.card := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' p

/--
@isnad1 id=ex.1h3v.s6.b894f8cc58f2 from=translated src=- shape=a099795a vocab=c1ae35c7
-/
theorem IsSemialgebraic.uniform_frontier_bound_polynomial_curves {ι : Type*}
    {S : Set (ι → ℝ)} (hS : IsSemialgebraic ι S) (D : ℕ) :
    ∃ N : ℕ, ∀ g : ι → Polynomial ℝ, (∀ i, (g i).natDegree ≤ D) →
      (frontier {t : ℝ | (fun i => (g i).eval t) ∈ S}).ncard ≤ N := by
  induction hS with
  | nonneg p =>
    obtain ⟨B, hB⟩ := polynomial_curve_uniform_degree_bound p D
    refine ⟨B, fun g hg => ?_⟩
    simpa only [polynomial_curve_eval, Set.mem_ofPred_eq] using
      (polynomial_nonneg_frontier_ncard_le (MvPolynomial.eval₂ Polynomial.C g p)).trans (hB g hg)
  | @inter s t hs ht ihs iht =>
    obtain ⟨N, hN⟩ := ihs
    obtain ⟨M, hM⟩ := iht
    refine ⟨N + M, fun g hg => ?_⟩
    have hsub : frontier {r : ℝ | (fun i => (g i).eval r) ∈ s ∩ t} ⊆
        frontier {r : ℝ | (fun i => (g i).eval r) ∈ s} ∪
        frontier {r : ℝ | (fun i => (g i).eval r) ∈ t} := by
      intro r hr
      rcases frontier_inter_subset _ _ hr with h | h
      · exact Or.inl h.1
      · exact Or.inr h.2
    exact (Set.ncard_le_ncard hsub ((hs.finite_frontier_polynomial_curve g).union
      (ht.finite_frontier_polynomial_curve g))).trans
        ((Set.ncard_union_le _ _).trans (Nat.add_le_add (hN g hg) (hM g hg)))
  | @union s t hs ht ihs iht =>
    obtain ⟨N, hN⟩ := ihs
    obtain ⟨M, hM⟩ := iht
    refine ⟨N + M, fun g hg => ?_⟩
    have hsub : frontier {r : ℝ | (fun i => (g i).eval r) ∈ s ∪ t} ⊆
        frontier {r : ℝ | (fun i => (g i).eval r) ∈ s} ∪
        frontier {r : ℝ | (fun i => (g i).eval r) ∈ t} := by
      intro r hr
      rcases frontier_union_subset _ _ hr with h | h
      · exact Or.inl h.1
      · exact Or.inr h.2
    exact (Set.ncard_le_ncard hsub ((hs.finite_frontier_polynomial_curve g).union
      (ht.finite_frontier_polynomial_curve g))).trans
        ((Set.ncard_union_le _ _).trans (Nat.add_le_add (hN g hg) (hM g hg)))
  | compl hs ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N, fun g hg => ?_⟩
    simpa only [Set.mem_compl_iff, ← Set.compl_ofPred, frontier_compl] using hN g hg

/--
@isnad1 id=ex.1h3v.s6.f49ac3c5fed5 from=translated src=- shape=7a5665cf vocab=50255624
-/
theorem IsSemialgebraic.uniform_convex_cover_polynomial_curves {ι : Type*}
    {S : Set (ι → ℝ)} (hS : IsSemialgebraic ι S) (D : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ g : ι → Polynomial ℝ, (∀ i, (g i).natDegree ≤ D) →
      ∃ C : Set (Set ℝ), C.Finite ∧ C.ncard ≤ N ∧
        (∀ A ∈ C, Convex ℝ A) ∧ ⋃₀ C = {t : ℝ | (fun i => (g i).eval t) ∈ S} := by
  obtain ⟨B, hB⟩ := hS.uniform_frontier_bound_polynomial_curves D
  refine ⟨3 ^ B, Nat.one_le_pow _ _ (by decide), fun g hg => ?_⟩
  obtain ⟨C, hC, hcard, hconv, hcover⟩ :=
    exists_convex_cover_card_le_of_finite_frontier (hS.finite_frontier_polynomial_curve g)
  refine ⟨C, hC, hcard.trans ?_, hconv, hcover⟩
  exact Nat.pow_le_pow_right (by decide) (hB g hg)

/--
@isnad1 id=ex.1h3v.s7.59b1f75e7b2a from=translated src=- shape=e424047e vocab=63615934
-/
theorem IsSemialgebraic.uniform_components_polynomial_curves {ι : Type*}
    {S : Set (ι → ℝ)} (hS : IsSemialgebraic ι S) (D : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ g : ι → Polynomial ℝ, (∀ i, (g i).natDegree ≤ D) →
      Finite (ConnectedComponents {t : ℝ | (fun i => (g i).eval t) ∈ S}) ∧
      Nat.card (ConnectedComponents {t : ℝ | (fun i => (g i).eval t) ∈ S}) ≤ N := by
  obtain ⟨N, hN, hcover⟩ := hS.uniform_convex_cover_polynomial_curves D
  refine ⟨N, hN, fun g hg => ?_⟩
  obtain ⟨C, hC, hcard, hconv, hcov⟩ := hcover g hg
  exact ⟨finite_connectedComponents_of_finite_preconnected_cover hC
    (fun A hA => (hconv A hA).isPreconnected) hcov,
    (card_connectedComponents_le_of_finite_preconnected_cover hC
      (fun A hA => (hconv A hA).isPreconnected) hcov).trans hcard⟩

/-- All parameter values are retained. No boundedness or compactness of their
range is assumed, and the natural number precedes the varying parameter.
@isnad1 id=ex.1h2v.s7.634b0fd19c92 from=translated src=- shape=8fbe98ad vocab=c417da63
-/
theorem IsSemialgebraic.uniform_components_line_fibers {ι : Type*}
    {S : Set ((ι ⊕ Unit) → ℝ)} (hS : IsSemialgebraic (ι ⊕ Unit) S) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ a : ι → ℝ,
      Finite (ConnectedComponents {t : ℝ | Sum.elim a (fun _ => t) ∈ S}) ∧
      Nat.card (ConnectedComponents {t : ℝ | Sum.elim a (fun _ => t) ∈ S}) ≤ N := by
  obtain ⟨N, hN, hbound⟩ := hS.uniform_components_polynomial_curves 1
  refine ⟨N, hN, fun a => ?_⟩
  let g : (ι ⊕ Unit) → Polynomial ℝ := Sum.elim (fun i => Polynomial.C (a i))
    (fun _ => Polynomial.X)
  have hg (i) : (g i).natDegree ≤ 1 := by cases i <;> simp [g]
  have he (t : ℝ) : (fun i => (g i).eval t) = Sum.elim a (fun _ => t) := by
    funext i
    cases i <;> simp [g]
  have hset : {t : ℝ | (fun i => (g i).eval t) ∈ S} =
      {t : ℝ | Sum.elim a (fun _ => t) ∈ S} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    rw [he t]
  have hb := hbound g hg
  rw [hset] at hb
  exact hb

/--
@isnad1 id=eq.1h1v.s4.96d68c0f3536 from=translated src=- shape=22b22273 vocab=8904f56e
-/
theorem real_finite_frontier_eq {S : Set ℝ} (hS : S.Finite) : frontier S = S := by
  have hi : interior S = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hne
    obtain ⟨a, b, hab, hsub⟩ := isOpen_interior.exists_Ioo_subset hne
    exact (Set.Ioo_infinite hab) (hS.subset (hsub.trans interior_subset))
  rw [frontier, hS.isClosed.closure_eq, hi, Set.sdiff_empty]

/--
@isnad1 id=ex.1h3v.s6.1b4b9967cc54 from=translated src=- shape=f708be61 vocab=158f8617
-/
theorem IsSemialgebraic.uniform_finite_intersection_bound {ι : Type*}
    {S : Set (ι → ℝ)} (hS : IsSemialgebraic ι S) (D : ℕ) :
    ∃ N : ℕ, ∀ g : ι → Polynomial ℝ, (∀ i, (g i).natDegree ≤ D) →
      ({t : ℝ | (fun i => (g i).eval t) ∈ S}).Finite →
      ({t : ℝ | (fun i => (g i).eval t) ∈ S}).ncard ≤ N := by
  obtain ⟨N, hN⟩ := hS.uniform_frontier_bound_polynomial_curves D
  refine ⟨N, fun g hg hfinite => ?_⟩
  simpa only [real_finite_frontier_eq hfinite] using hN g hg

/-- A uniform bound for the finite one-dimensional fibers of a fixed family.
Infinite fibers are permitted in the same family and are excluded only in the
pointwise implication, not by a global assumption on parameters.
@isnad1 id=ex.1h2v.s6.082a7d08f139 from=translated src=- shape=b8e7d1be vocab=8605e98e
-/
theorem IsSemialgebraic.uniform_finite_line_fibers {ι : Type*}
    {S : Set ((ι ⊕ Unit) → ℝ)} (hS : IsSemialgebraic (ι ⊕ Unit) S) :
    ∃ N : ℕ, ∀ a : ι → ℝ,
      ({t : ℝ | Sum.elim a (fun _ => t) ∈ S}).Finite →
      ({t : ℝ | Sum.elim a (fun _ => t) ∈ S}).ncard ≤ N := by
  obtain ⟨N, hbound⟩ := hS.uniform_finite_intersection_bound 1
  refine ⟨N, fun a hfinite => ?_⟩
  let g : (ι ⊕ Unit) → Polynomial ℝ := Sum.elim (fun i => Polynomial.C (a i))
    (fun _ => Polynomial.X)
  have hg (i) : (g i).natDegree ≤ 1 := by cases i <;> simp [g]
  have he (t : ℝ) : (fun i => (g i).eval t) = Sum.elim a (fun _ => t) := by
    funext i
    cases i <;> simp [g]
  have hset : {t : ℝ | (fun i => (g i).eval t) ∈ S} =
      {t : ℝ | Sum.elim a (fun _ => t) ∈ S} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    rw [he t]
  have hb := hbound g hg
  rw [hset] at hb
  exact hb hfinite

end
end DuistermaatVanDerKallen
