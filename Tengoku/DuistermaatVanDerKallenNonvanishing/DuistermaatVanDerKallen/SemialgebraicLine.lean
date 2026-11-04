import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicTail
import Tengoku.Seed.Algebra.Polynomial.Roots
import Tengoku.Seed.Topology.Algebra.Polynomial
import Tengoku.Seed.Analysis.Convex.PathConnected
import Tengoku.Seed.Topology.Connected.TotallyDisconnected
import Tengoku.Seed.Topology.Order.IntermediateValue
import Tengoku.Seed.Data.Set.Card.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Finite interval decomposition on the real line from polynomial roots and
Boolean closure. Real order cells are convex, and a finite frontier bounds
the number of cells. This proves no higher-dimensional projection or Hardt
triviality theorem. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set

theorem polynomial_nonneg_finite_frontier (p : Polynomial ℝ) :
    (frontier {t : ℝ | 0 ≤ p.eval t}).Finite := by
  by_cases hp : p = 0
  · simp [hp]
  · apply (Polynomial.finite_setOfPred_isRoot hp).subset
    intro t ht
    exact (frontier_le_subset_eq continuous_const p.continuous ht).symm

theorem IsSemialgebraic.finite_frontier_polynomial_curve {ι : Type*}
    {S : Set (ι → ℝ)} (hS : IsSemialgebraic ι S) (g : ι → Polynomial ℝ) :
    (frontier {t : ℝ | (fun i => (g i).eval t) ∈ S}).Finite := by
  induction hS with
  | nonneg p =>
    simpa only [polynomial_curve_eval, Set.mem_ofPred_eq] using
      polynomial_nonneg_finite_frontier (MvPolynomial.eval₂ Polynomial.C g p)
  | inter h₁ h₂ ih₁ ih₂ =>
    apply (ih₁.union ih₂).subset
    intro t ht
    rcases frontier_inter_subset _ _ ht with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2
  | union h₁ h₂ ih₁ ih₂ =>
    apply (ih₁.union ih₂).subset
    intro t ht
    rcases frontier_union_subset _ _ ht with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2
  | compl h ih => simpa only [Set.mem_compl_iff, ← Set.compl_ofPred, frontier_compl] using ih

theorem subset_of_preconnected_disjoint_frontier {X : Type*} [TopologicalSpace X]
    {S C : Set X} (hC : IsPreconnected C) (hdisj : Disjoint C (frontier S))
    (hne : (C ∩ S).Nonempty) : C ⊆ S := by
  have hCI : C ⊆ interior S ∪ interior Sᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact Set.disjoint_left.mp hdisj
  obtain ⟨x, hxC, hxS⟩ := hne
  have hxI : x ∈ interior S := (mem_interior_iff_notMem_frontier hxS).mpr
    (Set.disjoint_left.mp hdisj hxC)
  exact (hC.subset_left_of_subset_union isOpen_interior isOpen_interior
    (disjoint_compl_right.mono interior_subset interior_subset) hCI
    ⟨x, hxC, hxI⟩).trans interior_subset

def realOrderSide (r : ℝ) : Ordering → Set ℝ
  | .lt => Iio r
  | .eq => {r}
  | .gt => Ioi r

theorem convex_realOrderSide (r : ℝ) (o : Ordering) : Convex ℝ (realOrderSide r o) := by
  cases o
  · exact convex_Iio r
  · exact convex_singleton r
  · exact convex_Ioi r

def realOrderCell (T : Set ℝ) (label : T → Ordering) : Set ℝ :=
  ⋂ r : T, realOrderSide r.val (label r)

theorem convex_realOrderCell (T : Set ℝ) (label : T → Ordering) :
    Convex ℝ (realOrderCell T label) :=
  convex_iInter fun r => convex_realOrderSide r.val (label r)

theorem realOrderCell_subset_singleton {T : Set ℝ} (label : T → Ordering)
    (r : T) (hr : r.val ∈ realOrderCell T label) : realOrderCell T label ⊆ {r.val} := by
  intro x hx
  have hr' := mem_iInter.mp hr r
  have hx' := mem_iInter.mp hx r
  cases ho : label r <;> simp [realOrderSide, ho] at hr' hx' ⊢
  exact hx'

theorem exists_realOrderCell (T : Set ℝ) (x : ℝ) :
    ∃ label : T → Ordering, x ∈ realOrderCell T label := by
  classical
  refine ⟨fun r => if x < r.val then .lt else if x = r.val then .eq else .gt, ?_⟩
  apply mem_iInter.mpr
  intro r
  dsimp only
  split_ifs with hlt heq
  · exact hlt
  · exact heq
  · exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)

theorem realOrderCell_subset_of_meets (S : Set ℝ) (label : frontier S → Ordering)
    (hne : (realOrderCell (frontier S) label ∩ S).Nonempty) :
    realOrderCell (frontier S) label ⊆ S := by
  by_cases hdisj : Disjoint (realOrderCell (frontier S) label) (frontier S)
  · exact subset_of_preconnected_disjoint_frontier
      (convex_realOrderCell _ _).isPreconnected hdisj hne
  · obtain ⟨r, hrC, hrF⟩ := not_disjoint_iff.mp hdisj
    have hc := realOrderCell_subset_singleton label ⟨r, hrF⟩ hrC
    obtain ⟨x, hxC, hxS⟩ := hne
    have hxr : x = r := hc hxC
    exact hc.trans (singleton_subset_iff.mpr (hxr ▸ hxS))

theorem exists_convex_cover_card_le_of_finite_frontier {S : Set ℝ}
    (hS : (frontier S).Finite) :
    ∃ C : Set (Set ℝ), C.Finite ∧ C.ncard ≤ 3 ^ (frontier S).ncard ∧
      (∀ A ∈ C, Convex ℝ A) ∧ ⋃₀ C = S := by
  classical
  let : Fintype (frontier S) := hS.fintype
  let cell (label : frontier S → Ordering) : Set ℝ :=
    if (realOrderCell (frontier S) label ∩ S).Nonempty then
      realOrderCell (frontier S) label else ∅
  refine ⟨Set.range cell, Set.finite_range cell, ?_, ?_, ?_⟩
  · have h := Nat.card_le_card_of_surjective (Set.rangeFactorization cell)
      (Set.rangeFactorization_surjective (f := cell))
    have ho : Nat.card Ordering = 3 := by rw [Nat.card_eq_fintype_card]; rfl
    simpa only [Nat.card_fun, ho, Nat.card_coe_set_eq] using h
  · rintro A ⟨label, rfl⟩
    dsimp [cell]
    split_ifs
    · exact convex_realOrderCell _ _
    · exact convex_empty
  · ext x
    constructor
    · rintro ⟨A, ⟨label, rfl⟩, hx⟩
      dsimp [cell] at hx
      split_ifs at hx with h
      · exact realOrderCell_subset_of_meets S label h hx
      · exact False.elim hx
    · intro hx
      obtain ⟨label, hl⟩ := exists_realOrderCell (frontier S) x
      refine ⟨cell label, ⟨label, rfl⟩, ?_⟩
      simpa [cell, show (realOrderCell (frontier S) label ∩ S).Nonempty from
        ⟨x, hl, hx⟩] using hl

theorem exists_finite_convex_cover_of_finite_frontier {S : Set ℝ}
    (hS : (frontier S).Finite) :
    ∃ C : Set (Set ℝ), C.Finite ∧ (∀ A ∈ C, Convex ℝ A) ∧ ⋃₀ C = S := by
  obtain ⟨C, hC, _, hconv, hcover⟩ := exists_convex_cover_card_le_of_finite_frontier hS
  exact ⟨C, hC, hconv, hcover⟩

theorem IsSemialgebraic.finite_convex_cover_polynomial_curve {ι : Type*}
    {S : Set (ι → ℝ)} (hS : IsSemialgebraic ι S) (g : ι → Polynomial ℝ) :
    ∃ C : Set (Set ℝ), C.Finite ∧ (∀ A ∈ C, Convex ℝ A) ∧
      ⋃₀ C = {t : ℝ | (fun i => (g i).eval t) ∈ S} :=
  exists_finite_convex_cover_of_finite_frontier (hS.finite_frontier_polynomial_curve g)

theorem finite_connectedComponents_of_finite_preconnected_cover
    {X : Type*} [TopologicalSpace X] {S : Set X} {C : Set (Set X)}
    (hC : C.Finite) (hconn : ∀ A ∈ C, IsPreconnected A) (hcover : ⋃₀ C = S) :
    Finite (ConnectedComponents S) := by
  have hsub (A : Set X) (hA : A ∈ C) : A ⊆ S := by
    rw [← hcover]
    exact subset_sUnion_of_mem hA
  have hpre (A : Set X) (hA : A ∈ C) :
      IsPreconnected (((↑) : S → X) ⁻¹' A) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr (hsub A hA)]
    exact hconn A hA
  have hf : (⋃ A ∈ C, ConnectedComponents.mk '' (((↑) : S → X) ⁻¹' A)).Finite := by
    apply hC.biUnion
    intro A hA
    exact ((hpre A hA).image ConnectedComponents.mk
      ConnectedComponents.continuous_coe.continuousOn).subsingleton.finite
  apply Set.finite_univ_iff.mp
  apply hf.subset
  intro y _
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe y
  have hx : x.val ∈ ⋃₀ C := by rw [hcover]; exact x.property
  obtain ⟨A, hA, hxA⟩ := hx
  exact mem_iUnion.mpr ⟨A, mem_iUnion.mpr ⟨hA, ⟨x, hxA, rfl⟩⟩⟩

theorem card_connectedComponents_le_of_finite_preconnected_cover
    {X : Type*} [TopologicalSpace X] {S : Set X} {C : Set (Set X)}
    (hC : C.Finite) (hconn : ∀ A ∈ C, IsPreconnected A) (hcover : ⋃₀ C = S) :
    Nat.card (ConnectedComponents S) ≤ C.ncard := by
  classical
  let : Fintype C := hC.fintype
  let image (A : C) := ConnectedComponents.mk '' (((↑) : S → X) ⁻¹' A.val)
  have hsub (A : C) : A.val ⊆ S := by
    rw [← hcover]
    exact subset_sUnion_of_mem A.property
  have hpre (A : C) : IsPreconnected (((↑) : S → X) ⁻¹' A.val) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr (hsub A)]
    exact hconn _ A.property
  have hcard (A : C) : (image A).ncard ≤ 1 := by
    have hs := ((hpre A).image ConnectedComponents.mk
      ConnectedComponents.continuous_coe.continuousOn).subsingleton
    exact (Set.ncard_le_one hs.finite).mpr (fun _ ha _ hb => hs ha hb)
  have hcover' : ⋃ A : C, image A = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe y
    have hx : x.val ∈ ⋃₀ C := by rw [hcover]; exact x.property
    obtain ⟨A, hA, hxA⟩ := hx
    exact mem_iUnion.mpr ⟨⟨A, hA⟩, ⟨x, hxA, rfl⟩⟩
  calc
    _ = (⋃ A : C, image A).ncard := by rw [hcover', Set.ncard_univ]
    _ ≤ ∑ A : C, (image A).ncard := Set.ncard_iUnion_le_of_fintype image
    _ ≤ ∑ _A : C, 1 := Finset.sum_le_sum (fun A _ => hcard A)
    _ = C.ncard := by simp [← Nat.card_eq_fintype_card]

theorem IsSemialgebraic.finite_components_polynomial_curve {ι : Type*}
    {S : Set (ι → ℝ)} (hS : IsSemialgebraic ι S) (g : ι → Polynomial ℝ) :
    Finite (ConnectedComponents {t : ℝ | (fun i => (g i).eval t) ∈ S}) := by
  obtain ⟨C, hC, hconv, hcover⟩ := hS.finite_convex_cover_polynomial_curve g
  exact finite_connectedComponents_of_finite_preconnected_cover hC
    (fun A hA => (hconv A hA).isPreconnected) hcover

/-- Global interval decomposition of a one-dimensional semialgebraic set.
`OrdConnected` allows singleton, empty, bounded, and unbounded intervals.-/
theorem IsSemialgebraic.finite_interval_cover {S : Set (Fin 1 → ℝ)}
    (hS : IsSemialgebraic (Fin 1) S) :
    ∃ C : Set (Set ℝ), C.Finite ∧ (∀ A ∈ C, Set.OrdConnected A) ∧
      ⋃₀ C = {t : ℝ | (fun _ : Fin 1 => t) ∈ S} := by
  obtain ⟨C, hC, hconv, hcover⟩ :=
    hS.finite_convex_cover_polynomial_curve (fun _ => Polynomial.X)
  exact ⟨C, hC, fun A hA => (hconv A hA).ordConnected, by simpa using hcover⟩

end
end DuistermaatVanDerKallen
