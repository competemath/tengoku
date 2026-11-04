import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.FaceRestriction
import Tengoku.Seed.Analysis.Normed.Affine.AddTorsorBases
import Tengoku.Seed.LinearAlgebra.Projection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Supporting cuts and termination of the face reduction in the real span.
Lattice coordinates for the reduced polynomial are constructed separately. -/

open Set
open scoped Topology
namespace DuistermaatVanDerKallen
noncomputable section

/-- Interior relative to the linear span of a set containing the origin.-/
def OriginInSpanInterior {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  (0 : Submodule.span ℝ P) ∈ interior (Subtype.val ⁻¹' P)

/-- A set spans its own linear span when viewed in the subtype.-/
theorem span_preimage_span_eq_top {d : ℕ} (P : Set (Fin d → ℝ)) :
    Submodule.span ℝ (Subtype.val ⁻¹' P : Set (Submodule.span ℝ P)) = ⊤ := by
  apply (Submodule.span_val_image_eq_iff (Submodule.span ℝ P) _).mp
  have he : Subtype.val '' (Subtype.val ⁻¹' P : Set (Submodule.span ℝ P)) = P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩
  rw [he]

/-- A convex set containing zero and not interior at zero in its own span
admits a proper supporting hyperplane through zero in the ambient space.-/
theorem exists_proper_supporting_cut {d : ℕ} {P : Set (Fin d → ℝ)}
    (hc : Convex ℝ P) (h0 : (0 : Fin d → ℝ) ∈ P) (hi : ¬ OriginInSpanInterior P) :
    ∃ L : (Fin d → ℝ) →L[ℝ] ℝ,
      (∀ x ∈ P, 0 ≤ L x) ∧ ∃ x ∈ P, 0 < L x := by
  let W := Submodule.span ℝ P
  let Q : Set W := Subtype.val ⁻¹' P
  have hQ0 : (0 : W) ∈ Q := h0
  have hQspan : Submodule.span ℝ Q = ⊤ := span_preimage_span_eq_top P
  have hQaff : affineSpan ℝ Q = ⊤ := by
    have he := affineSpan_insert_zero (k := ℝ) Q
    rw [Set.insert_eq_of_mem hQ0, hQspan] at he
    exact SetLike.coe_injective he
  have hQc : Convex ℝ Q := hc.linear_preimage W.subtype
  have hQint : (interior Q).Nonempty := hQc.interior_nonempty_iff_affineSpan_eq_top.mpr hQaff
  obtain ⟨φ, hφ, hφle⟩ := geometric_hahn_banach_of_nonempty_interior_point hQc hi hQint
  have hneg : ∃ x ∈ Q, φ x < 0 := by
    by_contra! hh
    apply hφ
    apply ContinuousLinearMap.coe_injective
    apply (Submodule.linearMap_eq_zero_iff_of_span_eq_top φ.toLinearMap hQspan).mpr
    intro x
    have hle : φ x.val ≤ 0 := by simpa using hφle x.val x.property
    exact hle.antisymm (hh x.val x.property)
  obtain ⟨W', hW'⟩ := exists_isCompl W
  let π := W.projectionOnto W' hW'
  let L : (Fin d → ℝ) →L[ℝ] ℝ := (-φ.toLinearMap.comp π).toContinuousLinearMap
  have hL : ∀ (x : Fin d → ℝ) (hx : x ∈ P), L x = -φ ⟨x, Submodule.subset_span hx⟩ := by
    intro x hx
    change -φ (W.projectionOnto W' hW' x) = _
    rw [Submodule.projectionOnto_apply_of_mem_left hW' (Submodule.subset_span hx)]
  refine ⟨L, ?_, ?_⟩
  · intro x hx
    rw [hL x hx]
    have hn : φ ⟨x, Submodule.subset_span hx⟩ ≤ 0 := by
      simpa using hφle ⟨x, Submodule.subset_span hx⟩ hx
    exact neg_nonneg.mpr hn
  · obtain ⟨x, hx, hneg⟩ := hneg
    exact ⟨x.val, hx, by rw [hL x.val hx]; exact neg_pos.mpr hneg⟩

/-- Supporting cuts terminate, preserving all coefficients that survive and every
power constant term, with zero interior in the final real span. This is the
geometric stage of face reduction, before choosing integral lattice coordinates.-/
theorem exists_span_interior_restriction {d : ℕ} (f : MultiLaurent d)
    (hf : (0 : Fin d → ℝ) ∈ newtonPolytope f) :
    ∃ g : MultiLaurent d, g ≠ 0 ∧ g.coeff.support ⊆ f.coeff.support ∧
      (∀ a ∈ g.coeff.support, g.coeff a = f.coeff a) ∧
      (∀ n : ℕ, constantTerm (g ^ n) = constantTerm (f ^ n)) ∧
      (0 : Fin d → ℝ) ∈ newtonPolytope g ∧
      OriginInSpanInterior (newtonPolytope g) := by
  classical
  induction hn : f.coeff.support.card using Nat.strong_induction_on generalizing f with
  | h n ih =>
    subst hn
    by_cases hi : OriginInSpanInterior (newtonPolytope f)
    · refine ⟨f, ?_, Finset.Subset.refl _, by intros; rfl, by intros; rfl, hf, hi⟩
      intro he
      rw [he] at hf
      simp [newtonPolytope] at hf
    · obtain ⟨L, hL, x, hx, hpos⟩ :=
        exists_proper_supporting_cut (convex_convexHull ℝ _) hf hi
      have hs : ∀ a ∈ f.coeff.support, 0 ≤ L (exponentVector a) := by
        intro a ha
        exact hL _ (subset_convexHull ℝ _ ⟨a, ha, rfl⟩)
      have hp : ∃ a ∈ f.coeff.support, 0 < L (exponentVector a) := by
        by_contra! hh
        have hle : newtonPolytope f ⊆ {y | L y ≤ 0} :=
          convexHull_min (by rintro _ ⟨a, ha, rfl⟩; exact hh a ha)
            ((convex_Iic (0 : ℝ)).linear_preimage L.toLinearMap)
        exact (not_lt_of_ge (hle hx)) hpos
      obtain ⟨a, ha, hpa⟩ := hp
      let q := facePart (exponentFunctional L) f
      have hq : q.coeff.support.card < f.coeff.support.card :=
        facePart_support_card_lt (exponentFunctional L) f ha (ne_of_gt hpa)
      obtain ⟨g, hg, hgs, hgc, hgn, hg0, hgi⟩ :=
        ih _ hq q (origin_mem_newtonPolytope_facePart f L hs hf) rfl
      refine ⟨g, hg, ?_, ?_, ?_, hg0, hgi⟩
      · intro b hb
        exact ((mem_support_facePart (exponentFunctional L) f b).mp (hgs hb)).1
      · intro b hb
        rw [hgc b hb]
        have hwb := ((mem_support_facePart (exponentFunctional L) f b).mp (hgs hb)).2
        exact (facePart_coeff (exponentFunctional L) f b).trans (by simp [hwb])
      · intro k
        exact (hgn k).trans (constantTerm_facePart_pow f L hs k)

end
end DuistermaatVanDerKallen
