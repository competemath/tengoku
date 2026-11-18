import Tengoku.EgzFormalProof.EGZ.Decomposition.PruningData
import Tengoku.EgzFormalProof.EGZ.Decomposition.Rebuild
import Tengoku.EgzFormalProof.EGZ.Decomposition.FacePreservation
import Tengoku.EgzFormalProof.EGZ.Decomposition.PruningStability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometric gap cleanup

Surviving local weights first give a flag of their nonempty cumulative support
hulls. Restricting that flag to reduced nodes finishes the geometric cleanup.
The construction retains exactly the mass supplied by numerical pruning.
-/

open scoped BigOperators

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

/--
@isnad1 id=lt.1h5v.s6.11d42c34763f from=translated src=- shape=956c7992 vocab=5318d701
-/
theorem cumulativeMass_pos (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.flag.Node) : 0 < natMass (Φ.cumulativeWeight x) := by
  classical
  obtain ⟨q, hq⟩ := Φ.liftedSupport_nonempty x
  rw [← Φ.sum_liftedSupport hp x]
  exact (Nat.pos_of_ne_zero ((Φ.liftedSupport_spec x q).mp hq)).trans_le
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hq)

/-- Every decomposition has positive retained mass: its top lifted support
is nonempty and all its stored masses are positive.
@isnad1 id=lt.1h4v.s5.bc61d0d54993 from=translated src=- shape=12588182 vocab=6d8777cc
-/
theorem retainedMass_pos (Φ : FlagDecomposition p d f) (hp : Odd p) :
    0 < Φ.retainedMass := by
  classical
  obtain ⟨q, hq⟩ := Φ.liftedSupport_nonempty ⊤
  have hpos : 0 < ∑ z ∈ Φ.liftedSupport ⊤, Φ.hat ⊤ z :=
    (Nat.pos_of_ne_zero ((Φ.liftedSupport_spec ⊤ q).mp hq)).trans_le
      (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hq)
  rw [Φ.sum_liftedSupport hp] at hpos
  have heq : Φ.cumulativeWeight ⊤ = Φ.retainedWeight := by
    funext v
    simp [cumulativeWeight, FlagDecompositionRaw.cumulativeWeight,
      retainedWeight, FlagDecompositionRaw.retainedWeight]
  rw [heq] at hpos
  exact hpos

namespace PrunedWeights

variable {Φ : FlagDecomposition p d f} (D : PrunedWeights Φ)

/-- The old support polytopes supply all compatibility conditions for
the rebuilding construction; none is an additional geometric assumption.
@isnad1 id=rebuildd.1h5v.s5.b9e7edc0a76e from=translated src=- shape=9fb3fdde vocab=c4d53084
-/
theorem rebuildData (hp : Odd p) :
    FlagDecompositionRaw.RebuildData Φ.representation D.weight f where
  odd := hp
  nonzero := D.nonzero
  local_supported := D.weight_supported
  retained_le v := (Finset.sum_le_sum (fun x _ ↦ D.weight_le x v)).trans (Φ.retained_le v)
  transition_hat_nonzero h _z hz :=
    (D.mem_support _ _).mp (D.transition_mem_support h ((D.mem_support _ _).mpr hz))
  hat_exists_local x z hz := D.exists_localLift_of_hat_ne_zero hp x z hz

noncomputable abbrev rebuilt (hp : Odd p) : FlagDecomposition p d f :=
  (D.rebuildData hp).decomposition

noncomputable abbrev cleaned (hp : Odd p) : FlagDecomposition p d f :=
  (D.rebuilt hp).reduced hp

variable (hp : Odd p)

/--
@isnad1 id=le.1h6v.s7.c6a0b49d3754 from=translated src=- shape=9ce60e64 vocab=737e726f
-/
theorem rebuilt_polytope_subset (x : (D.rebuilt hp).flag.Node) :
    ((D.rebuilt hp).flag.polytope x).carrier ⊆ (Φ.flag.polytope x.1).carrier := by
  rw [(D.rebuildData hp).polytope_carrier]
  apply convexHull_min _ (Φ.flag.polytope x.1).convex
  rintro _ ⟨z, hz, rfl⟩
  exact D.mem_old_polytope ((D.mem_support x.1 z).mp hz)

/--
@isnad1 id=eq.1h6v.s7.51f80501ea09 from=translated src=- shape=d48e77e1 vocab=d9f8ea93
-/
@[simp]
theorem cleaned_localWeight (x : (D.cleaned hp).flag.Node) :
    (D.cleaned hp).localWeight x = D.weight x.1.1 := rfl

/--
@isnad1 id=eq.1h6v.s7.a4226eb600c5 from=translated src=- shape=7be6465a vocab=429aa698
-/
@[simp]
theorem cleaned_cumulativeWeight (x : (D.cleaned hp).flag.Node) :
    (D.cleaned hp).cumulativeWeight x = D.cumulative x.1.1 := by
  rw [reduced_cumulativeWeight, (D.rebuildData hp).decomposition_cumulativeWeight]

/--
@isnad1 id=eq.1h6v.s7.ea29ff447ee3 from=translated src=- shape=9098a9f0 vocab=581659a4
-/
@[simp]
theorem cleaned_hat (x : (D.cleaned hp).flag.Node) :
    (D.cleaned hp).hat x = D.hat x.1.1 := by
  rw [reduced_hat, (D.rebuildData hp).decomposition_hat]

/--
@isnad1 id=eq.1h5v.s6.10dad59b0d72 from=translated src=- shape=8954befa vocab=6b4b4fe4
-/
@[simp]
theorem cleaned_retainedMass : (D.cleaned hp).retainedMass =
    natMass (FlagDecompositionRaw.retainedWeight D.weight) := by
  rw [reduced_retainedMass, retainedMass,
    (D.rebuildData hp).decomposition_retainedWeight]

/--
@isnad1 id=isreduce.1h5v.s5.6f643cd6b310 from=translated src=- shape=ceec325e vocab=65ef8160
-/
theorem cleaned_isReduced : (D.cleaned hp).IsReduced :=
  (D.rebuilt hp).reduced_isReduced hp

/--
@isnad1 id=le.1h5v.s6.7d49efd7fe31 from=translated src=- shape=f98c9421 vocab=ac0f5f64
-/
theorem cleaned_card_le : @Fintype.card (D.cleaned hp).flag.Node
    (D.cleaned hp).flag.nodeFintype ≤
    Fintype.card Φ.flag.Node :=
  ((D.rebuilt hp).card_reduced_le hp).trans
    (D.rebuildData hp).card_decomposition_le

/--
@isnad1 id=le.1h6v.s8.cacc12a5591b from=translated src=- shape=d882d41e vocab=c2f00bd3
-/
theorem cleaned_polytope_subset (x : (D.cleaned hp).flag.Node) :
    ((D.cleaned hp).flag.polytope x).carrier ⊆ (Φ.flag.polytope x.1.1).carrier :=
  D.rebuilt_polytope_subset hp x.1

/--
@isnad1 id=iskbound.2h6v.s7.0739da98df7f from=translated src=- shape=abd59e24 vocab=b9239abe
-/
theorem cleaned_isKBounded {K : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K) :
    (D.cleaned hp).IsKBounded (fun x ↦ K x.1.1) :=
  fun x z hz ↦ hK x.1.1 z (D.cleaned_polytope_subset hp x hz)

noncomputable def rebuiltSubdivisionMap : SubdivisionMap Φ (D.rebuilt hp) :=
  SubdivisionMap.of_local_generators
    { toFun := Subtype.val, map_sup' := fun _ _ ↦ rfl }
    (fun _ ↦ AffineMap.id ℝ _)
    (fun x ↦ D.rebuilt_polytope_subset hp x)
    (fun _ _ ↦ rfl)
    (by
      rintro q ⟨z, hz, hmass⟩
      refine ⟨z, hz, ?_⟩
      change D.localLift q.base.1 z ≠ 0 at hmass
      exact ne_of_gt ((Nat.pos_of_ne_zero hmass).trans_le (D.localLift_le_old _ _)))

noncomputable def cleanedSubdivisionMap : SubdivisionMap Φ (D.cleaned hp) :=
  (D.rebuiltSubdivisionMap hp).comp ((D.rebuilt hp).reducedSubdivisionMap hp)

/-- A realized old face remains realized on its nonempty intersection with
the cleaned polytope. Its new index is allowed to move downwards.
@isnad1 id=isrealiz.3h7v.s9.5c94a27acde1 from=translated src=- shape=63e4ebac vocab=c6eff1d6
-/
theorem cleaned_isRealizedFace (x : (D.cleaned hp).flag.Node)
    (Γ : (Φ.flag.polytope x.1.1).Face)
    (hne : (((D.cleaned hp).flag.polytope x).carrier ∩ Γ.carrier).Nonempty)
    (hΓ : Φ.IsRealizedFace x.1.1 Γ) :
    (D.cleaned hp).IsRealizedFace x
      ((D.cleanedSubdivisionMap hp).face x Γ hne) :=
  (D.cleanedSubdivisionMap hp).isRealizedFace x Γ hne hΓ

/-- The cleanup thickness bound holds for every resulting parameter,
including negative ones, since every retained cumulative weight is nonzero.
@isnad1 id=iscomple.6h10v.s8.119cf2a2621d from=translated src=- shape=20cc26b8 vocab=e36d6860
-/
theorem cleaned_isCompleteElement {x : (D.cleaned hp).flag.Node} {t : ℕ}
    {ε δ α : ℝ} (hε : 0 < ε) (hα : 0 ≤ α)
    (hlarge : Φ.IsLargeElement ε x.1.1) (hcomplete : Φ.IsCompleteElement x.1.1 t δ)
    (hloss : (Φ.retainedMass : ℝ) - (D.cleaned hp).retainedMass ≤ α * Φ.retainedMass) :
    (D.cleaned hp).IsCompleteElement x t (δ - α / ε) := by
  intro ξ hξ
  by_cases hδ : 0 ≤ δ - α / ε
  · rw [D.cleaned_cumulativeWeight]
    rw [D.cleaned_retainedMass] at hloss
    exact hcomplete.thick_of_pruning hp D.weight_le hε hα hlarge hloss hδ ξ hξ
  · rw [isThickAlong_iff_compl]
    have hmass : (0 : ℝ) < natMass ((D.cleaned hp).cumulativeWeight x) := by
      exact_mod_cast (D.cleaned hp).cumulativeMass_pos hp x
    exact (mul_neg_of_neg_of_pos (lt_of_not_ge hδ) hmass).trans_le (Nat.cast_nonneg _)

/--
@isnad1 id=lt.2h7v.s7.5671e188e249 from=translated src=- shape=4f1cd06f vocab=464cedaa
-/
theorem cleaned_gap_gt (threshold : Φ.flag.Node → ℝ)
    (hgap : ∀ x q, D.hat x q ≠ 0 → threshold x < (D.hat x q : ℝ))
    (x : (D.cleaned hp).flag.Node) :
    threshold x.1.1 < ((D.cleaned hp).gap x : ℝ) := by
  classical
  let Ψ := D.cleaned hp
  have hmem := Finset.min'_mem ((Ψ.liftedSupport x).image (Ψ.hat x))
    ((Ψ.liftedSupport_nonempty x).image (Ψ.hat x))
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hmem
  have hq' := (Ψ.liftedSupport_spec x q).mp hq
  have heq' : Ψ.hat x q = Ψ.gap x := heq
  change (D.cleaned hp).hat x q ≠ 0 at hq'
  change (D.cleaned hp).hat x q = (D.cleaned hp).gap x at heq'
  rw [D.cleaned_hat] at hq' heq'
  rw [← heq']
  exact hgap x.1.1 q hq'

end PrunedWeights

/-- Gap cleanup with a rebuilt, reduced output decomposition. All geometric
properties of the output (including preservation of realized faces and
thickness) are supplied by the `PrunedWeights.cleaned_*` theorems above.
No coordinate-versus-prime bound is needed for this operation.
@isnad1 id=ex.4h6v.s9.20e2048b104b from=translated src=- shape=a7a4cc01 vocab=d2365b6f
-/
theorem gap_cleanup_lemma [Fact p.Prime] (Φ : FlagDecomposition p d f)
    (hp : Odd p) {K : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K)
    {α : ℝ} (hα : 0 ≤ α) (hαone : α < 1) :
    ∃ D : PrunedWeights Φ,
      (∀ x v, D.weight x v = 0 ∨ D.weight x v = Φ.localWeight x v) ∧
      (D.cleaned hp).IsReduced ∧
      (D.cleaned hp).IsKBounded (fun x ↦ K x.1.1) ∧
      (∀ x : (D.cleaned hp).flag.Node,
        α * (Φ.retainedMass : ℝ) /
          ((Fintype.card Φ.flag.Node : ℝ) * (2 * (K x.1.1 : ℝ) + 1) ^ d) ≤
            ((D.cleaned hp).gap x : ℝ)) ∧
      (1 - α) * (Φ.retainedMass : ℝ) ≤ ((D.cleaned hp).retainedMass : ℝ) := by
  classical
  obtain ⟨pieces, hatoms, hle, hgap, hmass⟩ := Φ.exists_bounded_gap_pruning hK hα
  have hpos : 0 < natMass (FlagDecompositionRaw.retainedWeight pieces) := by
    have hΦpos : (0 : ℝ) < Φ.retainedMass := by exact_mod_cast Φ.retainedMass_pos hp
    have hret := (mul_pos (sub_pos.mpr hαone) hΦpos).trans_le hmass
    exact_mod_cast hret
  have hnonzero : ∃ x v, pieces x v ≠ 0 := by
    change 0 < ∑ v, ∑ x, pieces x v at hpos
    obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hpos)
    obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
    exact ⟨x, v, hx⟩
  let D : PrunedWeights Φ := ⟨pieces, hle, hnonzero⟩
  refine ⟨D, hatoms, D.cleaned_isReduced hp, D.cleaned_isKBounded hp hK, ?_, ?_⟩
  · intro x
    exact (D.cleaned_gap_gt hp _ hgap x).le
  · rw [D.cleaned_retainedMass]
    exact hmass

end EGZ.FlagDecomposition
