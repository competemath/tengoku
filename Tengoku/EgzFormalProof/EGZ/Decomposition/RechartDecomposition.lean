import Tengoku.EgzFormalProof.EGZ.Decomposition.RechartRepresentation
import Tengoku.EgzFormalProof.EGZ.Decomposition.RechartMass
import Tengoku.EgzFormalProof.EGZ.Convex.Faces

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A decomposition in support-generated lattice coordinates

The recharted flag and finite-field representation form an actual flag
decomposition. Every face contains a new support generator; lifting its old
chart image to an old local generator produces a new proper point over that
face. All weights and lifted masses are preserved, and the new decomposition
has minimal ambient affine spaces and integer lattices.
-/

open scoped BigOperators
open Classical

namespace EGZ.FlagDecomposition.Rechart

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f)
    (C : ∀ x, IntegerLatticeChart (Φ.liftedSupport x))
    (hp : Odd p)
    (hinj : ∀ x, Function.Injective ((chart Φ C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

include hp hinj hcenter

/--
@isnad1 id=eq.3h7v.s10.0178651f214f from=translated src=- shape=87e7fcb7 vocab=087acd66
-/
theorem raw_hat (x : Φ.flag.Node) (q : IntCoord (C x).rank) :
    FlagDecompositionRaw.hat (representation Φ C hp hinj) Φ.localWeight x q =
      Φ.hat x ((C x).map q) :=
  Φ.hat_rechart hp x (C x) (hinj x) (hcenter x) q

/--
@isnad1 id=eq.3h7v.s10.e30a329275b1 from=translated src=- shape=87e7fcb7 vocab=4fa9b754
-/
theorem raw_localLift (x : Φ.flag.Node) (q : IntCoord (C x).rank) :
    FlagDecompositionRaw.localLift (representation Φ C hp hinj) Φ.localWeight x q =
      Φ.localLift x ((C x).map q) :=
  Φ.localLift_rechart hp x (C x) (hinj x) (hcenter x) q

/-- Every new face is visible to a local generator transported from the old
decomposition. This proves the visibility field of the new decomposition.
@isnad1 id=visiblef.3h7v.s10.1eed13ed7627 from=translated src=- shape=88324628 vocab=77f5f9e5
-/
theorem faces_visible (x : Φ.flag.Node) (Γ : (polytope Φ C x).Face) :
    FlagDecompositionRaw.VisibleFace (representation Φ C hp hinj) Φ.localWeight x Γ := by
  obtain ⟨q, hq⟩ := Γ.generatorFinset_nonempty
  have hq' := Finset.mem_filter.mp hq
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq'.1
  have hzold : (C x).map z ∈ Φ.liftedSupport x := (C x).mem_coordinateSupport.mp hz
  obtain ⟨y, hyx, w, hw, hwz⟩ := Φ.originalWeights.exists_localLift_of_hat_ne_zero hp
    x ((C x).map z) ((Φ.liftedSupport_spec x _).mp hzold)
  have hwold : Φ.localLift y w ≠ 0 := hw
  have hwsupport : w ∈ Φ.liftedSupport y :=
    (Φ.liftedSupport_spec y w).mpr
      (ne_of_gt ((Nat.pos_of_ne_zero hwold).trans_le (Φ.localLift_le_hat y w)))
  let w' := (C y).coordinates w
  have hwmap : (C y).map w' = w := (C y).map_coordinates_of_mem hwsupport
  have hwmem : w'.real ∈ (polytope Φ C y).carrier := by
    rw [polytope_carrier]
    exact _root_.subset_convexHull ℝ _
      ⟨w', (C y).coordinates_mem_coordinateSupport hwsupport, rfl⟩
  have hwlocal : FlagDecompositionRaw.localLift (representation Φ C hp hinj)
      Φ.localWeight y w' ≠ 0 := by
    rw [raw_localLift Φ C hp hinj hcenter, hwmap]
    exact hwold
  have htransition : (transition Φ C hyx).real w'.real = z.real := by
    apply chart_real_injective Φ C x
    rw [chart_transition_real, (chart Φ C y).real_integer,
      (chart Φ C x).real_integer]
    change (Φ.flag.transition hyx).real (((C y).map w').real) = ((C x).map z).real
    rw [hwmap, (Φ.flag.transition hyx).real_integer, hwz]
  let r : (flag Φ C).Point := ⟨y, w'.real, hwmem⟩
  refine ⟨r, ConvexFlag.subset_convexHull (flag Φ C) _ ?_, hyx, ?_⟩
  · exact ⟨w', rfl, hwlocal⟩
  · change (transition Φ C hyx).real w'.real ∈ Γ.carrier
    rw [htransition]
    exact hq'.2

/-- Replace every fibre by its support-generated integer lattice coordinates
and every ambient affine space by its cumulative support span.-/
noncomputable abbrev decomposition : FlagDecomposition p d f where
  flag := flag Φ C
  representation := representation Φ C hp hinj
  localWeight := Φ.localWeight
  local_supported := localWeight_supported Φ
  retained_le := Φ.retained_le
  liftedSupport x := (C x).coordinateSupport
  liftedSupport_spec x q := by
    rw [raw_hat Φ C hp hinj hcenter, (C x).mem_coordinateSupport]
    exact Φ.liftedSupport_spec x ((C x).map q)
  liftedSupport_nonempty x := (C x).coordinateSupport_nonempty (Φ.liftedSupport_nonempty x)
  polytope_eq_liftedSupport := polytope_carrier Φ C
  faces_visible := faces_visible Φ C hp hinj hcenter

/--
@isnad1 id=eq.3h6v.s10.47c95586f438 from=translated src=- shape=0965295a vocab=f5be9e5c
-/
@[simp]
theorem decomposition_localWeight (x : Φ.flag.Node) :
    (decomposition Φ C hp hinj hcenter).localWeight x = Φ.localWeight x := rfl

/--
@isnad1 id=eq.3h6v.s10.27debbff8e52 from=translated src=- shape=0965295a vocab=745377e2
-/
@[simp]
theorem decomposition_cumulativeWeight (x : Φ.flag.Node) :
    (decomposition Φ C hp hinj hcenter).cumulativeWeight x = Φ.cumulativeWeight x := rfl

/--
@isnad1 id=eq.3h5v.s10.ed86d3e96fa2 from=translated src=- shape=6b3ecde3 vocab=6c207e80
-/
@[simp]
theorem decomposition_retainedWeight :
    (decomposition Φ C hp hinj hcenter).retainedWeight = Φ.retainedWeight := rfl

/--
@isnad1 id=eq.3h5v.s10.d7b5a2703eb9 from=translated src=- shape=e5d1cc09 vocab=12d69e1d
-/
@[simp]
theorem decomposition_retainedMass :
    (decomposition Φ C hp hinj hcenter).retainedMass = Φ.retainedMass := rfl

/--
@isnad1 id=eq.3h6v.s10.00ffd50fd64a from=translated src=- shape=0485d5b9 vocab=527fce0b
-/
@[simp]
theorem decomposition_liftedSupport (x : Φ.flag.Node) :
    (decomposition Φ C hp hinj hcenter).liftedSupport x = (C x).coordinateSupport := rfl

/--
@isnad1 id=eq.3h7v.s10.c6db9839c04e from=translated src=- shape=cd8b6f32 vocab=8fbe3c1f
-/
@[simp]
theorem decomposition_hat (x : Φ.flag.Node) (q : IntCoord (C x).rank) :
    (decomposition Φ C hp hinj hcenter).hat x q = Φ.hat x ((C x).map q) :=
  raw_hat Φ C hp hinj hcenter x q

/--
@isnad1 id=eq.3h7v.s10.53b9a6a78aad from=translated src=- shape=cd8b6f32 vocab=4212714a
-/
@[simp]
theorem decomposition_localLift (x : Φ.flag.Node) (q : IntCoord (C x).rank) :
    (decomposition Φ C hp hinj hcenter).localLift x q = Φ.localLift x ((C x).map q) :=
  raw_localLift Φ C hp hinj hcenter x q

/-- The new ambient spaces and integer coordinate supports satisfy both
minimality conditions.
@isnad1 id=isminima.3h5v.s10.71a9d58b8c91 from=translated src=- shape=002d6aee vocab=e6fc9cb8
-/
theorem decomposition_isMinimal : (decomposition Φ C hp hinj hcenter).IsMinimal := by
  intro x
  exact ⟨rfl, (C x).coordinateSupport_affineIntSpans⟩

/--
@isnad1 id=iskbound.5h7v.s10.9650f3196fcb from=translated src=- shape=068af7fc vocab=c71f2bd9
-/
theorem decomposition_isKBounded {K B : Φ.flag.Node → ℕ} (hΦ : Φ.IsKBounded K)
    (hC : ∀ x (q : IntCoord (C x).rank),
      latticeSupNorm ((C x).map q) ≤ K x → latticeSupNorm q ≤ B x) :
    (decomposition Φ C hp hinj hcenter).IsKBounded B :=
  polytope_bound Φ C hΦ hC

/-- Recharting preserves the complete finite set of positive lifted masses,
so in particular it preserves their minimum.
@isnad1 id=eq.3h6v.s10.43d900418d20 from=translated src=- shape=a9d2b562 vocab=ab1bf93d
-/
theorem decomposition_gap (x : Φ.flag.Node) :
    (decomposition Φ C hp hinj hcenter).gap x = Φ.gap x := by
  have hmass : (C x).coordinateSupport.image
      (Φ.hat x ∘ (C x).map) = (Φ.liftedSupport x).image (Φ.hat x) := by
    rw [← Finset.image_image, (C x).image_coordinateSupport]
  have hhat : (decomposition Φ C hp hinj hcenter).hat x = Φ.hat x ∘ (C x).map :=
    funext (decomposition_hat Φ C hp hinj hcenter x)
  unfold gap
  change ((C x).coordinateSupport.image ((decomposition Φ C hp hinj hcenter).hat x)).min' _ = _
  simp only [hhat, hmass]

end EGZ.FlagDecomposition.Rechart
