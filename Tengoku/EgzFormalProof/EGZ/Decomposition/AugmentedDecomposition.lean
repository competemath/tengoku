import Tengoku.EgzFormalProof.EGZ.Decomposition.AugmentedDiagram
import Tengoku.EgzFormalProof.EGZ.Decomposition.AugmentedRepresentation
import Tengoku.EgzFormalProof.EGZ.Decomposition.SupportRechartMass
import Tengoku.EgzFormalProof.EGZ.Decomposition.SupportDecomposition
import Tengoku.EgzFormalProof.EGZ.Decomposition.SupportParameters
import Tengoku.EgzFormalProof.EGZ.Decomposition.FacePreservation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Decompositions with additional affine coordinates

Appending a common prefix of slab coordinates and then choosing the generated
integer lattice charts yields an actual minimal decomposition on the same
nodes and with the same local weights. Forgetting the additional coordinates
maps its proper points to the original decomposition.
-/

open scoped BigOperators
open Classical

namespace EGZ.FlagDecomposition

/-- Reduced nodes depend only on the bases carrying nonzero local weight,
and are unchanged when the coordinate maps or polytopes are replaced.
@isnad1 id=iff.1h5v.s7.748d12a401a6 from=translated src=- shape=102ada2c vocab=6af6a5f3
-/
theorem isReducedElement_iff_sup'_localWeight {p d : ℕ} [NeZero p]
    {f : FpCoord p d → ℕ} (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.flag.Node) :
    Φ.IsReducedElement x ↔
      ∃ (s : Finset Φ.flag.Node) (hs : s.Nonempty),
        (∀ y ∈ s, ∃ v, Φ.localWeight y v ≠ 0) ∧ s.sup' hs id = x := by
  rw [Φ.isReducedElement_iff_sup'_localLift]
  constructor
  · rintro ⟨s, hs, hlocal, hsup⟩
    refine ⟨s, hs, ?_, hsup⟩
    intro y hy
    obtain ⟨z, hz⟩ := hlocal y hy
    obtain ⟨_, v, _, hv⟩ := (FlagDecompositionRaw.centeredFibreMass_ne_zero_iff
      (Φ.localWeight y) (Φ.representation.map y) z).mp hz
    exact ⟨v, hv⟩
  · rintro ⟨s, hs, hlocal, hsup⟩
    refine ⟨s, hs, ?_, hsup⟩
    intro y hy
    obtain ⟨v, hv⟩ := hlocal y hy
    refine ⟨FpCoord.centeredLift (Φ.representation.map y v), ?_⟩
    exact (FlagDecompositionRaw.centeredFibreMass_ne_zero_iff
      (Φ.localWeight y) (Φ.representation.map y) _).mpr
      ⟨FpCoord.isCenteredLift_centeredLift hp _, v,
        (FpCoord.mod_centeredLift _).symm, hv⟩

end EGZ.FlagDecomposition

namespace EGZ.FlagDecomposition.Augmented

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (e : Φ.flag.Node → ℕ)
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p)
    (hp : Odd p)

include hp

/--
@isnad1 id=eq.1h8v.s9.78cdb47c3345 from=translated src=- shape=0206fd64 vocab=cecb365e
-/
theorem lift_eq_centeredLift (x : Φ.flag.Node) (v : FpCoord p d) :
    lift Φ e ξ x v = FpCoord.centeredLift (map Φ e ξ x v) :=
  (lift_centered Φ e ξ hp x v).eq_of_mod_eq
    (FpCoord.isCenteredLift_centeredLift hp _)
    ((lift_mod Φ e ξ x v).trans (FpCoord.mod_centeredLift _).symm)

/-- The augmented supports are exactly the nonzero centered cumulative
fibres, even though the augmented affine maps need not be surjective.
@isnad1 id=iff.1h8v.s9.6e5f174823c9 from=translated src=- shape=00dd728d vocab=288f1985
-/
theorem support_spec_centeredFibreMass (x : Φ.flag.Node)
    (q : IntCoord (Φ.flag.rank x + e x)) :
    q ∈ support Φ e ξ x ↔ FlagDecompositionRaw.centeredFibreMass
      (Φ.cumulativeWeight x) (map Φ e ξ x) q ≠ 0 := by
  rw [mem_support, FlagDecompositionRaw.centeredFibreMass_ne_zero_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨lift_centered Φ e ξ hp x v, v, (lift_mod Φ e ξ x v).symm, hv⟩
  · rintro ⟨hc, v, hmap, hv⟩
    exact ⟨v, hv, (lift_centered Φ e ξ hp x v).eq_of_mod_eq hc
      ((lift_mod Φ e ξ x v).trans hmap)⟩

/--
@isnad1 id=mem.2h8v.s9.892a187a5362 from=translated src=- shape=3db0b627 vocab=48a3c89e
-/
theorem centeredLift_map_mem_support (x : Φ.flag.Node) (v : FpCoord p d)
    (hv : Φ.cumulativeWeight x v ≠ 0) :
    FpCoord.centeredLift (map Φ e ξ x v) ∈ support Φ e ξ x := by
  rw [← lift_eq_centeredLift Φ e ξ hp]
  exact (mem_support Φ e ξ x _).mpr ⟨v, hv, rfl⟩

/-- Forgetting the additional coordinates sends a nonzero augmented local
fibre to a nonzero original local fibre.
@isnad1 id=ne.2h8v.s10.4ecdbc059e5c from=translated src=- shape=3a681896 vocab=0e6bba58
-/
theorem localLift_first_ne_zero (x : Φ.flag.Node)
    (q : IntCoord (Φ.flag.rank x + e x))
    (hq : FlagDecompositionRaw.centeredFibreMass
      (Φ.localWeight x) (map Φ e ξ x) q ≠ 0) :
    Φ.localLift x (Coord.first (Φ.flag.rank x) (e x) q) ≠ 0 := by
  obtain ⟨hc, v, hmap, hv⟩ :=
    (FlagDecompositionRaw.centeredFibreMass_ne_zero_iff _ _ _).mp hq
  have heq : lift Φ e ξ x v = q :=
    (lift_centered Φ e ξ hp x v).eq_of_mod_eq hc ((lift_mod Φ e ξ x v).trans hmap)
  rw [← heq, lift_first]
  exact (FlagDecompositionRaw.centeredFibreMass_ne_zero_iff
    (Φ.localWeight x) (Φ.representation.map x) _).mpr
    ⟨FpCoord.isCenteredLift_centeredLift hp _, v, (FpCoord.mod_centeredLift _).symm, hv⟩

variable (he : Antitone e)
    (C : ∀ x, IntegerLatticeChart (support Φ e ξ x))

/-- The map from charted augmented coordinates to the original coordinates.-/
noncomputable def forget (x : Φ.flag.Node) :
    IntegralAffineMap (C x).rank (Φ.flag.rank x) :=
  (IntegralAffineMap.first (Φ.flag.rank x) (e x)).comp
    ((diagram Φ e ξ hp he).chart C x)

/--
@isnad1 id=eq.2h8v.s10.04d010a50eb5 from=translated src=- shape=422d4e98 vocab=f9ca601d
-/
theorem forget_image_polytope (x : Φ.flag.Node) :
    (forget Φ e ξ hp he C x).real ''
        (((diagram Φ e ξ hp he).chartedFlag C).polytope x).carrier =
      (Φ.flag.polytope x).carrier := by
  change ((IntegralAffineMap.first (Φ.flag.rank x) (e x)).real ∘
    ((diagram Φ e ξ hp he).chart C x).real) '' _ = _
  rw [Set.image_comp, (diagram Φ e ξ hp he).chart_image_polytope,
    first_image_polytope]

/--
@isnad1 id=mapsto.2h8v.s10.6bf001170e0f from=translated src=- shape=69605f1f vocab=c84471e1
-/
theorem forget_mem_polytope (x : Φ.flag.Node) :
    Set.MapsTo (forget Φ e ξ hp he C x).real
      (((diagram Φ e ξ hp he).chartedFlag C).polytope x).carrier
      (Φ.flag.polytope x).carrier := by
  intro q hq
  rw [← forget_image_polytope Φ e ξ hp he C x]
  exact ⟨q, hq, rfl⟩

/--
@isnad1 id=eq.3h10v.s11.cdd3ab9dc607 from=translated src=- shape=1d6682c0 vocab=a2d99e9b
-/
theorem forget_transition {x y : Φ.flag.Node} (h : x ≤ y)
    (q : RealCoord (C x).rank) :
    (forget Φ e ξ hp he C y).real
        (((diagram Φ e ξ hp he).chartedFlag C).transition h |>.real q) =
      (Φ.flag.transition h).real ((forget Φ e ξ hp he C x).real q) := by
  change (IntegralAffineMap.first (Φ.flag.rank y) (e y)).real
      (((diagram Φ e ξ hp he).chart C y).real
        (((diagram Φ e ξ hp he).chartedTransition C h).real q)) = _
  rw [(diagram Φ e ξ hp he).chart_transition_real]
  exact AffineMap.congr_fun
    (congrArg IntegralAffineMap.real (first_comp_transition Φ e he h))
    (((diagram Φ e ξ hp he).chart C x).real q)

variable [Fact p.Prime]
    (hmod : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

/-- The new represented space is the cumulative support span and is
contained in the old represented space.
@isnad1 id=le.3h8v.s10.e0bf82a580cc from=translated src=- shape=1f751f6e vocab=7290b9ca
-/
theorem representation_space_le_original (x : Φ.flag.Node) :
    (representation Φ e ξ hp he C hmod).space x ≤ Φ.representation.space x := by
  change affineSpan (ZMod p) {v | Φ.cumulativeWeight x v ≠ 0} ≤ _
  exact affineSpan_le.mpr (fun v hv ↦ Φ.originalWeights.cumulative_supported x v hv)

/-- The modular chart retracts to the augmented affine map on the full
represented affine space, not only on its nonzero cumulative atoms.
@isnad1 id=eq.4h9v.s11.15a08afa63e6 from=translated src=- shape=d9d2ee6e vocab=e9d8811d
-/
theorem chart_representation_map (x : Φ.flag.Node) (v : FpCoord p d)
    (hv : v ∈ (representation Φ e ξ hp he C hmod).space x) :
    ((diagram Φ e ξ hp he).chart C x).modp p
        ((representation Φ e ξ hp he C hmod).map x v) = map Φ e ξ x v := by
  apply AffineMap.eqOn_affineSpan
    (f := (((diagram Φ e ξ hp he).chart C x).modp p).comp
      ((representation Φ e ξ hp he C hmod).map x)) (g := map Φ e ξ x) ?_ hv
  intro w hw
  exact (diagram Φ e ξ hp he).chart_coordinateMap C Φ.localWeight (map Φ e ξ) hmod
    (fun y ↦ (support_mod Φ e ξ y).symm) x w hw

/--
@isnad1 id=iff.5h10v.s12.85ee25b6f738 from=translated src=- shape=9fb6a3de vocab=f5a15f73
-/
theorem representation_map_eq_iff (x : Φ.flag.Node) (v w : FpCoord p d)
    (hv : v ∈ (representation Φ e ξ hp he C hmod).space x)
    (hw : w ∈ (representation Φ e ξ hp he C hmod).space x) :
    (representation Φ e ξ hp he C hmod).map x v =
        (representation Φ e ξ hp he C hmod).map x w ↔
      map Φ e ξ x v = map Φ e ξ x w := by
  constructor
  · intro heq
    rw [← chart_representation_map Φ e ξ hp he C hmod x v hv,
      ← chart_representation_map Φ e ξ hp he C hmod x w hw, heq]
  · intro heq
    exact congrArg (affineLeftInverse
      ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p)) heq

/-- The forgotten new coordinate is exactly the original coordinate on
the new represented affine space.
@isnad1 id=eq.4h9v.s11.e619b75f8341 from=translated src=- shape=e6b7b574 vocab=0eadd319
-/
theorem forget_representation_map (x : Φ.flag.Node) (v : FpCoord p d)
    (hv : v ∈ (representation Φ e ξ hp he C hmod).space x) :
    (forget Φ e ξ hp he C x).modp p ((representation Φ e ξ hp he C hmod).map x v) =
      Φ.representation.map x v := by
  have h := congrArg (Coord.first (Φ.flag.rank x) (e x))
    (chart_representation_map Φ e ξ hp he C hmod x v hv)
  exact h.trans (Coord.first_append _ _ _)

/-- The charted augmented flag has the exact cumulative support required by
the decomposition constructor.-/
noncomputable def supportData : FlagDecompositionRaw.SupportData
    (representation Φ e ξ hp he C hmod) Φ.localWeight where
  support x := (C x).coordinateSupport
  support_spec x q := (C x).coordinateSupport_spec_rechart (map Φ e ξ x) (hmod x)
    hp (hcenter x) (Φ.cumulativeWeight x) (support_spec_centeredFibreMass Φ e ξ hp x) q
  support_nonempty x := (C x).coordinateSupport_nonempty (support_nonempty Φ e ξ x)
  polytope_eq x := ((diagram Φ e ξ hp he).rechart C).polytope_carrier x
  transition_support h _q hq := (diagram Φ e ξ hp he).chartedTransition_support C h hq
  local_supported := local_supported Φ e ξ hp he C hmod

/-- The actual augmented and minimalized decomposition, with unchanged
nodes and unchanged local weights.-/
noncomputable abbrev decomposition : FlagDecomposition p d f :=
  (supportData Φ e ξ hp he C hmod hcenter).decomposition hp f Φ.retained_le

/--
@isnad1 id=isminima.4h7v.s10.a0303a8eb809 from=translated src=- shape=131df597 vocab=d2184fae
-/
theorem decomposition_isMinimal : (decomposition Φ e ξ hp he C hmod hcenter).IsMinimal := by
  intro x
  exact ⟨rfl, (C x).coordinateSupport_affineIntSpans⟩

/--
@isnad1 id=eq.4h7v.s10.7bfe0a5d9cd2 from=translated src=- shape=5ca1b577 vocab=511b0be7
-/
@[simp]
theorem decomposition_retainedWeight :
    (decomposition Φ e ξ hp he C hmod hcenter).retainedWeight = Φ.retainedWeight := rfl

/--
@isnad1 id=eq.4h7v.s10.bc9387a4045d from=translated src=- shape=416a0d89 vocab=bd466fd0
-/
@[simp]
theorem decomposition_retainedMass :
    (decomposition Φ e ξ hp he C hmod hcenter).retainedMass = Φ.retainedMass := rfl

/--
@isnad1 id=eq.4h8v.s10.388be25785a6 from=translated src=- shape=89843e81 vocab=72a8c80d
-/
@[simp]
theorem decomposition_cumulativeWeight (x : Φ.flag.Node) :
    (decomposition Φ e ξ hp he C hmod hcenter).cumulativeWeight x =
      Φ.cumulativeWeight x := rfl

/--
@isnad1 id=eq.4h8v.s10.f62afee01129 from=translated src=- shape=89843e81 vocab=40d0d1e7
-/
@[simp]
theorem decomposition_localWeight (x : Φ.flag.Node) :
    (decomposition Φ e ξ hp he C hmod hcenter).localWeight x = Φ.localWeight x := rfl

/--
@isnad1 id=eq.4h7v.s10.9d7e682ecec7 from=translated src=- shape=32cc7821 vocab=255cce3c
-/
@[simp]
theorem card_decomposition :
    @Fintype.card (decomposition Φ e ξ hp he C hmod hcenter).flag.Node
        (decomposition Φ e ξ hp he C hmod hcenter).flag.nodeFintype =
      Fintype.card Φ.flag.Node := rfl

/-- The new centered cumulative mass is the old augmented centered mass at
the image under the integer chart.
@isnad1 id=eq.4h9v.s11.caf4b1ad5ac2 from=translated src=- shape=7ab225f6 vocab=7aa780ae
-/
theorem decomposition_hat (x : Φ.flag.Node) (q : IntCoord (C x).rank) :
    (decomposition Φ e ξ hp he C hmod hcenter).hat x q =
      FlagDecompositionRaw.centeredFibreMass (Φ.cumulativeWeight x)
        (map Φ e ξ x) ((C x).map q) :=
  (C x).centeredFibreMass_rechart (map Φ e ξ x) (hmod x) hp (hcenter x)
    (Φ.cumulativeWeight x) (centeredLift_map_mem_support Φ e ξ hp x) q

/--
@isnad1 id=eq.4h9v.s11.baebe67d8a81 from=translated src=- shape=7ab225f6 vocab=370bf2b0
-/
theorem decomposition_localLift (x : Φ.flag.Node) (q : IntCoord (C x).rank) :
    (decomposition Φ e ξ hp he C hmod hcenter).localLift x q =
      FlagDecompositionRaw.centeredFibreMass (Φ.localWeight x)
        (map Φ e ξ x) ((C x).map q) :=
  (C x).centeredFibreMass_rechart (map Φ e ξ x) (hmod x) hp (hcenter x)
    (Φ.localWeight x) (fun v hv ↦ centeredLift_map_mem_support Φ e ξ hp x v
      (ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le
        (FlagDecompositionRaw.localWeight_le_cumulative Φ.localWeight x v)))) q

/-- Changing coordinates leaves the set of reduced nodes exactly unchanged.
@isnad1 id=iff.4h8v.s10.489bb2f3222b from=translated src=- shape=5bce5530 vocab=776ad2ee
-/
theorem decomposition_isReducedElement_iff (x : Φ.flag.Node) :
    (decomposition Φ e ξ hp he C hmod hcenter).IsReducedElement x ↔
      Φ.IsReducedElement x := by
  rw [(decomposition Φ e ξ hp he C hmod hcenter).isReducedElement_iff_sup'_localWeight hp,
    Φ.isReducedElement_iff_sup'_localWeight hp]

/--
@isnad1 id=iff.4h7v.s10.e72a7d5a3bf1 from=translated src=- shape=a2beac36 vocab=1f0c1ac1
-/
theorem decomposition_isReduced_iff :
    (decomposition Φ e ξ hp he C hmod hcenter).IsReduced ↔ Φ.IsReduced :=
  forall_congr' (decomposition_isReducedElement_iff Φ e ξ hp he C hmod hcenter)

/-- Completeness of an old element persists when the coordinate fibres are
refined by the additional affine directions.
@isnad1 id=iscomple.5h10v.s10.e6b4a6d5fe5b from=translated src=- shape=82fd2db1 vocab=355cf0f5
-/
theorem decomposition_isCompleteElement (x : Φ.flag.Node) (t : ℕ) (δ : ℝ)
    (hcomplete : Φ.IsCompleteElement x t δ) :
    (decomposition Φ e ξ hp he C hmod hcenter).IsCompleteElement x t δ := by
  intro η hη
  apply hcomplete η
  obtain ⟨v, w, hv, hw, heq, hne⟩ := hη
  refine ⟨v, w, representation_space_le_original Φ e ξ hp he C hmod x hv,
    representation_space_le_original Φ e ξ hp he C hmod x hw, ?_, hne⟩
  rw [← forget_representation_map Φ e ξ hp he C hmod x v hv,
    ← forget_representation_map Φ e ξ hp he C hmod x w hw]
  exact congrArg ((forget Φ e ξ hp he C x).modp p) heq

/-- Bounds for the slab block and the chart inverse bound every integer
point of the new polytope.
@isnad1 id=iskbound.7h10v.s11.783c8e0eb621 from=translated src=- shape=db9cc466 vocab=04234dbb
-/
theorem decomposition_isKBounded {K L B : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K)
    (hL : ∀ x v, Φ.cumulativeWeight x v ≠ 0 →
      latticeSupNorm (slabCoordinates (e x) ξ v) ≤ L x)
    (hC : ∀ x (q : IntCoord (C x).rank),
      latticeSupNorm ((C x).map q) ≤ max (K x) (L x) → latticeSupNorm q ≤ B x) :
    (decomposition Φ e ξ hp he C hmod hcenter).IsKBounded B :=
  (diagram Φ e ξ hp he).charted_polytope_bound C
    ((diagram Φ e ξ hp he).polytope_bound (support_bound Φ e ξ hp hK hL)) hC

/-- Project a new flag point by forgetting the augmented coordinate block.-/
noncomputable def forwardPoint
    (q : (decomposition Φ e ξ hp he C hmod hcenter).flag.Point) : Φ.flag.Point :=
  q.map (SupHom.id _) (fun x ↦ (forget Φ e ξ hp he C x).real)
    (forget_mem_polytope Φ e ξ hp he C)

/--
@isnad1 id=mem.5h8v.s10.3b27b2dd6a80 from=translated src=- shape=87952789 vocab=da4b6530
-/
theorem forwardPoint_mem_omegaZero
    {q : (decomposition Φ e ξ hp he C hmod hcenter).flag.Point}
    (hq : q ∈ (decomposition Φ e ξ hp he C hmod hcenter).omegaZero) :
    forwardPoint Φ e ξ hp he C hmod hcenter q ∈ Φ.omegaZero := by
  obtain ⟨z, hz, hw⟩ := hq
  refine ⟨Coord.first (Φ.flag.rank q.base) (e q.base) ((C q.base).map z), ?_, ?_⟩
  · change ((forget Φ e ξ hp he C q.base).integer z).real =
      (forget Φ e ξ hp he C q.base).real q.val
    rw [← hz, (forget Φ e ξ hp he C q.base).real_integer]
  · apply localLift_first_ne_zero Φ e ξ hp
    change (decomposition Φ e ξ hp he C hmod hcenter).localLift q.base z ≠ 0 at hw
    rwa [decomposition_localLift] at hw

/-- Forgetting the slab block is a subdivision map to the original flag.-/
noncomputable def subdivisionMap :
    SubdivisionMap Φ (decomposition Φ e ξ hp he C hmod hcenter) :=
  SubdivisionMap.of_local_generators (SupHom.id _)
    (fun x ↦ (forget Φ e ξ hp he C x).real)
    (forget_mem_polytope Φ e ξ hp he C) (forget_transition Φ e ξ hp he C)
    (fun _ hq ↦ forwardPoint_mem_omegaZero Φ e ξ hp he C hmod hcenter hq)

omit [Fact p.Prime] hmod hcenter in
/--
@isnad1 id=nonempty.2h9v.s10.b412ee27611d from=translated src=- shape=7f64a8bd vocab=593370fa
-/
theorem face_preimage_nonempty (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face) :
    ((((diagram Φ e ξ hp he).chartedFlag C).polytope x).carrier ∩
      (forget Φ e ξ hp he C x).real ⁻¹' Γ.carrier).Nonempty := by
  obtain ⟨q, hq⟩ := Γ.nonempty
  have hpoly := Γ.subset_polytope hq
  rw [← forget_image_polytope Φ e ξ hp he C x] at hpoly
  obtain ⟨r, hr, rfl⟩ := hpoly
  exact ⟨r, hr, hq⟩

/-- Previously realized faces remain realized after pulling back along the
old-coordinate projection.
@isnad1 id=isrealiz.5h9v.s10.af34db7fe767 from=translated src=- shape=bda7a9ee vocab=538da992
-/
theorem decomposition_isRealizedFace (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face)
    (hΓ : Φ.IsRealizedFace x Γ) :
    (decomposition Φ e ξ hp he C hmod hcenter).IsRealizedFace x
      ((subdivisionMap Φ e ξ hp he C hmod hcenter).face x Γ
        (face_preimage_nonempty Φ e ξ hp he C x Γ)) :=
  (subdivisionMap Φ e ξ hp he C hmod hcenter).isRealizedFace x Γ
    (face_preimage_nonempty Φ e ξ hp he C x Γ) hΓ

end EGZ.FlagDecomposition.Augmented
