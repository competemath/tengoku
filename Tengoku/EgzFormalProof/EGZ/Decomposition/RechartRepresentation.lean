import Tengoku.EgzFormalProof.EGZ.Decomposition.RechartFlag
import Tengoku.EgzFormalProof.EGZ.Decomposition.MinimalRepresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Minimal finite-field representations after changing lattice coordinates

Restrict each ambient affine space to the span of its cumulative support.
An affine left inverse of the modular lattice chart then gives a surjective
representation in the new coordinates, compatible with all transitions.
-/

namespace EGZ.FlagDecomposition.Rechart

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f)
    (C : ∀ x, IntegerLatticeChart (Φ.liftedSupport x))

/-- The minimal ambient affine space at a node.-/
def space (x : Φ.flag.Node) : AffineSubspace (ZMod p) (FpCoord p d) :=
  affineSpan (ZMod p) {v | Φ.cumulativeWeight x v ≠ 0}

/-- The old representation expressed through an affine left inverse of the
modular chart. The definition is an affine map on the whole ambient space.-/
noncomputable def map (x : Φ.flag.Node) :
    FpCoord p d →ᵃ[ZMod p] FpCoord p (C x).rank :=
  (affineLeftInverse ((chart Φ C x).modp p)).comp (Φ.representation.map x)

/--
@isnad1 id=le.1h6v.s9.d1e24bdc3eaa from=translated src=- shape=0884b6b3 vocab=50d3de6f
-/
theorem space_mono {x y : Φ.flag.Node} (h : x ≤ y) : space Φ x ≤ space Φ y :=
  affineSpan_mono (ZMod p) (fun _ hv ↦ Φ.originalWeights.cumulative_ne_zero_of_le h hv)

/--
@isnad1 id=le.0h5v.s8.1ae0b77b9137 from=translated src=- shape=ce356323 vocab=167808df
-/
theorem space_le_original (x : Φ.flag.Node) : space Φ x ≤ Φ.representation.space x :=
  affineSpan_le.mpr (fun v hv ↦ Φ.originalWeights.cumulative_supported x v hv)

/--
@isnad1 id=mem.1h6v.s8.93f61f0c68f8 from=translated src=- shape=2e979669 vocab=232b806b
-/
theorem localWeight_supported (x : Φ.flag.Node) (v : FpCoord p d)
    (hv : Φ.localWeight x v ≠ 0) : v ∈ space Φ x := by
  apply subset_affineSpan (ZMod p)
  exact (Φ.originalWeights.cumulative_ne_zero_iff x v).mpr ⟨x, le_rfl, hv⟩

omit [Fact p.Prime] in
/--
@isnad1 id=ex.2h6v.s9.164d54027f78 from=translated src=- shape=b38003b6 vocab=0c6bbe60
-/
theorem exists_liftedSupport_of_cumulative_ne_zero (hp : Odd p)
    (x : Φ.flag.Node) (v : FpCoord p d) (hv : Φ.cumulativeWeight x v ≠ 0) :
    ∃ z ∈ Φ.liftedSupport x, z.mod p = Φ.representation.map x v := by
  let z := FpCoord.centeredLift (Φ.representation.map x v)
  refine ⟨z, (Φ.liftedSupport_spec x z).mpr ?_, FpCoord.mod_centeredLift _⟩
  exact (Φ.originalWeights.hat_ne_zero_iff x z).mpr
    ⟨FpCoord.isCenteredLift_centeredLift hp _, v, (FpCoord.mod_centeredLift _).symm, hv⟩

omit [Fact p.Prime] in
/--
@isnad1 id=ex.1h6v.s9.90765c688b73 from=translated src=- shape=403caff9 vocab=46f9d976
-/
theorem exists_cumulative_of_liftedSupport (x : Φ.flag.Node)
    (z : IntCoord (Φ.flag.rank x)) (hz : z ∈ Φ.liftedSupport x) :
    ∃ v, Φ.cumulativeWeight x v ≠ 0 ∧ Φ.representation.map x v = z.mod p := by
  obtain ⟨_, v, heq, hv⟩ := (Φ.originalWeights.hat_ne_zero_iff x z).mp
    ((Φ.liftedSupport_spec x z).mp hz)
  exact ⟨v, hv, heq⟩

omit [Fact p.Prime] in
/--
@isnad1 id=mem.2h7v.s10.d2168cd4dbcb from=translated src=- shape=859a96ae vocab=09d53bfe
-/
theorem original_map_mem_chart_range (hp : Odd p) (x : Φ.flag.Node)
    (v : FpCoord p d) (hv : Φ.cumulativeWeight x v ≠ 0) :
    Φ.representation.map x v ∈ Set.range ((chart Φ C x).modp p) := by
  obtain ⟨z, hz, hmod⟩ := exists_liftedSupport_of_cumulative_ne_zero Φ hp x v hv
  refine ⟨((C x).coordinates z).mod p, ?_⟩
  rw [(chart Φ C x).mod_integer]
  change ((C x).map ((C x).coordinates z)).mod p = Φ.representation.map x v
  rw [(C x).map_coordinates_of_mem hz]
  exact hmod

variable (hp : Odd p)
    (hinj : ∀ x, Function.Injective ((chart Φ C x).modp p))

include hp hinj

/-- Retraction through a chart recovers the original representation on the
full minimal ambient affine space.
@isnad1 id=eq.3h7v.s11.380e4f32fb0f from=translated src=- shape=84da33ab vocab=3f716a49
-/
theorem chart_map (x : Φ.flag.Node) (v : FpCoord p d) (hv : v ∈ space Φ x) :
    (chart Φ C x).modp p (map Φ C x v) = Φ.representation.map x v :=
  affineLeftInverse_retract_affineSpan _ (hinj x) (Φ.representation.map x)
    {v | Φ.cumulativeWeight x v ≠ 0}
    (fun v hv ↦ original_map_mem_chart_range Φ C hp x v hv) hv

omit hp in
/-- The new representation takes the residue of a charted support point to
its new finite-field coordinates.
@isnad1 id=eq.2h8v.s11.8ab0541be9a6 from=translated src=- shape=e14802db vocab=e140fbbd
-/
theorem map_eq_mod (x : Φ.flag.Node) (v : FpCoord p d)
    (q : IntCoord (C x).rank)
    (hv : Φ.representation.map x v = ((C x).map q).mod p) :
    map Φ C x v = q.mod p := by
  change affineLeftInverse ((chart Φ C x).modp p) (Φ.representation.map x v) = _
  rw [hv]
  change affineLeftInverse ((chart Φ C x).modp p)
    (((chart Φ C x).integer q).mod p) = _
  rw [← (chart Φ C x).mod_integer]
  exact affineLeftInverse_apply _ (hinj x) _

/-- The representation image of the old cumulative support is exactly the
reduction of the coordinate support of the lattice chart.
@isnad1 id=eq.2h6v.s10.5729a76d3d8a from=translated src=- shape=d53c5925 vocab=0b413b9b
-/
theorem image_cumulative_support (x : Φ.flag.Node) :
    map Φ C x '' {v | Φ.cumulativeWeight x v ≠ 0} =
      IntCoord.mod p '' ((C x).coordinateSupport : Set (IntCoord (C x).rank)) := by
  ext a
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨z, hz, hmod⟩ := exists_liftedSupport_of_cumulative_ne_zero Φ hp x v hv
    refine ⟨(C x).coordinates z, (C x).coordinates_mem_coordinateSupport hz, ?_⟩
    symm
    apply map_eq_mod Φ C hinj x v
    rw [(C x).map_coordinates_of_mem hz]
    exact hmod.symm
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨v, hv, heq⟩ := exists_cumulative_of_liftedSupport Φ x ((C x).map q)
      ((C x).mem_coordinateSupport.mp hq)
    exact ⟨v, hv, map_eq_mod Φ C hinj x v q heq⟩

/--
@isnad1 id=surjon.2h6v.s10.2762ac7dccfe from=translated src=- shape=2fc921a6 vocab=c7bbb7b0
-/
theorem map_surjective (x : Φ.flag.Node) :
    Set.SurjOn (map Φ C x) (space Φ x : Set (FpCoord p d)) Set.univ := by
  apply surjOn_affineSpan_of_image_span_eq_top
  rw [image_cumulative_support Φ C hp hinj x]
  exact (C x).coordinateSupport_affineIntSpans.affineSpan_mod_eq_top

/--
@isnad1 id=eq.4h8v.s11.914d9fa544ac from=translated src=- shape=1ab44429 vocab=43101430
-/
theorem map_compatible {x y : Φ.flag.Node} (h : x ≤ y)
    {v : FpCoord p d} (hv : v ∈ space Φ x) :
    map Φ C y v = (transition Φ C h).modp p (map Φ C x v) := by
  apply hinj y
  rw [chart_map Φ C hp hinj y v (space_mono Φ h hv),
    chart_transition_modp, chart_map Φ C hp hinj x v hv]
  exact Φ.representation.compatible h (space_le_original Φ x hv)

/-- The finite-field representation in minimal lattice and ambient affine
coordinates. Modular injectivity is the only chart hypothesis.-/
noncomputable def representation : FpRepresentation p d (flag Φ C) where
  space := space Φ
  map := map Φ C
  space_mono h := space_mono Φ h
  map_surjective := map_surjective Φ C hp hinj
  compatible h := map_compatible Φ C hp hinj h
  lattice_eq_standard _ _ := Iff.rfl

end EGZ.FlagDecomposition.Rechart
