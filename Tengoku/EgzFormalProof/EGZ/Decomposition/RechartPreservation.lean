import Tengoku.EgzFormalProof.EGZ.Decomposition.RechartDecomposition
import Tengoku.EgzFormalProof.EGZ.Decomposition.FacePreservation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Properties preserved by changing lattice coordinates

The chart and its affine left inverse identify the node polytopes and their
proper points.  These maps preserve reducedness, realized faces, and
completeness of individual elements.
-/

namespace EGZ.FlagDecomposition.Rechart

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f)
    (C : ∀ x, IntegerLatticeChart (Φ.liftedSupport x))

/-- An affine inverse of the real chart, extended to the old ambient space.-/
noncomputable def inverseChart (x : Φ.flag.Node) :
    RealCoord (Φ.flag.rank x) →ᵃ[ℝ] RealCoord (C x).rank :=
  affineLeftInverse (chart Φ C x).real

/--
@isnad1 id=eq.0h7v.s10.4adcba57ed94 from=translated src=- shape=657d86ff vocab=021fbaad
-/
@[simp]
theorem inverseChart_chart (x : Φ.flag.Node) (q : RealCoord (C x).rank) :
    inverseChart Φ C x ((chart Φ C x).real q) = q :=
  affineLeftInverse_apply _ (chart_real_injective Φ C x) q

/--
@isnad1 id=eq.1h7v.s10.39d39eb37790 from=translated src=- shape=4bcebd44 vocab=67073f8a
-/
theorem chart_inverseChart (x : Φ.flag.Node) (q : RealCoord (Φ.flag.rank x))
    (hq : q ∈ (Φ.flag.polytope x).carrier) :
    (chart Φ C x).real (inverseChart Φ C x q) = q := by
  apply affineLeftInverse_retract _ (chart_real_injective Φ C x)
  rw [← chart_image_polytope Φ C x] at hq
  obtain ⟨r, _, rfl⟩ := hq
  exact ⟨r, rfl⟩

/--
@isnad1 id=mapsto.0h6v.s9.67da415a168a from=translated src=- shape=c12cbac6 vocab=d18bf008
-/
theorem inverseChart_mem_polytope (x : Φ.flag.Node) :
    Set.MapsTo (inverseChart Φ C x) (Φ.flag.polytope x).carrier (polytope Φ C x).carrier := by
  intro q hq
  apply (chart_mem_polytope_iff Φ C x _).mp
  rw [chart_inverseChart Φ C x q hq]
  exact hq

/--
@isnad1 id=mapsto.0h6v.s9.e6fcef527b6c from=translated src=- shape=e7e1a8bb vocab=efa387a1
-/
theorem chart_mem_polytope (x : Φ.flag.Node) :
    Set.MapsTo (chart Φ C x).real (polytope Φ C x).carrier (Φ.flag.polytope x).carrier :=
  fun _ hq ↦ (chart_mem_polytope_iff Φ C x _).mpr hq

/-- Inverse charts commute with transitions on the old source polytope.
@isnad1 id=eq.2h8v.s11.0471587e49b1 from=translated src=- shape=206c7512 vocab=1042c802
-/
theorem inverseChart_transition {x y : Φ.flag.Node} (h : x ≤ y)
    (q : RealCoord (Φ.flag.rank x)) (hq : q ∈ (Φ.flag.polytope x).carrier) :
    inverseChart Φ C y ((Φ.flag.transition h).real q) =
      (transition Φ C h).real (inverseChart Φ C x q) := by
  apply chart_real_injective Φ C y
  rw [chart_inverseChart Φ C y _ (Φ.flag.transition_mem h hq), chart_transition_real,
    chart_inverseChart Φ C x q hq]

/-- Map a point in the new coordinates to its original flag point.-/
noncomputable def forwardPoint (q : (flag Φ C).Point) : Φ.flag.Point :=
  q.map (SupHom.id _) (fun x ↦ (chart Φ C x).real) (chart_mem_polytope Φ C)

/-- Express an original flag point in the new coordinates.-/
noncomputable def inversePoint (q : Φ.flag.Point) : (flag Φ C).Point :=
  q.map (SupHom.id _) (inverseChart Φ C) (inverseChart_mem_polytope Φ C)

/--
@isnad1 id=eq.0h6v.s6.c0d2bdfba089 from=translated src=- shape=6afdea5a vocab=38710d7a
-/
@[simp]
theorem inversePoint_forwardPoint (q : (flag Φ C).Point) :
    inversePoint Φ C (forwardPoint Φ C q) = q := by
  cases q with
  | mk x v hv =>
    change (⟨x, inverseChart Φ C x ((chart Φ C x).real v), _⟩ : (flag Φ C).Point) = ⟨x, v, hv⟩
    congr 1
    exact inverseChart_chart Φ C x v

/--
@isnad1 id=eq.0h6v.s6.8906aa78f2f5 from=translated src=- shape=b190f915 vocab=cc986317
-/
@[simp]
theorem forwardPoint_inversePoint (q : Φ.flag.Point) :
    forwardPoint Φ C (inversePoint Φ C q) = q := by
  cases q with
  | mk x v hv =>
    change (⟨x, (chart Φ C x).real (inverseChart Φ C x v), _⟩ : Φ.flag.Point) = ⟨x, v, hv⟩
    congr 1
    exact chart_inverseChart Φ C x v hv

variable [Fact p.Prime] (hp : Odd p)
    (hinj : ∀ x, Function.Injective ((chart Φ C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

include hp hinj hcenter

/--
@isnad1 id=mem.4h6v.s10.e36e02f246d6 from=translated src=- shape=52b72605 vocab=f08efbda
-/
theorem forwardPoint_mem_omegaZero {q : (flag Φ C).Point}
    (hq : q ∈ (decomposition Φ C hp hinj hcenter).omegaZero) :
    forwardPoint Φ C q ∈ Φ.omegaZero := by
  obtain ⟨z, hz, hw⟩ := hq
  refine ⟨(C q.base).map z, ?_, ?_⟩
  · change ((C q.base).map z).real = (chart Φ C q.base).real q.val
    rw [← hz, (chart Φ C q.base).real_integer]
    rfl
  · change (decomposition Φ C hp hinj hcenter).localLift q.base z ≠ 0 at hw
    rwa [decomposition_localLift] at hw

/--
@isnad1 id=mem.4h6v.s10.071d02f370a3 from=translated src=- shape=ebb36155 vocab=308af972
-/
theorem inversePoint_mem_omegaZero {q : Φ.flag.Point} (hq : q ∈ Φ.omegaZero) :
    inversePoint Φ C q ∈ (decomposition Φ C hp hinj hcenter).omegaZero := by
  obtain ⟨z, hz, hw⟩ := hq
  have hw' : Φ.localLift q.base z ≠ 0 := hw
  have hzS : z ∈ Φ.liftedSupport q.base :=
    (Φ.liftedSupport_spec q.base z).mpr
      (ne_of_gt ((Nat.pos_of_ne_zero hw').trans_le (Φ.localLift_le_hat q.base z)))
  have hcoords := (C q.base).map_coordinates_of_mem hzS
  refine ⟨(C q.base).coordinates z, ?_, ?_⟩
  · change ((C q.base).coordinates z).real = inverseChart Φ C q.base q.val
    have hreal : (chart Φ C q.base).real ((C q.base).coordinates z).real = z.real := by
      rw [(chart Φ C q.base).real_integer]
      exact congrArg IntCoord.real hcoords
    rw [← hz, ← hreal, inverseChart_chart]
  · change (decomposition Φ C hp hinj hcenter).localLift q.base ((C q.base).coordinates z) ≠ 0
    rw [decomposition_localLift, hcoords]
    exact hw'

/-- Forward charts preserve the full proper-point set.
@isnad1 id=mem.4h6v.s10.2d5be94d4268 from=translated src=- shape=52b72605 vocab=d2ed0007
-/
theorem forwardPoint_mem_omega {q : (flag Φ C).Point}
    (hq : q ∈ (decomposition Φ C hp hinj hcenter).omega) :
    forwardPoint Φ C q ∈ Φ.omega := by
  obtain ⟨n, points, weight, hpoints, hcomb⟩ := hq
  refine ⟨n, fun i ↦ forwardPoint Φ C (points i), weight,
    fun i ↦ forwardPoint_mem_omegaZero Φ C hp hinj hcenter (hpoints i), ?_⟩
  exact hcomb.map (F := flag Φ C) (G := Φ.flag) (SupHom.id _) (fun x ↦ (chart Φ C x).real)
    (chart_mem_polytope Φ C) (chart_transition_real Φ C)

/-- The inverse charts preserve proper points even though their transition
commutation is only required on the polytopes.
@isnad1 id=mem.4h6v.s10.7423b73e513e from=translated src=- shape=ebb36155 vocab=9516a0bc
-/
theorem inversePoint_mem_omega {q : Φ.flag.Point} (hq : q ∈ Φ.omega) :
    inversePoint Φ C q ∈ (decomposition Φ C hp hinj hcenter).omega := by
  obtain ⟨n, points, weight, hpoints, hcomb⟩ := hq
  refine ⟨n, fun i ↦ inversePoint Φ C (points i), weight,
    fun i ↦ inversePoint_mem_omegaZero Φ C hp hinj hcenter (hpoints i), ?_⟩
  exact hcomb.map_on_polytope (F := Φ.flag) (G := flag Φ C) (SupHom.id _) (inverseChart Φ C)
    (inverseChart_mem_polytope Φ C) (inverseChart_transition Φ C)

/-- The new decomposition is a subdivision of the old one through its
coordinate charts.-/
noncomputable def subdivisionMap :
    SubdivisionMap Φ (decomposition Φ C hp hinj hcenter) :=
  SubdivisionMap.of_local_generators (SupHom.id _) (fun x ↦ (chart Φ C x).real)
    (chart_mem_polytope Φ C) (chart_transition_real Φ C)
    (fun _ hq ↦ forwardPoint_mem_omegaZero Φ C hp hinj hcenter hq)

/-- Recharting preserves every base occurring among the proper points.
@isnad1 id=isreduce.4h5v.s10.f70e1ce570e3 from=translated src=- shape=0b32c0fd vocab=4de2a57a
-/
theorem decomposition_isReduced (hΦ : Φ.IsReduced) :
    (decomposition Φ C hp hinj hcenter).IsReduced := by
  intro x
  obtain ⟨q, hq, hbase⟩ := hΦ x
  exact ⟨inversePoint Φ C q, inversePoint_mem_omega Φ C hp hinj hcenter hq, hbase⟩

/--
@isnad1 id=iff.3h5v.s10.c51311bea380 from=translated src=- shape=f0adf032 vocab=4de2a57a
-/
theorem decomposition_isReduced_iff :
    (decomposition Φ C hp hinj hcenter).IsReduced ↔ Φ.IsReduced := by
  constructor
  · intro hnew x
    obtain ⟨q, hq, hbase⟩ := hnew x
    exact ⟨forwardPoint Φ C q, forwardPoint_mem_omega Φ C hp hinj hcenter hq, hbase⟩
  · exact decomposition_isReduced Φ C hp hinj hcenter

omit hp hinj hcenter [Fact p.Prime] in
/-- Every old face has a nonempty pullback under a chart.
@isnad1 id=nonempty.0h7v.s9.24fdc956a646 from=translated src=- shape=83f28624 vocab=038a587e
-/
theorem face_preimage_nonempty (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face) :
    ((polytope Φ C x).carrier ∩ (chart Φ C x).real ⁻¹' Γ.carrier).Nonempty := by
  obtain ⟨q, hq⟩ := Γ.nonempty
  refine ⟨inverseChart Φ C x q, inverseChart_mem_polytope Φ C x (Γ.subset_polytope hq), ?_⟩
  change (chart Φ C x).real (inverseChart Φ C x q) ∈ Γ.carrier
  rw [chart_inverseChart Φ C x q (Γ.subset_polytope hq)]
  exact hq

/-- Every previously realized face is still realized in the new coordinates.
@isnad1 id=isrealiz.4h7v.s10.09cef14a1c65 from=translated src=- shape=e3b90f90 vocab=abfba503
-/
theorem decomposition_isRealizedFace (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face)
    (hΓ : Φ.IsRealizedFace x Γ) :
    (decomposition Φ C hp hinj hcenter).IsRealizedFace x
      ((subdivisionMap Φ C hp hinj hcenter).face x Γ (face_preimage_nonempty Φ C x Γ)) :=
  (subdivisionMap Φ C hp hinj hcenter).isRealizedFace x Γ
    (face_preimage_nonempty Φ C x Γ) hΓ

omit hcenter in
/-- A functional varying on new representation fibres already varies on
old representation fibres.
@isnad1 id=nonconst.3h7v.s10.b5a92ff27d05 from=translated src=- shape=87bdd277 vocab=3d6f8b48
-/
theorem nonconstantOnFibers_original (x : Φ.flag.Node)
    (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p)
    (hξ : (representation Φ C hp hinj).NonconstantOnFibers x ξ) :
    Φ.representation.NonconstantOnFibers x ξ := by
  obtain ⟨v, w, hv, hw, hmap, hne⟩ := hξ
  refine ⟨v, w, space_le_original Φ x hv, space_le_original Φ x hw, ?_, hne⟩
  change map Φ C x v = map Φ C x w at hmap
  calc
    Φ.representation.map x v = (chart Φ C x).modp p (map Φ C x v) :=
      (chart_map Φ C hp hinj x v hv).symm
    _ = (chart Φ C x).modp p (map Φ C x w) := congrArg _ hmap
    _ = Φ.representation.map x w := chart_map Φ C hp hinj x w hw

/-- Element completeness is preserved with exactly the same thresholds.
@isnad1 id=iscomple.4h8v.s10.d5e5398a7373 from=translated src=- shape=24e6d3b7 vocab=634b269a
-/
theorem decomposition_isCompleteElement (x : Φ.flag.Node) (t : ℕ) (δ : ℝ)
    (hcomplete : Φ.IsCompleteElement x t δ) :
    (decomposition Φ C hp hinj hcenter).IsCompleteElement x t δ := by
  intro ξ hξ
  exact hcomplete ξ (nonconstantOnFibers_original Φ C hp hinj x ξ hξ)

end EGZ.FlagDecomposition.Rechart
