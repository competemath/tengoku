import Tengoku.EgzFormalProof.EGZ.Decomposition.AugmentedCoordinates
import Tengoku.EgzFormalProof.EGZ.Decomposition.SupportDiagram
import Tengoku.EgzFormalProof.EGZ.Decomposition.FaceSelection
import Tengoku.EgzFormalProof.EGZ.Decomposition.SlabPruning

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Support diagrams with additional slab coordinates

At each node append an initial segment of a common sequence of affine
functionals to the old coordinate map. An antitone number of additional
coordinates ensures that transitions retain exactly the available prefix.
Centered lifts of cumulative atoms give a finite support diagram, even when
the augmented finite-field maps are not surjective.
-/

open Classical

namespace EGZ.FlagDecomposition.Augmented

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (e : Φ.flag.Node → ℕ)
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p)

/-- The integer lift of one ambient atom with its extra slab coordinates.-/
def lift (x : Φ.flag.Node) (v : FpCoord p d) : IntCoord (Φ.flag.rank x + e x) :=
  Fin.append (FpCoord.centeredLift (Φ.representation.map x v)) (slabCoordinates (e x) ξ v)

/--
@isnad1 id=eq.0h8v.s10.53f85c9f896e from=translated src=- shape=2b6ea91c vocab=1b0c5c08
-/
@[simp]
theorem lift_first (x : Φ.flag.Node) (v : FpCoord p d) :
    Coord.first (Φ.flag.rank x) (e x) (lift Φ e ξ x v) =
      FpCoord.centeredLift (Φ.representation.map x v) := by
  ext i
  simp [lift]

/--
@isnad1 id=eq.0h8v.s9.8e227500ea81 from=translated src=- shape=ff07f3da vocab=179c375d
-/
@[simp]
theorem lift_last (x : Φ.flag.Node) (v : FpCoord p d) :
    Coord.last (Φ.flag.rank x) (e x) (lift Φ e ξ x v) = slabCoordinates (e x) ξ v := by
  ext i
  simp [lift]

/-- The finite-field affine map augmented by the same sequence of directions.-/
def map (x : Φ.flag.Node) : FpCoord p d →ᵃ[ZMod p] FpCoord p (Φ.flag.rank x + e x) :=
  Coord.append (Φ.representation.map x) (AffineMap.pi fun i : Fin (e x) ↦ ξ i)

/--
@isnad1 id=eq.0h8v.s9.a264eeae310a from=translated src=- shape=9d05f88f vocab=4a469622
-/
@[simp]
theorem lift_mod (x : Φ.flag.Node) (v : FpCoord p d) : (lift Φ e ξ x v).mod p = map Φ e ξ x v := by
  apply Coord.ext_first_last
  · ext i
    simp [lift, map, IntCoord.mod, FpCoord.centeredLift]
  · ext i
    simp [lift, map, IntCoord.mod, slabCoordinates]

/-- The augmented support consists of lifts of the nonzero cumulative atoms.-/
noncomputable def support (x : Φ.flag.Node) : Finset (IntCoord (Φ.flag.rank x + e x)) :=
  (Finset.univ.filter fun v ↦ Φ.cumulativeWeight x v ≠ 0).image (lift Φ e ξ x)

/--
@isnad1 id=iff.0h8v.s8.f84a00b770b5 from=translated src=- shape=c6e1a965 vocab=dc6b307e
-/
@[simp]
theorem mem_support (x : Φ.flag.Node) (q : IntCoord (Φ.flag.rank x + e x)) :
    q ∈ support Φ e ξ x ↔ ∃ v, Φ.cumulativeWeight x v ≠ 0 ∧ lift Φ e ξ x v = q := by
  simp [support]

/--
@isnad1 id=nonempty.0h7v.s7.d3bc158cf9cc from=translated src=- shape=15cb41a0 vocab=a95f5723
-/
theorem support_nonempty (x : Φ.flag.Node) : (support Φ e ξ x).Nonempty := by
  obtain ⟨q, hq⟩ := Φ.liftedSupport_nonempty x
  obtain ⟨_, v, _, hv⟩ := (Φ.originalWeights.hat_ne_zero_iff x q).mp
    ((Φ.liftedSupport_spec x q).mp hq)
  exact ⟨lift Φ e ξ x v, (mem_support Φ e ξ x _).mpr ⟨v, hv, rfl⟩⟩

/-- Reducing the augmented integer support gives precisely the finite-field
image of the cumulative support.
@isnad1 id=eq.0h7v.s9.1cad39c72d52 from=translated src=- shape=ea1d5982 vocab=fc218584
-/
theorem support_mod (x : Φ.flag.Node) :
    IntCoord.mod p '' (support Φ e ξ x : Set (IntCoord (Φ.flag.rank x + e x))) =
      map Φ e ξ x '' {v | Φ.cumulativeWeight x v ≠ 0} := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨v, hv, rfl⟩ := (mem_support Φ e ξ x z).mp hz
    exact ⟨v, hv, (lift_mod Φ e ξ x v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨lift Φ e ξ x v, (mem_support Φ e ξ x _).mpr ⟨v, hv, rfl⟩,
      lift_mod Φ e ξ x v⟩

/-- Projection of the augmented support recovers the entire old lifted support.
@isnad1 id=eq.1h7v.s9.14c93c626477 from=translated src=- shape=30ee5d3c vocab=2956b694
-/
theorem first_image_support (hp : Odd p) (x : Φ.flag.Node) :
    (support Φ e ξ x).image (Coord.first (Φ.flag.rank x) (e x)) = Φ.liftedSupport x := by
  ext q
  constructor
  · rintro hq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨v, hv, rfl⟩ := (mem_support Φ e ξ x z).mp hz
    rw [lift_first]
    exact Φ.centeredLift_mem_liftedSupport hp x hv
  · intro hq
    obtain ⟨hc, v, hmap, hv⟩ := (Φ.originalWeights.hat_ne_zero_iff x q).mp
      ((Φ.liftedSupport_spec x q).mp hq)
    refine Finset.mem_image.mpr ⟨lift Φ e ξ x v,
      (mem_support Φ e ξ x _).mpr ⟨v, hv, rfl⟩, ?_⟩
    rw [lift_first, hmap, FpCoord.centeredLift_mod hc]

/-- Along an order relation keep only the upper node's prefix of directions.-/
noncomputable def transition (he : Antitone e) {x y : Φ.flag.Node} (h : x ≤ y) :
    IntegralAffineMap (Φ.flag.rank x + e x) (Φ.flag.rank y + e y) :=
  (Φ.flag.transition h).extendPrefix (e x) (e y) (he h)

/--
@isnad1 id=eq.4h9v.s8.245b82329835 from=translated src=- shape=1dc7a326 vocab=0a15782f
-/
theorem transition_lift (hp : Odd p) (he : Antitone e) {x y : Φ.flag.Node} (h : x ≤ y)
    (v : FpCoord p d) (hv : Φ.cumulativeWeight x v ≠ 0) :
    (transition Φ e he h).integer (lift Φ e ξ x v) = lift Φ e ξ y v := by
  apply Coord.ext_first_last
  · change Coord.first (Φ.flag.rank y) (e y)
        (Coord.extendPrefix (Φ.flag.transition h).toIntAffineMap (e x) (e y) (he h)
          (lift Φ e ξ x v)) = _
    rw [Coord.first_extendPrefix, lift_first, lift_first]
    exact Φ.transition_centeredLift hp h v hv
  · change Coord.last (Φ.flag.rank y) (e y)
        (Coord.extendPrefix (Φ.flag.transition h).toIntAffineMap (e x) (e y) (he h)
          (lift Φ e ξ x v)) = _
    rw [Coord.last_extendPrefix, lift_last, lift_last]
    rfl

/--
@isnad1 id=mem.4h9v.s9.e233c732c22f from=translated src=- shape=c35bf1ff vocab=12799d55
-/
theorem transition_support (hp : Odd p) (he : Antitone e) {x y : Φ.flag.Node} (h : x ≤ y)
    {q : IntCoord (Φ.flag.rank x + e x)} (hq : q ∈ support Φ e ξ x) :
    (transition Φ e he h).integer q ∈ support Φ e ξ y := by
  obtain ⟨v, hv, rfl⟩ := (mem_support Φ e ξ x q).mp hq
  rw [transition_lift Φ e ξ hp he h v hv]
  exact (mem_support Φ e ξ y _).mpr
    ⟨v, Φ.originalWeights.cumulative_ne_zero_of_le h hv, rfl⟩

/--
@isnad1 id=eq.1h6v.s7.02eebb8f9f44 from=translated src=- shape=ed1df503 vocab=694dd1b7
-/
theorem transition_refl (he : Antitone e) (x : Φ.flag.Node) :
    transition Φ e he (le_refl x) = IntegralAffineMap.id (Φ.flag.rank x + e x) := by
  unfold transition
  rw [Φ.flag.transition_refl]
  exact IntegralAffineMap.extendPrefix_id _ _

/--
@isnad1 id=eq.3h8v.s8.08f3120259e7 from=translated src=- shape=841a4d6e vocab=ae50ec7a
-/
theorem transition_trans (he : Antitone e) {x y z : Φ.flag.Node}
    (hxy : x ≤ y) (hyz : y ≤ z) :
    transition Φ e he (hxy.trans hyz) =
      (transition Φ e he hyz).comp (transition Φ e he hxy) := by
  unfold transition
  rw [Φ.flag.transition_trans]
  exact IntegralAffineMap.extendPrefix_comp _ _ (he hxy) (he hyz)

/-- The actual support diagram used before minimalizing augmented fibres.-/
noncomputable abbrev diagram (hp : Odd p) (he : Antitone e) : LatticeSupportDiagram where
  Node := Φ.flag.Node
  rank x := Φ.flag.rank x + e x
  support := support Φ e ξ
  support_nonempty := support_nonempty Φ e ξ
  transition h := transition Φ e he h
  transition_support h := transition_support Φ e ξ hp he h
  transition_refl := transition_refl Φ e he
  transition_trans := transition_trans Φ e he

/-- The old-coordinate projection maps the augmented support hull onto the
original node polytope.
@isnad1 id=eq.2h7v.s9.b11d5b1cee8b from=translated src=- shape=4c030267 vocab=ffb87c61
-/
theorem first_image_polytope (hp : Odd p) (he : Antitone e) (x : Φ.flag.Node) :
    (IntegralAffineMap.first (Φ.flag.rank x) (e x)).real ''
        ((diagram Φ e ξ hp he).polytope x).carrier = (Φ.flag.polytope x).carrier := by
  rw [(diagram Φ e ξ hp he).polytope_carrier, AffineMap.image_convexHull,
    Φ.polytope_eq_liftedSupport]
  congr 1
  ext q
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨Coord.first (Φ.flag.rank x) (e x) z, ?_, ?_⟩
    · rw [← first_image_support Φ e ξ hp x]
      exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
    · rfl
  · rintro ⟨z, hz, rfl⟩
    rw [← first_image_support Φ e ξ hp x] at hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨IntCoord.real q, ⟨q, hq, rfl⟩, rfl⟩

/-- The augmented affine maps commute with the augmented transitions on the
old represented affine spaces.
@isnad1 id=eq.3h9v.s11.dbe27847f40b from=translated src=- shape=027fa565 vocab=bf4cad45
-/
theorem map_compatible (he : Antitone e) {x y : Φ.flag.Node} (h : x ≤ y)
    {v : FpCoord p d} (hv : v ∈ Φ.representation.space x) :
    map Φ e ξ y v = (transition Φ e he h).modp p (map Φ e ξ x v) := by
  apply Coord.ext_first_last
  · change Coord.first (Φ.flag.rank y) (e y) (map Φ e ξ y v) =
      Coord.first (Φ.flag.rank y) (e y)
        (Coord.extendPrefix ((Φ.flag.transition h).modp p) (e x) (e y) (he h) (map Φ e ξ x v))
    simp only [map, Coord.first_append, Coord.first_extendPrefix]
    exact Φ.representation.compatible h hv
  · change Coord.last (Φ.flag.rank y) (e y) (map Φ e ξ y v) =
      Coord.last (Φ.flag.rank y) (e y)
        (Coord.extendPrefix ((Φ.flag.transition h).modp p) (e x) (e y) (he h) (map Φ e ξ x v))
    simp only [map, Coord.last_append, Coord.last_extendPrefix]
    rfl

/-- Forgetting the slab coordinates commutes with diagram transitions.
@isnad1 id=eq.2h7v.s8.f161cb8f857b from=translated src=- shape=eea551a9 vocab=8961bcc8
-/
theorem first_comp_transition (he : Antitone e) {x y : Φ.flag.Node} (h : x ≤ y) :
    (IntegralAffineMap.first (Φ.flag.rank y) (e y)).comp (transition Φ e he h) =
      (Φ.flag.transition h).comp (IntegralAffineMap.first (Φ.flag.rank x) (e x)) :=
  IntegralAffineMap.first_comp_extendPrefix _ _ _ (he h)

/--
@isnad1 id=iscenter.1h8v.s7.670a058749b3 from=translated src=- shape=75bcaf4a vocab=4a48b05a
-/
theorem lift_centered (hp : Odd p) (x : Φ.flag.Node) (v : FpCoord p d) :
    IsCenteredLift p (lift Φ e ξ x v) := by
  apply latticeSupNorm_le_of_first_last
  · rw [lift_first]
    exact FpCoord.isCenteredLift_centeredLift hp _
  · rw [lift_last]
    exact FpCoord.isCenteredLift_centeredLift hp (fun i : Fin (e x) ↦ ξ i v)

/--
@isnad1 id=iscenter.2h8v.s8.f7d8ef4a7191 from=translated src=- shape=29ec3a71 vocab=4ea3615a
-/
theorem support_centered (hp : Odd p) (x : Φ.flag.Node)
    (q : IntCoord (Φ.flag.rank x + e x)) (hq : q ∈ support Φ e ξ x) : IsCenteredLift p q := by
  obtain ⟨v, _, rfl⟩ := (mem_support Φ e ξ x q).mp hq
  exact lift_centered Φ e ξ hp x v

/-- Bounds for the old support and slab block give a uniform bound for every
augmented support point.
@isnad1 id=le.4h10v.s8.c5331d09fe4a from=translated src=- shape=d899f1eb vocab=27153670
-/
theorem support_bound (hp : Odd p) {K L : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K)
    (hL : ∀ x v, Φ.cumulativeWeight x v ≠ 0 → latticeSupNorm (slabCoordinates (e x) ξ v) ≤ L x)
    (x : Φ.flag.Node) (q : IntCoord (Φ.flag.rank x + e x)) (hq : q ∈ support Φ e ξ x) :
    latticeSupNorm q ≤ max (K x) (L x) := by
  obtain ⟨v, hv, rfl⟩ := (mem_support Φ e ξ x q).mp hq
  apply latticeSupNorm_le_of_first_last
  · rw [lift_first]
    apply (le_max_left _ _).trans'
    apply hK
    rw [Φ.polytope_eq_liftedSupport]
    exact subset_convexHull ℝ _
      ⟨_, Φ.centeredLift_mem_liftedSupport hp x hv, rfl⟩
  · rw [lift_last]
    exact (hL x v hv).trans (le_max_right _ _)

end EGZ.FlagDecomposition.Augmented
