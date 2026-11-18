import Tengoku.EgzFormalProof.EGZ.Main.Centerpoint
import Tengoku.EgzFormalProof.EGZ.Main.Interior
import Tengoku.EgzFormalProof.EGZ.BalancedCombination
import Tengoku.EgzFormalProof.EGZ.Decomposition.LatticeCoordinates
import Tengoku.EgzFormalProof.EGZ.Decomposition.FaceMassChain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The selected cumulative lattice configuration

These bridges package an integral interior centerpoint and the cumulative
lift at its base in the finite integer-coordinate language used by balanced
combinations. The bounds retain the selected node's own radius.
-/

open scoped BigOperators
open Classical

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f)

/--
@isnad1 id=ex.1h5v.s6.c757a61fced7 from=translated src=- shape=01cb9a8c vocab=6271aa8c
-/
theorem integralPoint_coordinates (q : Φ.flag.Point) (hq : q.IsIntegral) :
    ∃ c : IntCoord (Φ.flag.rank q.base), c.real = q.val :=
  (Φ.representation.lattice_eq_standard _ _).mp hq

/--
@isnad1 id=mem.1h6v.s9.0d773675ffff from=translated src=- shape=4e8a76a2 vocab=ae142545
-/
theorem integer_mem_affineSpan_liftedSupport (hmin : Φ.IsMinimal)
    (x : Φ.flag.Node) (c : IntCoord (Φ.flag.rank x)) :
    c ∈ affineSpan ℤ (↑(Φ.liftedSupport x) : Set (IntCoord (Φ.flag.rank x))) := by
  rw [(affineIntSpans_iff_affineSpan_eq_top _).mp (hmin x).2]
  exact AffineSubspace.mem_top _ _ _

/--
@isnad1 id=le.2h7v.s7.a13228d5d990 from=translated src=- shape=43bd062c vocab=dd7b8ccb
-/
theorem liftedSupport_bound {K : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K)
    (x : Φ.flag.Node) : ∀ z ∈ Φ.liftedSupport x, latticeSupNorm z ≤ K x := by
  intro z hz
  apply hK x z
  rw [Φ.polytope_eq_liftedSupport]
  exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩

/--
@isnad1 id=le.1h6v.s6.a428d9266658 from=translated src=- shape=1c9cd83e vocab=7241d192
-/
theorem liftedSupport_subset_latticeBox {K : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K)
    (x : Φ.flag.Node) : Φ.liftedSupport x ⊆ latticeBox (Φ.flag.rank x) (K x) := by
  intro z hz
  exact mem_latticeBox.mpr (Φ.liftedSupport_bound hK x z hz)

/--
@isnad1 id=le.2h7v.s7.29381c6fede2 from=translated src=- shape=8bd2e52b vocab=ce604a45
-/
theorem integralPoint_bound {K : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K)
    (q : Φ.flag.Point) (c : IntCoord (Φ.flag.rank q.base)) (hc : c.real = q.val) :
    latticeSupNorm c ≤ K q.base := hK q.base c (hc.symm ▸ q.val_mem)

/--
@isnad1 id=eq.1h5v.s8.9b5a9cb44511 from=translated src=- shape=f1e8616e vocab=915a6bdb
-/
theorem cumulativeSupport_sum (hodd : Odd p) (x : Φ.flag.Node) :
    (∑ q : Φ.liftedSupport x, Φ.hat x q) = natMass (Φ.cumulativeWeight x) := by
  simpa only [Finset.sum_coe_sort] using Φ.sum_liftedSupport hodd x

/-- The cumulative mass profile at an interior lattice center, in the
balanced-combination interface.-/
noncomputable def cumulativeBalancedData (hmin : Φ.IsMinimal) (x : Φ.flag.Node)
    (c : IntCoord (Φ.flag.rank x))
    (hc : c.real ∈ intrinsicInterior ℝ (Φ.flag.polytope x).carrier) :
    BalancedCombination.Data (Φ.flag.rank x) where
  support := Φ.liftedSupport x
  support_nonempty := Φ.liftedSupport_nonempty x
  weight q := Φ.hat x q
  weight_pos q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ((Φ.liftedSupport_spec x q).mp q.2))
  center := c
  center_mem_span := Φ.integer_mem_affineSpan_liftedSupport hmin x c
  center_mem_interior := by rwa [← Φ.polytope_eq_liftedSupport]

/-- Centrality normalized by the selected cumulative mass.-/
noncomputable def cumulativeCentrality (x : Φ.flag.Node) : ℝ :=
  (Φ.retainedMass : ℝ) /
    ((hollowConstant p d : ℝ) * (natMass (Φ.cumulativeWeight x) : ℝ))

/--
@isnad1 id=eq.1h5v.s6.26ff9b5ab66f from=translated src=- shape=345a2864 vocab=f6bc5120
-/
theorem cumulativeCentrality_mul_mass (hodd : Odd p) (x : Φ.flag.Node) :
    Φ.cumulativeCentrality x * (natMass (Φ.cumulativeWeight x) : ℝ) =
      (Φ.retainedMass : ℝ) / (hollowConstant p d : ℝ) := by
  have hm : (natMass (Φ.cumulativeWeight x) : ℝ) ≠ 0 := by
    exact_mod_cast (Φ.cumulativeMass_pos hodd x).ne'
  unfold cumulativeCentrality
  rw [div_mul_eq_div_mul_one_div, mul_assoc, one_div, inv_mul_cancel₀ hm, mul_one]

/--
@isnad1 id=lt.2h5v.s6.c6735dfe71ee from=translated src=- shape=5a9b3355 vocab=a93be284
-/
theorem cumulativeCentrality_pos (hodd : Odd p) (hw : 0 < hollowConstant p d)
    (x : Φ.flag.Node) : 0 < Φ.cumulativeCentrality x := by
  unfold cumulativeCentrality
  exact div_pos (by exact_mod_cast Φ.retainedMass_pos hodd)
    (mul_pos (by exact_mod_cast hw) (by exact_mod_cast Φ.cumulativeMass_pos hodd x))

/--
@isnad1 id=le.1h5v.s5.c286255f9793 from=translated src=- shape=1c3475e4 vocab=80506ad1
-/
theorem inv_hollowConstant_le_cumulativeCentrality (hodd : Odd p) (x : Φ.flag.Node) :
    (hollowConstant p d : ℝ)⁻¹ ≤ Φ.cumulativeCentrality x := by
  have hm : 0 < (natMass (Φ.cumulativeWeight x) : ℝ) := by
    exact_mod_cast Φ.cumulativeMass_pos hodd x
  apply (mul_le_mul_iff_left₀ hm).mp
  rw [Φ.cumulativeCentrality_mul_mass hodd]
  have hmass : (natMass (Φ.cumulativeWeight x) : ℝ) ≤ Φ.retainedMass := by
    exact_mod_cast Φ.cumulativeMass_le_retainedMass x
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_right hmass (inv_nonneg.mpr (Nat.cast_nonneg (hollowConstant p d)))

/--
@isnad1 id=iscentra.4h6v.s10.29ceffd51efe from=translated src=- shape=50b5db26 vocab=42434ab4
-/
theorem cumulativeBalancedData_isCentral (hodd : Odd p) (hmin : Φ.IsMinimal)
    (x : Φ.flag.Node) (c : IntCoord (Φ.flag.rank x))
    (hc : c.real ∈ intrinsicInterior ℝ (Φ.flag.polytope x).carrier)
    (hcentral : ∀ ξ : RealCoord (Φ.flag.rank x) →ᵃ[ℝ] ℝ,
      (Φ.retainedMass : ℝ) / (hollowConstant p d : ℝ) ≤
        (Φ.liftedMassOn x {z | ξ c.real ≤ ξ z} : ℝ)) :
    BalancedCombination.IsCentral (Φ.cumulativeBalancedData hmin x c hc).support
      (Φ.cumulativeBalancedData hmin x c hc).weight (Φ.cumulativeCentrality x) c.real := by
  intro ξ
  change Φ.cumulativeCentrality x * (∑ q : Φ.liftedSupport x, (Φ.hat x q : ℝ)) ≤ _
  have hsum : (∑ q : Φ.liftedSupport x, (Φ.hat x q : ℝ)) =
      (natMass (Φ.cumulativeWeight x) : ℝ) := by exact_mod_cast Φ.cumulativeSupport_sum hodd x
  rw [hsum, Φ.cumulativeCentrality_mul_mass hodd]
  have hm : (Φ.liftedMassOn x {z | ξ c.real ≤ ξ z} : ℝ) =
      ∑ q : Φ.liftedSupport x, if ξ c.real ≤ ξ q.val.real then (Φ.hat x q : ℝ) else 0 := by
    simp only [liftedMassOn, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Set.mem_ofPred_eq]
    exact (Finset.sum_coe_sort (Φ.liftedSupport x)
      (fun z ↦ if ξ c.real ≤ ξ z.real then (Φ.hat x z : ℝ) else 0)).symm
  exact (hcentral ξ).trans_eq hm

/-- The concrete cumulative fibre selected for the balanced-combination
and relative-expansion arguments. All bounds use its own node radius.-/
structure CumulativeSelection (T K : Φ.flag.Node → ℕ) (δ : ℝ) where
  node : Φ.flag.Node
  center : IntCoord (Φ.flag.rank node)
  center_mem_span : center ∈ affineSpan ℤ
    (↑(Φ.liftedSupport node) : Set (IntCoord (Φ.flag.rank node)))
  center_mem_interior : center.real ∈ intrinsicInterior ℝ
    (convexHull ℝ (IntCoord.real '' (↑(Φ.liftedSupport node) : Set (IntCoord (Φ.flag.rank node)))))
  center_mem_box : center ∈ latticeBox (Φ.flag.rank node) (K node)
  support_subset_box : Φ.liftedSupport node ⊆ latticeBox (Φ.flag.rank node) (K node)
  complete : Φ.IsCompleteElement node (T node) δ
  central : BalancedCombination.IsCentral (Φ.liftedSupport node)
    (fun q ↦ (Φ.hat node q : ℝ)) (Φ.cumulativeCentrality node) center.real
  centrality_pos : 0 < Φ.cumulativeCentrality node

namespace CumulativeSelection

variable {Φ} {T K : Φ.flag.Node → ℕ} {δ : ℝ}

noncomputable def data (D : Φ.CumulativeSelection T K δ) :
    BalancedCombination.Data (Φ.flag.rank D.node) where
  support := Φ.liftedSupport D.node
  support_nonempty := Φ.liftedSupport_nonempty D.node
  weight q := Φ.hat D.node q
  weight_pos q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ((Φ.liftedSupport_spec _ _).mp q.2))
  center := D.center
  center_mem_span := D.center_mem_span
  center_mem_interior := D.center_mem_interior

/--
@isnad1 id=le.0h8v.s6.0c4eb2fdf5c1 from=translated src=- shape=39683040 vocab=c5ee9091
-/
theorem centrality_le_one (D : Φ.CumulativeSelection T K δ) :
    Φ.cumulativeCentrality D.node ≤ 1 := D.data.centrality_le_one D.central

/--
@isnad1 id=lt.1h8v.s9.040d9568b628 from=translated src=- shape=ac81d072 vocab=4945cb2b
-/
theorem mass_pos (D : Φ.CumulativeSelection T K δ) (hodd : Odd p) :
    0 < ∑ q : Φ.liftedSupport D.node, (Φ.hat D.node q : ℝ) := by
  exact_mod_cast (Φ.cumulativeSupport_sum hodd D.node).symm ▸ Φ.cumulativeMass_pos hodd D.node

/--
@isnad1 id=le.1h8v.s9.96a348cf8cb9 from=translated src=- shape=1f6a3c15 vocab=66853bd9
-/
theorem mass_le_retained (D : Φ.CumulativeSelection T K δ) (hodd : Odd p) :
    (∑ q : Φ.liftedSupport D.node, (Φ.hat D.node q : ℝ)) ≤ Φ.retainedMass := by
  have h := (Φ.cumulativeSupport_sum hodd D.node).le.trans
    (Φ.cumulativeMass_le_retainedMass D.node)
  exact_mod_cast h

/--
@isnad1 id=eq.1h8v.s9.d98d99e387b7 from=translated src=- shape=ee770040 vocab=c595f00a
-/
theorem centrality_mul_mass (D : Φ.CumulativeSelection T K δ) (hodd : Odd p) :
    Φ.cumulativeCentrality D.node *
      (∑ q : Φ.liftedSupport D.node, (Φ.hat D.node q : ℝ)) =
        (Φ.retainedMass : ℝ) / (hollowConstant p d : ℝ) := by
  have hsum : (∑ q : Φ.liftedSupport D.node, (Φ.hat D.node q : ℝ)) =
      (natMass (Φ.cumulativeWeight D.node) : ℝ) := by
    exact_mod_cast Φ.cumulativeSupport_sum hodd D.node
  rw [hsum]
  exact Φ.cumulativeCentrality_mul_mass hodd D.node

end CumulativeSelection

/-- Completeness and the flag centerpoint theorem select a full-dimensional
interior lattice center in an element complete at the requested scale.
@isnad1 id=nonempty.6h8v.s6.14b41f254b73 from=translated src=- shape=cf8d8cdf vocab=b17abd78
-/
theorem select_cumulative_node (hp : p.Prime) (hodd : Odd p)
    {ε δ : ℝ} {T K : Φ.flag.Node → ℕ} (hε : 0 ≤ ε)
    (hεW : ε ≤ (hollowConstant p d : ℝ)⁻¹)
    (hcomplete : Φ.IsComplete T ε δ) (hK : Φ.IsKBounded K) :
    Nonempty (Φ.CumulativeSelection T K δ) := by
  obtain ⟨q, hq, hint, hcentral⟩ := Φ.exists_cumulative_centerpoint hp hodd
  obtain ⟨c, hc⟩ := Φ.integralPoint_coordinates q hint
  have hcentralε : ∀ ξ : RealCoord (Φ.flag.rank q.base) →ᵃ[ℝ] ℝ,
      ε * (Φ.retainedMass : ℝ) ≤ (Φ.liftedMassOn q.base {z | ξ q.val ≤ ξ z} : ℝ) := by
    intro ξ
    apply (mul_le_mul_of_nonneg_right hεW (Nat.cast_nonneg Φ.retainedMass)).trans
    simpa only [div_eq_mul_inv, mul_comm] using hcentral ξ
  have hlarge := Φ.isLargeElement_of_halfspace_lower hodd q hcentralε
  have hinterior := Φ.centerpoint_mem_interior hodd q hq hε hcentralε
    (hcomplete.2.2.2 q.base)
  have hcint : c.real ∈ intrinsicInterior ℝ (Φ.flag.polytope q.base).carrier :=
    hc.symm ▸ hinterior
  have hW : 0 < hollowConstant p d :=
    (ConvexFlag.hellyConstant_pos hq hint).trans_le (Φ.propositionSevenOne hp)
  refine ⟨{
    node := q.base
    center := c
    center_mem_span := Φ.integer_mem_affineSpan_liftedSupport hcomplete.1 q.base c
    center_mem_interior := by rwa [← Φ.polytope_eq_liftedSupport]
    center_mem_box := mem_latticeBox.mpr (Φ.integralPoint_bound hK q c hc)
    support_subset_box := Φ.liftedSupport_subset_latticeBox hK q.base
    complete := hcomplete.2.2.1 q.base hlarge
    central := ?_
    centrality_pos := Φ.cumulativeCentrality_pos hodd hW q.base }⟩
  apply Φ.cumulativeBalancedData_isCentral hodd hcomplete.1 q.base c hcint
  intro ξ
  simpa only [hc] using hcentral ξ

end EGZ.FlagDecomposition
