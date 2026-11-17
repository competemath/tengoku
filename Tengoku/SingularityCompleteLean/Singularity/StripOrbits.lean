import Tengoku.SingularityCompleteLean.Singularity.PeriodicStrip
import Tengoku.Seed.Data.Fintype.EquivFin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual cyclic coordinates on discrete-group strip vertices

The canonical height-band representatives are finite by proper discontinuity.
Their cyclic orbits are disjoint and exhaust all vertices in the coordinate
strip. Thus the enumeration required by the Green compression is constructed
from an actual discrete subgroup and a normalized hyperbolic element.
-/

noncomputable section
open Set
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) (a : Γ) {τ : ℝ}
  (ha : (a : SL(2, ℝ)) = dilationMatrix τ)

include ha

/-- The subgroup action of a cyclic power agrees with the diagonal action.
@isnad1 id=eq.1h5v.s11.55308fde8697 from=translated src=- shape=33b9ea5f vocab=cd629934
-/
theorem subgroup_dilation_zpow_smul (n : ℤ) (z : ℍ) :
    a ^ n • z = dilationMatrix τ ^ n • z := by
  change ((a ^ n : Γ) : SL(2, ℝ)) • z = _
  rw [Subgroup.coe_zpow, ha]

/-- A nontrivial normalized diagonal element has infinite order in the subgroup.
@isnad1 id=not.2h3v.s10.edd00028398c from=translated src=- shape=77247524 vocab=17855a85
-/
theorem subgroup_dilation_infinite_order (hτ : τ ≠ 0) : ¬IsOfFinOrder a := by
  apply injective_zpow_iff_not_isOfFinOrder.mp
  intro n m h
  have he := congrArg (fun g : Γ => (g : SL(2, ℝ))) h
  simp only [Subgroup.coe_zpow, ha] at he
  exact injective_zpow_iff_not_isOfFinOrder.mpr (dilationMatrix_infinite_order hτ) he

/-- Canonical representatives belong to distinct cyclic orbits of group vertices.
@isnad1 id=eq.3h8v.s12.f01c4ab6b226 from=translated src=- shape=7b777323 vocab=7cf7e65a
-/
theorem stripRepresentatives_disjoint (hτ : 0 < τ) (z : ℍ) (R : ℝ)
    (j k : stripRepresentatives Γ z R τ) (n : ℤ)
    (he : a ^ n * (j : Γ) = (k : Γ)) : j = k := by
  have hp : dilationMatrix τ ^ n • ((j : Γ) • z) = (k : Γ) • z := by
    rw [← subgroup_dilation_zpow_smul Γ a ha, ← mul_smul, he]
  have hn := dilationMatrix_height_band_unique hτ ((j : Γ) • z) j.property.2.1 j.property.2.2 n
    (by rw [hp]; exact k.property.2.1) (by rw [hp]; exact k.property.2.2)
  subst n
  apply Subtype.ext
  simpa using he

/-- Every strip vertex belongs to a canonical representative's cyclic orbit.
@isnad1 id=eq.2h5v.s12.b622a8cf0602 from=translated src=- shape=057b0b9d vocab=ef57a000
-/
theorem stripVertices_eq_cyclicOrbitUnion (hτ : 0 < τ) (z : ℍ) (R : ℝ) :
    {g : Γ | g • z ∈ axisRatioStrip R} =
      cyclicOrbitUnion a (fun j : stripRepresentatives Γ z R τ => (j : Γ)) := by
  ext g
  constructor
  · intro hg
    obtain ⟨n, hlo, hhi⟩ := exists_dilationMatrix_height_band hτ (g • z)
    have hp : (a ^ n * g) • z = dilationMatrix τ ^ n • (g • z) := by
      rw [mul_smul, subgroup_dilation_zpow_smul Γ a ha]
    have hb : a ^ n * g ∈ stripRepresentatives Γ z R τ := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hp]
        exact (dilationMatrix_zpow_mem_axisRatioStrip R τ n (g • z)).mpr hg
      · rwa [hp]
      · rwa [hp]
    refine ⟨(-n, ⟨a ^ n * g, hb⟩), ?_⟩
    change a ^ (-n) * (a ^ n * g) = g
    rw [← mul_assoc, ← zpow_add]
    simp
  · rintro ⟨⟨n, j⟩, rfl⟩
    change (a ^ n * (j : Γ)) • z ∈ axisRatioStrip R
    rw [mul_smul, subgroup_dilation_zpow_smul Γ a ha]
    exact (dilationMatrix_zpow_mem_axisRatioStrip R τ n ((j : Γ) • z)).mpr j.property.1

/-- The strip enumeration needed by the supported Green operator is a genuine
bijection for the actual subgroup vertices.-/
def stripOrbitEquiv (hτ : 0 < τ) (z : ℍ) (R : ℝ) :
    (ℤ × stripRepresentatives Γ z R τ) ≃ {g : Γ | g • z ∈ axisRatioStrip R} :=
  (cyclicOrbitEquiv a (fun j : stripRepresentatives Γ z R τ => (j : Γ))
    (subgroup_dilation_infinite_order Γ a ha hτ.ne')
    (stripRepresentatives_disjoint Γ a ha hτ z R)).trans
      (Equiv.subtypeEquivRight (fun g => by rw [stripVertices_eq_cyclicOrbitUnion Γ a ha hτ z R]))

/-- Its coordinate formula retains the expected a^n b_j group vertex.
@isnad1 id=eq.2h6v.s14.fc9476c33c38 from=translated src=- shape=d83cb13b vocab=b78dbccf
-/
theorem stripOrbitEquiv_apply (hτ : 0 < τ) (z : ℍ) (R : ℝ)
    (p : ℤ × stripRepresentatives Γ z R τ) :
    (stripOrbitEquiv Γ a ha hτ z R p : Γ) = a ^ p.1 * (p.2 : Γ) := rfl

/-- The actual strip admits a finite disjoint cyclic-orbit decomposition.
@isnad1 id=ex.3h5v.s12.2bdc100a30ff from=translated src=- shape=9f54da50 vocab=828a61a3
-/
theorem exists_finite_strip_orbits [DiscreteTopology Γ] (hτ : 0 < τ) (z : ℍ)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ (N : ℕ) (b : Fin N → Γ),
      Function.Injective (fun p : ℤ × Fin N => a ^ p.1 * b p.2) ∧
      {g : Γ | g • z ∈ axisRatioStrip R} = cyclicOrbitUnion a b := by
  let J := stripRepresentatives Γ z R τ
  let : Fintype J := (finite_stripRepresentatives Γ z hR τ).fintype
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let b : Fin (Fintype.card J) → Γ := fun j => (e j : Γ)
  refine ⟨Fintype.card J, b, ?_, ?_⟩
  · apply cyclicOrbit_injective a b (subgroup_dilation_infinite_order Γ a ha hτ.ne')
    intro j k n he
    exact e.injective (stripRepresentatives_disjoint Γ a ha hτ z R (e j) (e k) n he)
  · rw [stripVertices_eq_cyclicOrbitUnion Γ a ha hτ z R]
    ext g
    constructor
    · rintro ⟨⟨n, j⟩, rfl⟩
      refine ⟨(n, e.symm j), ?_⟩
      simp [b]
    · rintro ⟨⟨n, j⟩, rfl⟩
      exact ⟨(n, e j), rfl⟩

end Singularity
