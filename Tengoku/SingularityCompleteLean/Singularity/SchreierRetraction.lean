import Tengoku.SingularityCompleteLean.Singularity.WordDistance
import Tengoku.Seed.GroupTheory.Complement
import Tengoku.Seed.GroupTheory.FreeGroup.Reduce

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quantitative retraction to a subgroup using a right transversal

For a transversal containing one, write x = h r and retract x to h. Right
multiplication by a jump changes h by one of the Schreier transitions r s
retracted back to the subgroup. A uniform bound on those finitely many
transitions therefore controls the free-word norm along every permitted path.
-/

noncomputable section
open Set Subgroup
open scoped Classical

namespace Singularity

variable {G : Type*} [Group G] (H : Subgroup G) (R : Set G)
  (hR : Subgroup.IsComplement (H : Set G) R)

/-- The subgroup component in the right-transversal decomposition x = h r.-/
def schreierRetraction (x : G) : H :=
  ⟨x * (hR.toRightFun x : G)⁻¹, hR.mul_inv_toRightFun_mem x⟩

/-- Left multiplication by a subgroup element leaves the chosen right representative unchanged.
@isnad1 id=eq.1h5v.s6.4f8de2e116ed from=translated src=- shape=3834c1c8 vocab=179dbfdd
-/
theorem schreierRepresentative_left (h : H) (x : G) :
    hR.toRightFun ((h : G) * x) = hR.toRightFun x := by
  apply (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp hR ((h : G) * x)).unique
    (hR.mul_inv_toRightFun_mem _)
  change ((h : G) * x) * (hR.toRightFun x : G)⁻¹ ∈ H
  rw [mul_assoc]
  exact H.mul_mem h.property (hR.mul_inv_toRightFun_mem x)

/-- If the transversal contains one, every subgroup element has representative one.
@isnad1 id=eq.2h4v.s6.709f81606832 from=translated src=- shape=a1e52597 vocab=dc9d1cd1
-/
theorem schreierRepresentative_subgroup (hR1 : (1 : G) ∈ R) (h : H) :
    hR.toRightFun (h : G) = ⟨1, hR1⟩ := by
  apply (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp hR (h : G)).unique
    (hR.mul_inv_toRightFun_mem _)
  change (h : G) * (1 : G)⁻¹ ∈ H
  simpa only [inv_one, mul_one] using h.property

/-- The retraction is the identity on the subgroup.
@isnad1 id=eq.2h4v.s6.8d70525e86d4 from=translated src=- shape=45a677ce vocab=7741a105
-/
theorem schreierRetraction_subgroup (hR1 : (1 : G) ∈ R) (h : H) :
    schreierRetraction H R hR (h : G) = h := by
  apply Subtype.ext
  change (h : G) * (hR.toRightFun (h : G) : G)⁻¹ = h
  rw [schreierRepresentative_subgroup H R hR hR1 h]
  simp

/-- The retraction of a product satisfies the Schreier cocycle identity.
@isnad1 id=eq.1h5v.s7.79fc1560192d from=translated src=- shape=e0f041a1 vocab=312a80c3
-/
theorem schreierRetraction_mul (x g : G) :
    schreierRetraction H R hR (x * g) = schreierRetraction H R hR x *
      schreierRetraction H R hR ((hR.toRightFun x : G) * g) := by
  have hr : hR.toRightFun (x * g) = hR.toRightFun ((hR.toRightFun x : G) * g) := by
    have hh := schreierRepresentative_left H R hR (schreierRetraction H R hR x)
      ((hR.toRightFun x : G) * g)
    convert hh using 1
    congr 1
    change x * g = (x * (hR.toRightFun x : G)⁻¹) * ((hR.toRightFun x : G) * g)
    group
  apply Subtype.ext
  change x * g * (hR.toRightFun (x * g) : G)⁻¹ =
    (x * (hR.toRightFun x : G)⁻¹) *
      ((hR.toRightFun x : G) * g * (hR.toRightFun ((hR.toRightFun x : G) * g) : G)⁻¹)
  rw [hr]
  group

variable {α : Type*} (φ : H →* FreeGroup α)

/-- A bound on Schreier transitions bounds the norm change of one permitted jump.
@isnad1 id=le.3h9v.s10.af0088e5c72c from=translated src=- shape=24f1b496 vocab=3371b41f
-/
theorem schreierRetraction_jump_norm (s : Finset G) (L : ℕ)
    (hL : ∀ r : R, ∀ g ∈ s, FreeGroup.norm (φ (schreierRetraction H R hR ((r : G) * g))) ≤ L)
    (x : G) {g : G} (hg : g ∈ s) :
    FreeGroup.norm (φ (schreierRetraction H R hR (x * g))) ≤
      FreeGroup.norm (φ (schreierRetraction H R hR x)) + L := by
  rw [schreierRetraction_mul, map_mul]
  exact (FreeGroup.norm_mul_le _ _).trans (Nat.add_le_add_left (hL _ g hg) _)

/-- A path of n jumps changes the free-word norm of the retraction by at most nL.
@isnad1 id=le.2h10v.s10.460a48efc3b7 from=translated src=- shape=b3e35885 vocab=a9cc935d
-/
theorem schreierRetraction_word_norm (s : Finset G) (L : ℕ)
    (hL : ∀ r : R, ∀ g ∈ s, FreeGroup.norm (φ (schreierRetraction H R hR ((r : G) * g))) ≤ L)
    (n : ℕ) (w : WalkWord s n) (x : G) :
    FreeGroup.norm (φ (schreierRetraction H R hR (walkEndpoint s n x w))) ≤
      FreeGroup.norm (φ (schreierRetraction H R hR x)) + L * n := by
  induction n generalizing x with
  | zero => simp only [walkEndpoint, Nat.mul_zero, Nat.add_zero, le_refl]
  | succ n ih =>
    change FreeGroup.norm (φ (schreierRetraction H R hR (walkEndpoint s n (x * w.1) w.2))) ≤ _
    have h := (ih w.2 (x * w.1)).trans (Nat.add_le_add_right
      (schreierRetraction_jump_norm H R hR φ s L hL x w.1.property) (L * n))
    calc
      _ ≤ (FreeGroup.norm (φ (schreierRetraction H R hR x)) + L) + L * n := h
      _ = _ := by ring

end Singularity
