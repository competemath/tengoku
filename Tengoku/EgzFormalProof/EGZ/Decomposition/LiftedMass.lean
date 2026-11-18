import Tengoku.EgzFormalProof.EGZ.Decomposition.Pullback
import Tengoku.EgzFormalProof.EGZ.Decomposition.Thickness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lifted set mass as an ambient finite sum

The centered lift assigns each nonzero cumulative ambient atom to a unique
integer support coordinate. Thus mass on any set of real fibre coordinates
can be computed directly on the ambient finite-field space.
-/

open scoped BigOperators
open Classical

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f)

/--
@isnad1 id=eq.1h6v.s9.23c01bb7011f from=translated src=- shape=5df4d1e1 vocab=412bf515
-/
theorem liftedMassOn_eq_natMassOn (hp : Odd p) (x : Φ.flag.Node)
    (S : Set (RealCoord (Φ.flag.rank x))) :
    Φ.liftedMassOn x S = natMassOn (Φ.cumulativeWeight x)
      {v | (FpCoord.centeredLift (Φ.representation.map x v)).real ∈ S} := by
  have hsum : Φ.liftedMassOn x S =
      ∑ v, ∑ q ∈ Φ.liftedSupport x,
        if q.real ∈ S ∧ Φ.representation.map x v = q.mod p then Φ.cumulativeWeight x v else 0 := by
    unfold liftedMassOn
    calc
      (∑ q ∈ Φ.liftedSupport x, if q.real ∈ S then Φ.hat x q else 0) =
          ∑ q ∈ Φ.liftedSupport x, ∑ v,
            if q.real ∈ S ∧ Φ.representation.map x v = q.mod p then Φ.cumulativeWeight x v else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        have hc : IsCenteredLift p q :=
          ((Φ.originalWeights.hat_ne_zero_iff x q).mp ((Φ.liftedSupport_spec x q).mp hq)).1
        change (if q.real ∈ S then
          (if IsCenteredLift p q then FlagDecompositionRaw.affineFibreMass
            (Φ.cumulativeWeight x) (Φ.representation.map x) (q.mod p) else 0) else 0) = _
        rw [ite_eq_left hc]
        by_cases hqS : q.real ∈ S <;>
          simp only [hqS, ite_true, ite_false, true_and, false_and,
            FlagDecompositionRaw.affineFibreMass, Finset.sum_const_zero]
      _ = _ := Finset.sum_comm
  rw [hsum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : Φ.cumulativeWeight x v = 0
  · simp only [hv, ite_self, Finset.sum_const_zero]
  · let q := FpCoord.centeredLift (Φ.representation.map x v)
    have hq : q ∈ Φ.liftedSupport x := by
      apply (Φ.liftedSupport_spec x q).mpr
      exact (Φ.originalWeights.hat_ne_zero_iff x q).mpr
        ⟨FpCoord.isCenteredLift_centeredLift hp _, v, (FpCoord.mod_centeredLift _).symm, hv⟩
    rw [Finset.sum_eq_single q]
    · simp only [q, FpCoord.mod_centeredLift, and_true]
      rfl
    · intro z hz hzq
      have hc := ((Φ.originalWeights.hat_ne_zero_iff x z).mp
        ((Φ.liftedSupport_spec x z).mp hz)).1
      have hneq : Φ.representation.map x v ≠ z.mod p := by
        intro heq
        apply hzq
        change z = FpCoord.centeredLift (Φ.representation.map x v)
        rw [heq, FpCoord.centeredLift_mod hc]
      simp only [hneq, and_false, ite_false]
    · exact fun h ↦ (h hq).elim

/--
@isnad1 id=le.1h7v.s6.7140a14477d2 from=translated src=- shape=62d434ae vocab=81c93933
-/
theorem liftedMassOn_mono (x : Φ.flag.Node) {S T : Set (RealCoord (Φ.flag.rank x))}
    (h : S ⊆ T) : Φ.liftedMassOn x S ≤ Φ.liftedMassOn x T := by
  apply Finset.sum_le_sum
  intro q _
  by_cases hq : q.real ∈ S
  · simp only [ite_eq_left hq, ite_eq_left (h hq)]
    exact le_rfl
  · simp only [ite_eq_right hq]
    exact Nat.zero_le _

end EGZ.FlagDecomposition
