import Tengoku.EgzFormalProof.EGZ.Decomposition.QuotientMass
import Tengoku.EgzFormalProof.EGZ.Decomposition.CenteredLift
import Tengoku.EgzFormalProof.EGZ.Decomposition.Reduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact local-to-cumulative identity

Centered representatives turn the quotient-level fibre partition into the
integer-transition identity in Section 4.  Only local lifted weights occur
on the right-hand side.  Boundedness at the upper node prevents a transition
of a nonzero local lift from wrapping around modulo `p`.
-/

open scoped BigOperators
open Classical

namespace EGZ.FlagDecompositionRaw

variable {p d : ℕ} [NeZero p] {F : ConvexFlag}

/-- Local lifted masses below a node, transported by the integer transition
maps and summed over the finite centered boxes.-/
noncomputable def localIntegerMassBelow (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node)
    (q : IntCoord (F.rank x)) : ℕ := by
  classical
  exact ∑ y, if h : y ≤ x then
    ∑ z ∈ latticeBox (F.rank y) ((p - 1) / 2),
      if (F.transition h).integer z = q then localLift R pieces y z else 0
    else 0

/-- A residue fibre can be summed over centered integer representatives in
the source.
@isnad1 id=eq.2h8v.s10.889276e9f23b from=translated src=- shape=7a7d7628 vocab=86550cd5
-/
theorem sum_transitionFibres_eq_sum_localLift (hp : Odd p)
    (R : FpRepresentation p d F) (pieces : F.Node → FpCoord p d → ℕ)
    {y x : F.Node} (h : y ≤ x) (c : FpCoord p (F.rank x)) :
    (∑ a : FpCoord p (F.rank y),
      if (F.transition h).modp p a = c then
        affineFibreMass (pieces y) (R.map y) a else 0) =
    ∑ z ∈ latticeBox (F.rank y) ((p - 1) / 2),
      if ((F.transition h).integer z).mod p = c then
        localLift R pieces y z else 0 := by
  classical
  rw [← sum_latticeBox_mod hp]
  apply Finset.sum_congr rfl
  intro z hz
  have hcentered : IsCenteredLift p z := mem_latticeBox.mp hz
  rw [(F.transition h).mod_integer]
  congr 1
  exact (ite_eq_left hcentered).symm

/-- If a transition stays in the centered box on the local support,
congruence to a centered upper point is equality of integer coordinates.
@isnad1 id=iff.4h9v.s7.eb73a8bc2b10 from=translated src=- shape=919d4deb vocab=e2e91a16
-/
theorem transition_mod_eq_iff_of_localLift_ne_zero
    (R : FpRepresentation p d F) (pieces : F.Node → FpCoord p d → ℕ)
    {y x : F.Node} (h : y ≤ x) (z : IntCoord (F.rank y))
    (q : IntCoord (F.rank x)) (hq : IsCenteredLift p q)
    (hcentered : localLift R pieces y z ≠ 0 →
      IsCenteredLift p ((F.transition h).integer z))
    (hz : localLift R pieces y z ≠ 0) :
    ((F.transition h).integer z).mod p = q.mod p ↔
      (F.transition h).integer z = q := by
  constructor
  · exact IsCenteredLift.eq_of_mod_eq (hcentered hz) hq
  · intro heq
    rw [heq]

/-- The quotient-level partition is the exact integer-transition partition
when nonzero local lifts remain centered after transition.
@isnad1 id=eq.3h7v.s7.c3ba10987b51 from=translated src=- shape=f4bccbf2 vocab=df8167bc
-/
theorem localTransitionMassBelow_eq_localIntegerMassBelow (hp : Odd p)
    (R : FpRepresentation p d F) (pieces : F.Node → FpCoord p d → ℕ)
    (x : F.Node) (q : IntCoord (F.rank x)) (hq : IsCenteredLift p q)
    (hcentered : ∀ (y : F.Node) (h : y ≤ x) (z : IntCoord (F.rank y)),
      localLift R pieces y z ≠ 0 →
        IsCenteredLift p ((F.transition h).integer z)) :
    localTransitionMassBelow R pieces x (q.mod p) =
      localIntegerMassBelow R pieces x q := by
  classical
  unfold localTransitionMassBelow localIntegerMassBelow
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : y ≤ x
  · rw [dite_eq_left h, dite_eq_left h,
      sum_transitionFibres_eq_sum_localLift hp R pieces h]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : localLift R pieces y z = 0
    · simp [hz]
    · simp only [transition_mod_eq_iff_of_localLift_ne_zero R pieces h z q hq
        (hcentered y h z) hz]
  · rw [dite_eq_right h, dite_eq_right h]

/-- Exact local-to-cumulative identity using local lifted weights.
@isnad1 id=eq.4h7v.s8.05b532b1649e from=translated src=- shape=ccb27f82 vocab=04c5eba5
-/
theorem hat_eq_localIntegerMassBelow_of_centered (hp : Odd p)
    (R : FpRepresentation p d F) (pieces : F.Node → FpCoord p d → ℕ)
    (hsupported : ∀ y v, pieces y v ≠ 0 → v ∈ R.space y)
    (x : F.Node) (q : IntCoord (F.rank x)) (hq : IsCenteredLift p q)
    (hcentered : ∀ (y : F.Node) (h : y ≤ x) (z : IntCoord (F.rank y)),
      localLift R pieces y z ≠ 0 →
        IsCenteredLift p ((F.transition h).integer z)) :
    hat R pieces x q = localIntegerMassBelow R pieces x q := by
  rw [hat_eq_localTransitionMassBelow_of_centered R pieces hsupported x q hq]
  exact localTransitionMassBelow_eq_localIntegerMassBelow hp R pieces x q hq hcentered

/-- The local integer-transition sum has no mass outside the centered
upper box if all transitions of its nonzero local terms stay centered.
@isnad1 id=eq.2h7v.s6.60dbf0df63e5 from=translated src=- shape=36368ddd vocab=108a0fa5
-/
theorem localIntegerMassBelow_eq_zero_of_not_centered
    (R : FpRepresentation p d F) (pieces : F.Node → FpCoord p d → ℕ)
    (x : F.Node) (q : IntCoord (F.rank x)) (hq : ¬ IsCenteredLift p q)
    (hcentered : ∀ (y : F.Node) (h : y ≤ x) (z : IntCoord (F.rank y)),
      localLift R pieces y z ≠ 0 →
        IsCenteredLift p ((F.transition h).integer z)) :
    localIntegerMassBelow R pieces x q = 0 := by
  unfold localIntegerMassBelow
  apply Finset.sum_eq_zero
  intro y _
  split_ifs with h
  · apply Finset.sum_eq_zero
    intro z _
    split_ifs with heq
    · by_contra hz
      exact hq (heq ▸ hcentered y h z hz)
    · rfl
  · rfl

/-- The exact local-to-cumulative identity holds for every integer upper
coordinate; outside the centered box both sides vanish.
@isnad1 id=eq.3h7v.s8.f37b372a12cb from=translated src=- shape=7449b8ed vocab=04c5eba5
-/
theorem hat_eq_localIntegerMassBelow (hp : Odd p)
    (R : FpRepresentation p d F) (pieces : F.Node → FpCoord p d → ℕ)
    (hsupported : ∀ y v, pieces y v ≠ 0 → v ∈ R.space y)
    (x : F.Node) (q : IntCoord (F.rank x))
    (hcentered : ∀ (y : F.Node) (h : y ≤ x) (z : IntCoord (F.rank y)),
      localLift R pieces y z ≠ 0 →
        IsCenteredLift p ((F.transition h).integer z)) :
    hat R pieces x q = localIntegerMassBelow R pieces x q := by
  by_cases hq : IsCenteredLift p q
  · exact hat_eq_localIntegerMassBelow_of_centered hp R pieces hsupported x q hq hcentered
  · rw [hat, ite_eq_right hq,
      localIntegerMassBelow_eq_zero_of_not_centered R pieces x q hq hcentered]

end EGZ.FlagDecompositionRaw

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

/-- At an upper node of radius less than `p / 2`, every nonzero local lift
below it has centered integer transition coordinates.
@isnad1 id=iscenter.4h8v.s7.6387157a0c74 from=translated src=- shape=8e6c7415 vocab=6de56aae
-/
theorem isCenteredLift_transition_of_localLift_ne_zero
    (Φ : FlagDecomposition p d f) (K : Φ.flag.Node → ℕ)
    (hbounded : Φ.IsKBounded K) {y x : Φ.flag.Node} (h : y ≤ x)
    (hK : 2 * K x < p) (z : IntCoord (Φ.flag.rank y))
    (hz : Φ.localLift y z ≠ 0) :
    IsCenteredLift p ((Φ.flag.transition h).integer z) := by
  have hmem := Φ.flag.transition_mem h (Φ.mem_polytope_of_localLift_ne_zero y z hz)
  rw [(Φ.flag.transition h).real_integer] at hmem
  have hnorm := hbounded x ((Φ.flag.transition h).integer z) hmem
  unfold IsCenteredLift
  omega

/-- Section 4's corrected identity: the cumulative lift at `q` is the sum
of local lifts at all lower nodes whose integer transitions equal `q`.
@isnad1 id=eq.4h7v.s8.8ea8c72ec19d from=translated src=- shape=8233599e vocab=5421b7ae
-/
theorem hat_eq_sum_localLift_of_centered (hp : Odd p)
    (Φ : FlagDecomposition p d f) (K : Φ.flag.Node → ℕ)
    (hbounded : Φ.IsKBounded K) (x : Φ.flag.Node)
    (hK : 2 * K x < p) (q : IntCoord (Φ.flag.rank x))
    (hq : IsCenteredLift p q) :
    Φ.hat x q = ∑ y, if h : y ≤ x then
      ∑ z ∈ latticeBox (Φ.flag.rank y) ((p - 1) / 2),
        if (Φ.flag.transition h).integer z = q then Φ.localLift y z else 0
      else 0 := by
  classical
  exact FlagDecompositionRaw.hat_eq_localIntegerMassBelow_of_centered hp
    Φ.representation Φ.localWeight Φ.local_supported x q hq
    (fun y h z hz ↦ Φ.isCenteredLift_transition_of_localLift_ne_zero K hbounded h hK z hz)

/-- The corrected local-to-cumulative identity for arbitrary integer
coordinates, with the large-prime condition expressed by `2 * K x < p`.
@isnad1 id=eq.3h7v.s8.9a848134b9bd from=translated src=- shape=73cd4fd4 vocab=733c5fa9
-/
theorem hat_eq_sum_localLift (hp : Odd p)
    (Φ : FlagDecomposition p d f) (K : Φ.flag.Node → ℕ)
    (hbounded : Φ.IsKBounded K) (x : Φ.flag.Node)
    (hK : 2 * K x < p) (q : IntCoord (Φ.flag.rank x)) :
    Φ.hat x q = ∑ y, if h : y ≤ x then
      ∑ z ∈ latticeBox (Φ.flag.rank y) ((p - 1) / 2),
        if (Φ.flag.transition h).integer z = q then Φ.localLift y z else 0
      else 0 := by
  exact FlagDecompositionRaw.hat_eq_localIntegerMassBelow hp
    Φ.representation Φ.localWeight Φ.local_supported x q
    (fun y h z hz ↦ Φ.isCenteredLift_transition_of_localLift_ne_zero K hbounded h hK z hz)

end EGZ.FlagDecomposition
