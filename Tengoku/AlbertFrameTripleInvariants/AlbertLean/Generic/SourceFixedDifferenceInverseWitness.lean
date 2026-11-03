import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.RationalEvenFamilyFixedBranch
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorPairDephase

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms doubledCenter_norm_ne` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reflect_doubled_neg` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms two_even_negates_span` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms second_algorithmic_difference` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms full_source_inverse_witness` (it only prints; the queue checks the axioms of every declaration). -/

/-! A compatible inverse-image witness on the ENTIRE source carrier.
The two even centers are explicitly -2t and -2q for an orthogonal plane.
The output may have arbitrary S/C slots: cancellation recovers all of them.
This is the algebraic core of the generic root-cover nonvanishing witness. -/
noncomputable section
namespace AlbertLean.Generic.SourceFixedDifferenceInverseWitness

open AlbertLean.Triality ExteriorSix CoordinateTensor StructuredCubic
open StructuredAdjoint
open SourceEvenReflections SourceEvenAutomorphism
open SourceVectorPairDephase SourceVectorReflectionTransport
open SourceVectorPairReflection

universe u
variable {K : Type u} [Field K] [CharZero K]

def doubledCenter (t : VCoord K) : VCoord K := (-2 : K) • t

theorem doubledCenter_norm_ne (t : VCoord K) (ht : nV t ≠ 0) :
    nV (doubledCenter t) ≠ 0 := by
  rw [doubledCenter, nV_smul]
  exact mul_ne_zero (by norm_num) ht

theorem reflect_doubled_neg (t : VCoord K) (ht : nV t ≠ 0) :
    reflectV (doubledCenter t) (-t) = t := by
  have hd : -t - t = doubledCenter t := by unfold doubledCenter; module
  have hn : nV (-t - t) ≠ 0 := by rw [hd]; exact doubledCenter_norm_ne t ht
  simpa only [hd] using reflect_difference (-t) t (nV_neg t) hn

theorem reflect_doubled_self (t : VCoord K) (ht : nV t ≠ 0) :
    reflectV (doubledCenter t) t = -t := by
  have h := SourceEvenAutomorphism.reflectV_involutive
    (doubledCenter t) (-t) (doubledCenter_norm_ne t ht)
  rw [reflect_doubled_neg t ht] at h
  exact h

theorem even_doubled_self (e t : VCoord K) (ht : nV t ≠ 0)
    (het : BV e t = 0) : evenV e (doubledCenter t) t = -t := by
  rw [evenV, reflect_doubled_self t ht]
  apply reflectV_eq_of_orthogonal
  rw [BV_neg_right, het, neg_zero]

theorem even_doubled_orthogonal (e t q : VCoord K)
    (heq : BV e q = 0) (htq : BV t q = 0) :
    evenV e (doubledCenter t) q = q := by
  rw [evenV, reflectV_eq_of_orthogonal (doubledCenter t) q]
  · exact reflectV_eq_of_orthogonal e q heq
  · rw [doubledCenter, BV_smul_left, htq, mul_zero]

/-- The selected two even stages negate the whole target plane.-/
theorem two_even_negates_span (e t q : VCoord K)
    (ht : nV t ≠ 0) (hq : nV q ≠ 0)
    (het : BV e t = 0) (heq : BV e q = 0) (htq : BV t q = 0)
    (b c : K) :
    evenV e (doubledCenter q)
      (evenV e (doubledCenter t) (b • t + c • q)) = -(b • t + c • q) := by
  have hqt : BV q t = 0 := by rw [BV_symmetric]; exact htq
  have h1t := even_doubled_self e t ht het
  have h1q := even_doubled_orthogonal e t q heq htq
  have h2t := even_doubled_orthogonal e q t het hqt
  have h2q := even_doubled_self e q hq heq
  simp only [SourceVectorPairDephase.evenV_add,
    SourceVectorPairDephase.evenV_smul, h1t, h1q]
  have hneg : evenV e (doubledCenter q) (-t) = -t := by
    simpa only [neg_one_smul, h2t] using
      SourceVectorPairDephase.evenV_smul e (doubledCenter q) t (-1)
  rw [hneg, h2q]
  module

/-- The first fixed branch sends the negative target pair's second member
exactly to beta*t-q, so the SECOND algorithmic difference is really -2q.-/
theorem first_stage_negative_second (e t q : VCoord K)
    (ht : nV t ≠ 0) (het : BV e t = 0) (heq : BV e q = 0)
    (htq : BV t q = 0) (beta : K) :
    evenV e (doubledCenter t) (-(beta • t + q)) = beta • t - q := by
  have h1t := even_doubled_self e t ht het
  have h1q := even_doubled_orthogonal e t q heq htq
  have harg : -(beta • t + q) = (-beta) • t + (-1 : K) • q := by module
  rw [harg, SourceVectorPairDephase.evenV_add,
    SourceVectorPairDephase.evenV_smul, SourceVectorPairDephase.evenV_smul,
    h1t, h1q]
  module

theorem second_algorithmic_difference (e t q : VCoord K)
    (ht : nV t ≠ 0) (het : BV e t = 0) (heq : BV e q = 0)
    (htq : BV t q = 0) (beta : K) :
    orthogonalRemainder t
      (evenV e (doubledCenter t) (-(beta • t + q))) - q = doubledCenter q := by
  rw [first_stage_negative_second e t q ht het heq htq beta]
  have hproj : projectionCoeff t (beta • t - q) = beta := by
    rw [projectionCoeff, sub_eq_add_neg, BV_add_right,
      BV_smul_right, BV_neg_right, htq, BV_self_eq_two_nV]
    field_simp [ht]
    ring
  rw [orthogonalRemainder, hproj, doubledCenter]
  module

private theorem inverse_pair_of_v_intertwining
    (g1 g2 : JCoord K ≃ₗ[K] JCoord K) (T : VCoord K ≃ₗ[K] VCoord K)
    (hTv : ∀ z, (g2 (g1 z)).v = T z.v)
    (x y : JCoord K) (u v : VCoord K)
    (hTu : T u = x.v) (hTv' : T v = y.v) :
    ∃ X Y : JCoord K,
      X.v = u ∧ Y.v = v ∧ g2 (g1 X) = x ∧ g2 (g1 Y) = y := by
  let G := g1.trans g2
  let X := G.symm x
  let Y := G.symm y
  have hX : g2 (g1 X) = x := G.apply_symm_apply x
  have hY : g2 (g1 Y) = y := G.apply_symm_apply y
  refine ⟨X, Y, ?_, ?_, hX, hY⟩
  · apply T.injective
    rw [← hTv X, hX, hTu]
  · apply T.injective
    rw [← hTv Y, hY, hTv']

/-- Given actual target encoders with arbitrary spinor slots, the inverse
of the displayed two-stage lift is a compatible witness input. This proves
its negative V slots and exact full-carrier output, rather than assuming
that a choice of V normalization also recovers its S/C coordinates.-/
theorem full_source_inverse_witness
    (e t q : VCoord K) (rho1 rho2 beta : K)
    (he : nV e ≠ 0) (ht : nV t ≠ 0) (hq : nV q ≠ 0)
    (het : BV e t = 0) (heq : BV e q = 0) (htq : BV t q = 0)
    (hr1 : rho1 ^ 2 = nV e * nV (doubledCenter t)) (hr10 : rho1 ≠ 0)
    (hr2 : rho2 ^ 2 = nV e * nV (doubledCenter q)) (hr20 : rho2 ≠ 0)
    (x y : JCoord K) (hx : x.v = t) (hy : y.v = beta • t + q) :
    let g1 := sourceEvenAut e (doubledCenter t) rho1 he
      (doubledCenter_norm_ne t ht) hr1 hr10
    let g2 := sourceEvenAut e (doubledCenter q) rho2 he
      (doubledCenter_norm_ne q hq) hr2 hr20
    ∃ X Y : JCoord K,
      X.v = -t ∧ Y.v = -(beta • t + q) ∧
      g2.linear (g1.linear X) = x ∧ g2.linear (g1.linear Y) = y := by
  intro g1 g2
  let T := (evenVEquiv e (doubledCenter t) he (doubledCenter_norm_ne t ht)).trans
    (evenVEquiv e (doubledCenter q) he (doubledCenter_norm_ne q hq))
  have hTv (z : JCoord K) : (g2.linear (g1.linear z)).v = T z.v := rfl
  have hTnegT : T (-t) = t := by
    change evenV e (doubledCenter q) (evenV e (doubledCenter t) (-t)) = t
    have h := two_even_negates_span e t q ht hq het heq htq (-1) 0
    simpa only [zero_smul, add_zero, neg_one_smul, neg_neg] using h
  have hTnegY : T (-(beta • t + q)) = beta • t + q := by
    change evenV e (doubledCenter q)
      (evenV e (doubledCenter t) (-(beta • t + q))) = beta • t + q
    have h := two_even_negates_span e t q ht hq het heq htq (-beta) (-1)
    simpa only [neg_smul, neg_one_smul, one_smul, ← neg_add, neg_neg] using h
  exact inverse_pair_of_v_intertwining g1.linear g2.linear T hTv x y
    (-t) (-(beta • t + q)) (hTnegT.trans hx.symm) (hTnegY.trans hy.symm)

end AlbertLean.Generic.SourceFixedDifferenceInverseWitness
