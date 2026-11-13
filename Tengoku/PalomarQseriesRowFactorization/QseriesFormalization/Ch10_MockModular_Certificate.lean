import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Ch10_MockModular_Sigma
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Ch10_MockModular_Pell
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Ch10_MockModular_SlabIndicator
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Ch10_MockModular_OddTheta
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Ch10_MockModular_Shadow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ch10: Mock Modularity Certificate

The algebraic/combinatorial certificate for Chan's Θ₁₀ over Q(√5).
Conjuncts are the inputs to Zwegers' theorem specialized to our lattice.
`MockCertificate` is a historical project name: the structure below packages
finite algebraic inputs and does not itself prove a modular transformation law,
harmonicity, or a standard harmonic-Maass mock-modularity statement.

## Slab decomposition

BCoeff N = slabCoeff N is proved by σ-reindexing (not interior
cancellation). Each A-cone point (k,r) maps via σ_k to a slab+ point
with weight negOnePowInt(σ_k(r)) = -negOnePowInt(r), which is exactly
the ACoeff weight. Similarly for D-cone → slab-.
-/

namespace QseriesFormalization
namespace Ch10

/-! ## Slab coefficient via σ-reindex (extrinsic: same box as ACoeff/DCoeff) -/

def slabWeight (k r : Int) : Int := -slabInd k r * negOnePowInt r

def slabPlusCoeff (N : Nat) : Int :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (↑p.1) (↑p.2) = ↑N)).sum
    (fun p => negOnePowInt (sigma (↑p.1) (↑p.2)))

def slabMinusCoeff (N : Nat) : Int :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (-(↑p.1 + 1)) (-(↑p.2 + 1)) = ↑N)).sum
    (fun p => -negOnePowInt (sigma (-(↑p.1 + 1)) (-(↑p.2 + 1))))

def slabCoeff (N : Nat) : Int := slabPlusCoeff N + slabMinusCoeff N

/-! ## Slab decomposition proof -/

/--
@isnad1 id=eq.0h1v.s3.6ad768268a01 from=translated src=- shape=b70c6bb1 vocab=55e98ab6
-/
theorem ACoeff_eq_slabPlusCoeff (N : Nat) : ACoeff N = slabPlusCoeff N := by
  unfold ACoeff slabPlusCoeff
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  have := sigma_flips_sign (↑p.1) (↑p.2)
  omega

/--
@isnad1 id=eq.0h1v.s3.2450ede97b59 from=translated src=- shape=b70c6bb1 vocab=f3c9af52
-/
theorem DCoeff_eq_slabMinusCoeff (N : Nat) : DCoeff N = slabMinusCoeff N := by
  unfold DCoeff slabMinusCoeff
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  have := sigma_flips_sign (-(↑p.1 + 1)) (-(↑p.2 + 1))
  omega

/--
@isnad1 id=eq.0h1v.s3.d93f6a2ff19e from=translated src=- shape=b70c6bb1 vocab=48124412
-/
theorem BCoeff_eq_slabCoeff (N : Nat) : BCoeff N = slabCoeff N := by
  unfold BCoeff slabCoeff
  rw [ACoeff_eq_slabPlusCoeff, DCoeff_eq_slabMinusCoeff]
  ring

/-! ## The certificate structure -/

structure MockCertificate : Prop where
  slab_decomp : ∀ N : Nat, BCoeff N = slabCoeff N
  cone_indicator : ∀ k r : Int,
    2 * slabInd k r =
      sgnZ (BAff (pellCoord k r) c1) -
      sgnZ (BAff (pellCoord k r) c2)
  c1_norm : pellQ c1 = -5
  c2_norm : pellQ c2 = -20
  cusp_norms_distinct : pellQ c1 ≠ pellQ c2
  odd_theta_cancel : ∀ x : Int,
    negOnePowInt x + negOnePowInt (thetaInvol x) = 0
  shadow_witness : shadowCoeff 4 = 1
  shadow_nonzero : ∃ N : Nat, shadowCoeff N ≠ 0
  pell_form_invariant : ∀ v : ZVec, pellQ (Mmul v) = pellQ v
  cone_indecomp : pellB (Mmul c1) c2 < 0

/-! ## Inhabiting the certificate -/

/--
@isnad1 id=mockcert.0h0v.s0.74721e54f308 from=translated src=- shape=45709ebd vocab=74721e54
-/
theorem chanTheta10_mock_certificate : MockCertificate where
  slab_decomp := BCoeff_eq_slabCoeff
  cone_indicator := two_mul_slabInd_eq_sign_diff
  c1_norm := pellQ_c1
  c2_norm := pellQ_c2
  cusp_norms_distinct := cusp_norms_ne
  odd_theta_cancel := odd_theta_fiber_cancel
  shadow_witness := shadowCoeff_four
  shadow_nonzero := shadow_nonzero
  pell_form_invariant := pellQ_Mmul
  cone_indecomp := cone_indecomposable'

end Ch10
end QseriesFormalization
