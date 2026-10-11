import Tengoku.OpenaiMath.OAI.Analysis.Steinitz.LiftedRearrangement

namespace OAI

/-! Energy-preserving sections and adaptive coordinate selection. -/

section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace ShiftedSections
open HeatL2 HeatL2.Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma symbol_mul (t : ℝ≥0) (v : ι → ℝ≥0) :
    GaussianKernel.symbol (fun i => t*v i) = fun ξ => (t:ℝ)*GaussianKernel.symbol v ξ := by
  funext ξ
  simp only [GaussianKernel.symbol,NNReal.coe_mul]
  rw [← mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end ShiftedSections

end

section

open MeasureTheory Set
namespace ShiftedSections
open HeatL2.Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Coeff := EuclideanSpace ℝ ι

structure Good (K : Set (Coeff (ι := ι))) : Prop where
  nonempty : K.Nonempty
  isOpen : IsOpen K
  bounded : Bornology.IsBounded K
  convex : Convex ℝ K
  symmetric : ∀ x ∈ K,-x ∈ K
  bound : Bound K isOpen.measurableSet (1/10000)

noncomputable def backward : {n : ℕ} → (Fin n → ι) → Set (Coeff (ι := ι)) → Set (Coeff (ι := ι))
  | 0,_,K => K
  | _+1,j,K => sectionDomain (backward (fun i => j i.succ) K) (EuclideanSpace.single (j 0) 1) (5/2) 1

noncomputable def walk : {n : ℕ} → (Fin n → ι) → (Fin n → Coeff (ι := ι) → ℝ) →
    (Fin n → ℝ) → Coeff (ι := ι) → Coeff (ι := ι)
  | 0,_,_,_,x => x
  | _+1,j,q,ε,x => walk (fun i => j i.succ) (fun i => q i.succ) (fun i => ε i.succ)
      (x+(q 0 x+ε 0) • EuclideanSpace.single (j 0) 1)

end ShiftedSections

end

end OAI
