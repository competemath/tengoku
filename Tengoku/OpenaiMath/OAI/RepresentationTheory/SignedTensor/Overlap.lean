import Tengoku
import Tengoku.OpenaiMath.OAI.RepresentationTheory.SignedTensor.Blocks
import Tengoku.OpenaiMath.OAI.RepresentationTheory.Unitary.Spectral

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.TensorBoard
variable {R C J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]

end CoordinateSweeps.TensorBoard

namespace CoordinateSweeps.UnitaryIrrep
variable {Γ n : Type*} [Group Γ] [Fintype Γ] [Fintype n] [DecidableEq n]
lemma projector_commute_lift (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (x : MonoidAlgebra ℂ Γ) :
    ρ.projector τ*MonoidAlgebra.lift ℂ _ _ τ x=MonoidAlgebra.lift ℂ _ _ τ x*ρ.projector τ := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simpa using (ρ.projector_commute τ g).symm
  | add x y hx hy => simp only [map_add,add_mul,mul_add,hx,hy]
  | smul c x hx => simp only [map_smul,smul_mul_assoc,mul_smul_comm,hx]
end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.SignedTensor

lemma densityPower_commute_projector {p l : ℕ} (r : Matrix (Letter p) (Letter p) ℂ)
    (hr : IsEven r) (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    densityPower l r*ρ.projector (action p l)=ρ.projector (action p l)*densityPower l r := by
  simp only [UnitaryIrrep.projector,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact congrArg (fun A => ρ.coefficient σ • A) (densityPower_commute_of_even r hr σ).symm

lemma even_average_trace {R : Type*} [Fintype R] [Nonempty R] {p : ℕ}
    (r : R → EvenDensity p) (ε : ℝ) :
    Matrix.trace ((Fintype.card R : ℂ)⁻¹ • (∑ i, (r i).val)+
      (ε : ℂ) • (1 : Matrix (Letter p) (Letter p) ℂ)) = 1+ε*(2*p) := by
  rw [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_sum,Matrix.trace_smul,Matrix.trace_one]
  simp only [(r _).property.2.1,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    smul_eq_mul,Fintype.card_fin]
  have hc : (Fintype.card R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hc]
  push_cast
  rfl

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open TensorBoard Overlap
variable {R C I J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype I] [Fintype J]

abbrev groupOperator {p l : ℕ} (x : MonoidAlgebra ℂ (Equiv.Perm (Fin l))) :
    Matrix (Word p l) (Word p l) ℂ := MonoidAlgebra.lift ℂ _ _ (action p l) x

def rowProduct {p l : ℕ} {F : Finset (R × C)} (e : Fin l ≃ F) (r : R → EvenDensity p) :
    Matrix (Word p l) (Word p l) ℂ := TensorBoard.tensor (fun x => (r (e x).val.1).val)

def columnProduct {p l : ℕ} {F : Finset (R × C)} (e : Fin l ≃ F) (r : C → EvenDensity p) :
    Matrix (Word p l) (Word p l) ℂ := TensorBoard.tensor (fun x => (r (e x).val.2).val)

/- Literal deleted-board overlap with actual signed tensor action. The two
mixture dominations will be obtained by tensoring the local density theorem;
the whitening and the full-group dimension loss are constructed here. -/

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open TensorBoard Overlap
variable {R C I J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype I] [Fintype J]

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open TensorBoard
variable {p r c : ℕ} [NeZero r]

/- Source 06:eq19 for literal row and column subgroup projectors on an
arbitrary board with holes. The mixtures and signed regroupings are constructed. -/

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.TensorBoard
variable {R C J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]
end CoordinateSweeps.TensorBoard

namespace CoordinateSweeps.SignedTensor
open TensorBoard
variable {R C I J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype I] [Fintype J]

def labelRowProduct {p l : ℕ} (e : Fin l → R × C) (r : R → EvenDensity p) :
    Matrix (Word p l) (Word p l) ℂ := TensorBoard.tensor (fun x => (r (e x).1).val)

def labelColumnProduct {p l : ℕ} (e : Fin l → R × C) (r : C → EvenDensity p) :
    Matrix (Word p l) (Word p l) ℂ := TensorBoard.tensor (fun x => (r (e x).2).val)

/- Literal deleted-board overlap with actual signed tensor action. The two
mixture dominations will be obtained by tensoring the local density theorem;
the whitening and the full-group dimension loss are constructed here. -/

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open TensorBoard Overlap
variable {R C I J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype I] [Fintype J]

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open TensorBoard
variable {p r c : ℕ} [NeZero r]
  {L : Type*} [Fintype L] [DecidableEq L]

/- Source 06:eq19 for literal row and column subgroup projectors on an
arbitrary board with holes. The mixtures and signed regroupings are constructed. -/

end CoordinateSweeps.SignedTensor

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
