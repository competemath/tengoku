import Tengoku.OpenaiMath.OAI.Analysis.BackwardIntertwiners.PolarFactors

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

open scoped Classical

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] realOperatorTower realOperatorCommute complexNormalCalculus complexClosedCalculus realSelfAdjointCalculus

open InnerProductSpace ContinuousLinearMap

def MinimalProjection (A : StarSubalgebra ℂ (H →L[ℂ] H)) (P : H →L[ℂ] H) : Prop :=
  IsStarProjection P ∧ P ≠ 0 ∧ P ∈ A ∧ ∀ Q : H →L[ℂ] H,
    IsStarProjection Q → Q ∈ A → Q*P=Q → Q=0 ∨ Q=P

def AtomicAlgebra (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∃ (ι : Type u) (_ : Countable ι) (P : ι → H →L[ℂ] H),
    (∀ i, MinimalProjection A (P i)) ∧
    (∀ i j, i ≠ j → P i * P j = 0) ∧
    ∀ v : H, HasSum (fun i => P i v) v

def DiffuseAlgebra (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ¬∃ P, MinimalProjection A P

lemma selfAdjoint_commutes_rankOne {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    {u v : H} {t : ℝ} (hu : T u = (t:ℂ) • u) (hv : T v = (t:ℂ) • v) :
    T * rankOne ℂ u v = rankOne ℂ u v * T := by
  ext z
  change T (inner ℂ v z • u) = inner ℂ v (T z) • u
  have hi : inner ℂ (T v) z = inner ℂ v (T z) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) v z
  rw [map_smul,hu,←hi,hv,
    inner_smul_left,Complex.conj_ofReal,smul_smul,mul_comm]

lemma projection_reverse_mul {P Q : H →L[ℂ] H}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : Q*P=Q) : P*Q=Q := by
  have hh := congrArg star h
  simpa only [star_mul,hP.isSelfAdjoint.star_eq,hQ.isSelfAdjoint.star_eq] using hh

lemma eigenspace_projection_minimal {s : Set (H →L[ℂ] H)}
    (hs : ∀ T ∈ s, IsSelfAdjoint T) {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (hP₀ : P ≠ 0) (hPA : P ∈ strongGenerated s)
    (hscalar : ∀ T ∈ s, ∃ t : ℝ, ∀ v : H, P v = v → T v = (t:ℂ) • v) :
    MinimalProjection (strongGenerated s) P := by
  refine ⟨hP,hP₀,hPA,?_⟩
  intro Q hQ hQA hQP
  by_cases hQ₀ : Q=0
  · exact Or.inl hQ₀
  right
  obtain ⟨z,hz⟩ : ∃ z : H, Q z ≠ 0 := by
    by_contra! hz
    apply hQ₀
    ext z
    exact hz z
  let v := Q z
  have hv₀ : v ≠ 0 := hz
  have hQv : Q v = v := DFunLike.congr_fun hQ.isIdempotentElem z
  have hPv : P v = v := DFunLike.congr_fun (projection_reverse_mul hP hQ hQP) z
  have hcomm (u : H) (hPu : P u=u) : Q * rankOne ℂ u v = rankOne ℂ u v * Q := by
    have hle : strongGenerated s ≤ StarSubalgebra.centralizer ℂ {rankOne ℂ u v} := by
      apply strongGenerated_le (strong_centralizer_closed _)
      intro T hT
      apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
      intro R hR
      obtain rfl : R = rankOne ℂ u v := hR
      obtain ⟨t,ht⟩ := hscalar T hT
      refine ⟨(selfAdjoint_commutes_rankOne (hs T hT) (ht u hPu) (ht v hPv)).symm, ?_⟩
      change (rankOne ℂ u v).adjoint * T = T * (rankOne ℂ u v).adjoint
      rw [InnerProductSpace.adjoint_rankOne]
      exact (selfAdjoint_commutes_rankOne (hs T hT) (ht v hPv) (ht u hPu)).symm
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle hQA) _ (Set.mem_singleton _)).1.symm
  have hfix (u : H) (hPu : P u=u) : Q u=u := by
    have hh := DFunLike.congr_fun (hcomm u hPu) v
    change Q (inner ℂ v v • u) = inner ℂ v (Q v) • u at hh
    rw [hQv,map_smul] at hh
    exact (smul_right_injective H (inner_self_ne_zero.mpr hv₀)) hh
  have he : Q*P=P := by
    ext z
    exact hfix (P z) (DFunLike.congr_fun hP.isIdempotentElem z)
  exact hQP.symm.trans he

def halfExponentIndex (t : ℕ → ℕ) (k : ℕ) : ℤ :=
  10*((k:ℤ)+1) + if k=0 then 0 else 100*((residueScale k:ℤ)-2+(t (weightBlock k):ℤ))
lemma halfExponentIndex_cast (t : ℕ → ℕ) (k : ℕ) :
    (halfExponentIndex t k : ℝ) = halfExponent t k := by
  simp only [halfExponentIndex,halfExponent,residueCorrection]
  split_ifs <;> push_cast <;> rfl

def exponentIndex (x : Base) : ℤ → ℤ
  | .ofNat k => halfExponentIndex (plusResidue x) k
  | .negSucc k => halfExponentIndex (minusResidue x) k
lemma exponentIndex_cast (x : Base) (j : ℤ) : (exponentIndex x j : ℝ)=explicitExponent x j := by
  cases j <;> exact halfExponentIndex_cast _ _
lemma explicitBeta_exponentIndex (x : Base) (j : ℤ) :
    explicitBeta x j=Real.exp (-(exponentIndex x j : ℝ)) := by
  rw [exponentIndex_cast]
  rfl
lemma exp_neg_int_injective : Function.Injective (fun z : ℤ => Real.exp (-(z:ℝ))) := by
  intro a b h
  have hh := neg_injective (Real.exp_injective h)
  exact_mod_cast hh

def jointLevel (F : Finset ℤ) (t : ↥F → ℤ) (j : ℤ) : Set Base :=
  {x | ∀ n : ↥F, explicitBeta x (j+n)=Real.exp (-(t n:ℝ))}
lemma jointLevel_eq_iInter (F : Finset ℤ) (t : ↥F → ℤ) (j : ℤ) :
    jointLevel F t j=⋂ n : ↥F, {x : Base | explicitBeta x (j+(n:ℤ))=Real.exp (-(t n:ℝ))} := by
  ext x
  simp [jointLevel]
lemma jointLevel_measurable (F : Finset ℤ) (t : ↥F → ℤ) (j : ℤ) : MeasurableSet (jointLevel F t j) := by
  rw [jointLevel_eq_iInter]
  exact MeasurableSet.iInter fun n : ↥F => measurableSet_eq_fun (measurable_explicitBeta (j+(n:ℤ))) measurable_const
lemma jointLevel_partition (F : Finset ℤ) (x : Base) (j : ℤ) : ∃! t : ↥F → ℤ, x ∈ jointLevel F t j := by
  refine ⟨fun n => exponentIndex x (j+n),fun n => explicitBeta_exponentIndex _ _,?_⟩
  intro t ht
  funext n
  exact exp_neg_int_injective ((ht n).symm.trans (explicitBeta_exponentIndex x (j+n)))

def jointProjection (F : Finset ℤ) (t : ↥F → ℤ) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  diagonalProjection (jointLevel F t) (jointLevel_measurable F t)
def finitePolarAlgebra (F : Finset ℤ) : StarSubalgebra ℂ (GlobalHilbert →L[ℂ] GlobalHilbert) :=
  strongGenerated (polarDiagonal '' (F : Set ℤ))
lemma DiagonalSymbol.prod_apply {ι : Type*} (s : Finset ι) (a : ι → DiagonalSymbol) (x : Base) (j : ℤ) :
    (∏ i ∈ s, a i) x j = ∏ i ∈ s, a i x j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs => simp [Finset.prod_insert,hi,hs]
lemma projectionSymbol_prod {ι : Type*} [Fintype ι] (E : ι → ℤ → Set Base)
    (hE : ∀ i j, MeasurableSet (E i j)) :
    (∏ i, projectionSymbol (E i) (hE i)) =
      projectionSymbol (fun j => ⋂ i, E i j) (fun j => MeasurableSet.iInter fun i => hE i j) := by
  apply Subtype.ext
  funext x j
  rw [DiagonalSymbol.prod_apply]
  simp only [projectionSymbol_apply,Finset.prod_boole,Finset.mem_univ,true_implies,Set.mem_iInter]

def PurePointResolution (T : H →L[ℂ] H) : Prop :=
  ∃ (ι : Type u) (_ : Countable ι) (P : ι → H →L[ℂ] H) (eigenvalue : ι → ℝ),
    (∀ i, IsStarProjection (P i) ∧ P i ≠ 0 ∧ T * P i = (eigenvalue i:ℂ) • P i) ∧
    (∀ i j, i ≠ j → P i * P j = 0) ∧ ∀ v : H, HasSum (fun i => P i v) v

end
end BackwardIntertwiners

end OAI
