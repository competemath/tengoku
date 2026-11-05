import Tengoku.NsP23.P23.OneTie.RhoFourPure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The abstract pure residual family; no semigroup nonrealizability claim. -/
namespace P23.OneTie
noncomputable section
open P23.Artin P23.Presentation
variable {a b : ℕ} [NeZero a]
set_option maxHeartbeats 1200000

structure PureResidualThreeBorder (S : Finset (Normal a b 0)) where
  u : ℕ
  C : ℕ
  a_ge_two : 2 ≤ a
  b_ge_two : 2 ≤ b
  u_pos : 0 < u
  C_ge_two : 2 ≤ C
  border : borderFinset S =
    {(⟨1,u,0,by omega⟩ : Normal a b 0),zAxis C,
      (⟨0,u+b-1,C-1,Nat.pos_of_ne_zero (NeZero.ne a)⟩ : Normal a b 0)}

namespace PureResidualThreeBorder
variable {S : Finset (Normal a b 0)} (R : PureResidualThreeBorder S)

def generalData : PureThreeBorderData S where
  C := R.C
  r := 1
  u := R.u
  v := R.u+b-1
  w := R.C-1
  b_pos := by have := R.b_ge_two; omega
  r_pos := by omega
  r_lt := by have := R.a_ge_two; omega
  u_pos := R.u_pos
  v_pos := by have := R.u_pos; have := R.b_ge_two; omega
  v_lt := by have := R.u_pos; have := R.b_ge_two; omega
  w_pos := by have := R.C_ge_two; omega
  w_lt := by have := R.C_ge_two; omega
  border := R.border

def roots : Finset (Normal a b 0) :=
  {⟨a-1,R.u-1,R.C-1,by have := R.a_ge_two; omega⟩,
   ⟨0,R.u+b-2,R.C-1,Nat.pos_of_ne_zero (NeZero.ne a)⟩,
   ⟨0,R.u+b-1,R.C-2,Nat.pos_of_ne_zero (NeZero.ne a)⟩}

def formalTop (Y Z : ℕ) := (R.u+b-1)*Y+(R.C-1)*Z
end PureResidualThreeBorder

theorem pure_three_border_ng_residual {S : Finset (Normal a b 0)}
    (P : PureThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (hl : IsLiveTie S) (ha : IsRootAntichain S) (ht : quotientType ℚ S hS hd hl = 3)
    (hn : QuotientNearlyGorenstein ℚ S hS hd hl) : Nonempty (PureResidualThreeBorder S) := by
  obtain ⟨hr,hv,hw⟩ := pure_three_border_ng_forces_endpoints P hS hd hl ha ht hn
  have hb : 2 ≤ b := by rcases hd.2 with hm | hp <;> omega
  refine ⟨⟨P.u,P.C,hd.1,hb,P.u_pos,by have := P.w_pos; have := P.w_lt; omega,?_⟩⟩
  simpa [hr,hv,hw] using P.border

theorem pureResidual_roots_exact {S : Finset (Normal a b 0)}
    (R : PureResidualThreeBorder S) (hS : S.Nonempty) (ha : IsRootAntichain S) : S = R.roots := by
  have hd : IsLiveParameterDomain a b 0 := ⟨R.a_ge_two,Or.inr ⟨R.b_ge_two,rfl⟩⟩
  have huv : R.generalData.u < R.generalData.v := by
    dsimp [PureResidualThreeBorder.generalData]
    have := R.u_pos; have := R.b_ge_two; omega
  have he := pure_three_border_roots_exact R.generalData hS hd ha huv
  convert he using 1
  simp [PureResidualThreeBorder.roots,PureThreeBorderData.threeRoots,
    PureThreeBorderData.xRoot,PureThreeBorderData.yRoot,PureThreeBorderData.zRoot,
    PureResidualThreeBorder.generalData,Nat.sub_sub]

theorem pureResidual_type_three {S : Finset (Normal a b 0)}
    (R : PureResidualThreeBorder S) (hS : S.Nonempty) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) :
    quotientType ℚ S hS ⟨R.a_ge_two,Or.inr ⟨R.b_ge_two,rfl⟩⟩ hl = 3 := by
  apply (pure_three_border_type_three_iff R.generalData hS _ hl ha).mpr
  dsimp [PureResidualThreeBorder.generalData]
  have := R.u_pos; have := R.b_ge_two; omega

theorem polynomialLift_eq_variable_powers (p : Normal a b 0) :
    polynomialLift (k := ℚ) p = polyX^p.x * polyY^p.y * polyZ^p.z := by
  simp [polynomialLift,normalExponent,MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial,polyX,polyY,polyZ]

theorem pureResidual_presentation_exact {S : Finset (Normal a b 0)}
    (R : PureResidualThreeBorder S) :
    finitePresentationIdeal (k := ℚ) S = Ideal.span
      {polyX^a-polyY^b,polyX*polyY^R.u,polyZ^R.C,polyY^(R.u+b-1)*polyZ^(R.C-1)} := by
  have hs : polynomialBorderSet (k := ℚ) S =
      {polyX*polyY^R.u,polyZ^R.C,polyY^(R.u+b-1)*polyZ^(R.C-1)} := by
    ext f
    simp only [polynomialBorderSet,R.border,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨g,hg,rfl⟩
      rcases hg with rfl | rfl | rfl <;>
        simp [polynomialLift_eq_variable_powers,zAxis]
    · intro hf
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl | rfl
      · refine ⟨⟨1,R.u,0,by have := R.a_ge_two; omega⟩,Or.inl rfl,?_⟩
        simp [polynomialLift_eq_variable_powers]
      · refine ⟨zAxis R.C,Or.inr (Or.inl rfl),?_⟩
        simp [polynomialLift_eq_variable_powers,zAxis]
      · refine ⟨⟨0,R.u+b-1,R.C-1,Nat.pos_of_ne_zero (NeZero.ne a)⟩,
          Or.inr (Or.inr rfl),?_⟩
        simp [polynomialLift_eq_variable_powers]
  rw [finitePresentationIdeal,polynomialBorderIdeal,hs,tieIdeal,← Ideal.span_union]
  congr 1
  ext f
  simp [tiePolynomial]
  tauto

theorem pureResidual_top_equations {S : Finset (Normal a b 0)}
    (R : PureResidualThreeBorder S) (X Y Z : ℕ) (htie : a*X=b*Y) :
    (a-1)*X+(R.u-1)*Y+(R.C-1)*Z+X = R.formalTop Y Z ∧
    (R.u+b-2)*Y+(R.C-1)*Z+Y = R.formalTop Y Z ∧
    (R.u+b-1)*Y+(R.C-2)*Z+Z = R.formalTop Y Z := by
  have hau : a-1+1=a := by have := R.a_ge_two; omega
  have huu : R.u-1+1=R.u := by have := R.u_pos; omega
  have hvv : R.u+b-1+1=R.u+b := by have := R.u_pos; have := R.b_ge_two; omega
  have huub : R.u+b-2+1=R.u+b-1 := by have := R.u_pos; have := R.b_ge_two; omega
  have hCC : R.C-2+1=R.C-1 := by have := R.C_ge_two; omega
  dsimp [PureResidualThreeBorder.formalTop]
  constructor
  · have hh : (a-1)*X+X=a*X := by
      calc
        _ = (a-1+1)*X := by ring
        _ = a*X := by rw [hau]
    have hh' : (R.u+b-1)*Y = (R.u-1)*Y+b*Y := by
      rw [← Nat.add_mul]
      have he : R.u+b-1=R.u-1+b := by have := R.u_pos; omega
      rw [he]
    omega
  · constructor
    · have hh : (R.u+b-2)*Y+Y=(R.u+b-1)*Y := by
        calc
          _ = (R.u+b-2+1)*Y := by ring
          _ = (R.u+b-1)*Y := by rw [huub]
      omega
    · have hh : (R.C-2)*Z+Z=(R.C-1)*Z := by
        calc
          _ = (R.C-2+1)*Z := by ring
          _ = (R.C-1)*Z := by rw [hCC]
      omega
end
end P23.OneTie
