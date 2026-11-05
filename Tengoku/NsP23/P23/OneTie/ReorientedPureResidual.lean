import Tengoku.NsP23.P23.OneTie.PureReorientation
import Tengoku.NsP23.P23.OneTie.PureResidualThreeBorder
import Tengoku.NsP23.P23.OneTie.RhoFourMixedClassification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Scope-explicit residual presentation together with an actual quotient equivalence. -/
namespace P23.OneTie
noncomputable section
open P23.Artin P23.Presentation
variable {a b c : ℕ} [NeZero a]
set_option backward.isDefEq.respectTransparency false

def coordinateGenerator (j : Fin 3) : Normal a b c :=
  if j = 0 then Normal.xGenerator else if j = 1 then Normal.yGenerator else Normal.zGenerator

structure ReorientedPureResidual (S : Finset (Normal a b c)) where
  a' : ℕ
  b' : ℕ
  a'_ge_two : 2 ≤ a'
  b'_ge_two : 2 ≤ b'
  roots : Finset (Normal a' b' 0)
  residual : letI : NeZero a' := ⟨by omega⟩; PureResidualThreeBorder roots
  nonempty : roots.Nonempty
  antichain : letI : NeZero a' := ⟨by omega⟩; IsRootAntichain roots
  live : letI : NeZero a' := ⟨by omega⟩; IsLiveTie roots
  typeThree : letI : NeZero a' := ⟨by omega⟩;
    quotientType ℚ roots nonempty ⟨a'_ge_two,Or.inr ⟨b'_ge_two,rfl⟩⟩ live = 3
  nearlyGorenstein : letI : NeZero a' := ⟨by omega⟩;
    QuotientNearlyGorenstein ℚ roots nonempty ⟨a'_ge_two,Or.inr ⟨b'_ge_two,rfl⟩⟩ live
  equivalence : letI : NeZero a' := ⟨by omega⟩;
    FinitePolynomialQuotient ℚ S ≃ₐ[ℚ] FinitePolynomialQuotient ℚ roots
  coordinatePermutation : Equiv.Perm (Fin 3)
  swappedXY : Bool
  permutation_eq : coordinatePermutation = if swappedXY then Equiv.swap 0 1 else Equiv.refl _
  normalCoordinates : letI : NeZero a' := ⟨by omega⟩; Normal a b c ≃* Normal a' b' 0
  standardCorrespondence : letI : NeZero a' := ⟨by omega⟩;
    ∀ p, normalCoordinates p ∈ standardSet roots ↔ p ∈ standardSet S
  variablesCorrespondence : letI : NeZero a' := ⟨by omega⟩;
    ∀ j, normalCoordinates (coordinateGenerator j) = coordinateGenerator (coordinatePermutation j)
  quotientCoordinates : letI : NeZero a' := ⟨by omega⟩;
    ∀ p, finitePolynomialQuotientEquiv (k := ℚ) roots nonempty
        ⟨a'_ge_two,Or.inr ⟨b'_ge_two,rfl⟩⟩
        (equivalence (Ideal.Quotient.mk _ (polynomialLift (k := ℚ) p))) =
      truncatedMonomial (k := ℚ) roots (normalCoordinates p)

theorem pure_three_border_reoriented_residual (S : Finset (Normal a b 0))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (ht : quotientType ℚ S hS hd hl = 3)
    (hcard : (borderFinset S).card = 3)
    (hnf : ∀ q ∈ borderFinset S, ¬NormalHasFullSupport q)
    (hn : QuotientNearlyGorenstein ℚ S hS hd hl) : Nonempty (ReorientedPureResidual S) := by
  have hb : 2 ≤ b := by rcases hd.2 with hm | hp <;> omega
  rcases pure_three_border_support_classification S hS hd hl ha ht hcard hnf with hP | hP
  · obtain ⟨P⟩ := hP
    obtain ⟨R⟩ := pure_three_border_ng_residual P hS hd hl ha ht hn
    refine ⟨⟨a,b,hd.1,hb,S,R,hS,ha,hl,ht,hn,AlgEquiv.refl,
      Equiv.refl _,false,rfl,MulEquiv.refl _,fun _ => Iff.rfl,fun _ => rfl,?_⟩⟩
    intro p
    simp [polynomialLift,finitePolynomialQuotientEquiv_monomial]
  · letI : NeZero b := ⟨by omega⟩
    obtain ⟨P⟩ := hP
    obtain ⟨P'⟩ := pureXZ_reoriented_threeBorder S P hS hd hl ha ht hcard
    have hS' : (pureSwapXYFinset S).Nonempty := by
      obtain ⟨s,hs⟩ := hS
      exact ⟨pureSwapXY s,Finset.mem_map.mpr ⟨s,hs,rfl⟩⟩
    have hd' : IsLiveParameterDomain b a 0 := ⟨hb,Or.inr ⟨hd.1,rfl⟩⟩
    have hl' := pureSwapXYLive S hd.1 hb hl
    have ha' := pureSwapXYAntichain S ha
    have ht' : quotientType ℚ (pureSwapXYFinset S) hS' hd' hl' = 3 := by
      rw [quotientType_eq_rootCard _ _ _ _ ha',pureSwapXYFinset,normalEquivFinset,Finset.card_map]
      exact (quotientType_eq_three_iff S hS hd hl ha).mp ht
    have hn' : QuotientNearlyGorenstein ℚ (pureSwapXYFinset S) hS' hd' hl' := by
      apply (quotientNearlyGorenstein_iff_directNearlyGorenstein _ _ _ _).mpr
      apply (directNearlyGorenstein_iff_variablesInTrace _ _ _ _).mpr
      apply pureSwapXYVariablesInTrace S hd.1 hb hl
      exact (directNearlyGorenstein_iff_variablesInTrace S hS hd hl).mp
        ((quotientNearlyGorenstein_iff_directNearlyGorenstein S hS hd hl).mp hn)
    obtain ⟨R⟩ := pure_three_border_ng_residual P' hS' hd' hl' ha' ht' hn'
    let E := (finitePolynomialQuotientEquiv (k := ℚ) S hS hd).trans
      ((pureSwapXYDirectEquiv S).trans (finitePolynomialQuotientEquiv (k := ℚ)
        (pureSwapXYFinset S) hS' hd').symm)
    refine ⟨⟨b,a,hb,hd.1,pureSwapXYFinset S,R,hS',ha',hl',ht',hn',E,
      Equiv.swap 0 1,true,rfl,pureSwapXYMulEquiv,
      normalEquiv_standard_iff pureSwapXYMulEquiv S,?_,?_⟩⟩
    · intro j
      have ha1 : a ≠ 1 := by have := hd.1; omega
      have hb1 : b ≠ 1 := by omega
      have hbL : 1 < b := by omega
      fin_cases j <;> simp [coordinateGenerator,Equiv.swap_apply_def,pureSwapXYMulEquiv,pureSwapXY,
        rawSwapXY,Normal.raw,Normal.normalize,Normal.xGenerator,Normal.yGenerator,
        Normal.zGenerator,ha1,hb1,Nat.div_eq_of_lt hbL,Nat.mod_eq_of_lt hbL]
    · intro p
      dsimp [E]
      rw [AlgEquiv.apply_symm_apply]
      have hh : finitePolynomialQuotientEquiv (k := ℚ) S hS hd
          (Ideal.Quotient.mk _ (polynomialLift (k := ℚ) p)) = truncatedMonomial (k := ℚ) S p := by
        simp [polynomialLift,finitePolynomialQuotientEquiv_monomial]
      rw [hh]
      exact normalModelCongr_truncated pureSwapXYMulEquiv
        (normalEquiv_standard_iff pureSwapXYMulEquiv S) p

theorem three_border_ng_reoriented_residual (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (ht : quotientType ℚ S hS hd hl = 3)
    (hcard : (borderFinset S).card = 3)
    (hnf : ∀ q ∈ borderFinset S, ¬NormalHasFullSupport q)
    (hn : QuotientNearlyGorenstein ℚ S hS hd hl) : Nonempty (ReorientedPureResidual S) := by
  cases c with
  | zero => exact pure_three_border_reoriented_residual S hS hd hl ha ht hcard hnf hn
  | succ c => exact False.elim (rho_four_mixed_canonical_impossible S hS hd hl ha
      (by omega) ht hcard hnf hn)
end
end P23.OneTie
