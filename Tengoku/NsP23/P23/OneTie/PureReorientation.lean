import Tengoku.NsP23.P23.OneTie.RhoFourPureClassification
import Tengoku.NsP23.P23.Artin.ThreeBorderSymmetry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Genuine pure x/y reorientation, including renormalization. -/
namespace P23.OneTie
noncomputable section
open P23.Artin P23.Presentation
variable {a b : ℕ} [NeZero a] [NeZero b]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def pureXYPolynomialRename : ThreePoly ℚ ≃ₐ[ℚ] ThreePoly ℚ :=
  MvPolynomial.renameEquiv ℚ (Equiv.swap 0 1)

theorem pureXYPolynomialRename_tie :
    pureXYPolynomialRename (tiePolynomial (k := ℚ) a b 0) =
      -tiePolynomial (k := ℚ) b a 0 := by
  simp [pureXYPolynomialRename,tiePolynomial,polyX,polyY,polyZ]

def rawSwapXY (p : Raw) : Raw := ⟨p.y,p.x,p.z⟩

def pureSwapXY (p : Normal a b 0) : Normal b a 0 :=
  Normal.normalize b a 0 (Nat.pos_of_ne_zero (NeZero.ne b)) (rawSwapXY p.raw)

theorem pureSwapXY_normalize (p : Raw) :
    pureSwapXY (Normal.normalize a b 0 (Nat.pos_of_ne_zero (NeZero.ne a)) p) =
    Normal.normalize b a 0 (Nat.pos_of_ne_zero (NeZero.ne b)) (rawSwapXY p) := by
  have ha := Nat.pos_of_ne_zero (NeZero.ne a)
  have hb := Nat.pos_of_ne_zero (NeZero.ne b)
  apply Normal.ext
  · simp [pureSwapXY,rawSwapXY,Normal.raw,Normal.normalize,Nat.add_mul_mod_self_right]
  · simp only [pureSwapXY,rawSwapXY,Normal.raw,Normal.normalize]
    rw [Nat.add_mul_div_right _ _ hb]
    have h := Nat.mod_add_div p.x a
    rw [Nat.mul_comm a (p.x/a)] at h
    simp only [Nat.add_mul]
    omega
  · simp [pureSwapXY,rawSwapXY,Normal.raw,Normal.normalize]

@[simp] theorem pureSwapXY_pureSwapXY (p : Normal a b 0) : pureSwapXY (pureSwapXY p) = p := by
  change pureSwapXY (Normal.normalize b a 0 (Nat.pos_of_ne_zero (NeZero.ne b))
    (rawSwapXY p.raw)) = p
  rw [pureSwapXY_normalize]
  simpa [rawSwapXY,Normal.raw] using Normal.normalize_raw (Nat.pos_of_ne_zero (NeZero.ne a)) p

def pureSwapXYMulEquiv : Normal a b 0 ≃* Normal b a 0 where
  toFun := pureSwapXY
  invFun := pureSwapXY
  left_inv := pureSwapXY_pureSwapXY
  right_inv := pureSwapXY_pureSwapXY
  map_mul' p q := by
    change pureSwapXY (Normal.normalize a b 0 (Nat.pos_of_ne_zero (NeZero.ne a)) (p.raw+q.raw)) =
      Normal.normalize b a 0 (Nat.pos_of_ne_zero (NeZero.ne b)) ((pureSwapXY p).raw+(pureSwapXY q).raw)
    rw [pureSwapXY_normalize]
    unfold pureSwapXY
    rw [Normal.normalize_normalize_add]
    rw [add_comm (rawSwapXY p.raw)]
    rw [Normal.normalize_normalize_add]
    congr 1
    apply Raw.ext <;> simp [rawSwapXY,Raw.add,add_comm]

def normalEquivFinset {a' b' c c' : ℕ} [NeZero a']
    (e : Normal a b c ≃* Normal a' b' c') (S : Finset (Normal a b c)) := S.map e.toEmbedding

theorem normalEquiv_dvd_iff {a' b' c c' : ℕ} [NeZero a']
    (e : Normal a b c ≃* Normal a' b' c') (p q : Normal a b c) : e p ∣ e q ↔ p ∣ q := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨e.symm r,e.injective ?_⟩
    simpa using hr
  · rintro ⟨r,rfl⟩
    exact ⟨e r,map_mul e p r⟩

theorem normalEquiv_standard_iff {a' b' c c' : ℕ} [NeZero a']
    (e : Normal a b c ≃* Normal a' b' c') (S : Finset (Normal a b c)) (p : Normal a b c) :
    e p ∈ standardSet (normalEquivFinset e S) ↔ p ∈ standardSet S := by
  constructor
  · rintro ⟨q,hq,hd⟩
    obtain ⟨q',hq',rfl⟩ := Finset.mem_map.mp hq
    exact ⟨q',hq',(normalEquiv_dvd_iff e p q').mp hd⟩
  · rintro ⟨q,hq,hd⟩
    exact ⟨e q,Finset.mem_map.mpr ⟨q,hq,rfl⟩,(normalEquiv_dvd_iff e p q).mpr hd⟩

theorem normalEquiv_border_mem_iff {a' b' c c' : ℕ} [NeZero a']
    (e : Normal a b c ≃* Normal a' b' c') (S : Finset (Normal a b c))
    (hS : S.Nonempty) (ha : 2 ≤ a) (ha' : 2 ≤ a') (p : Normal a b c) :
    e p ∈ borderFinset (normalEquivFinset e S) ↔ p ∈ borderFinset S := by
  have hS' : (normalEquivFinset e S).Nonempty := by
    obtain ⟨s,hs⟩ := hS
    exact ⟨e s,Finset.mem_map.mpr ⟨s,hs,rfl⟩⟩
  rw [mem_borderFinset_iff hS',mem_borderFinset_iff hS,
    isMinimalBorder_iff_isDivisibilityMinimalKilled _ _ (variableGenerators_ne_one_of_two_le ha'),
    isMinimalBorder_iff_isDivisibilityMinimalKilled _ _ (variableGenerators_ne_one_of_two_le ha)]
  constructor
  · rintro ⟨hk,hmin⟩
    refine ⟨mt (normalEquiv_standard_iff e S p).mpr hk,?_⟩
    intro q hd hn
    exact (normalEquiv_standard_iff e S q).mp
      (hmin (e q) ((normalEquiv_dvd_iff e q p).mpr hd) (fun hh => hn (e.injective hh)))
  · rintro ⟨hk,hmin⟩
    refine ⟨mt (normalEquiv_standard_iff e S p).mp hk,?_⟩
    intro q hd hn
    have hd' : e.symm q ∣ p := (normalEquiv_dvd_iff e _ p).mp (by simpa using hd)
    have hn' : e.symm q ≠ p := fun hh => hn (by simpa using congrArg e hh)
    simpa using (normalEquiv_standard_iff e S (e.symm q)).mpr (hmin _ hd' hn')

def pureSwapXYFinset (S : Finset (Normal a b 0)) := normalEquivFinset pureSwapXYMulEquiv S

theorem pureSwapXYBorder (S : Finset (Normal a b 0))
    (hS : S.Nonempty) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    borderFinset (pureSwapXYFinset S) = (borderFinset S).map pureSwapXYMulEquiv.toEmbedding := by
  ext q
  constructor
  · intro hq
    refine Finset.mem_map.mpr ⟨pureSwapXY q,?_,by simp [pureSwapXYMulEquiv]⟩
    exact (normalEquiv_border_mem_iff pureSwapXYMulEquiv S hS ha hb _).mp (by
      simpa [pureSwapXYFinset,pureSwapXYMulEquiv] using hq)
  · rintro hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hq
    exact (normalEquiv_border_mem_iff pureSwapXYMulEquiv S hS ha hb p).mpr hp

def pureSwapXYDirectEquiv (S : Finset (Normal a b 0)) :
    MonomialArtin ℚ S ≃ₐ[ℚ] MonomialArtin ℚ (pureSwapXYFinset S) :=
  normalModelCongr pureSwapXYMulEquiv (normalEquiv_standard_iff pureSwapXYMulEquiv S)

theorem pureSwapXYAntichain (S : Finset (Normal a b 0)) (ha : IsRootAntichain S) :
    IsRootAntichain (pureSwapXYFinset S) := by
  intro p hp q hq hn hd
  obtain ⟨p',hp',rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨q',hq',rfl⟩ := Finset.mem_map.mp hq
  exact ha p' hp' q' hq' (fun he => hn (he ▸ rfl))
    ((normalEquiv_dvd_iff pureSwapXYMulEquiv p' q').mp hd)

theorem pureSwapXYLive (S : Finset (Normal a b 0))
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hl : IsLiveTie S) : IsLiveTie (pureSwapXYFinset S) := by
  have ha1 : a ≠ 1 := by omega
  have hb1 : b ≠ 1 := by omega
  have haL : 1 < a := by omega
  have hbL : 1 < b := by omega
  refine ⟨?_,?_,?_,?_⟩
  · simpa [pureSwapXYFinset,pureSwapXYMulEquiv,pureSwapXY,rawSwapXY,Normal.raw,Normal.normalize,
      Normal.yGenerator,Normal.xGenerator,ha1,hb1,Nat.div_eq_of_lt hbL,Nat.mod_eq_of_lt hbL] using
      (normalEquiv_standard_iff pureSwapXYMulEquiv S Normal.yGenerator).mpr hl.2.1
  · simpa [pureSwapXYFinset,pureSwapXYMulEquiv,pureSwapXY,rawSwapXY,Normal.raw,Normal.normalize,
      Normal.yGenerator,Normal.xGenerator,ha1,hb1] using
      (normalEquiv_standard_iff pureSwapXYMulEquiv S Normal.xGenerator).mpr hl.1
  · simpa [pureSwapXYFinset,pureSwapXYMulEquiv,pureSwapXY,rawSwapXY,Normal.raw,Normal.normalize,
      Normal.zGenerator] using
      (normalEquiv_standard_iff pureSwapXYMulEquiv S Normal.zGenerator).mpr hl.2.2.1
  · simpa [pureSwapXYFinset,pureSwapXYMulEquiv,pureSwapXY,rawSwapXY,Normal.raw,Normal.normalize,
      liveTiePoint,Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne b))] using
      (normalEquiv_standard_iff pureSwapXYMulEquiv S liveTiePoint).mpr hl.2.2.2

theorem pureSwapXYVariablesInTrace (S : Finset (Normal a b 0))
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hl : IsLiveTie S) (hv : VariablesInTrace ℚ S hl) :
    VariablesInTrace ℚ (pureSwapXYFinset S) (pureSwapXYLive S ha hb hl) := by
  have ha1 : a ≠ 1 := by omega
  have hb1 : b ≠ 1 := by omega
  have hbL : 1 < b := by omega
  rcases hv with ⟨hx,hy,hz⟩
  have hx' := directTrace_transport (pureSwapXYDirectEquiv S) hx
  have hy' := directTrace_transport (pureSwapXYDirectEquiv S) hy
  have hz' := directTrace_transport (pureSwapXYDirectEquiv S) hz
  dsimp only [pureSwapXYDirectEquiv] at hx' hy' hz'
  rw [normalModelCongr_X] at hx' hy' hz'
  refine ⟨?_,?_,?_⟩
  · simpa [pureSwapXYMulEquiv,pureSwapXY,rawSwapXY,Normal.raw,Normal.normalize,
      Normal.yGenerator,Normal.xGenerator,ha1,hb1,Nat.div_eq_of_lt hbL,Nat.mod_eq_of_lt hbL] using hy'
  · simpa [pureSwapXYMulEquiv,pureSwapXY,rawSwapXY,Normal.raw,Normal.normalize,
      Normal.yGenerator,Normal.xGenerator,ha1,hb1] using hx'
  · simpa [pureSwapXYMulEquiv,pureSwapXY,rawSwapXY,Normal.raw,Normal.normalize,Normal.zGenerator] using hz'

theorem pureXZ_reoriented_threeBorder (S : Finset (Normal a b 0))
    (P : PureXZThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (hl : IsLiveTie S) (ha : IsRootAntichain S) (ht : quotientType ℚ S hS hd hl = 3)
    (hcard : (borderFinset S).card = 3) : Nonempty (PureThreeBorderData (pureSwapXYFinset S)) := by
  have hb : 2 ≤ b := by rcases hd.2 with hm | hp <;> omega
  have hS' : (pureSwapXYFinset S).Nonempty := by
    obtain ⟨s,hs⟩ := hS
    exact ⟨pureSwapXY s,Finset.mem_map.mpr ⟨s,hs,rfl⟩⟩
  have hd' : IsLiveParameterDomain b a 0 := ⟨hb,Or.inr ⟨hd.1,rfl⟩⟩
  have hl' := pureSwapXYLive S hd.1 hb hl
  have ha' := pureSwapXYAntichain S ha
  have ht' : quotientType ℚ (pureSwapXYFinset S) hS' hd' hl' = 3 := by
    rw [quotientType_eq_rootCard _ _ _ _ ha',pureSwapXYFinset,normalEquivFinset,Finset.card_map]
    exact (quotientType_eq_three_iff S hS hd hl ha).mp ht
  have hcard' : (borderFinset (pureSwapXYFinset S)).card = 3 := by
    rw [pureSwapXYBorder S hS hd.1 hb,Finset.card_map,hcard]
  let U := P.r + P.u/b*a
  have hU : 0 < U := by dsimp [U]; have := P.r_pos; omega
  have hborder : borderFinset (pureSwapXYFinset S) =
      {(⟨P.u%b,U,0,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne b))⟩ : Normal b a 0),
        zAxis P.C,(⟨0,P.s,P.w,Nat.pos_of_ne_zero (NeZero.ne b)⟩ : Normal b a 0)} := by
    rw [pureSwapXYBorder S hS hd.1 hb,P.border]
    simp [pureSwapXYMulEquiv,pureSwapXY,rawSwapXY,Normal.raw,Normal.normalize,zAxis,U]
  have hnf : ∀ q ∈ borderFinset (pureSwapXYFinset S), ¬NormalHasFullSupport q := by
    intro q hq
    simp only [hborder,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> simp [NormalHasFullSupport,zAxis]
  have hr : 0 < P.u % b := by
    by_contra hn
    have hr0 : P.u % b = 0 := by omega
    have hY : yAxis U ∈ borderFinset (pureSwapXYFinset S) := by
      rw [hborder]
      simp [hr0,yAxis]
    exact pure_three_border_no_y_axis _ hS' hd' hl' ha' ht' hcard' hnf U hY
  refine ⟨⟨P.C,P.u%b,U,P.s,P.w,by have := hd.1; omega,hr,
    Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne b)),hU,P.s_pos,?_,P.w_pos,P.w_lt,hborder⟩⟩
  have := P.s_lt
  omega
end
end P23.OneTie
