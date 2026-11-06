import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_NegV2
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_CartierModule
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_CartierModuleHomothety

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u

open MvPolynomial in

theorem WittVector.teichmuller_mul_coeff (p : ℕ) [hp : Fact p.Prime] {A : Type u} [CommRing A]
    (a : A) (y : WittVector p A) (n : ℕ) :
    (WittVector.teichmuller p a * y).coeff n = a ^ p ^ n * y.coeff n := by

  let f : ∀ ⦃S : Type u⦄ [CommRing S], WittVector p S → WittVector p S → WittVector p S :=
    fun S _ x y => WittVector.teichmuller p (x.coeff 0) * y
  let g : ∀ ⦃S : Type u⦄ [CommRing S], WittVector p S → WittVector p S → WittVector p S :=
    fun S _ x y => WittVector.mk p fun n => x.coeff 0 ^ p ^ n * y.coeff n
  have hteich : WittVector.IsPoly p fun S _ (x : WittVector p S) =>
      WittVector.teichmuller p (x.coeff 0) := by
    refine ⟨⟨fun n => if n = 0 then X 0 else 0, ?_⟩⟩
    intro S _ x
    funext n
    cases n with
    | zero => simp [WittVector.teichmuller_coeff_zero]
    | succ n => simp [WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos n)]
  have hf : WittVector.IsPoly₂ p f :=
    @WittVector.IsPoly₂.comp p _ _ _ WittVector.mulIsPoly₂ hteich (WittVector.idIsPolyI' p)
  have hg : WittVector.IsPoly₂ p g := by
    refine ⟨⟨fun n => X ((0 : Fin 2), 0) ^ p ^ n * X ((1 : Fin 2), n), ?_⟩⟩
    intro S _ x y
    funext n
    simp [g, WittVector.peval, Function.uncurry]
  have key := WittVector.IsPoly₂.ext hf hg (fun S _ x y n => by
    simp only [f, g, map_mul, WittVector.ghostComponent_teichmuller]
    rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply, aeval_wittPolynomial,
      aeval_wittPolynomial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [WittVector.coeff_mk]
    rw [mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hi']
    ring) A (WittVector.mk p fun n => if n = 0 then a else 0) y
  have h0 : (WittVector.mk p fun n => if n = 0 then a else (0 : A)).coeff 0 = a := by simp
  simp only [f, g, h0] at key
  rw [key, WittVector.coeff_mk]

namespace MvFormalGroup

open MvPowerSeries WittLaw

theorem _root_.WittVector.mk_coeff_eq {p : ℕ} {A : Type*} [CommRing A] (x : WittVector p A) :
    WittVector.mk p (fun m => x.coeff m) = x := by
  ext m; rfl

theorem _root_.WittVector.map_peval {k : ℕ} {A B : Type*} [CommRing A] [CommRing B]
    {F : Type*} [FunLike F A B] [RingHomClass F A B]
    (φ : F) (Q : MvPolynomial (Fin k × ℕ) ℤ) (x : Fin k → ℕ → A) :
    φ (WittVector.peval Q x) = WittVector.peval Q fun i m => φ (x i m) := by
  unfold WittVector.peval
  let φ' : A →+* B := RingHomClass.toRingHom φ
  show φ' _ = _
  let ψ₁ : MvPolynomial (Fin k × ℕ) ℤ →+* B := φ'.comp (MvPolynomial.aeval (Function.uncurry x)).toRingHom
  let ψ₂ : MvPolynomial (Fin k × ℕ) ℤ →+* B :=
    (MvPolynomial.aeval (Function.uncurry fun i m => φ (x i m))).toRingHom
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun im => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (ψ₁.comp MvPolynomial.C) (ψ₂.comp MvPolynomial.C)) r
    · rcases im with ⟨i, m⟩
      simp [ψ₁, ψ₂, φ', Function.uncurry]
  exact RingHom.congr_fun hψ Q

theorem _root_.WittVector.peval_X {k : ℕ} (R : Type*) [CommRing R]
    (Q : MvPolynomial (Fin k × ℕ) ℤ) :
    WittVector.peval Q (fun i m => (MvPolynomial.X (i, m) : MvPolynomial (Fin k × ℕ) R)) =
      MvPolynomial.map (Int.castRingHom R) Q := by
  unfold WittVector.peval
  let ψ₁ : MvPolynomial (Fin k × ℕ) ℤ →+* MvPolynomial (Fin k × ℕ) R :=
    (MvPolynomial.aeval (Function.uncurry fun i m =>
      (MvPolynomial.X (i, m) : MvPolynomial (Fin k × ℕ) R))).toRingHom
  have hψ : ψ₁ = MvPolynomial.map (Int.castRingHom R) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun im => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (ψ₁.comp MvPolynomial.C)
        ((MvPolynomial.map (Int.castRingHom R)).comp MvPolynomial.C)) r
    · rcases im with ⟨i, m⟩
      simp [ψ₁, Function.uncurry]
  exact RingHom.congr_fun hψ Q

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R]

abbrev cVec {τ : Type} (w : WittVector p R) : WittVector p (MvPolynomial τ R) :=
  WittVector.map (MvPolynomial.C : R →+* MvPolynomial τ R) w

def mulPoly (w : WittVector p R) (n : ℕ) : MvPolynomial ℕ R :=
  (cVec p w * WittVector.mk p (MvPolynomial.X : ℕ → MvPolynomial ℕ R)).coeff n

def mulFam (w : WittVector p R) : ℕ → MvPowerSeries ℕ R := fun n => (mulPoly p w n : MvPowerSeries ℕ R)

variable {p}

@[simp] theorem mulFam_apply (w : WittVector p R) (n : ℕ) :
    mulFam p w n = (mulPoly p w n : MvPowerSeries ℕ R) := rfl

omit hp in

theorem coe_aeval {σ τ : Type*} (y : σ → MvPolynomial τ R) (P : MvPolynomial σ R) :
    ((MvPolynomial.aeval y P : MvPolynomial τ R) : MvPowerSeries τ R) =
      subst (fun i => (y i : MvPowerSeries τ R)) (P : MvPowerSeries σ R) := by
  rw [subst_coe]
  let ψ₁ : MvPolynomial σ R →ₐ[R] MvPowerSeries τ R :=
    (MvPolynomial.coeToMvPowerSeries.algHom R).comp (MvPolynomial.aeval y)
  let ψ₂ : MvPolynomial σ R →ₐ[R] MvPowerSeries τ R :=
    MvPolynomial.aeval fun i => (y i : MvPowerSeries τ R)
  have hψ : ψ₁ = ψ₂ := MvPolynomial.algHom_ext fun i => by simp [ψ₁, ψ₂]
  exact AlgHom.congr_fun hψ P

omit hp in

theorem coe_peval {k : ℕ} {τ : Type*} (Q : MvPolynomial (Fin k × ℕ) ℤ) (x : Fin k → ℕ → MvPolynomial τ R) :
    subst (fun im : Fin k × ℕ => (x im.1 im.2 : MvPowerSeries τ R))
      ((MvPolynomial.map (Int.castRingHom R) Q : MvPolynomial (Fin k × ℕ) R) :
        MvPowerSeries (Fin k × ℕ) R) =
      ((WittVector.peval Q x : MvPolynomial τ R) : MvPowerSeries τ R) := by
  rw [subst_coe]
  unfold WittVector.peval
  let ψ₁ : MvPolynomial (Fin k × ℕ) ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.aeval fun im : Fin k × ℕ => (x im.1 im.2 : MvPowerSeries τ R)).toRingHom.comp
      (MvPolynomial.map (Int.castRingHom R))
  let ψ₂ : MvPolynomial (Fin k × ℕ) ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.coeToMvPowerSeries.ringHom (σ := τ) (R := R)).comp
      (MvPolynomial.aeval (Function.uncurry x)).toRingHom
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun im => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (ψ₁.comp MvPolynomial.C) (ψ₂.comp MvPolynomial.C)) r
    · rcases im with ⟨i, m⟩
      simp [ψ₁, ψ₂, Function.uncurry]
  exact RingHom.congr_fun hψ Q

@[simp] theorem cVec_coeff {τ : Type} (w : WittVector p R) (m : ℕ) :
    (cVec p (τ := τ) w).coeff m = MvPolynomial.C (w.coeff m) :=
  WittVector.map_coeff _ _ _

@[simp] theorem cVec_add {τ : Type} (w₁ w₂ : WittVector p R) :
    cVec p (τ := τ) (w₁ + w₂) = cVec p w₁ + cVec p w₂ := map_add _ _ _

@[simp] theorem cVec_mul {τ : Type} (w₁ w₂ : WittVector p R) :
    cVec p (τ := τ) (w₁ * w₂) = cVec p w₁ * cVec p w₂ := map_mul _ _ _

@[simp] theorem cVec_one {τ : Type} : cVec p (τ := τ) (1 : WittVector p R) = 1 := map_one _

@[simp] theorem cVec_zero {τ : Type} : cVec p (τ := τ) (0 : WittVector p R) = 0 := map_zero _

theorem mulPoly_eq_peval (w : WittVector p R) (n : ℕ) :
    mulPoly p w n = WittVector.peval (WittVector.wittMul p n)
      ![fun m => MvPolynomial.C (w.coeff m), MvPolynomial.X] := by
  rw [mulPoly, WittVector.mul_coeff]
  congr 1

theorem aeval_mulPoly {τ : Type} (w : WittVector p R) (y : ℕ → MvPolynomial τ R) (n : ℕ) :
    MvPolynomial.aeval y (mulPoly p w n) = (cVec p w * WittVector.mk p y).coeff n := by
  rw [mulPoly, WittVector.mul_coeff, WittVector.mul_coeff,
    WittVector.map_peval (MvPolynomial.aeval y : MvPolynomial ℕ R →ₐ[R] MvPolynomial τ R)]
  congr 1
  funext i m
  fin_cases i
  · show MvPolynomial.aeval y ((cVec p (τ := ℕ) w).coeff m) = (cVec p (τ := τ) w).coeff m
    rw [cVec_coeff, cVec_coeff, MvPolynomial.aeval_C]
    rfl
  · show MvPolynomial.aeval y ((WittVector.mk p MvPolynomial.X).coeff m) = (WittVector.mk p y).coeff m
    rw [WittVector.coeff_mk, WittVector.coeff_mk, MvPolynomial.aeval_X]

theorem mulPoly_add (w₁ w₂ : WittVector p R) (n : ℕ) :
    mulPoly p (w₁ + w₂) n = WittVector.peval (WittVector.wittAdd p n) ![mulPoly p w₁, mulPoly p w₂] := by
  rw [mulPoly, cVec_add, add_mul, WittVector.add_coeff]
  rfl

theorem mulPoly_mul (w₁ w₂ : WittVector p R) (n : ℕ) :
    mulPoly p (w₁ * w₂) n = MvPolynomial.aeval (mulPoly p w₂) (mulPoly p w₁ n) := by
  rw [aeval_mulPoly, mulPoly, cVec_mul, mul_assoc]
  show _ = (cVec p w₁ * WittVector.mk p (fun m =>
    (cVec p w₂ * WittVector.mk p (MvPolynomial.X : ℕ → MvPolynomial ℕ R)).coeff m)).coeff n
  rw [WittVector.mk_coeff_eq]

theorem mulPoly_one (n : ℕ) : mulPoly p (1 : WittVector p R) n = MvPolynomial.X n := by
  rw [mulPoly, cVec_one, one_mul, WittVector.coeff_mk]

theorem mulPoly_zero (n : ℕ) : mulPoly p (0 : WittVector p R) n = 0 := by
  rw [mulPoly, cVec_zero, zero_mul, WittVector.zero_coeff]

def verPoly (R : Type u) [CommRing R] : ℕ → MvPolynomial ℕ R
  | 0 => 0
  | n + 1 => MvPolynomial.X n

omit hp in
@[simp] theorem verPoly_zero : verPoly R 0 = 0 := rfl

omit hp in
@[simp] theorem verPoly_succ (n : ℕ) : verPoly R (n + 1) = MvPolynomial.X n := rfl

omit hp in

theorem isWeightedHomogeneous_peval_C_X {N : ℕ} {Q : MvPolynomial (Fin 2 × ℕ) ℤ}
    (hQ : MvPolynomial.IsWeightedHomogeneous (weight p ![0, 1]) Q N) (c : ℕ → R) :
    MvPolynomial.IsWeightedHomogeneous (fun m => p ^ m)
      (WittVector.peval Q ![fun m => MvPolynomial.C (c m), (MvPolynomial.X : ℕ → MvPolynomial ℕ R)])
      N := by
  classical
  unfold WittVector.peval
  set g : Fin 2 × ℕ → MvPolynomial ℕ R :=
    Function.uncurry ![fun m => MvPolynomial.C (c m), (MvPolynomial.X : ℕ → MvPolynomial ℕ R)]
    with hg
  rw [MvPolynomial.as_sum Q, map_sum]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun e he => ?_
  have hwe : Finsupp.weight (weight p ![0, 1]) e = N := hQ (MvPolynomial.mem_support_iff.mp he)
  rw [MvPolynomial.aeval_monomial, eq_intCast, ← map_intCast (MvPolynomial.C (σ := ℕ) (R := R))]
  have hprod : MvPolynomial.IsWeightedHomogeneous (fun m => p ^ m)
      (e.prod fun im k => g im ^ k) N := by
    rw [Finsupp.prod, ← hwe, Finsupp.weight_apply, Finsupp.sum]
    refine MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun im _ => ?_
    rcases im with ⟨i, m⟩
    fin_cases i
    ·
      have h := (MvPolynomial.isWeightedHomogeneous_C (fun m => p ^ m) (c m)).pow (e (0, m))
      simp only [smul_zero] at h
      simpa [g, weight] using h
    · have h := (MvPolynomial.isWeightedHomogeneous_X (R := R) (fun m => p ^ m) m).pow (e (1, m))
      simpa [g, weight, smul_eq_mul, mul_comm] using h
  have := (MvPolynomial.isWeightedHomogeneous_C (fun m => p ^ m)
    ((MvPolynomial.coeff e Q : ℤ) : R)).mul hprod
  rwa [zero_add] at this

theorem isWeightedHomogeneous_mulPoly (w : WittVector p R) (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun m => p ^ m) (mulPoly p w n) (p ^ n) := by
  rw [mulPoly_eq_peval]
  exact isWeightedHomogeneous_peval_C_X (isWeightedHomogeneous_wittMul p n) _

theorem weight_eq_of_coeff_mulFam_ne_zero (w : WittVector p R) {n : ℕ} {e : ℕ →₀ ℕ}
    (h : coeff e (mulFam p w n) ≠ 0) : Finsupp.weight (fun m => p ^ m) e = p ^ n := by
  rw [mulFam_apply, MvPolynomial.coeff_coe] at h
  exact isWeightedHomogeneous_mulPoly w n h

theorem constantCoeff_mulFam (w : WittVector p R) (n : ℕ) : (mulFam p w n).constantCoeff = 0 := by
  by_contra h
  have h' : coeff (0 : ℕ →₀ ℕ) (mulFam p w n) ≠ 0 := by
    rwa [coeff_zero_eq_constantCoeff_apply]
  have hw := weight_eq_of_coeff_mulFam_ne_zero w h'
  rw [map_zero] at hw
  exact absurd hw.symm (pow_ne_zero n hp.out.ne_zero)

theorem hasSubst_mulFam (w : WittVector p R) : HasSubst (mulFam p w) := by
  refine ⟨fun n => by rw [constantCoeff_mulFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight (fun m => p ^ m) e)).subset fun n hn => ?_
  have hw := weight_eq_of_coeff_mulFam_ne_zero w hn
  show n < Finsupp.weight (fun m => p ^ m) e
  rw [hw]
  exact Nat.lt_pow_self hp.out.one_lt

def xVec (R : Type u) [CommRing R] (i : Fin 2) : WittVector p (MvPolynomial (Fin 2 × ℕ) R) :=
  WittVector.mk p fun m => MvPolynomial.X (i, m)

def addPolyR (R : Type u) [CommRing R] (m : ℕ) : MvPolynomial (Fin 2 × ℕ) R :=
  MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p m)

theorem coe_addPolyR (m : ℕ) :
    (addPolyR (p := p) R m : MvPowerSeries (Fin 2 × ℕ) R) = addFam p R m := rfl

omit hp in
@[simp] theorem xVec_coeff (i : Fin 2) (m : ℕ) :
    (xVec (p := p) R i).coeff m = MvPolynomial.X (i, m) := rfl

theorem xVec_add : xVec (p := p) R 0 + xVec R 1 = WittVector.mk p (addPolyR (p := p) R) := by
  refine WittVector.ext fun m => ?_
  rw [WittVector.add_coeff]
  show WittVector.peval (WittVector.wittAdd p m) ![(xVec (p := p) R 0).coeff, (xVec (p := p) R 1).coeff] =
    addPolyR (p := p) R m
  rw [addPolyR, ← WittVector.peval_X R (WittVector.wittAdd p m)]
  congr 1
  funext i k
  fin_cases i <;> rfl

theorem pairFam_mulFam (w : WittVector p R) :
    pairFam (mulFam p w) = fun im : Fin 2 × ℕ =>
      (((cVec p w * xVec R im.1).coeff im.2 : MvPolynomial (Fin 2 × ℕ) R) :
        MvPowerSeries (Fin 2 × ℕ) R) := by
  funext ⟨i, m⟩
  rw [pairFam_apply, mulFam_apply, xVec, ← aeval_mulPoly, coe_aeval]
  congr 1
  funext k
  exact (MvPolynomial.coe_X _).symm

theorem subst_addFam_mulFam (w : WittVector p R) (n : ℕ) :
    subst (addFam p R) (mulFam p w n) =
      (((cVec p w * (xVec R 0 + xVec R 1)).coeff n : MvPolynomial (Fin 2 × ℕ) R) :
        MvPowerSeries (Fin 2 × ℕ) R) := by
  have h : addFam p R = fun i => (addPolyR (p := p) R i : MvPowerSeries (Fin 2 × ℕ) R) := rfl
  rw [h, mulFam_apply, ← coe_aeval, aeval_mulPoly, xVec_add]

theorem isEndo_mulFam (w : WittVector p R) : IsEndo p (mulFam p w) := by
  refine ⟨hasSubst_mulFam w, constantCoeff_mulFam w, fun n => ?_⟩

  have hR : subst (pairFam (mulFam p w)) (addFam p R n) =
      (((cVec p w * xVec R 0 + cVec p w * xVec R 1).coeff n : MvPolynomial (Fin 2 × ℕ) R) :
        MvPowerSeries (Fin 2 × ℕ) R) := by
    have key := coe_peval (R := R) (WittVector.wittAdd p n)
      (fun i m => (cVec p w * xVec (p := p) R i).coeff m)
    rw [WittVector.add_coeff, pairFam_mulFam, ← coe_addPolyR, addPolyR]
    refine key.trans ?_
    congr 2
    funext i
    fin_cases i <;> rfl
  rw [subst_addFam_mulFam, hR, mul_add]

theorem subst_mulFam_mulFam (w₁ w₂ : WittVector p R) (n : ℕ) :
    subst (mulFam p w₂) (mulFam p w₁ n) = mulFam p (w₁ * w₂) n := by
  rw [mulFam_apply, mulFam_apply, mulPoly_mul, coe_aeval]
  rfl

theorem mulFam_add (w₁ w₂ : WittVector p R) (n : ℕ) :
    mulFam p (w₁ + w₂) n = subst (fun im : Fin 2 × ℕ =>
      (Fin.cases (mulFam p w₁ im.2) (fun _ => mulFam p w₂ im.2) im.1 : MvPowerSeries ℕ R))
        (addFam p R n) := by
  have hfun : (fun im : Fin 2 × ℕ =>
      (Fin.cases (mulFam p w₁ im.2) (fun _ => mulFam p w₂ im.2) im.1 : MvPowerSeries ℕ R)) =
      fun im : Fin 2 × ℕ => ((![mulPoly p w₁, mulPoly p w₂] im.1 im.2 : MvPolynomial ℕ R) :
        MvPowerSeries ℕ R) := by
    funext ⟨i, m⟩
    fin_cases i <;> rfl
  rw [hfun, addFam, coe_peval, mulFam_apply, mulPoly_add]

theorem mulFam_one : mulFam p (1 : WittVector p R) = fun n => X n := by
  funext n
  rw [mulFam_apply, mulPoly_one, MvPolynomial.coe_X]

theorem mulFam_zero : mulFam p (0 : WittVector p R) = fun _ => 0 := by
  funext n
  rw [mulFam_apply, mulPoly_zero, MvPolynomial.coe_zero]

end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}

def wittSMul [Φ.IsComm] (w : WittVector p R) : CartierModule p Φ →+ CartierModule p Φ :=
  precomp (WittLaw.isEndo_mulFam w)

@[simp] theorem toPowerSeries_wittSMul [Φ.IsComm] (w : WittVector p R) (f : CartierModule p Φ) :
    (wittSMul w f).toPowerSeries = fun j => subst (WittLaw.mulFam p w) (f.toPowerSeries j) := rfl

theorem wittSMul_one [Φ.IsComm] (f : CartierModule p Φ) : wittSMul (1 : WittVector p R) f = f := by
  apply CartierModule.ext
  funext j
  rw [toPowerSeries_wittSMul, WittLaw.mulFam_one]
  exact congrFun subst_self _

theorem wittSMul_zero_left [Φ.IsComm] (f : CartierModule p Φ) :
    wittSMul (0 : WittVector p R) f = 0 := by
  apply CartierModule.ext
  funext j
  rw [toPowerSeries_wittSMul, WittLaw.mulFam_zero]
  exact subst_zero_of_constantCoeff_eq_zero (f.constantCoeff_eq_zero j)

theorem wittSMul_mul [Φ.IsComm] (w₁ w₂ : WittVector p R) (f : CartierModule p Φ) :
    wittSMul (w₁ * w₂) f = wittSMul w₁ (wittSMul w₂ f) := by
  apply CartierModule.ext
  funext j
  show (precomp _ f).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, toPowerSeries_precomp]
  show subst (WittLaw.mulFam p (w₁ * w₂)) (f.toPowerSeries j) = _
  congr 1
  funext n
  rw [WittLaw.subst_mulFam_mulFam, mul_comm]

theorem wittSMul_add_left [Φ.IsComm] (w₁ w₂ : WittVector p R) (f : CartierModule p Φ) :
    wittSMul (w₁ + w₂) f = wittSMul w₁ f + wittSMul w₂ f := by
  apply CartierModule.ext
  funext j
  have hf := f.constantCoeff_eq_zero
  have hS : HasSubst (fun im : Fin 2 × ℕ => (Fin.cases (WittLaw.mulFam p w₁ im.2)
      (fun _ => WittLaw.mulFam p w₂ im.2) im.1 : MvPowerSeries ℕ R)) :=
    WittLaw.hasSubst_finCases (WittLaw.hasSubst_mulFam w₁) (WittLaw.hasSubst_mulFam w₂)
  have hfam : WittLaw.mulFam p (w₁ + w₂) = fun k => subst (fun im : Fin 2 × ℕ =>
      (Fin.cases (WittLaw.mulFam p w₁ im.2) (fun _ => WittLaw.mulFam p w₂ im.2) im.1 :
        MvPowerSeries ℕ R)) (WittLaw.addFam p R k) :=
    funext (WittLaw.mulFam_add w₁ w₂)
  rw [toPowerSeries_wittSMul, toPowerSeries_add]
  show subst (WittLaw.mulFam p (w₁ + w₂)) (f.toPowerSeries j) = _
  rw [hfam, ← subst_comp_subst_apply (hasSubst_addFam p R) hS, f.subst_addFam,
    subst_subst_elim Φ (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf) hS]
  congr 1
  funext s
  rcases s with l | l
  · show subst _ (subst (blk 0) (f.toPowerSeries l)) = (wittSMul w₁ f).toPowerSeries l
    rw [subst_comp_subst_apply (hasSubst_blk 0) hS]
    congr 1
    funext m
    exact subst_X hS ((0 : Fin 2), m)
  · show subst _ (subst (blk 1) (f.toPowerSeries l)) = (wittSMul w₂ f).toPowerSeries l
    rw [subst_comp_subst_apply (hasSubst_blk 1) hS]
    congr 1
    funext m
    exact subst_X hS ((1 : Fin 2), m)

instance instModuleWittVector [Φ.IsComm] : Module (WittVector p R) (CartierModule p Φ) where
  smul w f := wittSMul w f
  one_smul := wittSMul_one
  mul_smul := wittSMul_mul
  smul_zero w := map_zero (wittSMul w)
  smul_add w := map_add (wittSMul w)
  add_smul := wittSMul_add_left
  zero_smul := wittSMul_zero_left

@[simp] theorem toPowerSeries_smul_witt [Φ.IsComm] (w : WittVector p R) (f : CartierModule p Φ) :
    (w • f).toPowerSeries = fun j => subst (WittLaw.mulFam p w) (f.toPowerSeries j) := rfl

theorem map_smul_witt [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (w : WittVector p R)
    (f : CartierModule p Φ) : map φ (w • f) = w • map φ f :=
  map_precomp φ _ f

def mapLinear [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') :
    CartierModule p Φ →ₗ[WittVector p R] CartierModule p Φ' :=
  { map φ with map_smul' := fun w f => map_smul_witt φ w f }

@[simp] theorem mapLinear_apply [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    mapLinear φ f = map φ f := rfl

namespace Examples

end Examples

end CartierModule

end MvFormalGroup

end
