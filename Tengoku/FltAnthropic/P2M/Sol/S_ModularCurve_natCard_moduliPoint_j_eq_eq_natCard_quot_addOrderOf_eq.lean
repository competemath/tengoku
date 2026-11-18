import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ModuliPoint
import Tengoku.FltAnthropic.Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_natCard_moduliPoint_j_eq_eq_natCard_quot_addOrderOf_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_natCard_moduliPoint_j_eq_eq_natCard_quot_addOrderOf_eq

set_option autoImplicit false
set_option maxHeartbeats 4800000

open WeierstrassCurve WeierstrassCurve.Affine

namespace P2MWs13
namespace ModuliFibre

variable {K : Type*} [Field K]

/--
@isnad1 id=injectiv.0h2v.s4.e988a5c466af from=translated src=- shape=5922b6b2 vocab=58530f4b
-/
theorem vcX_injective (C : VariableChange K) : Function.Injective (vcX C) := fun a b h => by
  simpa using congrArg (vcXInv C) h

/--
@isnad1 id=injectiv.0h3v.s4.59285b71052c from=translated src=- shape=7d54893b vocab=d6b18354
-/
theorem vcY_injective (C : VariableChange K) (x' : K) : Function.Injective (vcY C x') := fun a b h => by
  simpa using congrArg (vcYInv C (vcX C x')) h

/--
@isnad1 id=eq.0h4v.s5.f422ac622bad from=translated src=- shape=7f4d2bc9 vocab=7eff00d3
-/
theorem vcX_mul (γ₁ γ₂ : VariableChange K) (x : K) :
    vcX (γ₂ * γ₁) x = vcX γ₁ (vcX γ₂ x) := by
  simp only [WeierstrassCurve.Affine.vcX, VariableChange.mul_def, Units.val_mul]
  ring

/--
@isnad1 id=eq.0h5v.s6.56df4eb0ecd2 from=translated src=- shape=ed2a821f vocab=f1d4a98e
-/
theorem vcY_mul (γ₁ γ₂ : VariableChange K) (x y : K) :
    vcY (γ₂ * γ₁) x y = vcY γ₁ (vcX γ₂ x) (vcY γ₂ x y) := by
  simp only [WeierstrassCurve.Affine.vcY, WeierstrassCurve.Affine.vcX,
    VariableChange.mul_def, Units.val_mul]
  ring

/--
@isnad1 id=eq.0h4v.s5.53c551a57b1e from=translated src=- shape=bfdf2488 vocab=3c6a194e
-/
theorem vcXInv_mul (γ₁ γ₂ : VariableChange K) (x : K) :
    vcXInv (γ₂ * γ₁) x = vcXInv γ₂ (vcXInv γ₁ x) := by
  refine vcX_injective (γ₂ * γ₁) ?_
  rw [vcX_vcXInv, vcX_mul, vcX_vcXInv, vcX_vcXInv]

/--
@isnad1 id=eq.0h5v.s6.af12acd79189 from=translated src=- shape=48edf284 vocab=a0811577
-/
theorem vcYInv_mul (γ₁ γ₂ : VariableChange K) (x y : K) :
    vcYInv (γ₂ * γ₁) x y = vcYInv γ₂ (vcXInv γ₁ x) (vcYInv γ₁ x y) := by
  refine vcY_injective (γ₂ * γ₁) (vcXInv (γ₂ * γ₁) x) ?_
  rw [vcY_vcYInv, vcXInv_mul, vcY_mul, vcX_vcXInv, vcY_vcYInv, vcY_vcYInv]

/--
@isnad1 id=eq.0h2v.s5.96f9891142dd from=translated src=- shape=fb780b06 vocab=e839589e
-/
theorem vcXInv_one (x : K) : vcXInv (1 : VariableChange K) x = x := by
  simp [WeierstrassCurve.Affine.vcXInv, VariableChange.one_def]

/--
@isnad1 id=eq.0h3v.s5.441b382e416a from=translated src=- shape=c3aee2bf vocab=5345b7c1
-/
theorem vcYInv_one (x y : K) : vcYInv (1 : VariableChange K) x y = y := by
  simp [WeierstrassCurve.Affine.vcYInv, VariableChange.one_def]

variable [DecidableEq K]

/--
@isnad1 id=eq.1h5v.s6.e3bf27b7d629 from=translated src=- shape=971f5536 vocab=7b130d02
-/
theorem vcInvFun_some (γ : VariableChange K) (W : WeierstrassCurve.Affine K) {x y : K} (h : W.Nonsingular x y) :
    Point.vcInvFun γ W (Point.some x y h) = Point.some (vcXInv γ x) (vcYInv γ x y)
      ((nonsingular_variableChange_iff (vcXInv γ x) (vcYInv γ x y)).mpr (by rwa [vcX_vcXInv, vcY_vcYInv])) := rfl

/--
@isnad1 id=heq.2h6v.s7.823c43dacdb2 from=translated src=- shape=9762855e vocab=70f09b7e
-/
theorem Point.heq_vcInvFun (γ : VariableChange K) {V V' : WeierstrassCurve.Affine K}
    (hV : V' = V) {S : V'.Point} {T : V.Point} (h : HEq S T) :
    HEq (Point.vcInvFun γ V' S) (Point.vcInvFun γ V T) := by
  subst hV
  rw [eq_of_heq h]

noncomputable def vcInvHom (γ : VariableChange K) (W : WeierstrassCurve.Affine K) : W.Point →+ (γ • W).toAffine.Point :=
  AddMonoidHom.mk' (Point.vcInvFun γ W) (WeierstrassCurve.Affine.Point.vcInvFun_add γ W)

/--
@isnad1 id=injectiv.0h3v.s5.482761e50096 from=translated src=- shape=cba06c80 vocab=808e146f
-/
theorem vcInvFun_injective (γ : VariableChange K) (W : WeierstrassCurve.Affine K) :
    Function.Injective (Point.vcInvFun γ W) :=
  (Point.vcFun_rightInverse (C := γ) (W := W)).injective

/--
@isnad1 id=eq.0h4v.s7.c5959ffe3182 from=translated src=- shape=1082f5d6 vocab=d2ae226b
-/
theorem addOrderOf_vcInvFun (γ : VariableChange K) (W : WeierstrassCurve.Affine K) (P : W.Point) :
    addOrderOf (Point.vcInvFun γ W P) = addOrderOf P :=
  addOrderOf_injective (vcInvHom γ W) (vcInvFun_injective γ W) P

/--
@isnad1 id=eq.0h5v.s8.23b782afe306 from=translated src=- shape=1eaa28ac vocab=ea715075
-/
theorem vcInvFun_nsmul (γ : VariableChange K) (W : WeierstrassCurve.Affine K) (k : ℕ) (P : W.Point) :
    Point.vcInvFun γ W (k • P) = k • Point.vcInvFun γ W P :=
  map_nsmul (vcInvHom γ W) k P

/--
@isnad1 id=heq.0h5v.s7.ddc7e40ff1a6 from=translated src=- shape=f17f6ee0 vocab=81ef449f
-/
theorem vcInvFun_mul_heq (γ₁ γ₂ : VariableChange K) (W : WeierstrassCurve.Affine K) (P : W.Point) :
    HEq (Point.vcInvFun (γ₂ * γ₁) W P)
      (Point.vcInvFun γ₂ ((γ₁ • W : WeierstrassCurve K).toAffine) (Point.vcInvFun γ₁ W P)) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ModularCurve.Point.heq_zero (mul_smul γ₂ γ₁ W)
  · simp only [vcInvFun_some]
    exact ModularCurve.Point.heq_some (mul_smul γ₂ γ₁ W) (vcXInv_mul γ₁ γ₂ x) (vcYInv_mul γ₁ γ₂ x y)

/--
@isnad1 id=heq.0h4v.s7.97d9aeadc57f from=translated src=- shape=5686b263 vocab=1ad4e830
-/
theorem vcInvFun_inv_heq (γ : VariableChange K) (W : WeierstrassCurve.Affine K) (P : W.Point) :
    HEq (Point.vcInvFun γ⁻¹ ((γ • W : WeierstrassCurve K).toAffine) (Point.vcInvFun γ W P)) P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ModularCurve.Point.heq_zero (inv_smul_smul γ W)
  · simp only [vcInvFun_some]
    refine ModularCurve.Point.heq_some (inv_smul_smul γ W) ?_ ?_
    · rw [← vcXInv_mul, inv_mul_cancel, vcXInv_one]
    · rw [← vcYInv_mul, inv_mul_cancel, vcYInv_one]

/--
@isnad1 id=heq.0h3v.s6.a087e03aecad from=translated src=- shape=2b706cef vocab=70f09b7e
-/
theorem vcInvFun_one_heq (W : WeierstrassCurve.Affine K) (P : W.Point) :
    HEq (Point.vcInvFun (1 : VariableChange K) W P) P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ModularCurve.Point.heq_zero (one_smul _ W)
  · simp only [vcInvFun_some]
    exact ModularCurve.Point.heq_some (one_smul _ W) (vcXInv_one x) (vcYInv_one x y)

omit [DecidableEq K] in
/--
@isnad1 id=ex.2h4v.s6.0e235f2fe92f from=translated src=- shape=0bfa79a1 vocab=fb0150ac
-/
theorem exists_nsmul_nsmul_eq_self {M : Type*} [AddCommGroup M] {N k : ℕ}
    (hk : k.Coprime N) {x : M} (hx : addOrderOf x = N) :
    ∃ m : ℕ, m.Coprime N ∧ m • k • x = x := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have hk1 : k = 1 := Nat.coprime_zero_right k |>.mp hk
    exact ⟨1, Nat.coprime_one_left 0, by rw [hk1, one_nsmul, one_nsmul]⟩
  by_cases hN1 : N = 1
  · have hx0 : x = 0 := by
      have h1 : addOrderOf x = 1 := by rw [hx, hN1]
      exact AddMonoid.addOrderOf_eq_one_iff.mp h1
    exact ⟨1, Nat.coprime_one_left N, by rw [hx0, smul_zero, smul_zero]⟩
  · have h1N : 1 < N := by omega
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk h1N
    have hNx : N • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
    have hdiv : N * (k * m / N) + 1 = k * m := by
      have h := Nat.div_add_mod (k * m) N
      rw [hm] at h
      exact h
    refine ⟨m, ?_, ?_⟩
    · have hdm : Nat.gcd m N ∣ N * (k * m / N) + 1 := by
        rw [hdiv]
        exact Dvd.dvd.mul_left (Nat.gcd_dvd_left m N) k
      have hdN : Nat.gcd m N ∣ N * (k * m / N) :=
        Dvd.dvd.mul_right (Nat.gcd_dvd_right m N) _
      exact Nat.dvd_one.mp ((Nat.dvd_add_right hdN).mp hdm)
    · rw [← mul_nsmul x k m, ← hdiv, add_nsmul, mul_nsmul x N (k * m / N), hNx, smul_zero,
        zero_add, one_nsmul]

open ModularCurve

variable {N : ℕ}

/--
@isnad1 id=step.0h3v.s4.85ee01564b0a from=translated src=- shape=e2d2dbc3 vocab=17a1763f
-/
theorem step_refl (P : Gamma0Pair N K) : Gamma0Pair.Step P P :=
  ⟨1, one_smul _ _, 1, Nat.coprime_one_left N,
    ((heq_of_eq (one_nsmul _)).trans (vcInvFun_one_heq P.toCurve.toAffine P.gen)).symm⟩

/--
@isnad1 id=step.1h4v.s5.547b895d1078 from=translated src=- shape=c9ab4263 vocab=17a1763f
-/
theorem step_symm {P Q : Gamma0Pair N K} (h : Gamma0Pair.Step P Q) : Gamma0Pair.Step Q P := by
  obtain ⟨γ, hγ, k, hk, hgen⟩ := h
  obtain ⟨QC, Qell, Qgen, Qord⟩ := Q
  subst hγ
  have hg : Qgen = k • Point.vcInvFun γ P.toCurve.toAffine P.gen := eq_of_heq hgen
  obtain ⟨m, hm, hmx⟩ := exists_nsmul_nsmul_eq_self hk P.addOrderOf_gen
  refine ⟨γ⁻¹, inv_smul_smul γ P.toCurve, m, hm, ?_⟩
  show HEq P.gen (m • Point.vcInvFun γ⁻¹ (γ • P.toCurve).toAffine Qgen)
  rw [hg, vcInvFun_nsmul]
  refine (heq_of_eq hmx.symm).trans ?_
  exact ModularCurve.Point.heq_nsmul (inv_smul_smul γ P.toCurve).symm m
    (ModularCurve.Point.heq_nsmul (inv_smul_smul γ P.toCurve).symm k
      (vcInvFun_inv_heq γ P.toCurve.toAffine P.gen).symm)

/--
@isnad1 id=step.2h5v.s5.33fc0cc692cc from=translated src=- shape=df7bb567 vocab=17a1763f
-/
theorem step_trans {P Q R : Gamma0Pair N K} (hPQ : Gamma0Pair.Step P Q)
    (hQR : Gamma0Pair.Step Q R) : Gamma0Pair.Step P R := by
  obtain ⟨γ₁, hγ₁, k₁, hk₁, hgen₁⟩ := hPQ
  obtain ⟨γ₂, hγ₂, k₂, hk₂, hgen₂⟩ := hQR
  refine ⟨γ₂ * γ₁, by rw [mul_smul, hγ₁, hγ₂], k₂ * k₁,
    Nat.coprime_mul_iff_left.mpr ⟨hk₂, hk₁⟩, ?_⟩
  have hVQ : (γ₂ • Q.toCurve : WeierstrassCurve K) = γ₂ • (γ₁ • P.toCurve) := by rw [hγ₁]
  have hV2 : (γ₂ • (γ₁ • P.toCurve) : WeierstrassCurve K) = (γ₂ * γ₁) • P.toCurve :=
    (mul_smul γ₂ γ₁ P.toCurve).symm
  refine hgen₂.trans ?_
  refine HEq.trans (ModularCurve.Point.heq_nsmul hVQ k₂
    ((Point.heq_vcInvFun γ₂ hγ₁.symm hgen₁).trans
      (heq_of_eq (vcInvFun_nsmul γ₂ _ k₁ _)))) ?_
  exact (heq_of_eq (smul_smul k₂ k₁ _)).trans
    (ModularCurve.Point.heq_nsmul hV2 (k₂ * k₁) (vcInvFun_mul_heq γ₁ γ₂ P.toCurve.toAffine P.gen).symm)

/--
@isnad1 id=equivale.0h2v.s4.26d3aabb4115 from=translated src=- shape=69951633 vocab=04995623
-/
theorem stepEquivalence : Equivalence (Gamma0Pair.Step (N := N) (L := K)) :=
  ⟨step_refl, step_symm, step_trans⟩

/--
@isnad1 id=iff.0h4v.s6.26960ac92f73 from=translated src=- shape=28a334b1 vocab=517a773d
-/
theorem mk_eq_mk_iff_step {P Q : Gamma0Pair N K} :
    (Quot.mk _ P : ModuliPoint N K) = Quot.mk _ Q ↔ Gamma0Pair.Step P Q :=
  Quot.eq.trans (stepEquivalence (N := N) (K := K)).eqvGen_iff

end P2MWs13.ModuliFibre

open P2MWs13.ModuliFibre ModularCurve in
/--
@isnad1 id=eq.0h3v.s9.770cb62a587f from=translated src=- shape=43e0a8d9 vocab=802e5910
-/
theorem solution
    (N : ℕ) (L : Type*) [Field L] [DecidableEq L] [IsAlgClosed L]
    (W : WeierstrassCurve L) [W.IsElliptic] :
    Nat.card {x : ModuliPoint N L // ModuliPoint.j x = W.j}
      = Nat.card (Quot (fun (T T' : {T : W.toAffine.Point // addOrderOf T = N}) =>
          ∃ γ : VariableChange L, ∃ _ : γ • W = W, ∃ k : ℕ, k.Coprime N ∧
            HEq T'.1 (k • Point.vcInvFun γ W.toAffine T.1))) := by

  let mkP : {T : W.toAffine.Point // addOrderOf T = N} → Gamma0Pair N L :=
    fun T => ⟨W, inferInstance, T.1, T.2⟩
  have hR : ∀ T T' : {T : W.toAffine.Point // addOrderOf T = N},
      (∃ γ : VariableChange L, ∃ _ : γ • W = W, ∃ k : ℕ, k.Coprime N ∧
        HEq T'.1 (k • Point.vcInvFun γ W.toAffine T.1)) ↔ Gamma0Pair.Step (mkP T) (mkP T') :=
    fun T T' => Iff.rfl
  let f : Quot (fun (T T' : {T : W.toAffine.Point // addOrderOf T = N}) =>
          ∃ γ : VariableChange L, ∃ _ : γ • W = W, ∃ k : ℕ, k.Coprime N ∧
            HEq T'.1 (k • Point.vcInvFun γ W.toAffine T.1)) → {x : ModuliPoint N L // ModuliPoint.j x = W.j} :=
    Quot.lift (fun T => ⟨Quot.mk _ (mkP T), rfl⟩)
      (fun T T' h => Subtype.ext (Quot.sound ((hR T T').mp h)))
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  ·
    intro a b
    induction a using Quot.ind with | _ T => ?_
    induction b using Quot.ind with | _ T' => ?_
    intro hab
    have h1 : (Quot.mk _ (mkP T) : ModuliPoint N L) = Quot.mk _ (mkP T') := congrArg Subtype.val hab
    exact Quot.sound ((hR T T').mpr (mk_eq_mk_iff_step.mp h1))
  ·
    rintro ⟨x, hx⟩
    induction x using Quot.ind with | _ P => ?_
    obtain ⟨E, hE, gen, hord⟩ := P
    have hj : E.j = W.j := hx
    obtain ⟨γ, hγ⟩ := WeierstrassCurve.exists_variableChange_of_j_eq E W hj

    subst hγ
    let T : (γ • E).toAffine.Point := Point.vcInvFun γ E.toAffine gen
    have hT : addOrderOf T = N := by rw [addOrderOf_vcInvFun]; exact hord
    refine ⟨Quot.mk _ ⟨T, hT⟩, Subtype.ext ?_⟩
    show (Quot.mk _ (mkP ⟨T, hT⟩) : ModuliPoint N L) = Quot.mk _ ⟨E, hE, gen, hord⟩
    refine (Quot.sound (?_ : Gamma0Pair.Step ⟨E, hE, gen, hord⟩ (mkP ⟨T, hT⟩))).symm
    exact ⟨γ, rfl, 1, Nat.coprime_one_left N, heq_of_eq (one_nsmul _).symm⟩
