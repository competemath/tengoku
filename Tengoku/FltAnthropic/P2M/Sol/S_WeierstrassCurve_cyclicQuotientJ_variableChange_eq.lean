import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Tengoku.FltAnthropic.Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_WeierstrassCurve_cyclicQuotientJ_variableChange_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_WeierstrassCurve_cyclicQuotientJ_variableChange_eq

open WeierstrassCurve WeierstrassCurve.Affine

namespace P2MKcCQJvc

variable {L : Type*} [Field L] [DecidableEq L] (C : VariableChange L)

noncomputable def vcInvHom (W : WeierstrassCurve L) : W.toAffine.Point →+ (C • W).toAffine.Point where
  toFun := Point.vcInvFun C W
  map_zero' := rfl
  map_add' := Point.vcInvFun_add C W

/--
@isnad1 id=eq.0h4v.s8.4997ec19574d from=translated src=- shape=4735f3e8 vocab=d373206b
-/
theorem vcFun_vcInvHom (W : WeierstrassCurve L) (P : W.toAffine.Point) :
    Point.vcFun C W (vcInvHom C W P) = P := Point.vcFun_rightInverse P

/--
@isnad1 id=eq.0h4v.s8.e70e9e7c96d9 from=translated src=- shape=0b0e1831 vocab=d373206b
-/
theorem vcInvHom_vcFun (W : WeierstrassCurve L) (P : (C • W).toAffine.Point) :
    vcInvHom C W (Point.vcFun C W P) = P := Point.vcFun_leftInverse P

/--
@isnad1 id=injectiv.0h3v.s8.65a0fb34978b from=translated src=- shape=054fa54b vocab=540cd62f
-/
theorem vcInvHom_injective (W : WeierstrassCurve L) : Function.Injective (vcInvHom C W) :=
  Function.LeftInverse.injective (g := Point.vcFun C W) (vcFun_vcInvHom C W)

/--
@isnad1 id=iff.0h4v.s8.bc7d3dee69c6 from=translated src=- shape=83914c05 vocab=9775b045
-/
theorem vcInvHom_ne_zero (W : WeierstrassCurve L) {P : W.toAffine.Point} :
    vcInvHom C W P ≠ 0 ↔ P ≠ 0 := by
  rw [Ne, Ne, ← map_zero (vcInvHom C W), (vcInvHom_injective C W).eq_iff]

/--
@isnad1 id=eq.1h4v.s8.3f154843aaa1 from=translated src=- shape=1703f598 vocab=58873802
-/
theorem fst_coordsOrZero_vcInvHom (W : WeierstrassCurve L) {P : W.toAffine.Point} (hP : P ≠ 0) :
    (vcInvHom C W P).coordsOrZero.1 = vcXInv C P.coordsOrZero.1 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

/--
@isnad1 id=eq.0h5v.s7.d8acee053bba from=translated src=- shape=5e1659d3 vocab=593fb22c
-/
theorem kernelXSet_vc (W : WeierstrassCurve L) (H : AddSubgroup W.toAffine.Point) (ℓ : ℕ) :
    (C • W).kernelXSet (H.map (vcInvHom C W)) ℓ = vcXInv C '' W.kernelXSet H ℓ := by
  ext x'
  simp only [kernelXSet, Set.mem_image, Set.mem_ofPred_eq, AddSubgroup.mem_map]
  constructor
  · rintro ⟨P', ⟨⟨P, hP, rfl⟩, hne, hsm⟩, rfl⟩
    have hne' : P ≠ 0 := (vcInvHom_ne_zero C W).1 hne
    refine ⟨P.coordsOrZero.1, ⟨P, ⟨hP, hne', ?_⟩, rfl⟩, (fst_coordsOrZero_vcInvHom C W hne').symm⟩
    apply vcInvHom_injective C W
    rw [map_nsmul, hsm, map_zero]
  · rintro ⟨x, ⟨P, ⟨hP, hne, hsm⟩, rfl⟩, rfl⟩
    refine ⟨vcInvHom C W P, ⟨⟨P, hP, rfl⟩, (vcInvHom_ne_zero C W).2 hne, ?_⟩,
      fst_coordsOrZero_vcInvHom C W hne⟩
    rw [← map_nsmul, hsm, map_zero]

/--
@isnad1 id=eq.0h5v.s7.51531fd1f0d6 from=translated src=- shape=5e1659d3 vocab=b3ad85d4
-/
theorem coKernelXSet_vc (W : WeierstrassCurve L) (H : AddSubgroup W.toAffine.Point) (ℓ : ℕ) :
    (C • W).coKernelXSet (H.map (vcInvHom C W)) ℓ = vcXInv C '' W.coKernelXSet H ℓ := by
  ext x'
  simp only [coKernelXSet, Set.mem_image, Set.mem_ofPred_eq, AddSubgroup.mem_map]
  constructor
  · rintro ⟨P', ⟨⟨P, hP, rfl⟩, hsm⟩, rfl⟩
    have hne' : P ≠ 0 := by rintro rfl; exact hsm (by rw [map_zero, smul_zero])
    refine ⟨P.coordsOrZero.1, ⟨P, ⟨hP, fun h => hsm ?_⟩, rfl⟩, (fst_coordsOrZero_vcInvHom C W hne').symm⟩
    rw [← map_nsmul, h, map_zero]
  · rintro ⟨x, ⟨P, ⟨hP, hsm⟩, rfl⟩, rfl⟩
    have hne : P ≠ 0 := by rintro rfl; exact hsm (smul_zero _)
    refine ⟨vcInvHom C W P, ⟨⟨P, hP, rfl⟩, fun h => hsm ?_⟩, fst_coordsOrZero_vcInvHom C W hne⟩
    apply vcInvHom_injective C W
    rw [map_nsmul, h, map_zero]

omit [DecidableEq L] in
/--
@isnad1 id=eq.0h4v.s7.49eda46186bf from=translated src=- shape=8c92602a vocab=1c05dc0f
-/
theorem xVeluT_vc (W : WeierstrassCurve L) (x : L) :
    (C • W).xVeluT (vcXInv C x) = ((C.u⁻¹ : Lˣ) : L) ^ 4 * W.xVeluT x := by
  simp only [xVeluT, vcXInv, variableChange_b₂, variableChange_b₄]
  ring

omit [DecidableEq L] in
/--
@isnad1 id=eq.0h4v.s7.6f155a34799f from=translated src=- shape=8c92602a vocab=f724afde
-/
theorem xVeluU_vc (W : WeierstrassCurve L) (x : L) :
    (C • W).xVeluU (vcXInv C x) = ((C.u⁻¹ : Lˣ) : L) ^ 6 * W.xVeluU x := by
  simp only [xVeluU, vcXInv, variableChange_b₂, variableChange_b₄, variableChange_b₆]
  ring

omit [DecidableEq L] in
/--
@isnad1 id=eq.0h4v.s7.08b03370de76 from=translated src=- shape=81d3d4d9 vocab=ed152bb4
-/
theorem xVeluW_vc (W : WeierstrassCurve L) (x : L) :
    (C • W).xVeluW (vcXInv C x) = ((C.u⁻¹ : Lˣ) : L) ^ 6 * (W.xVeluW x - C.r * W.xVeluT x) := by
  rw [xVeluW, xVeluW, xVeluU_vc, xVeluT_vc, vcXInv]
  ring

omit [DecidableEq L] in
/--
@isnad1 id=eq.1h3v.s6.78bdeb8680bb from=translated src=- shape=6bc0d6f7 vocab=8b65eb04
-/
theorem xVeluG_eq (W : WeierstrassCurve L) (h2 : (2 : L) ≠ 0) (x : L) : W.xVeluG x = W.xVeluT x / 2 := by
  rw [xVeluG, twoTorsionY, veluGx, xVeluT, b₂, b₄]
  field_simp
  ring

omit [DecidableEq L] in
/--
@isnad1 id=eq.1h4v.s7.cddc28e6a5fa from=translated src=- shape=c7d36f48 vocab=976660ab
-/
theorem xVeluG_vc (W : WeierstrassCurve L) (h2 : (2 : L) ≠ 0) (x : L) :
    (C • W).xVeluG (vcXInv C x) = ((C.u⁻¹ : Lˣ) : L) ^ 4 * W.xVeluG x := by
  rw [xVeluG_eq (C • W) h2, xVeluG_eq W h2, xVeluT_vc, mul_div_assoc]

omit [DecidableEq L] in
/--
@isnad1 id=eq.0h4v.s5.ae258f936ff2 from=translated src=- shape=79a9884c vocab=3a707d8b
-/
theorem absSum_image_vc (X : Set L) (g : L → L) :
    absSum (vcXInv C '' X) g = absSum X (fun x => g (vcXInv C x)) := by
  have hinj : Set.InjOn (vcXInv C) X := fun a _ b _ h => by
    simpa only [vcX_vcXInv] using congrArg (vcX C) h
  by_cases hX : X.Finite
  · rw [absSum, ite_eq_left (hX.image _), absSum, ite_eq_left hX, finsum_mem_image hinj]
  · have hX' : ¬ (vcXInv C '' X).Finite := fun h => hX (Set.Finite.of_finite_image h hinj)
    rw [absSum, ite_eq_right hX', absSum, ite_eq_right hX]

omit [DecidableEq L] in
/--
@isnad1 id=eq.0h4v.s6.64b7feb2e1de from=translated src=- shape=9ae25565 vocab=f7f203ca
-/
theorem absSum_mul (X : Set L) (c : L) (g : L → L) :
    absSum X (fun x => c * g x) = c * absSum X g := by
  by_cases hX : X.Finite
  · rw [absSum_of_finite hX, absSum_of_finite hX, Finset.mul_sum]
  · rw [absSum_of_infinite hX, absSum_of_infinite hX, mul_zero]

omit [DecidableEq L] in
/--
@isnad1 id=eq.0h4v.s6.e0ceb4dd18fa from=translated src=- shape=31c87ca5 vocab=319599e5
-/
theorem absSum_sub (X : Set L) (g h : L → L) :
    absSum X (fun x => g x - h x) = absSum X g - absSum X h := by
  by_cases hX : X.Finite
  · rw [absSum_of_finite hX, absSum_of_finite hX, absSum_of_finite hX, Finset.sum_sub_distrib]
  · rw [absSum_of_infinite hX, absSum_of_infinite hX, absSum_of_infinite hX, sub_zero]

omit [DecidableEq L] in
/--
@isnad1 id=eq.1h4v.s5.4632d2107cf4 from=translated src=- shape=cb0f234b vocab=1ed430dc
-/
theorem absSum_congr (X : Set L) {g h : L → L} (hgh : ∀ x, g x = h x) : absSum X g = absSum X h := by
  rw [show g = h from funext hgh]

omit [DecidableEq L] in
/--
@isnad1 id=eq.0h4v.s6.e4c4f6d4403c from=translated src=- shape=41a3ffa4 vocab=cbc7119f
-/
theorem xVeluCurve_vc (W : WeierstrassCurve L) (X : Set L) :
    (C • W).xVeluCurve (vcXInv C '' X) = C • (W.xVeluCurve X) := by
  have hT : absSum (vcXInv C '' X) (C • W).xVeluT = ((C.u⁻¹ : Lˣ) : L) ^ 4 * absSum X W.xVeluT := by
    rw [absSum_image_vc, absSum_congr X (xVeluT_vc C W), absSum_mul]
  have hW : absSum (vcXInv C '' X) (C • W).xVeluW =
      ((C.u⁻¹ : Lˣ) : L) ^ 6 * (absSum X W.xVeluW - C.r * absSum X W.xVeluT) := by
    rw [absSum_image_vc, absSum_congr X (xVeluW_vc C W), absSum_mul, absSum_sub, absSum_mul]
  ext
  · rfl
  · rfl
  · rfl
  · rw [xVeluCurve_a₄, hT, variableChange_a₄, variableChange_a₄]
    simp only [xVeluCurve_a₁, xVeluCurve_a₂, xVeluCurve_a₃, xVeluCurve_a₄]
    ring
  · rw [xVeluCurve_a₆, hT, hW, variableChange_a₆, variableChange_a₆, variableChange_b₂]
    simp only [xVeluCurve_a₁, xVeluCurve_a₂, xVeluCurve_a₃, xVeluCurve_a₄, xVeluCurve_a₆]
    ring

omit [DecidableEq L] in
/--
@isnad1 id=eq.1h4v.s6.38d082d0d217 from=translated src=- shape=ce77e172 vocab=c904abee
-/
theorem twoVeluCurve_vc (W : WeierstrassCurve L) (h2 : (2 : L) ≠ 0) (X : Set L) :
    (C • W).twoVeluCurve (vcXInv C '' X) = C • (W.twoVeluCurve X) := by
  have hG : absSum (vcXInv C '' X) (C • W).xVeluG = ((C.u⁻¹ : Lˣ) : L) ^ 4 * absSum X W.xVeluG := by
    rw [absSum_image_vc, absSum_congr X (xVeluG_vc C W h2), absSum_mul]
  have hXG : absSum (vcXInv C '' X) (fun x => x * (C • W).xVeluG x) =
      ((C.u⁻¹ : Lˣ) : L) ^ 6 * (absSum X (fun x => x * W.xVeluG x) - C.r * absSum X W.xVeluG) := by
    rw [absSum_image_vc, ← absSum_mul X C.r, ← absSum_sub, ← absSum_mul]
    refine absSum_congr X fun x => ?_
    rw [xVeluG_vc C W h2, vcXInv]
    ring
  ext
  · rfl
  · rfl
  · rfl
  · rw [twoVeluCurve_a₄, hG, variableChange_a₄, variableChange_a₄]
    simp only [twoVeluCurve_a₁, twoVeluCurve_a₂, twoVeluCurve_a₃, twoVeluCurve_a₄]
    ring
  · rw [twoVeluCurve_a₆, hG, hXG, variableChange_a₆, variableChange_a₆, variableChange_b₂]
    simp only [twoVeluCurve_a₁, twoVeluCurve_a₂, twoVeluCurve_a₃, twoVeluCurve_a₄, twoVeluCurve_a₆]
    ring

omit [DecidableEq L] in
/--
@isnad1 id=eq.0h5v.s6.02263631c780 from=translated src=- shape=d27bd4f6 vocab=d1560ebc
-/
theorem xVeluX_vc (W : WeierstrassCurve L) (X : Set L) (x : L) :
    (C • W).xVeluX (vcXInv C '' X) (vcXInv C x) = vcXInv C (W.xVeluX X x) := by
  rw [xVeluX, xVeluX, absSum_image_vc]
  have hu : (C.u : L) ≠ 0 := C.u.ne_zero
  have key : ∀ x₀, (C • W).xVeluT (vcXInv C x₀) / (vcXInv C x - vcXInv C x₀) +
      (C • W).xVeluU (vcXInv C x₀) / (vcXInv C x - vcXInv C x₀) ^ 2 =
      ((C.u⁻¹ : Lˣ) : L) ^ 2 * (W.xVeluT x₀ / (x - x₀) + W.xVeluU x₀ / (x - x₀) ^ 2) := by
    intro x₀
    rw [xVeluT_vc, xVeluU_vc]
    have hd : vcXInv C x - vcXInv C x₀ = ((C.u⁻¹ : Lˣ) : L) ^ 2 * (x - x₀) := by
      simp only [vcXInv]; ring
    rw [hd]
    rcases eq_or_ne x x₀ with rfl | hne
    · simp
    · have hx : x - x₀ ≠ 0 := sub_ne_zero.2 hne
      simp only [Units.val_inv_eq_inv_val]
      field_simp
  rw [absSum_congr X key, absSum_mul]
  simp only [vcXInv]
  ring

omit [DecidableEq L] in
/--
@isnad1 id=eq.1h5v.s6.a3994ff9f196 from=translated src=- shape=0e588cf9 vocab=d5cc3603
-/
theorem twoVeluX_vc (W : WeierstrassCurve L) (h2 : (2 : L) ≠ 0) (X : Set L) (x : L) :
    (C • W).twoVeluX (vcXInv C '' X) (vcXInv C x) = vcXInv C (W.twoVeluX X x) := by
  rw [twoVeluX, twoVeluX, absSum_image_vc]
  have hu : (C.u : L) ≠ 0 := C.u.ne_zero
  have key : ∀ x₀, (C • W).xVeluG (vcXInv C x₀) / (vcXInv C x - vcXInv C x₀) =
      ((C.u⁻¹ : Lˣ) : L) ^ 2 * (W.xVeluG x₀ / (x - x₀)) := by
    intro x₀
    rw [xVeluG_vc C W h2]
    have hd : vcXInv C x - vcXInv C x₀ = ((C.u⁻¹ : Lˣ) : L) ^ 2 * (x - x₀) := by
      simp only [vcXInv]; ring
    rw [hd]
    rcases eq_or_ne x x₀ with rfl | hne
    · simp
    · have hx : x - x₀ ≠ 0 := sub_ne_zero.2 hne
      simp only [Units.val_inv_eq_inv_val]
      field_simp
  rw [absSum_congr X key, absSum_mul]
  simp only [vcXInv]
  ring

/--
@isnad1 id=eq.1h5v.s8.dbe6ab47a189 from=translated src=- shape=6343d95b vocab=6c6a723b
-/
theorem stepCurve_vc (W : WeierstrassCurve L) (H : AddSubgroup W.toAffine.Point) (ℓ : ℕ)
    (h2 : ℓ = 2 → (2 : L) ≠ 0) :
    (C • W).stepCurve (H.map (vcInvHom C W)) ℓ = C • (W.stepCurve H ℓ) := by
  by_cases hℓ : ℓ = 2
  · subst hℓ
    rw [stepCurve_two, stepCurve_two, kernelXSet_vc, twoVeluCurve_vc C W (h2 rfl)]
  · rw [stepCurve_of_ne_two _ _ hℓ, stepCurve_of_ne_two _ _ hℓ, kernelXSet_vc, xVeluCurve_vc]

/--
@isnad1 id=eq.1h6v.s8.041ecf508a6c from=translated src=- shape=4e6e6039 vocab=94038e0c
-/
theorem stepX_vc (W : WeierstrassCurve L) (H : AddSubgroup W.toAffine.Point) (ℓ : ℕ)
    (h2 : ℓ = 2 → (2 : L) ≠ 0) (x : L) :
    (C • W).stepX (H.map (vcInvHom C W)) ℓ (vcXInv C x) = vcXInv C (W.stepX H ℓ x) := by
  by_cases hℓ : ℓ = 2
  · subst hℓ
    rw [stepX_two, stepX_two, kernelXSet_vc, twoVeluX_vc C W (h2 rfl)]
  · rw [stepX_of_ne_two _ _ hℓ, stepX_of_ne_two _ _ hℓ, kernelXSet_vc, xVeluX_vc]

/--
@isnad1 id=eq.0h4v.s8.c6c355de3eb4 from=translated src=- shape=251b4701 vocab=77aa5c39
-/
theorem subgroupOfX_vc (V : WeierstrassCurve L) (Y : Set L) :
    subgroupOfX (C • V) (vcXInv C '' Y) = (subgroupOfX V Y).map (vcInvHom C V) := by
  rw [subgroupOfX, subgroupOfX, AddMonoidHom.map_closure]
  congr 1
  ext P'
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hne, ⟨y, hyY, hy⟩⟩
    have hne' : Point.vcFun C V P' ≠ 0 := by
      intro h
      apply hne
      rw [← vcInvHom_vcFun C V P', h, map_zero]
    refine ⟨Point.vcFun C V P', ⟨hne', ?_⟩, vcInvHom_vcFun C V P'⟩
    have := fst_coordsOrZero_vcInvHom C V hne'
    rw [vcInvHom_vcFun] at this
    have h' : vcX C P'.coordsOrZero.1 = (Point.vcFun C V P').coordsOrZero.1 := by
      rw [this, vcX_vcXInv]
    rw [← h', ← hy, vcX_vcXInv]
    exact hyY
  · rintro ⟨P, ⟨hne, hY⟩, rfl⟩
    exact ⟨(vcInvHom_ne_zero C V).2 hne, ⟨_, hY, (fst_coordsOrZero_vcInvHom C V hne).symm⟩⟩

noncomputable def vcState (s : CQJState L) : CQJState L :=
  ⟨⟨C • s.1.1, s.1.2.map (vcInvHom C s.1.1)⟩, s.2⟩

/--
@isnad1 id=eq.2h5v.s7.0fa39f3cc36c from=translated src=- shape=19721559 vocab=a91756ad
-/
theorem sigma_eq_of_eq {V₁ V₂ : WeierstrassCurve L} (h : V₁ = V₂) {Y₁ Y₂ : Set L} (hY : Y₁ = Y₂) :
    (⟨V₁, subgroupOfX V₁ Y₁⟩ : Σ V : WeierstrassCurve L, AddSubgroup V.toAffine.Point) =
      ⟨V₂, subgroupOfX V₂ Y₂⟩ := by
  subst h hY; rfl

/--
@isnad1 id=eq.1h3v.s6.12da008bd434 from=translated src=- shape=58cf254d vocab=7ea69bc8
-/
theorem cqjStep_vcState (s : CQJState L) (h2 : s.2.minFac = 2 → (2 : L) ≠ 0) :
    cqjStep (vcState C s) = vcState C (cqjStep s) := by
  obtain ⟨⟨V, H⟩, n⟩ := s
  change (⟨⟨(C • V).stepCurve (H.map (vcInvHom C V)) n.minFac,
      (C • V).stepSubgroup (H.map (vcInvHom C V)) n.minFac⟩, n / n.minFac⟩ : CQJState L) =
    ⟨⟨C • (V.stepCurve H n.minFac), (V.stepSubgroup H n.minFac).map (vcInvHom C _)⟩, n / n.minFac⟩
  congr 1
  rw [stepSubgroup, stepSubgroup, ← subgroupOfX_vc]
  refine sigma_eq_of_eq (stepCurve_vc C V H _ h2) ?_
  rw [coKernelXSet_vc, Set.image_image, Set.image_image]
  exact Set.image_congr fun x _ => stepX_vc C V H _ h2 x

/--
@isnad1 id=dvd.0h2v.s6.2a1714ed1946 from=translated src=- shape=9d2de3b6 vocab=ab36d913
-/
theorem cqjStep_snd_dvd (s : CQJState L) : (cqjStep s).2 ∣ s.2 :=
  Nat.div_dvd_of_dvd (Nat.minFac_dvd _)

/--
@isnad1 id=eq.2h5v.s7.c6338d22687f from=translated src=- shape=cc1f2846 vocab=a22d6434
-/
theorem iterate_cqjStep_vcState {N : ℕ} (hN2 : 2 ∣ N → (2 : L) ≠ 0) (k : ℕ) (s : CQJState L)
    (hs : s.2 ∣ N) : cqjStep^[k] (vcState C s) = vcState C (cqjStep^[k] s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, cqjStep_vcState C s, ih]
    · exact (cqjStep_snd_dvd s).trans hs
    · intro h
      exact hN2 ((h ▸ Nat.minFac_dvd s.2).trans hs)

/--
@isnad1 id=eq.1h5v.s8.649268fbab84 from=translated src=- shape=dd452aea vocab=73e09336
-/
theorem cyclicQuotientJ_vc (W : WeierstrassCurve L) (H : AddSubgroup W.toAffine.Point) (N : ℕ)
    (hN2 : 2 ∣ N → (2 : L) ≠ 0) :
    (C • W).cyclicQuotientJ (H.map (vcInvHom C W)) N = W.cyclicQuotientJ H N := by
  have h := iterate_cqjStep_vcState C hN2 N.primeFactorsList.length ⟨⟨W, H⟩, N⟩ dvd_rfl
  have hc : (C • W).cyclicQuotientCurve (H.map (vcInvHom C W)) N = C • (W.cyclicQuotientCurve H N) := by
    rw [cyclicQuotientCurve_def, cyclicQuotientCurve_def, cqjIterate_def, cqjIterate_def]
    exact congrArg (fun s : CQJState L => s.1.1) h
  rw [cyclicQuotientJ_def, cyclicQuotientJ_def, hc, variableChange_c₄, variableChange_Δ]
  have hu : ((C.u⁻¹ : Lˣ) : L) ≠ 0 := (C.u⁻¹).ne_zero
  rw [mul_pow, ← pow_mul, show 4 * 3 = 12 by norm_num, mul_div_mul_left _ _ (pow_ne_zero 12 hu)]

end P2MKcCQJvc

open P2MKcCQJvc in
universe u in
/--
@isnad1 id=eq.2h6v.s9.e4db48d0a5cd from=translated src=- shape=6b548aa7 vocab=97c7f486
-/
theorem solution
    {L : Type u} [Field L] [DecidableEq L] (C : VariableChange L) (E : WeierstrassCurve L)
    (H : AddSubgroup E.toAffine.Point) (H' : AddSubgroup (C • E).toAffine.Point)
    (hH' : ∀ P, P ∈ H' ↔ WeierstrassCurve.Affine.Point.vcFun C E P ∈ H)
    (N : ℕ) (hN : (N : L) ≠ 0) :
    (C • E).cyclicQuotientJ H' N = E.cyclicQuotientJ H N := by
  have hH'eq : H' = H.map (vcInvHom C E) := by
    ext P
    rw [hH', AddSubgroup.mem_map]
    constructor
    · intro h
      exact ⟨_, h, vcInvHom_vcFun C E P⟩
    · rintro ⟨Q, hQ, rfl⟩
      rwa [vcFun_vcInvHom]
  rw [hH'eq]
  refine cyclicQuotientJ_vc C E H N fun h2 h => hN ?_
  obtain ⟨m, rfl⟩ := h2
  rw [Nat.cast_mul, Nat.cast_ofNat, h, zero_mul]
