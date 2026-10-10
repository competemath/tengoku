import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.CriticalCount

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma continuous_class_deriv : Continuous (fun p : DiskClass × halfPlane => deriv (classFun p.1) p.2) := by
  simpa only [iteratedDeriv_one] using continuous_classJet_eval 1

lemma continuous_class_deriv_deriv :
    Continuous (fun p : DiskClass × halfPlane => deriv (deriv (classFun p.1)) p.2) := by
  simpa only [show 2 = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using continuous_classJet_eval 2

lemma continuous_class_criticalMap (k : ℝ) :
    Continuous (fun p : DiskClass × halfPlane => criticalMap (classFun p.1) k p.2) := by
  exact continuous_classFun_eval.sub ((continuous_const.mul
    (Complex.continuous_ofReal.comp (Complex.continuous_im.comp
      (continuous_subtype_val.comp continuous_snd)))).mul continuous_class_deriv)

lemma continuous_class_fderiv_criticalMap (k : ℝ) :
    Continuous (fun p : DiskClass × halfPlane => fderiv ℝ (criticalMap (classFun p.1) k) p.2) := by
  let A : ℂ →L[ℝ] ℂ := 1
  let B : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM
  have he (p : DiskClass × halfPlane) : fderiv ℝ (criticalMap (classFun p.1) k) p.2 =
      deriv (classFun p.1) p.2 • A -
      (Complex.I / (k : ℂ) * (p.2.val.im : ℂ) * deriv (deriv (classFun p.1)) p.2) • A -
      (Complex.I / (k : ℂ) * deriv (classFun p.1) p.2) • B := by
    ext v
    rw [fderiv_criticalMap_apply (classFun_schlicht p.1).1 p.2.property]
    change _ = deriv (classFun p.1) p.2 * v -
      (Complex.I / (k : ℂ) * (p.2.val.im : ℂ) * deriv (deriv (classFun p.1)) p.2) * v -
      (Complex.I / (k : ℂ) * deriv (classFun p.1) p.2) * (v.im : ℂ)
    ring
  simp_rw [he]
  have hy : Continuous (fun p : DiskClass × halfPlane => (p.2.val.im : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp (continuous_subtype_val.comp continuous_snd))
  exact ((continuous_class_deriv.smul continuous_const).sub
    (((continuous_const.mul hy).mul continuous_class_deriv_deriv).smul continuous_const)).sub
    ((continuous_const.mul continuous_class_deriv).smul continuous_const)

lemma continuous_class_normalizedJacobian (k : ℝ) :
    Continuous (fun p : DiskClass × halfPlane => normalizedJacobian (classFun p.1) k p.2) := by
  apply (ContinuousLinearMap.continuous_det.comp (continuous_class_fderiv_criticalMap k)).div
    (continuous_class_deriv.norm.pow 2)
  intro p
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr
    (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht p.1).1 p.2.property))

def criticalHeight (f : ℂ → ℂ) (k : ℝ) (z : ℂ) : ℝ :=
  k * z.im^(k-1) * ‖reciprocalDeriv f z‖

lemma criticalHeight_pos {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {z : ℂ} (hz : z ∈ halfPlane) : 0 < criticalHeight f k z := by
  exact mul_pos (mul_pos hk (Real.rpow_pos_of_pos hz _))
    (norm_pos_iff.mpr (inv_ne_zero (univalent_deriv_ne_zero isOpen_halfPlane hf hz)))

lemma continuous_class_criticalHeight (k : ℝ) :
    Continuous (fun p : DiskClass × halfPlane => criticalHeight (classFun p.1) k p.2) := by
  have hy : Continuous (fun p : DiskClass × halfPlane => p.2.val.im^(k-1)) :=
    (Complex.continuous_im.comp (continuous_subtype_val.comp continuous_snd)).rpow_const
      (fun p => Or.inl (ne_of_gt p.2.property))
  have hh : Continuous (fun p : DiskClass × halfPlane =>
      k * p.2.val.im^(k-1) * ‖deriv (classFun p.1) p.2‖⁻¹) :=
    (continuous_const.mul hy).mul (continuous_class_deriv.norm.inv₀
      (fun p => norm_ne_zero_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane
        (classFun_schlicht p.1).1 p.2.property)))
  exact hh.congr (fun p => by simp only [criticalHeight,reciprocalDeriv,norm_inv])

lemma criticalMap_congr {f g : ℂ → ℂ} (he : EqOn f g halfPlane) (k : ℝ) :
    EqOn (criticalMap f k) (criticalMap g k) halfPlane := by
  intro z hz
  rw [criticalMap,criticalMap,he hz,he.deriv isOpen_halfPlane hz]

lemma normalizedJacobian_congr {f g : ℂ → ℂ} (he : EqOn f g halfPlane) (k : ℝ) :
    EqOn (normalizedJacobian f k) (normalizedJacobian g k) halfPlane := by
  intro z hz
  have hG : criticalMap f k =ᶠ[𝓝 z] criticalMap g k := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz] with w hw
    exact criticalMap_congr he k hw
  rw [normalizedJacobian,normalizedJacobian,hG.fderiv_eq,he.deriv isOpen_halfPlane hz]

lemma criticalHeight_congr {f g : ℂ → ℂ} (he : EqOn f g halfPlane) (k : ℝ) :
    EqOn (criticalHeight f k) (criticalHeight g k) halfPlane := by
  intro z hz
  rw [criticalHeight,criticalHeight,reciprocalDeriv,reciprocalDeriv,he.deriv isOpen_halfPlane hz]

lemma goodPair_congr {f g : ℂ → ℂ} (he : EqOn f g halfPlane) (k : ℝ) (ξ : ℂ) :
    GoodPair f k ξ ↔ GoodPair g k ξ := by
  have hs (δ : ℝ) : {z | z ∈ halfPlane ∧ ENNReal.ofReal δ ≤ potential f k ξ z} =
      {z | z ∈ halfPlane ∧ ENNReal.ofReal δ ≤ potential g k ξ z} := by
    ext z
    by_cases hz : z ∈ halfPlane
    · simp only [mem_ofPred_eq,hz,true_and,potential,he hz]
    · simp only [mem_ofPred_eq,hz,false_and]
  simp only [GoodPair,hs]
  apply and_congr_right
  intro _
  constructor <;> intro h z hz hG
  · rw [← normalizedJacobian_congr he k hz]
    exact h z hz ((criticalMap_congr he k hz).trans hG)
  · rw [normalizedJacobian_congr he k hz]
    exact h z hz ((criticalMap_congr he k hz).symm.trans hG)

def affineHome (t : ℂ) (ht : t ∈ halfPlane) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (t.im : ℂ) (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))).trans
    (Homeomorph.addLeft (t.re : ℂ))

lemma affineHome_apply (t : ℂ) (ht : t ∈ halfPlane) (z : ℂ) :
    affineHome t ht z = affine t z := rfl

lemma affine_mem_iff {t : ℂ} (ht : t ∈ halfPlane) (z : ℂ) :
    affine t z ∈ halfPlane ↔ z ∈ halfPlane := by
  change 0 < (affine t z).im ↔ 0 < z.im
  simp only [affine,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    zero_mul,zero_add,add_zero]
  exact mul_pos_iff_of_pos_left ht

def rerootTarget (f : ℂ → ℂ) (t ξ : ℂ) : ℂ :=
  (ξ-f t)/((t.im : ℂ)*deriv f t)

def heightScaleInverse (f : ℂ → ℂ) (k : ℝ) (t : ℂ) : ℝ :=
  t.im^(k-1) / ‖deriv f t‖

lemma heightScaleInverse_pos {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) (k : ℝ)
    {t : ℂ} (ht : t ∈ halfPlane) : 0 < heightScaleInverse f k t :=
  div_pos (Real.rpow_pos_of_pos ht _) (norm_pos_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane hf ht))

lemma reciprocalPotential_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) (k : ℝ)
    {t z : ℂ} (ht : t ∈ halfPlane) (hz : z ∈ halfPlane) (ξ : ℂ) :
    reciprocalPotential (reroot f t) k (rerootTarget f t ξ) z =
      heightScaleInverse f k t * reciprocalPotential f k ξ (affine t z) := by
  have he : reroot f t z-rerootTarget f t ξ =
      (f (affine t z)-ξ)/((t.im : ℂ)*deriv f t) := by
    simp only [reroot,rerootTarget,← sub_div]
    congr 1
    ring
  have hn : ‖deriv f t‖ ≠ 0 := norm_ne_zero_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane hf ht)
  have hpow : z.im^k ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hz k)
  have him : (affine t z).im = t.im*z.im := by simp [affine]
  rw [reciprocalPotential,he,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht,
    reciprocalPotential,him,Real.mul_rpow ht.le hz.le,heightScaleInverse,Real.rpow_sub_one (ne_of_gt ht)]
  have htp : t.im^k ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  field_simp

lemma criticalHeight_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) (k : ℝ)
    {t z : ℂ} (ht : t ∈ halfPlane) (hz : z ∈ halfPlane) :
    criticalHeight (reroot f t) k z = criticalHeight f k (affine t z) / heightScaleInverse f k t := by
  have him : (affine t z).im = t.im*z.im := by simp [affine]
  have hn : ‖deriv f t‖ ≠ 0 := norm_ne_zero_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane hf ht)
  have hp : t.im^(k-1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  rw [criticalHeight,reciprocalDeriv_reroot hf ht hz,norm_div,criticalHeight,him,
    Real.mul_rpow ht.le hz.le,heightScaleInverse]
  simp only [reciprocalDeriv,norm_inv]
  field_simp

lemma criticalMap_reroot_fiber {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) (k : ℝ)
    {t z : ℂ} (ht : t ∈ halfPlane) (hz : z ∈ halfPlane) (ξ : ℂ) :
    criticalMap (reroot f t) k z = rerootTarget f t ξ ↔ criticalMap f k (affine t z) = ξ := by
  rw [criticalMap_reroot hf ht hz,rerootTarget,div_left_inj' (mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)) (univalent_deriv_ne_zero isOpen_halfPlane hf ht)),sub_left_inj]

lemma potential_level_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 ≤ k)
    {t : ℂ} (ht : t ∈ halfPlane) (ξ : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    {z | z ∈ halfPlane ∧ ENNReal.ofReal δ ≤ potential (reroot f t) k (rerootTarget f t ξ) z} =
      (affineHome t ht) ⁻¹' {w | w ∈ halfPlane ∧
        ENNReal.ofReal (δ*heightScaleInverse f k t) ≤ potential f k ξ w} := by
  have hc := heightScaleInverse_pos hf k ht
  ext z
  simp only [mem_ofPred_eq,mem_preimage,affineHome_apply,affine_mem_iff ht]
  apply and_congr_right
  intro hz
  rw [potential_ge_iff_reciprocalPotential_le hk hδ hz,
    potential_ge_iff_reciprocalPotential_le hk (mul_pos hδ hc) (affine_mem ht hz),
    reciprocalPotential_reroot hf k ht hz ξ,mul_inv_rev]
  rw [mul_comm,← le_div_iff₀ hc,div_eq_mul_inv]
  rw [mul_comm δ⁻¹]

lemma goodPair_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {t : ℂ} (ht : t ∈ halfPlane) (ξ : ℂ) :
    GoodPair (reroot f t) k (rerootTarget f t ξ) ↔ GoodPair f k ξ := by
  have hc := heightScaleInverse_pos hf k ht
  constructor
  · rintro ⟨hcompact,hregular⟩
    constructor
    · intro δ hδ
      have h := hcompact (δ/heightScaleInverse f k t) (div_pos hδ hc)
      rw [potential_level_reroot hf hk.le ht ξ (div_pos hδ hc),div_mul_cancel₀ _ (ne_of_gt hc)] at h
      exact (affineHome t ht).isCompact_preimage.mp h
    · intro w hw hG
      let z := (affineHome t ht).symm w
      have he : affine t z = w := (affineHome t ht).apply_symm_apply w
      have hz : z ∈ halfPlane := (affine_mem_iff ht z).mp (he.symm ▸ hw)
      have hr := hregular z hz ((criticalMap_reroot_fiber hf k ht hz ξ).mpr (he.symm ▸ hG))
      rwa [normalizedJacobian_reroot hf ht hz k (ne_of_gt hk),he] at hr
  · rintro ⟨hcompact,hregular⟩
    constructor
    · intro δ hδ
      rw [potential_level_reroot hf hk.le ht ξ hδ]
      exact (affineHome t ht).isCompact_preimage.mpr (hcompact _ (mul_pos hδ hc))
    · intro z hz hG
      rw [normalizedJacobian_reroot hf ht hz k (ne_of_gt hk)]
      exact hregular _ (affine_mem ht hz) ((criticalMap_reroot_fiber hf k ht hz ξ).mp hG)

def orderRank.{u_1} {α : Type u_1} [LinearOrder α] (S : Set α) (x : α) : ℕ := (S ∩ Iio x).ncard

lemma orderRank_strictMonoOn.{u_1} {α : Type u_1} [LinearOrder α] {S : Set α}
    (hfin : ∀ x ∈ S, (S ∩ Iio x).Finite) : StrictMonoOn (orderRank S) S := by
  intro x hx y hy hxy
  apply Set.ncard_lt_ncard _ (hfin y hy)
  refine ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
  · exact fun a ha => ⟨ha.1,ha.2.trans hxy⟩
  · intro he
    have : x ∈ S ∩ Iio x := he ▸ (show x ∈ S ∩ Iio y from ⟨hx,hxy⟩)
    exact lt_irrefl x this.2

lemma orderRank_injOn.{u_1} {α : Type u_1} [LinearOrder α] {S : Set α}
    (hfin : ∀ x ∈ S, (S ∩ Iio x).Finite) : InjOn (orderRank S) S :=
  (orderRank_strictMonoOn hfin).injOn

lemma orderRank_finset_enum.{u_1} {α : Type u_1} [LinearOrder α] (s : Finset α)
    (j : Fin s.card) : orderRank (s : Set α) (s.orderEmbOfFin rfl j) = j.val := by
  classical
  let e := s.orderEmbOfFin rfl
  have he : (s : Set α) ∩ Iio (e j) = e '' Iio j := by
    ext a
    constructor
    · intro ha
      obtain ⟨i,rfl⟩ := (s.range_orderEmbOfFin rfl).symm ▸ ha.1
      exact ⟨i,e.lt_iff_lt.mp ha.2,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨s.orderEmbOfFin_mem rfl i,e.strictMono hi⟩
  rw [orderRank,he,Set.ncard_image_of_injective _ e.injective]
  rw [← Finset.coe_Iio,Set.ncard_coe_finset,Fin.card_Iio]

lemma exists_orderRank_of_finite_initial.{u_1} {α : Type u_1} [LinearOrder α]
    {S A : Set α} (hA : A.Finite) (hAS : A ⊆ S)
    (hinit : ∀ x ∈ A, ∀ y ∈ S, y < x → y ∈ A)
    {j : ℕ} (hj : j < A.ncard) : ∃ x ∈ A, orderRank S x = j := by
  classical
  let s := hA.toFinset
  have hscard : s.card = A.ncard := (Set.ncard_eq_toFinset_card A hA).symm
  let x : α := s.orderEmbOfFin rfl ⟨j,by simpa [hscard] using hj⟩
  have hx : x ∈ A := hA.mem_toFinset.mp (s.orderEmbOfFin_mem rfl ⟨j,by simpa [hscard] using hj⟩)
  refine ⟨x,hx,?_⟩
  have he : S ∩ Iio x = A ∩ Iio x := by
    ext y
    exact ⟨fun hy => ⟨hinit x hx y hy.1 hy.2,hy.2⟩,fun hy => ⟨hAS hy.1,hy.2⟩⟩
  calc
    orderRank S x = orderRank A x := congrArg Set.ncard he
    _ = j := by simpa only [s,Set.Finite.coe_toFinset] using
      orderRank_finset_enum s ⟨j,by simpa [hscard] using hj⟩

def heightKey (H : ℂ → ℝ) (z : ℂ) : Lex (ℝ × Lex (ℝ × ℝ)) :=
  toLex (-H z,toLex (z.re,z.im))

lemma heightKey_injective (H : ℂ → ℝ) : Injective (heightKey H) := by
  intro z w he
  have he' := congrArg (fun a : Lex (ℝ × Lex (ℝ × ℝ)) => ofLex ((ofLex a).2)) he
  exact Complex.ext (congrArg Prod.fst he') (congrArg Prod.snd he')

def heightOrder (H : ℂ → ℝ) : LinearOrder ℂ := LinearOrder.lift' (heightKey H) (heightKey_injective H)

def heightRank (H : ℂ → ℝ) (S : Set ℂ) (z : ℂ) : ℕ := @orderRank ℂ (heightOrder H) S z

def heightPrecedes (H : ℂ → ℝ) (z w : ℂ) : Prop :=
  H w < H z ∨ H z = H w ∧ (z.re < w.re ∨ z.re = w.re ∧ z.im < w.im)

lemma heightOrder_lt_iff (H : ℂ → ℝ) (z w : ℂ) :
    @LT.lt ℂ (heightOrder H).toLT z w ↔ heightPrecedes H z w := by
  change heightKey H z < heightKey H w ↔ _
  simp only [heightKey,Prod.Lex.toLex_lt_toLex,neg_lt_neg_iff,neg_inj,heightPrecedes]

lemma heightOrder_height_le {H : ℂ → ℝ} {z w : ℂ}
    (h : @LT.lt ℂ (heightOrder H).toLT z w) : H w ≤ H z := by
  rcases (heightOrder_lt_iff H z w).mp h with h | ⟨h,_⟩
  · exact h.le
  · exact h.ge

lemma heightRank_pred_finite {H : ℂ → ℝ} {S : Set ℂ} {z : ℂ}
    (hfin : (S ∩ {w | H z ≤ H w}).Finite) :
    @Set.Finite ℂ (S ∩ @Iio ℂ (heightOrder H).toPreorder z) := by
  exact hfin.subset (fun w hw => ⟨hw.1,heightOrder_height_le hw.2⟩)

lemma heightRank_lt_segment {H : ℂ → ℝ} {S : Set ℂ} {z : ℂ} (hz : z ∈ S)
    (hfin : (S ∩ {w | H z ≤ H w}).Finite) :
    heightRank H S z < (S ∩ {w | H z ≤ H w}).ncard := by
  let _ := heightOrder H
  apply Set.ncard_lt_ncard _ hfin
  refine ssubset_iff_subset_ne.mpr ⟨fun w hw => ⟨hw.1,heightOrder_height_le hw.2⟩,?_⟩
  intro he
  have : z ∈ S ∩ Iio z := he ▸ (show z ∈ S ∩ {w | H z ≤ H w} from ⟨hz,show H z ≤ H z from le_refl _⟩)
  exact lt_irrefl z this.2

lemma exists_equal_heightRank {H : ℂ → ℝ} {A B : Set ℂ} {z : ℂ}
    (hz : z ∈ A) (hAf : (A ∩ {w | H z ≤ H w}).Finite)
    (hBf : (B ∩ {w | H z ≤ H w}).Finite)
    (hc : (A ∩ {w | H z ≤ H w}).ncard ≤ (B ∩ {w | H z ≤ H w}).ncard) :
    ∃ w ∈ B, H z ≤ H w ∧ heightRank H B w = heightRank H A z := by
  let _ := heightOrder H
  have hj := (heightRank_lt_segment hz hAf).trans_le hc
  obtain ⟨w,hw,hr⟩ := exists_orderRank_of_finite_initial hBf inter_subset_left
    (fun x hx y hy hyx => ⟨hy,hx.2.trans (heightOrder_height_le hyx)⟩) hj
  exact ⟨w,hw.1,hw.2,hr⟩

lemma heightRank_injOn {H : ℂ → ℝ} {S : Set ℂ}
    (hfin : ∀ z ∈ S, (S ∩ {w | H z ≤ H w}).Finite) : InjOn (heightRank H S) S :=
  @orderRank_injOn ℂ (heightOrder H) S (fun z hz => heightRank_pred_finite (hfin z hz))

lemma heightRank_eq_ncard (H : ℂ → ℝ) (S : Set ℂ) (z : ℂ) :
    heightRank H S z = {w | w ∈ S ∧ heightPrecedes H w z}.ncard := by
  let := heightOrder H
  rw [heightRank,orderRank]
  congr 1
  ext w
  exact and_congr_right (fun _ => heightOrder_lt_iff H w z)

lemma heightRank_transport {H H' : ℂ → ℝ} {S S' : Set ℂ} (e : ℂ ≃ ℂ)
    (hS : ∀ z, z ∈ S' ↔ e z ∈ S)
    (hord : ∀ z w, heightPrecedes H' z w ↔ heightPrecedes H (e z) (e w)) (z : ℂ) :
    heightRank H' S' z = heightRank H S (e z) := by
  rw [heightRank_eq_ncard,heightRank_eq_ncard]
  apply Set.ncard_congr (fun w _ => e w)
  · intro w hw
    exact ⟨(hS w).mp hw.1,(hord w z).mp hw.2⟩
  · intro a b _ _ hab
    exact e.injective hab
  · intro w hw
    refine ⟨e.symm w,⟨?_,?_⟩,e.apply_symm_apply w⟩
    · exact (hS _).mpr (by simpa using hw.1)
    · exact (hord _ z).mpr (by simpa using hw.2)

def rankPartner (H : ℂ → ℝ) (A B : Set ℂ) (z : ℂ) : ℂ :=
  if h : ∃ w ∈ B, heightRank H B w = heightRank H A z then h.choose else z

lemma rankPartner_spec {H : ℂ → ℝ} {A B : Set ℂ} {z : ℂ}
    (h : ∃ w ∈ B, heightRank H B w = heightRank H A z) :
    rankPartner H A B z ∈ B ∧
      heightRank H B (rankPartner H A B z) = heightRank H A z := by
  rw [rankPartner,dite_eq_left h]
  exact h.choose_spec

lemma rankPartner_eq {H : ℂ → ℝ} {A B : Set ℂ} {z w : ℂ}
    (hri : InjOn (heightRank H B) B) (hw : w ∈ B)
    (hr : heightRank H B w = heightRank H A z) : rankPartner H A B z = w := by
  have hs := rankPartner_spec ⟨w,hw,hr⟩
  exact hri hs.1 hw (hs.2.trans hr.symm)

lemma rankPartner_height {H : ℂ → ℝ} {A B : Set ℂ} {z : ℂ}
    (hz : z ∈ A) (hAf : (A ∩ {w | H z ≤ H w}).Finite)
    (hBf : (B ∩ {w | H z ≤ H w}).Finite)
    (hc : (A ∩ {w | H z ≤ H w}).ncard ≤ (B ∩ {w | H z ≤ H w}).ncard)
    (hri : InjOn (heightRank H B) B) : H z ≤ H (rankPartner H A B z) := by
  obtain ⟨w,hw,hh,hr⟩ := exists_equal_heightRank hz hAf hBf hc
  rw [rankPartner_eq hri hw hr]
  exact hh

lemma rankPartner_injOn {H : ℂ → ℝ} {A B : Set ℂ}
    (he : ∀ z ∈ A, ∃ w ∈ B, heightRank H B w = heightRank H A z)
    (hri : InjOn (heightRank H A) A) : InjOn (rankPartner H A B) A := by
  intro z hz w hw heq
  apply hri hz hw
  rw [← (rankPartner_spec (he z hz)).2,← (rankPartner_spec (he w hw)).2,heq]

def positiveFiber (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) : Set ℂ :=
  {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ 0 < normalizedJacobian f k z}

def negativeFiber (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) : Set ℂ :=
  {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ normalizedJacobian f k z < 0}

def criticalPair (f : ℂ → ℂ) (k : ℝ) (z : ℂ) : ℂ :=
  rankPartner (criticalHeight f k) (positiveFiber f k (criticalMap f k z))
    (negativeFiber f k (criticalMap f k z)) z

end Brennan

end

end OAI
