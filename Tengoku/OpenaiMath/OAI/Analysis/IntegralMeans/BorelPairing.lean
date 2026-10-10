import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.RankPairing

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

lemma exists_borel_partial_inverse.{u_1, u_2} {X : Type u_1} {Y : Type u_2}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {s : Set X} (hs : MeasurableSet s) (hf : ContinuousOn f s) (hi : InjOn f s) :
    ∃ b : Y → X, Measurable b ∧ MeasurableSet (f '' s) ∧
      (∀ y ∈ f '' s, b y ∈ s ∧ f (b y) = y) ∧ ∀ x ∈ s, b (f x) = x := by
  classical
  have hm := hf.measurableEmbedding hs hi
  by_cases hne : s.Nonempty
  · let : Nonempty s := Set.nonempty_coe_sort.mpr hne
    let b : Y → X := fun y => (hm.invFun y).val
    refine ⟨b,measurable_subtype_coe.comp hm.measurable_invFun,?_,?_,?_⟩
    · simpa only [Set.range_domRestrict] using hm.measurableSet_range
    · rintro y ⟨x,hx,rfl⟩
      have hb : b (f x) = x := congrArg Subtype.val (hm.leftInverse_invFun ⟨x,hx⟩)
      exact ⟨hb.symm ▸ hx,congrArg f hb⟩
    · intro x hx
      exact congrArg Subtype.val (hm.leftInverse_invFun ⟨x,hx⟩)
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨fun _ => Classical.arbitrary X,measurable_const,?_,?_,?_⟩ <;> simp [he]

structure BorelBranches.{u_1, u_2} {X : Type u_1} {Y : Type u_2} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (s : Set X) where
  part : ℕ → Set X
  branch : ℕ → Y → X
  measurable_part : ∀ n, MeasurableSet (part n)
  disjoint : Pairwise (Disjoint on part)
  cover : (⋃ n, part n) = s
  injective : ∀ n, InjOn f (part n)
  measurable_branch : ∀ n, Measurable (branch n)
  measurable_image : ∀ n, MeasurableSet (f '' part n)
  right_inv : ∀ n y, y ∈ f '' part n → branch n y ∈ part n ∧ f (branch n y) = y
  left_inv : ∀ n x, x ∈ part n → branch n (f x) = x

lemma exists_borelBranches.{u_1, u_2} {X : Type u_1} {Y : Type u_2}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {s : Set X} (hf : ContinuousOn f s)
    (hp : ∃ p : ℕ → Set X, (∀ n, MeasurableSet (p n)) ∧ Pairwise (Disjoint on p) ∧
      (⋃ n, p n) = s ∧ ∀ n, InjOn f (p n)) : Nonempty (BorelBranches f s) := by
  obtain ⟨p,hpm,hpd,hpc,hpi⟩ := hp
  have hb (n) := exists_borel_partial_inverse (hpm n)
    (hf.mono (show p n ⊆ s from hpc ▸ subset_iUnion p n)) (hpi n)
  choose b hbm him hbr hbl using hb
  exact ⟨⟨p,b,hpm,hpd,hpc,hpi,hbm,him,hbr,hbl⟩⟩

def identityHalf (z : ℂ) : ℂ := z-Complex.I

lemma identityHalf_schlicht : HalfPlaneSchlicht identityHalf := by
  refine ⟨⟨(differentiable_id.sub_const Complex.I).differentiableOn,?_⟩,by simp [identityHalf],?_⟩
  · exact (sub_left_injective).injOn
  · exact (hasDerivAt_id Complex.I |>.sub_const Complex.I).deriv

def identityClass : DiskClass := classOfHalf identityHalf identityHalf_schlicht

def jointCriticalMap (k : ℝ) (q : DiskClass × halfPlane) : DiskClass × ℂ :=
  (q.1,criticalMap (classFun q.1) k q.2)

def nonsingularClass (k : ℝ) : Set (DiskClass × halfPlane) :=
  {q | normalizedJacobian (classFun q.1) k q.2 ≠ 0}

lemma continuous_jointCriticalMap (k : ℝ) : Continuous (jointCriticalMap k) :=
  continuous_fst.prodMk (continuous_class_criticalMap k)

def classPrecedes (k : ℝ) (q r : DiskClass × halfPlane) : Prop :=
  criticalHeight (classFun r.1) k r.2 < criticalHeight (classFun q.1) k q.2 ∨
  criticalHeight (classFun q.1) k q.2 = criticalHeight (classFun r.1) k r.2 ∧
    (q.2.val.re < r.2.val.re ∨ q.2.val.re = r.2.val.re ∧ q.2.val.im < r.2.val.im)

lemma measurableSet_classPrecedes (k : ℝ) :
    MeasurableSet {p : (DiskClass × halfPlane) × (DiskClass × halfPlane) | classPrecedes k p.1 p.2} := by
  have hH := (continuous_class_criticalHeight k).measurable
  have hr : Measurable (fun q : DiskClass × halfPlane => q.2.val.re) :=
    Complex.continuous_re.measurable.comp (measurable_subtype_coe.comp measurable_snd)
  have hi : Measurable (fun q : DiskClass × halfPlane => q.2.val.im) :=
    Complex.continuous_im.measurable.comp (measurable_subtype_coe.comp measurable_snd)
  exact (measurableSet_lt (hH.comp measurable_snd) (hH.comp measurable_fst)).union
    ((measurableSet_eq_fun (hH.comp measurable_fst) (hH.comp measurable_snd)).inter
      ((measurableSet_lt (hr.comp measurable_fst) (hr.comp measurable_snd)).union
        ((measurableSet_eq_fun (hr.comp measurable_fst) (hr.comp measurable_snd)).inter
          (measurableSet_lt (hi.comp measurable_fst) (hi.comp measurable_snd)))))

def classRankCount (k σ : ℝ) (q : DiskClass × halfPlane) : ℝ≥0∞ :=
  Measure.count {r | r ∈ nonsingularClass k ∧ jointCriticalMap k r = jointCriticalMap k q ∧
    0 < σ * normalizedJacobian (classFun r.1) k r.2 ∧ classPrecedes k r q}

def signedFiber (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) (σ : ℝ) : Set ℂ :=
  {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ 0 < σ * normalizedJacobian f k z}

lemma signedFiber_one (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) :
    signedFiber f k ξ 1 = positiveFiber f k ξ := by ext z; simp [signedFiber,positiveFiber]

lemma signedFiber_neg_one (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) :
    signedFiber f k ξ (-1) = negativeFiber f k ξ := by ext z; simp [signedFiber,negativeFiber]

lemma heightRank_transport_on {H H' : ℂ → ℝ} {S S' : Set ℂ} (e : ℂ ≃ ℂ)
    (hS : ∀ w, w ∈ S' ↔ e w ∈ S) (z : ℂ)
    (hord : ∀ w ∈ S', heightPrecedes H' w z ↔ heightPrecedes H (e w) (e z)) :
    heightRank H' S' z = heightRank H S (e z) := by
  rw [heightRank_eq_ncard,heightRank_eq_ncard]
  apply Set.ncard_congr (fun w _ => e w)
  · intro w hw
    exact ⟨(hS w).mp hw.1,(hord w hw.1).mp hw.2⟩
  · intro a b _ _ hab
    exact e.injective hab
  · intro w hw
    have hm : e.symm w ∈ S' := (hS _).mpr (by simpa using hw.1)
    exact ⟨e.symm w,⟨hm,(hord _ hm).mpr (by simpa using hw.2)⟩,e.apply_symm_apply w⟩

lemma heightPrecedes_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) (k : ℝ)
    {t z w : ℂ} (ht : t ∈ halfPlane) (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    heightPrecedes (criticalHeight (reroot f t) k) z w ↔
      heightPrecedes (criticalHeight f k) (affine t z) (affine t w) := by
  have hc := heightScaleInverse_pos hf k ht
  have hre (v : ℂ) : (affine t v).re = t.re+t.im*v.re := by simp [affine]
  have him (v : ℂ) : (affine t v).im = t.im*v.im := by simp [affine]
  simp only [heightPrecedes,criticalHeight_reroot hf k ht hz,criticalHeight_reroot hf k ht hw,
    div_lt_div_iff_of_pos_right hc,div_left_inj' (ne_of_gt hc),hre,him,
    add_lt_add_iff_left,add_right_inj,mul_lt_mul_iff_right₀ (show 0 < t.im from ht),mul_right_inj' (ne_of_gt (show 0 < t.im from ht))]

lemma signedFiber_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {t : ℂ} (ht : t ∈ halfPlane) (ξ : ℂ) (σ : ℝ) (w : ℂ) :
    w ∈ signedFiber (reroot f t) k (rerootTarget f t ξ) σ ↔
      affine t w ∈ signedFiber f k ξ σ := by
  simp only [signedFiber,mem_ofPred_eq,affine_mem_iff ht]
  apply and_congr_right
  intro hw
  rw [criticalMap_reroot_fiber hf k ht hw,normalizedJacobian_reroot hf ht hw k (ne_of_gt hk)]

lemma heightRank_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {t z : ℂ} (ht : t ∈ halfPlane) (hz : z ∈ halfPlane) (ξ : ℂ) (σ : ℝ) :
    heightRank (criticalHeight (reroot f t) k) (signedFiber (reroot f t) k (rerootTarget f t ξ) σ) z =
      heightRank (criticalHeight f k) (signedFiber f k ξ σ) (affine t z) := by
  apply heightRank_transport_on (affineHome t ht).toEquiv
    (signedFiber_reroot hf hk ht ξ σ) z
  intro w hw
  exact heightPrecedes_reroot hf k ht hw.1 hz

lemma heightRank_congr_on {H H' : ℂ → ℝ} {S : Set ℂ} (hS : S ⊆ halfPlane)
    (he : EqOn H H' halfPlane) {z : ℂ} (hz : z ∈ halfPlane) :
    heightRank H S z = heightRank H' S z := by
  rw [heightRank_eq_ncard,heightRank_eq_ncard]
  congr 1
  ext w
  apply and_congr_right
  intro hw
  simp only [heightPrecedes,he hz,he (hS hw)]

lemma signedFiber_congr {f g : ℂ → ℂ} (he : EqOn f g halfPlane) (k : ℝ) (ξ : ℂ) (σ : ℝ) :
    signedFiber f k ξ σ = signedFiber g k ξ σ := by
  ext z
  simp only [signedFiber,mem_ofPred_eq]
  apply and_congr_right
  intro hz
  rw [criticalMap_congr he k hz,normalizedJacobian_congr he k hz]

def halfOne : halfPlane := ⟨Complex.I,by simp [halfPlane]⟩

lemma class_normalizedJacobian_reroot (g : DiskClass) {k : ℝ} (hk : 0 < k)
    (t w : halfPlane) :
    normalizedJacobian (classFun (rerootClass g t)) k w =
      normalizedJacobian (classFun g) k (affine t w) := by
  rw [normalizedJacobian_congr (classFun_rerootClass g t) k w.property,
    normalizedJacobian_reroot (classFun_schlicht g).1 t.property w.property k (ne_of_gt hk)]

lemma class_goodPair_reroot (g : DiskClass) {k : ℝ} (hk : 0 < k) (t w : halfPlane) :
    GoodPair (classFun (rerootClass g t)) k
        (criticalMap (classFun (rerootClass g t)) k w) ↔
      GoodPair (classFun g) k (criticalMap (classFun g) k (affine t w)) := by
  rw [criticalMap_congr (classFun_rerootClass g t) k w.property,
    goodPair_congr (classFun_rerootClass g t) k,
    criticalMap_reroot (classFun_schlicht g).1 t.property w.property k]
  exact goodPair_reroot (classFun_schlicht g).1 hk t.property _

lemma class_normalizedJacobian_root (g : DiskClass) {k : ℝ} (hk : 0 < k) (z : halfPlane) :
    normalizedJacobian (classFun (rerootClass g z)) k Complex.I =
      normalizedJacobian (classFun g) k z := by
  simpa only [halfOne,affine_I] using class_normalizedJacobian_reroot g hk z halfOne

lemma class_goodPair_root (g : DiskClass) {k : ℝ} (hk : 0 < k) (z : halfPlane) :
    GoodPair (classFun (rerootClass g z)) k
        (criticalMap (classFun (rerootClass g z)) k Complex.I) ↔
      GoodPair (classFun g) k (criticalMap (classFun g) k z) := by
  simpa only [halfOne,affine_I] using class_goodPair_reroot g hk z halfOne

end Brennan

end

end OAI
