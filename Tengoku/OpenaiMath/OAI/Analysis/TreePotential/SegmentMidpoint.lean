import Tengoku.OpenaiMath.OAI.Analysis.TreePotential.SegmentDual

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.Segments

def treeNode (h : ℕ) (s : Tree h) : Node := ⟨h,⟨s.val,s.property.trans (Nat.le_succ h)⟩⟩

def rootSegment (h : ℕ) (s : Tree h) : Segment :=
  ⟨⟨h,⟨[],by simp⟩⟩,treeNode h s,⟨rfl,List.nil_prefix⟩⟩

lemma rootSegment_mem (h : ℕ) (s : Tree h) (v : Node) :
    v ∈ (rootSegment h s).nodes ↔ v.1=h ∧ v.2.val <+: s.val := by
  rw [Segment.mem_nodes]
  constructor
  · intro hv
    exact hv.2
  · rintro ⟨hv,hp⟩
    exact ⟨⟨hv.symm,List.nil_prefix⟩,⟨hv,hp⟩⟩

lemma treeNode_child_injective {h : ℕ} (s : Tree h) (hs : s.val.length < h) :
    Function.Injective (fun n => treeNode h (child s hs n)) := by
  intro i j hij
  have he := congrArg (fun v : Node => v.2.val) hij
  change s.val++[i]=s.val++[j] at he
  simpa using (List.append_cancel_left he)

lemma treeNode_child_prefix {h : ℕ} (s : Tree h) (hs : s.val.length < h) {i j : ℕ}
    (hp : Prefix (treeNode h (child s hs i)) (treeNode h (child s hs j))) : i=j := by
  have he := hp.2.eq_of_length (by simp [treeNode,child])
  simpa only [treeNode,child,List.append_cancel_left_eq,List.cons.injEq,and_true] using he

lemma segmentVector_root_child {h : ℕ} (s : Tree h) (hs : s.val.length < h) (j : ℕ) :
    segmentVector (rootSegment h (child s hs j))=
      segmentVector (rootSegment h s)+Finsupp.single (treeNode h (child s hs j)) 1 := by
  ext v
  simp only [Finsupp.add_apply,segmentVector_apply,rootSegment_mem,Finsupp.single_apply]
  by_cases he : treeNode h (child s hs j)=v
  · subst v
    have hn : ¬(child s hs j).val <+: s.val := by
      intro hh
      have hl := hh.length_le
      simp only [child,List.length_append,List.length_singleton] at hl
      omega
    simp [treeNode,hn]
  · have hn : ¬(v.1=h ∧ v.2.val=s.val++[j]) := by
      rintro ⟨hc,hl⟩
      apply he
      cases v with
      | mk n v =>
        dsimp at hc hl
        subst n
        unfold treeNode
        congr 1
        exact Subtype.ext hl.symm
    rw [ite_eq_right he,add_zero]
    simp only [child,prefix_child_iff,and_or_left]
    have hnot : ¬(v.1=h ∧ v.2.val=s.val++[j]) := hn
    simp only [hnot,or_false]

def boundedPath (h : ℕ) (s : Tree h) : DualCore := coreLift (segmentVector (rootSegment h s))

lemma boundedPath_norm (h : ℕ) (s : Tree h) : ‖boundedPath h s‖=1 := by
  change ‖(((testVectorEquiv unitTests).symm (segmentVector (rootSegment h s)) : TestVector unitTests) : DualCore)‖=1
  rw [UniformSpace.Completion.norm_coe,segmentVector_norm]

lemma boundedPath_increment {h : ℕ} (s : Tree h) (hs : s.val.length < h) (j : ℕ) :
    boundedPath h (child s hs j)-boundedPath h s=coordinateVector unitTests (treeNode h (child s hs j)) := by
  unfold boundedPath
  rw [segmentVector_root_child,map_add,add_sub_cancel_left]
  rfl

lemma core_child_hilbert_upper {h : ℕ} (s : Tree h) (hs : s.val.length < h)
    (A : Finset ℕ) (a : ℕ → ℝ) :
    ‖∑ j ∈ A,a j • coordinateVector unitTests (treeNode h (child s hs j))‖ ≤
      Real.sqrt (∑ j ∈ A,(a j)^2) := by
  let v := fun j => treeNode h (child s hs j)
  let S := fun j => Segment.singleton (v j)
  have hinj : Function.Injective S := by
    intro i j hij
    exact treeNode_child_injective s hs (congrArg Segment.start hij)
  have hinc : Incomparable (A.image S) := by
    rintro U hU V hV hUV
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hV
    constructor
    · intro hp
      exact hUV (congrArg S (treeNode_child_prefix s hs hp))
    · intro hp
      exact hUV (congrArg S (treeNode_child_prefix s hs hp).symm)
  have hg (g : unitTests) : (∑ j ∈ A,(g.val (v j))^2) ≤ 1 := by
    have hh := g.property (A.image S) hinc
    rw [Finset.sum_image (fun i hi j hj hij => hinj hij)] at hh
    simpa only [S,Segment.eval_singleton] using hh
  have he : (∑ j ∈ A,a j • coordinateVector unitTests (v j))=
      coreLift (∑ j ∈ A,a j • Finsupp.single (v j) 1) := by
    simp only [map_sum,map_smul]
    rfl
  change ‖∑ j ∈ A,a j • coordinateVector unitTests (v j)‖≤_
  rw [he]
  change ‖(((testVectorEquiv unitTests).symm (∑ j ∈ A,a j • Finsupp.single (v j) 1) : TestVector unitTests) : DualCore)‖≤_
  rw [UniformSpace.Completion.norm_coe]
  change testNorm unitTests (∑ j ∈ A,a j • Finsupp.single (v j) 1)≤_
  apply ciSup_le
  intro g
  simp only [map_sum,map_smul,smul_eq_mul]
  have hT : 0 ≤ ∑ j ∈ A,(a j)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb := Finset.sum_mul_sq_le_sq_mul_sq A a (fun j => g.val (v j))
  have hc := mul_le_mul_of_nonneg_left (hg g) hT
  have hh : |∑ j ∈ A,a j*g.val (v j)| ≤ Real.sqrt (∑ j ∈ A,(a j)^2) := by
    nlinarith [Real.sq_sqrt hT,Real.sqrt_nonneg (∑ j ∈ A,(a j)^2),
      sq_abs (∑ j ∈ A,a j*g.val (v j)),abs_nonneg (∑ j ∈ A,a j*g.val (v j))]
  simpa [finitePairing,Finsupp.linearCombination_single] using hh

lemma core_children_weaklyNull {h : ℕ} (s : Tree h) (hs : s.val.length < h) :
    WeaklyNull (fun j => coordinateVector unitTests (treeNode h (child s hs j))) :=
  weaklyNull_of_hilbert_upper _ (core_child_hilbert_upper s hs)

theorem incomparable_core_renorming_obstruction {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : DualCore ≃L[ℝ] Y) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (he : ∀ x, α*‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β*‖x‖) :
    oneSidedModulus Y (α/(2*β))=0 := by
  have hb : ∀ h, 1 ≤ h → ∀ s : Tree h, (1:ℝ) ≤ ‖boundedPath h s‖ ∧ ‖boundedPath h s‖ ≤ 1 := by
    intro h hh s
    simp [boundedPath_norm]
  have hw : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun j => boundedPath h (child s hs j)-boundedPath h s) := by
    intro h hh s hs
    simpa only [boundedPath_increment] using core_children_weaklyNull s hs
  have hi : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (j : ℕ),
      (1:ℝ) ≤ ‖boundedPath h (child s hs j)-boundedPath h s‖ := by
    intro h hh s hs j
    simp only [boundedPath_increment,norm_coordinateVector,le_refl]
  simpa only [mul_one] using bounded_tree_renorming_obstruction boundedPath zero_lt_one le_rfl
    zero_lt_one hb hw hi e hα hαβ he

lemma core_head_approx (x : DualCore) {ε : ℝ} (hε : 0 < ε) :
    ∃ E : Finset Node, Initial (E : Set Node) ∧ ‖completedTail unitTests E x‖ < ε := by
  obtain ⟨w,hw⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x hε
  let z := testVectorEquiv unitTests w
  let E := prefixClosure z.support
  have hE : Initial (E : Set Node) := initial_prefixClosure z.support
  have hz : Finsupp.filter (fun v => v ∈ E) z=z := by
    ext v
    by_cases hv : v ∈ z.support
    · have hvE : v ∈ E := subset_prefixClosure z.support hv
      simp [hvE]
    · simp [Finsupp.filter_apply,Finsupp.notMem_support_iff.mp hv]
  have hhead : completedHead unitTests E (w : DualCore)=(w : DualCore) := by
    rw [completedHead_coe]
    change (((testVectorEquiv unitTests).symm (Finsupp.filter (fun v => v ∈ E) z) : TestVector unitTests) : DualCore)=_
    rw [hz]
    rfl
  have he : completedTail unitTests E x=completedTail unitTests E (x-(w : DualCore)) := by
    simp only [map_sub,completedTail_apply,hhead,sub_self,sub_zero]
  refine ⟨E,hE,?_⟩
  rw [he]
  exact (core_tail_norm E hE _).trans_lt (by simpa only [dist_eq_norm] using hw)

lemma incomparable_squared_core {E : Finset Node} (hE : Initial (E : Set Node))
    (x y : DualCore) (hx : completedHead unitTests E x=x) {R : ℝ}
    (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖completedTail unitTests E y‖^2 ≤ (Real.sqrt 2+Real.sqrt 6)^2*R*(R-‖x‖) := by
  have hxn : ‖x‖ ≤ R := by linarith [norm_center_le_avg x y]
  have hyn : ‖y‖ ≤ R := by linarith [norm_displacement_le_avg x y]
  have hR : 0 ≤ R := (norm_nonneg x).trans hxn
  by_cases hz : R=0
  · have hy0 : y=0 := norm_eq_zero.mp (by linarith [norm_nonneg y])
    subst y
    rw [map_zero,norm_zero,hz]
    ring_nf
    exact le_refl _
  · have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
    have hxp : completedHead unitTests E (R⁻¹ • x)=R⁻¹ • x := by rw [map_smul,hx]
    have hpn : ‖R⁻¹ • x+R⁻¹ • y‖ ≤ 1 := by
      rw [← smul_add,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR)]
      exact (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hR)).trans_eq (inv_mul_cancel₀ hz)
    have hmn : ‖R⁻¹ • x-R⁻¹ • y‖ ≤ 1 := by
      rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR)]
      exact (mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hR)).trans_eq (inv_mul_cancel₀ hz)
    have hh := incomparable_tail_core hE (R⁻¹ • x) (R⁻¹ • y) hxp hpn hmn
    rw [map_smul,norm_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR)] at hh
    have hgap : 0 ≤ 1-R⁻¹*‖x‖ := by
      have he := mul_le_mul_of_nonneg_left hxn (inv_nonneg.mpr hR)
      rw [inv_mul_cancel₀ hz] at he
      linarith
    have hs := Real.sq_sqrt hgap
    have hn := Real.sqrt_nonneg (1-R⁻¹*‖x‖)
    have hK : 0 ≤ Real.sqrt 2+Real.sqrt 6 := by positivity
    have he : (R⁻¹*‖completedTail unitTests E y‖)^2 ≤
        (Real.sqrt 2+Real.sqrt 6)^2*(1-R⁻¹*‖x‖) := by
      have hp := mul_nonneg (sub_nonneg.mpr hh)
        (show 0 ≤ (Real.sqrt 2+Real.sqrt 6)*Real.sqrt (1-R⁻¹*‖x‖)+R⁻¹*‖completedTail unitTests E y‖ by positivity)
      nlinarith
    have ht := mul_le_mul_of_nonneg_left he (sq_nonneg R)
    field_simp [hz] at ht
    nlinarith

end BoundedTreePotentials.Segments

end

end OAI
