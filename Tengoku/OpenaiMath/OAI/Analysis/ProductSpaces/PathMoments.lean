import Tengoku.OpenaiMath.OAI.Analysis.ProductSpaces.TreeObstruction

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts
section CoordinateProducts

instance productMeasure_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (productMeasure μ) := by
  unfold productMeasure
  infer_instance

@[simp] theorem pathProduct_root (ω : Sample) : pathProduct [] ω = 1 := by
  simp [pathProduct]

lemma pathPrefix_length (v : Vertex) (j : Fin v.length) :
    (pathPrefix v j).val.length = j.val + 1 := by
  simp only [pathPrefix, List.length_take]
  exact min_eq_left (by omega)

lemma pathPrefix_injective (v : Vertex) : Function.Injective (pathPrefix v) := by
  intro i j h
  have hh := congrArg (fun e : Edge => e.val.length) h
  simp only [pathPrefix_length] at hh
  exact Fin.ext (by omega)

/-- The finite set of multiplier coordinates on a path. -/
def pathEdges (v : Vertex) : Finset Edge :=
  Finset.univ.map ⟨pathPrefix v, pathPrefix_injective v⟩

lemma pathProduct_eq_prod_pathEdges (v : Vertex) (ω : Sample) :
    pathProduct v ω = ∏ e ∈ pathEdges v, ω e := by
  simp [pathEdges, pathProduct]

lemma measurable_pathProduct (v : Vertex) : Measurable (pathProduct v) := by
  unfold pathProduct
  exact Finset.measurable_prod _ (fun _ _ => measurable_pi_apply _)

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma pathProduct_pos (hpos : ∀ᵐ w ∂μ, (0 : ℝ) < w) (v : Vertex) :
    ∀ᵐ ω ∂productMeasure μ, 0 < pathProduct v ω := by
  have hcoord : ∀ j : Fin v.length, ∀ᵐ ω ∂productMeasure μ,
      0 < ω (pathPrefix v j) := fun j =>
    (measurePreserving_eval_infinitePi (fun _ : Edge => μ) (pathPrefix v j)).quasiMeasurePreserving.ae hpos
  filter_upwards [ae_all_iff.mpr hcoord] with ω hω
  exact Finset.prod_pos (fun j _ => hω j)

end CoordinateProducts
end IndependentProducts

namespace IndependentProducts

@[simp] lemma child_length (v : Vertex) (n : ℕ) : (child v n).length = v.length + 1 := by
  unfold child
  rw [List.length_append]
  rfl

/-- The new coordinate on the edge from a vertex to one of its children. -/
def childEdge (v : Vertex) (n : ℕ) : Edge :=
  ⟨child v n, by simp [child]⟩

lemma childEdge_injective (v : Vertex) : Function.Injective (childEdge v) := by
  intro m n h
  have h' := congrArg Subtype.val h
  change v ++ [_] = v ++ [_] at h'
  have hh := List.cons.inj (List.append_cancel_left h')
  have := congrArg (fun x : ℕ+ => x.val) hh.1
  dsimp at this
  omega

lemma childEdge_not_mem_pathEdges (v : Vertex) (n : ℕ) : childEdge v n ∉ pathEdges v := by
  intro h
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
  have he := congrArg (fun e : Edge => e.val.length) hj
  simp only [Function.Embedding.coeFn_mk, pathPrefix_length, childEdge, child_length] at he
  omega

lemma pathProduct_child (v : Vertex) (n : ℕ) (ω : Sample) :
    pathProduct (child v n) ω = pathProduct v ω * ω (childEdge v n) := by
  let e : Fin (v.length + 1) ≃ Fin (child v n).length := finCongr (child_length v n).symm
  have he := Fintype.prod_equiv e
    (fun i => ω (pathPrefix (child v n) (e i)))
    (fun j => ω (pathPrefix (child v n) j)) (fun _ => rfl)
  change _ = (∏ j, ω (pathPrefix v j)) * _
  rw [show pathProduct (child v n) ω = ∏ i : Fin (v.length + 1),
    ω (pathPrefix (child v n) (e i)) from he.symm, Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    congr 1
    apply Subtype.ext
    change (child v n).take (j.val + 1) = v.take (j.val + 1)
    exact List.take_append_of_le_length (by omega)
  · congr 1
    apply Subtype.ext
    change (child v n).take (v.length + 1) = child v n
    rw [← child_length, List.take_length]

lemma measurable_childIncrement (v : Vertex) (n : ℕ) :
    Measurable (fun ω : Sample => pathProduct v ω * (ω (childEdge v n) - 1)) :=
  (measurable_pathProduct v).mul ((measurable_pi_apply _).sub_const 1)

section ChildMoments
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma indepFun_path_coordinate (v : Vertex) (e : Edge) (he : e ∉ pathEdges v) :
    IndepFun (pathProduct v) (fun ω : Sample => ω e) (productMeasure μ) := by
  have hi : iIndepFun (fun e : Edge => fun ω : Sample => ω e) (productMeasure μ) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hh := hi.indepFun_finsetProd_of_notMem (fun e => measurable_pi_apply e) he
  have heq : (∏ j ∈ pathEdges v, fun ω : Sample => ω j) = pathProduct v := by
    funext ω
    simp only [Finset.prod_apply, ← pathProduct_eq_prod_pathEdges]
  rwa [heq] at hh

lemma indepFun_finset_coordinates (s : Finset Edge) (f : Edge → ℝ → ℝ)
    (hf : ∀ e, Measurable (f e)) (e : Edge) (he : e ∉ s) :
    IndepFun (fun ω : Sample => ∏ i ∈ s, f i (ω i)) (fun ω : Sample => ω e)
      (productMeasure μ) := by
  classical
  let g : Edge → ℝ → ℝ := fun i => if i = e then id else f i
  have gmeas : ∀ i, Measurable (g i) := fun i => by
    dsimp [g]
    split_ifs
    · exact measurable_id
    · exact hf i
  have hi : iIndepFun (fun i : Edge => fun ω : Sample => g i (ω i)) (productMeasure μ) :=
    iIndepFun_infinitePi gmeas
  have hh := hi.indepFun_finsetProd_of_notMem
    (fun i => (gmeas i).comp (measurable_pi_apply i)) he
  have hg : (∏ i ∈ s, fun ω : Sample => g i (ω i)) = fun ω => ∏ i ∈ s, f i (ω i) := by
    funext ω
    simp only [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro i hi
    have hie : i ≠ e := fun hie => he (hie ▸ hi)
    simp [g, hie]
  rwa [hg, show (fun ω : Sample => g e (ω e)) = (fun ω => ω e) by simp [g]] at hh

lemma integral_coordinate (e : Edge) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ ω : Sample, f (ω e) ∂productMeasure μ) = ∫ w, f w ∂μ := by
  have hm : MeasurePreserving (fun ω : Sample => ω e) (productMeasure μ) μ :=
    measurePreserving_eval_infinitePi (fun _ : Edge => μ) e
  rw [← integral_map hm.measurable.aemeasurable hf.aestronglyMeasurable, hm.map_eq]

lemma integral_path_mul_coordinate (v : Vertex) (e : Edge) (he : e ∉ pathEdges v)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) :
    (∫ ω : Sample, f (pathProduct v ω) * g (ω e) ∂productMeasure μ) =
      (∫ ω, f (pathProduct v ω) ∂productMeasure μ) * ∫ w, g w ∂μ := by
  rw [(indepFun_path_coordinate μ v e he).integral_fun_comp_mul_comp
    (measurable_pathProduct v).aemeasurable (measurable_pi_apply e).aemeasurable
    hf.aestronglyMeasurable hg.aestronglyMeasurable, integral_coordinate μ e g hg]

lemma mean_abs_deviation_pos (h₂ : MemLp (fun w : ℝ => w) 2 μ)
    (hnot : ∀ c : ℝ, ¬ (∀ᵐ w ∂μ, w = c)) : 0 < ∫ w : ℝ, |w - 1| ∂μ := by
  have hi : Integrable (fun w : ℝ => |w - 1|) μ :=
    ((h₂.integrable (by norm_num)).sub (integrable_const 1)).abs
  have hnonneg : 0 ≤ ∫ w : ℝ, |w - 1| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
  apply lt_of_le_of_ne hnonneg
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ (fun w => abs_nonneg (w - 1))) hi).mp he.symm
  apply hnot 1
  filter_upwards [hz] with w hw
  exact sub_eq_zero.mp (abs_eq_zero.mp hw)

end ChildMoments
end IndependentProducts

end

end OAI
