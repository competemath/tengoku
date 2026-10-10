import Tengoku.OpenaiMath.OAI.Analysis.DiamondDistortion.Incomparable

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace RecursiveModel

lemma aggregate_sq {ι : Type*} (f : ι →₀ ℝ) :
    (aggregate 2 f)^2=∑ i ∈ f.support,f i^2 := by
  have hh := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (finiteLp 2 f)
  have he : (aggregate 2 f)^2=∑' i,f i^2 := by
    simpa only [aggregate,ENNReal.toReal_ofNat,Real.rpow_two,finiteLp_apply,Real.norm_eq_abs,sq_abs] using hh
  rw [he]
  exact tsum_eq_sum (fun i hi => by rw [Finsupp.notMem_support_iff.mp hi]; norm_num)

lemma components_zero (p : ForestVec) (h : ℕ) (hh : h ∉ p.support.image Sigma.fst) :
    components p h=0 := by
  ext i
  change p ⟨h,i⟩=0
  apply Finsupp.notMem_support_iff.mp
  intro hi
  exact hh (Finset.mem_image.mpr ⟨⟨h,i⟩,hi,rfl⟩)

lemma outer_support (s : ∀ h,Seminorm ℝ (Vec (h+1))) (p : ForestVec) :
    (outerValues s p).support ⊆ p.support.image Sigma.fst := by
  intro h hh
  by_contra hn
  have he : outerValues s p h=0 := by rw [outerValues_apply,components_zero p h hn,map_zero]
  exact (Finsupp.mem_support_iff.mp hh) he

lemma outer_sq (s : ∀ h,Seminorm ℝ (Vec (h+1))) (p : ForestVec) (C : Finset ℕ)
    (hC : p.support.image Sigma.fst ⊆ C) :
    (outerSeminorm s p)^2=∑ h ∈ C,(s h (components p h))^2 := by
  change (aggregate 2 (outerValues s p))^2=_
  rw [aggregate_sq]
  apply Finset.sum_subset ((outer_support s p).trans hC)
  intro h _ hh
  rw [Finsupp.notMem_support_iff.mp hh]
  norm_num

lemma components_filter (p : ForestVec) (C : Set ℕ) (h : ℕ) :
    components (p.filter (fun i => i.1 ∈ C)) h=if h ∈ C then components p h else 0 := by
  ext i
  by_cases hh : h ∈ C
  · rw [ite_eq_left hh]
    change (p.filter (fun i => i.1 ∈ C)) ⟨h,i⟩=p ⟨h,i⟩
    rw [Finsupp.filter_apply,ite_eq_left hh]
  · rw [ite_eq_right hh]
    change (p.filter (fun i => i.1 ∈ C)) ⟨h,i⟩=0
    rw [Finsupp.filter_apply,ite_eq_right hh]

lemma outer_contractive (s : ∀ h,Seminorm ℝ (Vec (h+1))) (p : ForestVec) (C : Set ℕ) :
    outerSeminorm s (p.filter (fun i => i.1 ∈ C)) ≤ outerSeminorm s p := by
  apply aggregate_mono 2
  · exact outerValues_nonneg s _
  · intro h
    rw [outerValues_apply,outerValues_apply,components_filter]
    split_ifs
    · exact le_rfl
    · rw [map_zero]; exact apply_nonneg _ _

lemma outer_orthogonal (s : ∀ h,Seminorm ℝ (Vec (h+1))) (p q : ForestVec)
    (hd : Disjoint (p.support.image Sigma.fst) (q.support.image Sigma.fst)) :
    (outerSeminorm s (p+q))^2 ≤ (outerSeminorm s p)^2+(outerSeminorm s q)^2 := by
  let C := p.support.image Sigma.fst ∪ q.support.image Sigma.fst
  have hp : p.support.image Sigma.fst ⊆ C := Finset.subset_union_left
  have hq : q.support.image Sigma.fst ⊆ C := Finset.subset_union_right
  have hpq : (p+q).support.image Sigma.fst ⊆ C := by
    intro h hh
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hh
    rcases Finset.mem_union.mp (Finsupp.support_add hi) with hi | hi
    · exact hp (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    · exact hq (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  rw [outer_sq s p C hp,outer_sq s q C hq,outer_sq s (p+q) C hpq,← Finset.sum_add_distrib]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro h _
  rw [map_add,DFinsupp.add_apply]
  by_cases hh : h ∈ p.support.image Sigma.fst
  · have hhq := Finset.disjoint_left.mp hd hh
    rw [components_zero q h hhq,add_zero,map_zero,zero_pow (by decide : 2 ≠ 0),add_zero]
  · rw [components_zero p h hh,zero_add,map_zero,zero_pow (by decide : 2 ≠ 0),zero_add]

lemma energy_components (p : ForestVec) (C : Finset ℕ) (hC : p.support.image Sigma.fst ⊆ C) :
    (∑ i ∈ p.support,p i^2)=∑ h ∈ C,∑ i ∈ (components p h).support,(components p h i)^2 := by
  have he (h : ℕ) : p.split h=components p h := by ext i; rw [Finsupp.split_apply]; rfl
  have hh := p.sigma_sum (fun _ a => a^2)
  simp only [Finsupp.sum,he] at hh
  rw [hh]
  have hes : p.splitSupport=p.support.image Sigma.fst := by
    ext h
    simp only [Finsupp.splitSupport,Finset.mem_image]
  rw [hes]
  apply Finset.sum_subset hC
  intro h _ hh
  have hzero := components_zero p h hh
  rw [hzero,Finsupp.support_zero,Finset.sum_empty]

end RecursiveModel

namespace PathModel
open RecursiveModel
lemma path_norm (h : ℕ) (μ : L1 h) : ‖path h μ‖ ≤ (h+1:ℝ)*‖μ‖ := by
  have hb : ‖path h‖ ≤ (h+1:ℝ) :=
    LinearMap.mkContinuous_norm_le _ (by positivity : (0:ℝ) ≤ h+1) _
  exact ((path h).le_opNorm μ).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

lemma linear_l2 (h : ℕ) (v : L2 h) : ‖v‖ ≤ (h+1:ℝ)*cost 1 h v := by
  apply (presentation 1 h).bound v (by positivity : (0:ℝ) ≤ h+1)
  intro d hd
  change d.fst+path h d.snd=v at hd
  rw [← hd,WithLp.prod_norm_eq_of_L1]
  have hb := (norm_add_le d.fst (path h d.snd)).trans (add_le_add le_rfl (path_norm h d.snd))
  have hhn : 1 ≤ (h+1:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) h]
  have hn := norm_nonneg d.fst
  nlinarith

end PathModel

namespace StartModel
open RecursiveModel PathModel
namespace ContractiveMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def lift (f : E →ₗ[ℝ] F) (hf : ∀ x,‖f x‖ ≤ ‖x‖) :
    lp (fun _ : ℕ => E) 2 →ₗ[ℝ] lp (fun _ : ℕ => F) 2 where
  toFun v := ⟨fun i => f (v i),v.property.mono' (fun i => hf (v i))⟩
  map_add' v w := by ext i; exact f.map_add _ _
  map_smul' c v := by ext i; exact f.map_smul c _
lemma lift_norm (f : E →ₗ[ℝ] F) (hf : ∀ x,‖f x‖ ≤ ‖x‖)
    (v : lp (fun _ : ℕ => E) 2) : ‖lift f hf v‖ ≤ ‖v‖ :=
  lp.norm_mono (by norm_num) (fun i => hf (v i))

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
def prod₁ (f : E →ₗ[ℝ] F) (g : G →ₗ[ℝ] H) : WithLp 1 (E × G) →ₗ[ℝ] WithLp 1 (F × H) :=
  (WithLp.linearEquiv 1 ℝ (F × H)).symm.toLinearMap.comp
    ((f.prodMap g).comp (WithLp.linearEquiv 1 ℝ (E × G)).toLinearMap)
lemma prod₁_norm (f : E →ₗ[ℝ] F) (g : G →ₗ[ℝ] H) (hf : ∀ x,‖f x‖ ≤ ‖x‖)
    (hg : ∀ x,‖g x‖ ≤ ‖x‖) (d : WithLp 1 (E × G)) : ‖prod₁ f g d‖ ≤ ‖d‖ := by
  change ‖WithLp.toLp 1 (f d.fst,g d.snd)‖ ≤ ‖d‖
  rw [WithLp.prod_norm_eq_of_L1,WithLp.prod_norm_eq_of_L1]
  exact add_le_add (hf d.fst) (hg d.snd)
def single (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    {f : E →ₗ[ℝ] lp (fun _ : ℕ => E) 1 // ∀ d,‖f d‖ ≤ ‖d‖} :=
  ⟨lp.lsingle (𝕜 := ℝ) (E := fun _ : ℕ => E) 1 0,fun d => by
    change ‖(lp.single 1 0 d : lp (fun _ : ℕ => E) 1)‖ ≤ ‖d‖
    exact (lp.norm_single (E := fun _ : ℕ => E) (p := 1) (by norm_num) 0 d).le⟩
end ContractiveMap

/-- Repetition labels are retained: each start node admits a countable sequence
    of signed coefficient arrays over all its possible endpoints. Its mass is
    the ℓ¹ sum of the ℓ¹ norms of these arrays, before any cancellation. -/
abbrev rawRepresentationModel : ℕ → RealNormed
  | 0 => ⟨lp (fun _ : ℕ => ℝ) 1⟩
  | h+1 => ⟨WithLp 1 (lp (fun _ : ℕ => L1 (h+1)) 1 ×
      lp (fun _ : ℕ => rawRepresentationModel h) 2)⟩
abbrev Raw (h : ℕ) := rawRepresentationModel h

/-- Group repetitions at every start/end pair. Triangle inequalities make this
    operation contractive, rather than an unjustified equality of costs. -/
def compression : (h : ℕ) → {f : Raw h →ₗ[ℝ] Rep h // ∀ d,‖f d‖ ≤ ‖d‖}
  | 0 => ⟨(lp.tsumCLM ℝ ℕ ℝ).toLinearMap,lp.norm_tsum_le⟩
  | h+1 =>
    let prev := compression h
    let rootMap := (lp.tsumCLM ℝ ℕ (L1 (h+1))).toLinearMap
    let child := ContractiveMap.lift prev.val prev.property
    ⟨ContractiveMap.prod₁ rootMap child,
      ContractiveMap.prod₁_norm rootMap child lp.norm_tsum_le
        (ContractiveMap.lift_norm prev.val prev.property)⟩

/-- A representation with no repetitions is also one of the arbitrary countable
    representations, by placing all its coefficients in repetition row zero. -/
def expansion : (h : ℕ) → {f : Rep h →ₗ[ℝ] Raw h // ∀ d,‖f d‖ ≤ ‖d‖}
  | 0 => ContractiveMap.single ℝ
  | h+1 =>
    let prev := expansion h
    let rootMap := ContractiveMap.single (L1 (h+1))
    let child := ContractiveMap.lift prev.val prev.property
    ⟨ContractiveMap.prod₁ rootMap.val child,
      ContractiveMap.prod₁_norm rootMap.val child rootMap.property
        (ContractiveMap.lift_norm prev.val prev.property)⟩

lemma tsum_single_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (x : E) :
    lp.tsumCLM ℝ ℕ E (lp.single 1 0 x)=x := by
  change ∑' i,(lp.single 1 0 x : lp (fun _ : ℕ => E) 1) i=x
  rw [tsum_eq_single 0,lp.single_apply_self]
  intro i hi
  exact lp.single_apply_ne _ _ _ hi

lemma compression_expansion (h : ℕ) (d : Rep h) :
    (compression h).val ((expansion h).val d)=d := by
  induction h with
  | zero => exact tsum_single_zero d
  | succ h ih =>
    apply WithLp.ofLp_injective
    apply Prod.ext
    · change lp.tsumCLM ℝ ℕ (L1 (h+1)) (lp.single 1 0 d.fst)=d.fst
      exact tsum_single_zero d.fst
    · ext i
      exact ih (d.snd i)

/-- Literal coordinatewise output of countably many signed segments: first sum
    all rows with a common start/end, then use the absolutely summable path map. -/
def rawOutput (h : ℕ) : Raw h →ₗ[ℝ] (Coord h → ℝ) :=
  (output h).comp (compression h).val

def rawRelation (h : ℕ) : InfimalCost.Relation (Raw h) (Vec h) (Coord h → ℝ) where
  output := rawOutput h
  value := (relation h).value
  sectionMap := (expansion h).val.comp (finiteSection h)
  section_output v := by
    change output h ((compression h).val ((expansion h).val (finiteSection h v)))=(relation h).value v
    rw [compression_expansion]
    exact (relation h).section_output v

end StartModel

end DiamondDistortion

end

end OAI
