import Tengoku.OpenaiMath.OAI.Geometry.PinnedDistances.TreeContradiction

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23

section
namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma transformed_half (r : ℝ) (C : Finset P) (hC : C ∈ d.transformed r) :
    2*C.card≤Fintype.card P := by
  rw [transformed,Multiset.mem_add] at hC
  rcases hC with hC | hC
  · exact Nat.le_of_not_gt (Finset.mem_filter.mp hC).2
  · obtain ⟨B,hB,hBC⟩ := Multiset.mem_map.mp hC
    have hh := (d.mem_giants r B).mp hB
    subst C
    rw [Finset.card_compl]
    have := Finset.card_le_univ B
    omega

lemma mass_half (C : Finset P) (hC : Fintype.card P<2*C.card) : d.mass C=0 := by
  have hz (r : ℝ) : d.count r C=0 := by
    unfold count
    have hh : C ∉ d.transformed r := fun hc => hC.not_ge (d.transformed_half r C hc)
    simp [Multiset.count_eq_zero.mpr hh]
  simp [mass,hz]
end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Global
open Hierarchy
variable {P : Type u2} [Fintype P] [DecidableEq P]
variable {K : Type u3} [Field K] [NumberField K]
variable (Z : P → K) (hZ : Function.Injective Z)
lemma cellMass_half (C : Finset P) (hC : Fintype.card P<2*C.card) : cellMass Z hZ C=0 := by
  simp only [cellMass,Depth.mass_half _ C hC,MeasureTheory.integral_zero,mul_zero,Finset.sum_const_zero,add_zero]

lemma totalMass_half (Z₂ : P → K) (h₂ : Function.Injective Z₂)
    (C : Finset P) (hC : 1/2<Variance.cellProb Finset.univ C) :
    totalMass Z Z₂ hZ h₂ C=0 := by
  have hn0 : (0:ℝ)<Fintype.card P := by
    by_contra! hn
    have hz : Fintype.card P=0 := by exact_mod_cast (le_antisymm hn (Nat.cast_nonneg _))
    simp [Variance.cellProb,hz] at hC
    linarith
  have hh : Fintype.card P<2*C.card := by
    simp only [Variance.cellProb,Finset.univ_inter,Finset.card_univ] at hC
    have hl := (lt_div_iff₀ hn0).mp hC
    exact_mod_cast (show (Fintype.card P:ℝ)<2*C.card by linarith)
  simp only [totalMass,cellMass_half _ _ C hh,add_zero]
end WeakPinned.Global

namespace WeakPinned.Variance
open scoped BigOperators
open Cuts SmallFiber
variable {P : Type u4} {I : Type u5} [Fintype P] [Fintype I] [DecidableEq P]

omit [Fintype P] in
lemma uniform_slice_nonneg (w : I → ℝ) (B : I → Finset P) (src : I → P) (lam : ℝ)
    (hw : ∀ i, 0≤w i) (C : Finset P) : 0 ≤ slice w (fun i => prob (B i)) src lam C := by
  unfold slice
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (by
    split_ifs
    · simp only [SmallFiber.mass,sum_prob_cell]; exact cellProb_nonneg _ _
    · exact le_rfl))

omit [Fintype P] in
lemma edgeCell_le_one (w : I → ℝ) (B : I → Finset P) (src : I → P)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (C : Finset P) :
    edgeCell w (fun i => prob (B i)) src C≤1 := by
  rw [edgeCell_formula]
  apply le_trans _ hW
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : src i ∈ C
  · simp only [ite_eq_left hi,SmallFiber.mass,sum_prob_cell]
    nlinarith [mul_le_mul_of_nonneg_left (cellProb_le_one (B i) C) (hw i)]
  · simp [hi,hw i]

/-- Positive balanced cut length pays all q-overlap except the small-fiber
slice and cell variance. This is the exact occurrence extraction inequality. -/
lemma balanced_mass_extraction (m : Finset P → ℝ) (hm : ∀ C, 0 ≤ m C)
    (hhalf : ∀ C, 1/2<cellProb Finset.univ C → m C=0)
    (w : I → ℝ) (B : I → Finset P) (src : I → P) (T δ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hδ : 0<δ) (_hδ4 : δ≤1/4)
    (hk : ∀ i, 2/((B i).card:ℝ)≤4*δ) :
    weightedIntegral m (edgeCell w (fun i => prob (B i)) src)≤
      weightedIntegral m (slice w (fun i => prob (B i)) src (4*δ))+
      (1/δ)*weightedIntegral m (varianceCell w B T)+
      (1/δ)*weightedIntegral m (fun C => tent δ (cellProb Finset.univ C)) := by
  have hpoint (C : Finset P) :
      m C*edgeCell w (fun i => prob (B i)) src C ≤
        m C*(slice w (fun i => prob (B i)) src (4*δ) C+
          (1/δ)*varianceCell w B T C+(1/δ)*tent δ (cellProb Finset.univ C)) := by
    by_cases hh : 1/2<cellProb Finset.univ C
    · rw [hhalf C hh]; simp
    have ha : cellProb Finset.univ C≤1/2 := le_of_not_gt hh
    apply mul_le_mul_of_nonneg_left _ (hm C)
    by_cases hs : cellProb Finset.univ C≤2*δ
    · have hx := small_mass_qCell (B := B) src T (2*δ) hw (by positivity) (fun i => by nlinarith [hk i]) C hs
      have he : (∑ i, w i*(if src i ∈ C then cellProb (B i) C else 0)) =
          edgeCell w (fun i => prob (B i)) src C := by
        rw [edgeCell_formula]; simp only [SmallFiber.mass,sum_prob_cell]
      have hf : (∑ i, w i*(if src i ∈ C ∧ cellProb (B i) C<2*(2*δ) then cellProb (B i) C else 0)) =
          slice w (fun i => prob (B i)) src (4*δ) C := by
        unfold slice
        simp only [SmallFiber.mass,sum_prob_cell,show (2:ℝ)*(2*δ)=4*δ by ring]
      rw [he,hf,show (2:ℝ)/(2*δ)=1/δ by ring] at hx
      exact hx.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) (tent_nonneg _ _)))
    · have htent : δ≤tent δ (cellProb Finset.univ C) := tent_lower (le_of_not_ge hs) (by linarith)
      have hh : 1≤(1/δ)*tent δ (cellProb Finset.univ C) := by
        have := mul_le_mul_of_nonneg_left htent (show 0≤1/δ by positivity)
        simpa [ne_of_gt hδ] using this
      have he := (edgeCell_le_one w B src hw hW C).trans hh
      have hn := uniform_slice_nonneg w B src (4*δ) hw C
      have hv := mul_nonneg (show 0≤1/δ by positivity) (varianceCell_nonneg w B T hw C)
      linarith
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun C _ => hpoint C)
  change weightedIntegral m (edgeCell w (fun i => prob (B i)) src)≤_ at hh
  convert hh using 1
  simp only [weightedIntegral,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  have hcomm (f : Finset P → ℝ) :
      (1/δ) * ∑ C, m C * f C = ∑ C, m C * ((1/δ)*f C) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  simp only [Finset.mul_sum] at hcomm
  rw [hcomm, hcomm]
end WeakPinned.Variance

namespace WeakPinned
open Filter Variance Global Cuts
open scoped Topology BigOperators

lemma change_scale_rate (W A X : ℕ → ℝ) (C : ℝ) (hC : 0<C)
    (hW : ∀ j, 0≤W j) (hA : ∀ j, 0≤A j) (hX : ∀ j, 0≤X j)
    (hWtop : Tendsto W atTop atTop)
    (hcomp : ∀ᶠ j in atTop, A j≤C*(W j+1))
    (hrate : Tendsto (fun j => X j/(W j+A j+1)) atTop (𝓝 0)) :
    Tendsto (fun j => X j/W j) atTop (𝓝 0) := by
  have hb : ∀ᶠ j in atTop, X j/W j≤(2+2*C)*(X j/(W j+A j+1)) := by
    filter_upwards [hWtop.eventually (eventually_ge_atTop (1:ℝ)),hcomp] with j hj hc
    have hw : 0<W j := by linarith
    have hd : 0<W j+A j+1 := by linarith [hA j]
    apply (div_le_iff₀ hw).mpr
    have hbound : W j+A j+1≤(2+2*C)*W j := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hbound (hX j)
    convert (div_le_div_of_nonneg_right hh hd.le) using 1 <;> field_simp
  exact squeeze_zero' (Eventually.of_forall (fun j => div_nonneg (hX j) (hW j))) hb
    (by simpa using hrate.const_mul (2+2*C))

lemma balanced_extraction_rate (W A V L Q S a : ℕ → ℝ) (C δ b : ℝ)
    (hC : 0<C) (hδ : 0<δ) (hb : 0≤b) (hbC : 2*b*C≤1/8)
    (hW : ∀ j, 0≤W j) (hA : ∀ j, 0≤A j) (hV : ∀ j, 0≤V j)
    (hWtop : Tendsto W atTop atTop)
    (hcomp : ∀ᶠ j in atTop, A j≤C*(W j+1))
    (ha : Tendsto a atTop (𝓝 0))
    (hvar : Tendsto (fun j => V j/(W j+A j+1)) atTop (𝓝 0))
    (hQ : ∀ᶠ j in atTop, W j-a j*A j≤Q j)
    (hS : ∀ᶠ j in atTop, S j≤W j/8+b*A j+32)
    (hext : ∀ᶠ j in atTop, Q j≤S j+V j/δ+L j/δ) :
    ∀ᶠ j in atTop, (δ/4)*W j≤L j := by
  have hv := change_scale_rate W A V C hC hW hA hV hWtop hcomp hvar
  have ha0 : Tendsto (fun j => |a j|) atTop (𝓝 0) := by simpa using ha.abs
  filter_upwards [hWtop.eventually (eventually_ge_atTop (256:ℝ)),hcomp,
    ha0.eventually (gt_mem_nhds (show 0<1/(8*C) by positivity)),
    hv.eventually (gt_mem_nhds (show 0<δ/8 by positivity)),hQ,hS,hext] with j hw hc ha hv hq hs he
  have hw0 : 0<W j := by linarith
  have hac : A j≤2*C*W j := by nlinarith
  have ha' : a j*A j≤W j/4 := by
    have hh := mul_le_mul_of_nonneg_right (le_trans (le_abs_self (a j)) ha.le) (hA j)
    have hh' := mul_le_mul_of_nonneg_left hac (show 0≤1/(8*C) by positivity)
    have hz : (1/(8*C))*(2*C*W j)=W j/4 := by field_simp; ring
    rw [hz] at hh'
    exact hh.trans hh'
  have hbA : b*A j≤W j/8 := by
    have h1 := mul_le_mul_of_nonneg_left hac hb
    have h2 := mul_le_mul_of_nonneg_right hbC hw0.le
    nlinarith
  have hv' : V j/δ≤W j/8 := by
    have hh := (div_lt_iff₀ hw0).mp hv
    apply (div_le_iff₀ hδ).mpr
    nlinarith
  have hL : W j/4≤L j/δ := by linarith
  have := (le_div_iff₀ hδ).mp hL
  nlinarith

end WeakPinned

namespace WeakPinned
open Filter Variance Global Cuts SmallFiber
open scoped Topology BigOperators
variable {V : ℕ → Type u6} {I : ℕ → Type u7} {K : ℕ → Type u8} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

end WeakPinned
noncomputable section
namespace WeakPinned.Cuts
open Hierarchy Variance
variable {P : Type u9} [Fintype P] [DecidableEq P]
lemma tent_length_occurrence (d : Depth P) (hn : 2≤Fintype.card P) (δ : ℝ) (hδ : 0≤δ)
    (has : ∀ x, prob (Finset.univ : Finset P) x≤δ) :
    (∑ C ∈ d.allCuts, d.cutLength (fun B => tent δ (mass (prob Finset.univ) B)) C)=
      weightedIntegral d.mass (fun C => tent δ (cellProb Finset.univ C)) := by
  have ha : ∑ x, prob (Finset.univ : Finset P) x=1 :=
    sum_prob _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))
  symm
  simp only [← sum_prob_cell]
  change weightedIntegral d.mass (fun C => tent δ (mass (prob Finset.univ) C))=_
  exact d.symmetric_integral_cut_sum hn _ (fun C hC => tent_zero_left (mass_small _ δ hδ has C hC))
    (fun C => by rw [mass_complement _ ha,tent_symm])
end WeakPinned.Cuts

namespace WeakPinned.Global
open Hierarchy Variance Cuts MeasureTheory
open scoped BigOperators
variable {P : Type u10} [Fintype P] [DecidableEq P]
variable {K : Type u11} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

lemma average_swap (f : Depth P → Depth P → ℝ) :
    average Z₂ Z₁ h₂ h₁ f=average Z₁ Z₂ h₁ h₂ (fun d d' => f d' d) := by
  classical
  unfold average placeUnion
  rw [Finset.union_comm (badPlaces Z₂ h₂)]

def localTotalIntegral (f : Finset P → ℝ) (d d' : Depth P) : ℝ :=
  weightedIntegral d.mass f+weightedIntegral d'.mass f

end WeakPinned.Global

namespace WeakPinned.Core.Fibers
open Hierarchy Variance Cuts Global
variable {V : Type u12} {I : Type u13} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)
lemma two_length_upper (d d' : Depth V) (δ T : ℝ) (hδ : 0≤δ) (hT : 0<T)
    (hn : 2≤Fintype.card V) (hG : 0<G.edgeCount)
    (has : ∀ x, prob (Finset.univ : Finset V) x≤δ)
    (hps : ∀ e x, prob (G.targets e) x≤δ) (hpn : ∀ e, (G.targets e).Nonempty)
    (hrs : ∀ y x, prob (G.retainedSet T y) x≤δ) (hrn : ∀ y, (G.retainedSet T y).Nonempty) :
    δ^3*localTotalIntegral (fun C => tent δ (cellProb Finset.univ C)) d d'≤
      2*(fiberCutDiscrepancy G.fiberWeight (fun e => prob (G.targets e)) G.source δ d d'+
        fiberCutDiscrepancy G.fiberWeight (fun e => prob (G.targets e)) G.source δ d' d)+
      6*localTotalIntegral (familyCutError G.fiberWeight G.targets δ) d d'+
      2*localTotalIntegral (familyCutError (G.retainedWeight T) (G.retainedSet T) δ) d d'+
      2*G.omittedMass T*localTotalIntegral (fun C => tent δ (cellProb Finset.univ C)) d d' := by
  have h1 := G.graph_length_upper d d' δ T hδ hT hn hG has hps hpn hrs hrn
  have h2 := G.graph_length_upper d' d δ T hδ hT hn hG has hps hpn hrs hrn
  simp only [tent_length_occurrence _ hn δ hδ has,
    family_charge_occurrence _ hn G.fiberWeight G.targets hpn δ hδ hps has,
    family_charge_occurrence _ hn (G.retainedWeight T) (G.retainedSet T) hrn δ hδ hrs has] at h1 h2
  dsimp only [localTotalIntegral]
  linarith
end WeakPinned.Core.Fibers

namespace WeakPinned.Global
open Hierarchy Variance Cuts MeasureTheory
variable {V : Type u14} {I : Type u15} [Fintype V] [Fintype I] [DecidableEq V]
variable {K : Type u16} [Field K] [NumberField K]
variable (G : Core.Fibers V I) (Z₁ Z₂ : V → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

end WeakPinned.Global
noncomputable section
namespace WeakPinned
open Filter Variance Core.Fibers
open scoped Topology
variable {V : Type u17} {I : Type u18} [Fintype V] [Fintype I] [DecidableEq V]

omit [Fintype V] in
lemma prob_bound_of_size (B : Finset V) (δ : ℝ) (hδ : 0<δ) (hB : 1/δ≤(B.card:ℝ)) :
    B.Nonempty ∧ ∀ x, prob B x≤δ := by
  have hb : 0<(B.card:ℝ) := (one_div_pos.mpr hδ).trans_le hB
  refine ⟨Finset.card_pos.mp (by exact_mod_cast hb),?_⟩
  intro x
  unfold prob
  split_ifs
  · exact (div_le_iff₀ hb).mpr (by have := (div_le_iff₀ hδ).mp hB; nlinarith)
  · exact hδ.le

lemma PreparedGraph.omitted_bound {G : Core.Fibers V I} {θ γ c η : ℝ}
    (hG : PreparedGraph V I G θ γ c η) (hθ : 0<θ) (hη : η≤θ/2) :
    G.omittedMass ((Fintype.card V:ℝ)^γ) ≤ (4/θ)*(Fintype.card V:ℝ)^(γ-1) := by
  let n : ℝ := Fintype.card V
  have hn : 2≤n := by dsimp only [n]; exact_mod_cast hG.card_ge
  have hn0 : 0<n := by linarith
  have hE := hG.edgeCount_pos (by linarith)
  have hEl : (θ/4)*n^2≤G.edgeCount := by
    have hp : 0≤(n-1)*n := mul_nonneg (by linarith) hn0.le
    have hh := mul_nonneg (show 0≤θ-η-θ/2 by linarith) hp
    have hh' := mul_nonneg (show 0≤θ/4 by positivity) (show 0≤n*(n-2) by positivity)
    dsimp [n] at *
    nlinarith [hG.lower]
  apply (G.small_incoming_mass _ (Real.rpow_nonneg hn0.le γ)).trans
  change n*n^γ/G.edgeCount≤(4/θ)*n^(γ-1)
  rw [Real.rpow_sub hn0,Real.rpow_one]
  apply (div_le_iff₀ hE).mpr
  have hh := mul_le_mul_of_nonneg_left hEl (show 0≤(4/θ)*(n^γ/n) by positivity)
  have he : (4/θ)*(n^γ/n)*((θ/4)*n^2)=n*n^γ := by field_simp
  rw [he] at hh
  exact hh

variable {Vn : ℕ → Type u19} {In : ℕ → Type u20} [∀ j, Fintype (Vn j)] [∀ j, Fintype (In j)] [∀ j, DecidableEq (Vn j)]
lemma omitted_rate (G : ∀ j, Core.Fibers (Vn j) (In j)) (θ γ c : ℝ) (η : ℕ → ℝ)
    (hθ : 0<θ) (hγ1 : γ<1) (hη : ∀ j, η j≤θ/2)
    (hn : Tendsto (fun j => (Fintype.card (Vn j):ℝ)) atTop atTop)
    (hG : ∀ j, PreparedGraph (Vn j) (In j) (G j) θ γ c (η j)) :
    Tendsto (fun j => (G j).omittedMass ((Fintype.card (Vn j):ℝ)^γ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => (G j).omittedMass_nonneg _) (fun j => (hG j).omitted_bound hθ (hη j))
  have hh := (tendsto_rpow_neg_atTop (show 0<1-γ by linarith)).comp hn
  have he : -(1-γ)=γ-1 := by ring
  rw [he] at hh
  simpa using hh.const_mul (4/θ)

lemma sampling_atoms_eventually (G : ∀ j, Core.Fibers (Vn j) (In j)) (θ γ c : ℝ) (η : ℕ → ℝ)
    (γ0 : 0<γ) (γ1 : γ<1) (δ : ℝ) (hδ : 0<δ)
    (hn : Tendsto (fun j => (Fintype.card (Vn j):ℝ)) atTop atTop)
    (hG : ∀ j, PreparedGraph (Vn j) (In j) (G j) θ γ c (η j)) :
    ∀ᶠ j in atTop,
      (∀ x, prob (Finset.univ : Finset (Vn j)) x≤δ) ∧
      (∀ e, ((G j).targets e).Nonempty) ∧ (∀ e x, prob ((G j).targets e) x≤δ) ∧
      (∀ y, ((G j).retainedSet ((Fintype.card (Vn j):ℝ)^γ) y).Nonempty) ∧
      (∀ y x, prob ((G j).retainedSet ((Fintype.card (Vn j):ℝ)^γ) y) x≤δ) := by
  have hpow := (tendsto_rpow_atTop γ0).comp hn
  filter_upwards [hn.eventually (eventually_ge_atTop (1/δ)),hpow.eventually (eventually_ge_atTop (1/δ))] with j hnδ hnγ
  have hn1 : (1:ℝ)≤Fintype.card (Vn j) := by exact_mod_cast (show 1≤Fintype.card (Vn j) by have := (hG j).card_ge; omega)
  have hs : (Fintype.card (Vn j):ℝ)^γ≤Fintype.card (Vn j) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 γ1.le
  have hf (e) := prob_bound_of_size ((G j).targets e) δ hδ (hnγ.trans ((hG j).fiber e).le)
  have hr (y) := prob_bound_of_size ((G j).retainedSet ((Fintype.card (Vn j):ℝ)^γ) y) δ hδ
    (hnγ.trans ((G j).retainedSet_size _ hs y))
  exact ⟨(prob_bound_of_size Finset.univ δ hδ (by simpa using hnδ)).2,
    fun e => (hf e).1,fun e => (hf e).2,fun y => (hr y).1,fun y => (hr y).2⟩
end WeakPinned
noncomputable section
namespace WeakPinned
open Filter Variance Global Cuts
open scoped Topology BigOperators

lemma length_rate_contradiction (W F R L o : ℕ → ℝ) (δ b : ℝ) (hδ : 0<δ) (hb : 0<b)
    (hW : Tendsto W atTop atTop)
    (hF : Tendsto (fun j => F j/W j) atTop (𝓝 0))
    (hR : Tendsto (fun j => R j/W j) atTop (𝓝 0))
    (ho : Tendsto o atTop (𝓝 0))
    (hlow : ∀ᶠ j in atTop, b*W j≤L j)
    (hupp : ∀ᶠ j in atTop, δ^3*L j≤48+6*F j+2*R j+2*o j*L j) : False := by
  have h48 : Tendsto (fun j => (48:ℝ)/W j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero, Function.comp_apply] using (tendsto_inv_atTop_zero.comp hW).const_mul 48
  have he : Tendsto (fun j => (48+6*F j+2*R j)/W j) atTop (𝓝 0) := by
    convert (h48.add (hF.const_mul 6)).add (hR.const_mul 2) using 1
    · ext j; ring
    · norm_num
  have hbound := ho.eventually (gt_mem_nhds (show 0<δ^3/4 by positivity))
  have hsmall := he.eventually (gt_mem_nhds (show 0<δ^3*b/2 by positivity))
  obtain ⟨j,hjW,hjo,hje,hjl,hju⟩ := (hW.eventually (eventually_gt_atTop (0:ℝ)) |>.and
    (hbound.and (hsmall.and (hlow.and hupp)))).exists
  have hl0 : 0<L j := (mul_pos hb hjW).trans_le hjl
  have hopen := mul_le_mul_of_nonneg_right hjo.le hl0.le
  have he' := (div_lt_iff₀ hjW).mp hje
  have hl' := mul_le_mul_of_nonneg_left hjl (show 0≤δ^3/2 by positivity)
  nlinarith

variable {V : ℕ → Type u21} {I : ℕ → Type u22} {K : ℕ → Type u23} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

end WeakPinned

end
end
end
end

end OAI
