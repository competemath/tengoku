import Tengoku.OpenaiMath.OAI.Geometry.LatticeCovering.Bits

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical

namespace SingleLatticeCovering.Folded
open ConstructionA MeasureTheory Filter Topology
open scoped BigOperators
universe u
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gridMass_eq_usableMass {p : ℕ} [NeZero p] (h : ℝ) (E : Finset (ι → ZMod p)) :
    gridMass h p E = Blocks.usableMass E (fun z => folded h (anchor p z)) := by
  classical
  unfold gridMass Blocks.usableMass
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow, div_eq_mul_inv,
    ←Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [inv_pow]
  ring

lemma probability_eq_bitMass {h : ℝ} (hh : 0 < h) (t : ℝ) (e : Bool) :
    probability h t e = Bits.bitMass (probability h t true) e := by
  cases e
  · simp only [Bits.bitMass, Bool.false_eq_true, ↓reduceIte]
    linarith [probability_sum hh t]
  · simp only [Bits.bitMass, ↓reduceIte]

lemma wordMass_eq_productMass {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℝ} (hh : 0 < h) (t : ι → ℝ) (e : ι → Bool) :
    wordMass h t e = Bits.productMass (fun j => probability h (t j) true) e := by
  unfold wordMass Bits.productMass
  apply Finset.prod_congr rfl
  intro j _
  exact probability_eq_bitMass hh _ _

lemma mean_fairRate_lower {ι : Type*} [Fintype ι] [DecidableEq ι] {h r : ℝ} (hh : 0 < h) (t : ι → ℝ)
    (hN : r ≤ ((Finset.univ.filter fun j => |t j-1/2| ≤ (h^2)⁻¹).card : ℝ)) :
    2*Bits.alpha*r ≤ Bits.meanCount (fun j => Bits.fairRate (probability h (t j) true)) := by
  classical
  let S := Finset.univ.filter fun j => |t j-1/2| ≤ (h^2)⁻¹
  have hsum : (2*Bits.alpha)*(S.card : ℝ) ≤
      ∑ j ∈ S, Bits.fairRate (probability h (t j) true) := by
    calc
      _ = ∑ _j ∈ S, 2*Bits.alpha := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have ht := probability_central hh (Finset.mem_filter.mp hj).2 true
        unfold Bits.fairRate
        apply mul_le_mul_of_nonneg_left (le_min ht.1 (by change alpha ≤ _; linarith)) (by norm_num)
  have hall : (∑ j ∈ S, Bits.fairRate (probability h (t j) true)) ≤
      Bits.meanCount (fun j => Bits.fairRate (probability h (t j) true)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    intro j _ _
    exact Bits.fairRate_nonneg (probability_pos hh _ _).le (probability_le_one hh _ _)
  exact (mul_le_mul_of_nonneg_left hN (mul_nonneg (by norm_num) Bits.alpha_pos.le)).trans (hsum.trans hall)

lemma eligible_window {p : ℕ} [NeZero p] {h μ D r : ℝ} (hh : 0 < h)
    {z : ι → ZMod p} (hz : z ∈ gridEligible h μ D r p) :
    Real.exp ((Fintype.card ι : ℝ)*μ-D) ≤ folded h (anchor p z) ∧
    folded h (anchor p z) ≤ Real.exp ((Fintype.card ι : ℝ)*μ+D) := by
  classical
  have he := (Finset.mem_filter.mp hz).2.1
  have hl : (Fintype.card ι : ℝ)*μ-D ≤ Real.log (folded h (anchor p z)) := by linarith [(abs_le.mp he).1]
  have hu : Real.log (folded h (anchor p z)) ≤ (Fintype.card ι : ℝ)*μ+D := by linarith [(abs_le.mp he).2]
  exact ⟨(Real.exp_le_exp.mpr hl).trans_eq (Real.exp_log (folded_pos hh _)),
    (Real.exp_log (folded_pos hh _)).symm.trans_le (Real.exp_le_exp.mpr hu)⟩

end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open Filter Topology Real ConstructionA Blocks
open scoped BigOperators

lemma eventually_previous_cap : ∀ᶠ b : ℝ in atTop, ∀ a : ℝ, 1 ≤ a →
    a ≤ b^((1 : ℝ)/(9/10)) → 5*a^(56/100 : ℝ) ≤ b^(65/100 : ℝ) := by
  filter_upwards [eventually_rpow_ratio_bound (by norm_num : ((1 : ℝ)/(9/10))*(56/100) < 65/100)
    (by norm_num : (0 : ℝ) < 1/5), eventually_gt_atTop (0 : ℝ)] with b hb hb0
  intro a ha hab
  have ht := Real.rpow_le_rpow (show 0 ≤ a by linarith) hab (by norm_num : (0 : ℝ) ≤ 56/100)
  rw [←Real.rpow_mul hb0.le] at ht
  linarith

lemma eventually_line_collision : ∀ᶠ b : ℝ in atTop,
    Real.exp (-2*b^(56/100 : ℝ)) ≤ b^(-(1/20 : ℝ)) := by
  have ht := Sampler.Numeric.tendsto_rpow_mul_exp_neg_rpow (1/20 : ℝ)
    (by norm_num : (0 : ℝ) < 56/100) (by norm_num : (0 : ℝ) < 2)
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ)] with b hb hb0
  rw [Real.rpow_neg hb0.le]
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hb0 (1/20 : ℝ))).mpr
  simpa only [mul_comm] using hb.le

lemma window_line_choice {b p : ℕ} (hb : 1 ≤ b) [Fact p.Prime]
    (U : Finset (Fin b → ZMod p)) (hU : U ⊆ gridEligible (height b) (logMean (height b))
      ((b : ℝ)^(56/100 : ℝ)) ((b : ℝ)^(70/100 : ℝ)) p)
    (hh : 0 < height b)
    (hpl : (b : ℝ)*logMean (height b)-4*(b : ℝ)^(56/100 : ℝ) ≤ Real.log p)
    (hpu : Real.log p ≤ (b : ℝ)*logMean (height b)-3*(b : ℝ)^(56/100 : ℝ))
    (hM : usableMass U (fun z => folded (height b) (anchor p z)) ≤ 2) :
    ∃ v : Direction (Fin b → ZMod p),
      usableMass U (fun z => folded (height b) (anchor p z)) -
        4*usableMass U (fun z => folded (height b) (anchor p z))*Real.exp (-2*(b : ℝ)^(56/100 : ℝ)) ≤
        (𝔼 x, lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U (fun z => folded (height b) (anchor p z))) v x) ∧
      (𝔼 x, lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U (fun z => folded (height b) (anchor p z))) v x) ≤
        usableMass U (fun z => folded (height b) (anchor p z)) ∧
      ∀ x, 0 ≤ lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U (fun z => folded (height b) (anchor p z))) v x ∧
        lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U (fun z => folded (height b) (anchor p z))) v x ≤
          Real.exp (5*(b : ℝ)^(56/100 : ℝ)) := by
  classical
  let : Nonempty (Fin b) := ⟨⟨0,by omega⟩⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  apply gaussian_window_sparse_line U (fun z => folded (height b) (anchor p z))
    (fun z => (folded_pos hh _).le) ((b : ℝ)*logMean (height b)) ((b : ℝ)^(56/100 : ℝ))
    (fun z hz => by simpa only [Fintype.card_fin] using (eligible_window hh (hU hz)).1)
    (fun z hz => by simpa only [Fintype.card_fin] using (eligible_window hh (hU hz)).2)
    _ _ hM
  · simpa only [ZMod.card, Real.exp_log hp0] using Real.exp_le_exp.mpr hpl
  · simpa only [ZMod.card, Real.exp_log hp0] using Real.exp_le_exp.mpr hpu

lemma line_mean_error {M g D ε τ : ℝ} (hM : |M-1| ≤ D*ε) (hM2 : M ≤ 2)
    (hτ : 0 ≤ τ) (hτε : τ ≤ ε) (hgl : M-4*M*τ ≤ g) (hgu : g ≤ M) :
    |g-1| ≤ (D+8)*ε := by
  have hε : 0 ≤ ε := hτ.trans hτε
  have hmul := mul_le_mul_of_nonneg_right hM2 hτ
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hM).1,(abs_le.mp hM).2]

lemma usable_mass_error {M U C b : ℝ} (hb : 1 ≤ b) (hC : 0 ≤ C)
    (hM : |M-1| ≤ 7*b^(-(1/20 : ℝ))) (hM2 : M ≤ 2)
    (hu : M-C*b^(-(9/20 : ℝ))*M ≤ U) (hu' : U ≤ M) :
    |U-1| ≤ (7+2*C)*b^(-(1/20 : ℝ)) := by
  have he := Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (-(9/20 : ℝ)) ≤ -(1/20 : ℝ))
  have hp : 0 ≤ b^(-(9/20 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hs := mul_le_mul_of_nonneg_left he hC
  have hm := mul_le_mul_of_nonneg_left hM2 (mul_nonneg hC hp)
  apply abs_le.mpr
  constructor <;> nlinarith [(abs_le.mp hM).1,(abs_le.mp hM).2,
    mul_nonneg hC (Real.rpow_nonneg (by linarith : 0 ≤ b) (-(1/20 : ℝ)))]

lemma sampler_factor_lower {b A : ℝ} (hb : 1 ≤ b) (hA : 4 ≤ A) :
    1-A*b^(-(1/100 : ℝ)) ≤ (1-b^(-(1/20 : ℝ)))*(1-3*b^(-(1/10 : ℝ))) := by
  have h1 := Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (-(1/20 : ℝ)) ≤ -(1/100 : ℝ))
  have h2 := Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (-(1/10 : ℝ)) ≤ -(1/100 : ℝ))
  have h3 := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (by linarith : 0 ≤ b) (-(1/100 : ℝ)))
  nlinarith [mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ b) (-(1/20 : ℝ)))
    (Real.rpow_nonneg (by linarith : 0 ≤ b) (-(1/10 : ℝ)))]

end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open Filter Topology Real ConstructionA Blocks
open scoped BigOperators
universe u

def eligible (b p : ℕ) [NeZero p] : Finset (Fin b → ZMod p) :=
  gridEligible (height b) (logMean (height b)) ((b : ℝ)^(56/100 : ℝ)) ((b : ℝ)^(70/100 : ℝ)) p

def anchorWeight (b p : ℕ) (z : Fin b → ZMod p) : ℝ := folded (height b) (anchor p z)

def blockFunction (b p : ℕ) [Fact p.Prime] (U : Finset (Fin b → ZMod p))
    (v : Fin b → ZMod p) : (Fin b → ZMod p) → ℝ :=
  lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U (anchorWeight b p)) v

end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Filter Topology

def balanced (h : ℝ) (t : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun j => |t j-1/2| ≤ (h^2)⁻¹)

lemma eventually_atom_exponent :
    ∀ᶠ b : ℝ in atTop, 5*b^(56/100 : ℝ)+1 ≤ (alpha/2)*b^(70/100 : ℝ) := by
  have hratio : Tendsto (fun b : ℝ => b^(56/100 : ℝ)/b^(70/100 : ℝ)) atTop (𝓝 0) := by
    refine (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 14/100)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
    rw [← Real.rpow_sub hb]
    norm_num
  have hinv := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 70/100)).inv_tendsto_atTop
  have ht : Tendsto (fun b : ℝ => (5*b^(56/100 : ℝ)+1)/b^(70/100 : ℝ)) atTop (𝓝 0) := by
    convert (hratio.const_mul 5).add hinv using 1 <;> try norm_num
    funext b
    ring
  filter_upwards [ht.eventually (gt_mem_nhds (div_pos alpha_pos (by norm_num) : 0 < alpha/2)),
    eventually_gt_atTop (0 : ℝ)] with b hb hb0
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hb0 _)).mp hb).le

end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.ConstructionA
open SingleLatticeCovering.Folded SingleLatticeCovering.Blocks
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma anchor_mem_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (hp : 0 < p) (z : ι → ZMod p) (j : ι) :
    anchor p z j ∈ Set.Icc 0 1 := by
  let : NeZero p := ⟨hp.ne'⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  refine ⟨div_nonneg (Nat.cast_nonneg _) hp0.le, ?_⟩
  apply (div_le_one hp0).mpr
  exact_mod_cast (ZMod.val_lt (z j)).le

lemma lineMax_anchor {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} [Fact p.Prime] (U : Finset (ι → ZMod p))
    (F : (ι → ZMod p) → ℝ) (v x : ι → ZMod p)
    (hg : 0 < lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U F) v x) :
    ∃ z ∈ U, x-z ∈ Submodule.span (ZMod p) {v} ∧
      lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U F) v x = F z / p := by
  classical
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun a : ZMod p => sparseWeight (K := ZMod p) U F (x-a • v))
  have hae : lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U F) v x =
      sparseWeight (K := ZMod p) U F (x-a • v) := ha
  have hz : x-a • v ∈ U := by
    by_contra hz
    simp only [hae, sparseWeight, hz, ↓reduceIte] at hg
    exact lt_irrefl _ hg
  refine ⟨x-a • v,hz,?_,?_⟩
  · rw [sub_sub_cancel]
    exact Submodule.mem_span_singleton.mpr ⟨a,rfl⟩
  · simp only [hae, sparseWeight, hz, ↓reduceIte, ZMod.card]

end SingleLatticeCovering.ConstructionA

namespace SingleLatticeCovering.Folded
open Filter Topology Real ConstructionA
open scoped BigOperators

end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open Real Filter Topology
open scoped BigOperators

lemma eventually_logMean_height_le : ∀ᶠ b : ℕ in atTop, logMean (height b) ≤ (b : ℝ) := by
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  have he : ∀ᶠ b : ℝ in atTop, logMean (heightR b) ≤ b := by
    filter_upwards [eventually_height_bound (s := 1) (c := Real.sqrt (2*Real.pi)/2)
      (by norm_num) (by positivity), eventually_gt_atTop (1 : ℝ)] with b hb hb1
    have hh := heightR_pos hb1
    have ht : 0 < 2*heightR b/Real.sqrt (2*Real.pi) := by positivity
    calc
      _ ≤ Real.log (2*heightR b/Real.sqrt (2*Real.pi)) := logMean_upper hh
      _ ≤ 2*heightR b/Real.sqrt (2*Real.pi) :=
        (Real.log_le_sub_one_of_pos ht).trans (by linarith)
      _ ≤ b := by
        rw [div_le_iff₀ hs]
        rw [Real.rpow_one] at hb
        nlinarith
  exact tendsto_natCast_atTop_atTop.eventually he

lemma group_log_bound {a b p : ℕ} [NeZero p] (hb : 1 ≤ b)
    (ha : logMean (height a) ≤ (a : ℝ))
    (hab : (a : ℝ) ≤ (b : ℝ)^((1 : ℝ)/(9/10)))
    (hp : Real.log p ≤ (a : ℝ)*logMean (height a)-3*(a : ℝ)^(56/100 : ℝ)) :
    Real.log (Fintype.card (Fin a → ZMod p)) ≤ (b : ℝ)^4 := by
  have hp' : Real.log p ≤ (a : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
    have ht : 0 ≤ (a : ℝ)^(56/100 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith
  calc
    _ = (a : ℝ)*Real.log p := by simp [Real.log_pow]
    _ ≤ (a : ℝ)^3 := by
      have h := mul_le_mul_of_nonneg_left hp' (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
      nlinarith
    _ ≤ ((b : ℝ)^((1 : ℝ)/(9/10)))^3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hab _
    _ = (b : ℝ)^(10/3 : ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg b)]
      norm_num
    _ ≤ (b : ℝ)^4 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ b by exact_mod_cast hb)
        (by norm_num : (10/3 : ℝ) ≤ (4 : ℝ))
      simpa using h

end SingleLatticeCovering.Folded

noncomputable section
open scoped BigOperators

namespace SingleLatticeCovering.Vertical

variable {E V W : Type*} [Fintype E]

def join (P : E → Finset V) (point : E → W) : Finset (V × W) := by
  classical
  exact Finset.univ.biUnion (fun e => (P e).image (fun x => (x,point e)))

lemma mem_join (P : E → Finset V) (point : E → W) (x : V × W) :
    x ∈ join P point ↔ ∃ e, x.1 ∈ P e ∧ x.2 = point e := by
  classical
  simp only [join, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨e,v,hv,rfl⟩
    exact ⟨e,hv,rfl⟩
  · rintro ⟨e,hv,he⟩
    exact ⟨e,x.1,hv,Prod.ext rfl he.symm⟩

lemma sum_join (P : E → Finset V) (point : E → W) (hp : Function.Injective point)
    (f : V × W → ℝ) :
    ∑ x ∈ join P point, f x = ∑ e, ∑ x ∈ P e, f (x,point e) := by
  classical
  rw [join, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_image]
    exact fun x hx y hy h => congrArg Prod.fst h
  · intro e he e' he' hee'
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨v,hv,hv'⟩ := Finset.mem_image.mp hx
    obtain ⟨v',hw,hw'⟩ := Finset.mem_image.mp hx'
    exact hee' (hp (congrArg Prod.snd (hv'.trans hw'.symm)))

theorem weighted_join (P : E → Finset V) (point : E → W) (hp : Function.Injective point)
    (preWeight : E → V → ℝ) (block : E → ℝ) (weight : V × W → ℝ)
    (prob g : E → ℝ) (a c d s : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hprob : ∀ e, 0 ≤ prob e) (hg : ∀ e, 0 ≤ g e)
    (hb : ∀ e, c*d*prob e ≤ block e)
    (hpreWeight : ∀ e, a*g e ≤ ∑ x ∈ P e, preWeight e x)
    (hweight : ∀ e, ∀ x ∈ P e, weight (x,point e) = preWeight e x * block e)
    (hs : s ≤ ∑ e, prob e*g e) :
    a*c*d*s ≤ ∑ x ∈ join P point, weight x := by
  classical
  rw [sum_join P point hp]
  calc
    a*c*d*s ≤ a*c*d * ∑ e, prob e*g e :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg ha hc) hd)
    _ = ∑ e, (a*g e)*(c*d*prob e) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ ∑ e, (∑ x ∈ P e, preWeight e x)*block e := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul (hpreWeight e) (hb e) (mul_nonneg (mul_nonneg hc hd) (hprob e))
        ((mul_nonneg ha (hg e)).trans (hpreWeight e))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun x hx => (hweight e x hx).symm)

lemma join_subset_product (P : E → Finset V) (point : E → W)
    (S : Set V) (T : Set W) (hP : ∀ e, ↑(P e) ⊆ S) (hp : ∀ e, point e ∈ T) :
    ↑(join P point) ⊆ S ×ˢ T := by
  intro x hx
  obtain ⟨e,he,he'⟩ := (mem_join P point x).mp hx
  exact ⟨hP e he,he' ▸ hp e⟩

def SuffixBinary {m : ℕ} (P : Finset (Fin m → ℝ)) : Prop :=
  ∀ j : Fin m, ∀ y : Fin m → ℝ, ∃ a : ℝ, ∀ x ∈ P,
    (∀ k, j<k → x k=y k) → x j=a ∨ x j=a+1

def bits (b : ℕ) (lam : Fin b → ℝ) (e : Fin b → Bool) : Fin b → ℝ :=
  fun j => lam j + if e j then 1 else 0

lemma bits_injective (b : ℕ) (lam : Fin b → ℝ) : Function.Injective (bits b lam) := by
  intro e e' h
  funext j
  have hj := congrFun h j
  dsimp only [bits] at hj
  cases he : e j <;> cases he' : e' j <;> simp_all

lemma bits_scalar (b : ℕ) (lam : Fin b → ℝ) (e : Fin b → Bool) (j : Fin b) :
    bits b lam e j=lam j ∨ bits b lam e j=lam j+1 := by
  cases he : e j <;> simp [bits,he]

end SingleLatticeCovering.Vertical

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
