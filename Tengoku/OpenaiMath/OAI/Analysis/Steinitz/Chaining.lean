import Tengoku.OpenaiMath.OAI.Analysis.Steinitz.GaussianProcess

namespace OAI

/-! Gaussian chaining, finite nets, and uniform process bounds. -/

section

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal BigOperators
namespace GaussianChaining

noncomputable def radius (A : ℝ) (j l : ℕ) : ℝ :=
  100*(A+1)*(2:ℝ)^j*(l+1)*(1/2:ℝ)^l
noncomputable def variance (A : ℝ) (j l : ℕ) : ℝ :=
  A*((2:ℝ)^j)^2*((1/2:ℝ)^l)^4

def exponent (j l : ℕ) : ℕ := j+25*(l+1)+4

lemma nat_add_one_le_two_pow (j : ℕ) : (j:ℝ)+1 ≤ (2:ℝ)^j := by
  exact_mod_cast j.lt_two_pow_self

lemma exponent_le (j l : ℕ) : (exponent j l : ℝ) ≤ 30*(2:ℝ)^j*(l+1) := by
  have hj := nat_add_one_le_two_pow j
  have h0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : (0:ℝ) ≤ l := Nat.cast_nonneg l
  have hp : 0 ≤ (j:ℝ)*l := mul_nonneg h0 h1
  calc
    _ ≤ 30*((j:ℝ)+1)*(l+1) := by simp only [exponent,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]; nlinarith
    _ ≤ _ := by gcongr

lemma radius_nonneg {A : ℝ} (hA : 0 ≤ A) (j l : ℕ) : 0 ≤ radius A j l := by
  unfold radius
  positivity

lemma tail_threshold_le {A : ℝ} (hA : 1 ≤ A) (j l : ℕ) :
    2*variance A j l+8*Real.sqrt (variance A j l)*(exponent j l) ≤ (radius A j l)^2 := by
  let p : ℝ := (2:ℝ)^j
  let z : ℝ := (1/2:ℝ)^l
  let m : ℝ := l+1
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hz2 : z^2 ≤ 1 := by nlinarith
  have hm : 1 ≤ m := by dsimp [m]; have := Nat.cast_nonneg (α := ℝ) l; linarith
  have hs : Real.sqrt (variance A j l) = Real.sqrt A*p*z^2 := by
    unfold variance
    rw [Real.sqrt_mul (mul_nonneg (by linarith) (sq_nonneg _)),Real.sqrt_mul (by linarith : 0 ≤ A)]
    rw [Real.sqrt_sq hp,show (((1/2:ℝ)^l)^4) = (((1/2:ℝ)^l)^2)^2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  have hr : (exponent j l : ℝ) ≤ 30*p*m := exponent_le j l
  have ha : 0 ≤ A := by linarith
  have hsa : Real.sqrt A ≤ A+1 := by
    have := Real.sq_sqrt ha
    have := Real.sqrt_nonneg A
    nlinarith [sq_nonneg (A-1)]
  have hc : 2*A+240*Real.sqrt A*m ≤ (100*(A+1)*m)^2 := by
    calc
      _ ≤ 2*(A+1)*m^2+240*(A+1)*m^2 := by
        apply add_le_add
        · have hm2 : 1 ≤ m^2 := by nlinarith
          nlinarith [mul_nonneg (by linarith : 0 ≤ A+1) (sub_nonneg.mpr hm2)]
        · have hm2 : m ≤ m^2 := by nlinarith
          exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsa (by norm_num)) (by linarith)).trans
            (mul_le_mul_of_nonneg_left hm2 (by positivity))
      _ ≤ _ := by
        have h : 242*(A+1) ≤ 10000*(A+1)^2 := by nlinarith [sq_nonneg (A+1)]
        nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg m)]
  rw [hs]
  calc
    _ ≤ 2*(A*p^2*z^4)+8*(Real.sqrt A*p*z^2)*(30*p*m) := by
      unfold variance
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hr (by positivity))
    _ ≤ (2*A+240*Real.sqrt A*m)*(p*z)^2 := by
      have hh : A*p^2*z^2*z^2 ≤ A*p^2*z^2 :=
        mul_le_of_le_one_right (by positivity) hz2
      nlinarith
    _ ≤ (100*(A+1)*m)^2*(p*z)^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by dsimp [radius,p,z,m]; ring

lemma exp_exponent_le (j l : ℕ) :
    Real.exp (-(exponent j l : ℝ)) ≤ (1/2:ℝ)^(exponent j l) := by
  rw [show -(exponent j l : ℝ) = (exponent j l : ℝ)*(-1) by ring,Real.exp_nat_mul]
  apply pow_le_pow_left₀ (Real.exp_pos _).le
  have h : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) h

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

lemma entropy_weight (j l : ℕ) :
    (2:ℝ≥0∞)^(24*(l+1)) * (1/2:ℝ≥0∞)^(exponent j l) =
      (1/2:ℝ≥0∞)^(j+l+5) := by
  rw [show exponent j l = 24*(l+1)+(j+l+5) by simp [exponent]; omega,pow_add,← mul_assoc,← mul_pow]
  norm_num only [one_div]
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),one_pow,one_mul]

lemma weight_sum (j : ℕ) :
    (∑' l : ℕ, (1/2:ℝ≥0∞)^(j+l+5)) = (1/2:ℝ≥0∞)^(j+4) := by
  have he (l : ℕ) : j+l+5 = (j+4)+(l+1) := by omega
  simp only [he,pow_add,pow_succ]
  rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_right,ENNReal.tsum_geometric]
  norm_num only [one_div,inv_inv]
  norm_num
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]

lemma weight_sum_all : (∑' j : ℕ, (1/2:ℝ≥0∞)^(j+4)) = 1/8 := by
  simp only [pow_add]
  rw [ENNReal.tsum_mul_right,ENNReal.tsum_geometric]
  norm_num
  calc
    _ = ((2:ℝ≥0∞)*2⁻¹)*(2⁻¹)^3 := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),one_mul,← ENNReal.inv_pow]; norm_num

lemma radius_sum (A : ℝ) (j : ℕ) :
    (∑' l : ℕ, radius A j l) = 400*(A+1)*(2:ℝ)^j := by
  have he (l : ℕ) : radius A j l = (100*(A+1)*(2:ℝ)^j)*((l+1)*(1/2:ℝ)^l) := by
    dsimp [radius]; ring
  simp only [he]
  rw [tsum_mul_left]
  have hs : (∑' l : ℕ, ((l:ℝ)+1)*(1/2:ℝ)^l) = 4 := by
    have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/2:ℝ)) (by norm_num)
    have h2 := hasSum_geometric_of_norm_lt_one (ξ := (1/2:ℝ)) (by norm_num)
    have ht := (h1.add h2).tsum_eq
    norm_num at ht
    simpa only [add_mul,one_mul] using ht
  rw [hs]
  ring

end GaussianChaining

end

section

open Filter
open scoped Topology BigOperators
namespace GridNets

noncomputable def cell (l : ℕ) (a : ℝ) : ℕ := ⌊(64:ℝ)^l*a⌋₊

def InSquare (p : ℝ × ℝ) : Prop := 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

noncomputable def cellPair (l : ℕ) (p : ℝ × ℝ) : ℕ × ℕ := (cell l p.1,cell l p.2)

def grid (l : ℕ) : Finset (ℕ × ℕ) := Finset.range (64^l+1) ×ˢ Finset.range (64^l+1)

lemma cell_le (l : ℕ) {a : ℝ} (ha : a ≤ 1) : cell l a ≤ 64^l := by
  apply Nat.floor_le_of_le
  push_cast
  exact mul_le_of_le_one_right (by positivity) ha

lemma cellPair_mem {k l : ℕ} (hkl : k ≤ l) {p : ℝ × ℝ} (hp : InSquare p) :
    cellPair k p ∈ grid l := by
  have hn : 64^k ≤ 64^l := Nat.pow_le_pow_right (by norm_num) hkl
  simp only [grid,cellPair,Finset.mem_product,Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le ((cell_le k hp.2.1).trans hn),
    Nat.lt_succ_of_le ((cell_le k hp.2.2.2).trans hn)⟩

lemma abs_sub_lt_width (l : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : cell l a = cell l b) : |a-b| < (1/64:ℝ)^l := by
  have hp : 0 < (64:ℝ)^l := by positivity
  have hfa := Nat.floor_le (mul_nonneg hp.le ha)
  have hfb := Nat.floor_le (mul_nonneg hp.le hb)
  have hga := Nat.lt_floor_add_one ((64:ℝ)^l*a)
  have hgb := Nat.lt_floor_add_one ((64:ℝ)^l*b)
  change ⌊(64:ℝ)^l*a⌋₊ = ⌊(64:ℝ)^l*b⌋₊ at h
  rw [h] at hfa hga
  rw [div_pow,one_pow,abs_lt]
  constructor
  · have hh : b-a < 1/(64:ℝ)^l := (lt_div_iff₀ hp).mpr (by nlinarith)
    linarith
  · apply (lt_div_iff₀ hp).mpr
    nlinarith

lemma eventually_cell_separates {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ᶠ l : ℕ in atTop, cell l a = cell l b → a = b := by
  by_cases hab : a = b
  · exact Eventually.of_forall fun _ _ => hab
  · have hp : 0 < |a-b| := abs_pos.mpr (sub_ne_zero.mpr hab)
    have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/64)
      (by norm_num : (1/64:ℝ)<1)
    filter_upwards [hlim.eventually (gt_mem_nhds hp)] with l hl he
    exact False.elim ((not_lt_of_ge (le_of_lt hl)) (abs_sub_lt_width l ha hb he))

variable {I : Type*} [Fintype I] [Nonempty I]

noncomputable def point (p : I → ℝ × ℝ) (l : ℕ) (c : ℕ × ℕ) : I :=
  if h : ∃ i, cellPair l (p i) = c then h.choose else Classical.arbitrary I

noncomputable def rep (p : I → ℝ × ℝ) (l : ℕ) (i : I) : I := point p l (cellPair l (p i))

lemma rep_cell (p : I → ℝ × ℝ) (l : ℕ) (i : I) :
    cellPair l (p (rep p l i)) = cellPair l (p i) := by
  dsimp [rep,point]
  rw [dite_eq_left ⟨i,rfl⟩]
  exact Classical.choose_spec (show ∃ k, cellPair l (p k) = cellPair l (p i) from ⟨i,rfl⟩)

lemma rep_distance (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i)) (l : ℕ) (i : I) :
    |(p (rep p l i)).1-(p i).1| < (1/64:ℝ)^l ∧
    |(p (rep p l i)).2-(p i).2| < (1/64:ℝ)^l := by
  have he := rep_cell p l i
  exact ⟨abs_sub_lt_width l (hp _).1 (hp _).1 (congrArg Prod.fst he),
    abs_sub_lt_width l (hp _).2.2.1 (hp _).2.2.1 (congrArg Prod.snd he)⟩

lemma eventually_rep_eq (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i)) :
    ∀ᶠ l : ℕ in atTop, ∀ i, p (rep p l i) = p i := by
  have hall : ∀ᶠ l : ℕ in atTop, ∀ i k, cellPair l (p i) = cellPair l (p k) → p i = p k := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro k
    filter_upwards [eventually_cell_separates (hp i).1 (hp k).1,
      eventually_cell_separates (hp i).2.2.1 (hp k).2.2.1] with l h1 h2 h
    exact Prod.ext (h1 (congrArg Prod.fst h)) (h2 (congrArg Prod.snd h))
  filter_upwards [hall] with l hl i
  exact hl _ _ (rep_cell p l i)

lemma grid_card (l : ℕ) : (grid l).card = (64^l+1)^2 := by simp [grid,pow_two]

lemma grid_card_square_le (l : ℕ) : (grid l).card^2 ≤ 2^(24*(l+1)) := by
  rw [grid_card]
  have hp : 1 ≤ 64^l := Nat.one_le_pow l 64 (by norm_num)
  calc
    ((64^l+1)^2)^2 ≤ ((2*64^l)^2)^2 := by gcongr; omega
    _ = 2^(24*l+4) := by
      rw [← pow_mul, mul_pow, show (64:ℕ)=2^6 by norm_num,← pow_mul,← pow_mul,← pow_add]
      congr 1
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma image_pair_card_le {α : Type*} [DecidableEq α] (p : I → ℝ × ℝ)
    (hp : ∀ i, InSquare (p i)) (l : ℕ) (f : I → I → α) :
    (Finset.univ.image (fun i => f (rep p l i) (rep p (l-1) i))).card ≤ 2^(24*(l+1)) := by
  classical
  have hs : Finset.univ.image (fun i => f (rep p l i) (rep p (l-1) i)) ⊆
      (grid l ×ˢ grid l).image (fun c => f (point p l c.1) (point p (l-1) c.2)) := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨(cellPair l (p i),cellPair (l-1) (p i)),
      Finset.mem_product.mpr ⟨cellPair_mem le_rfl (hp i),cellPair_mem (Nat.sub_le _ _) (hp i)⟩,rfl⟩
  exact ((Finset.card_le_card hs).trans Finset.card_image_le).trans (by
    simpa only [Finset.card_product,pow_two] using grid_card_square_le l)

end GridNets

end

section

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal BigOperators Topology
namespace GaussianTail
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

@[simp] lemma matrixMap_add (B C : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) :
    matrixMap (B+C) x = matrixMap B x+matrixMap C x := by
  apply WithLp.ofLp_injective
  exact Matrix.add_mulVec _ _ _
@[simp] lemma matrixMap_sub (B C : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) :
    matrixMap (B-C) x = matrixMap B x-matrixMap C x := by
  apply WithLp.ofLp_injective
  exact Matrix.sub_mulVec _ _ _
@[simp] lemma matrixMap_zero (x : EuclideanSpace ℝ ι) : matrixMap (0 : Matrix κ ι ℝ) x = 0 := by
  apply WithLp.ofLp_injective
  exact Matrix.zero_mulVec _

omit [DecidableEq ι] in
lemma squareMass_eq_zero {B : Matrix κ ι ℝ} (h : squareMass B = 0) : B = 0 := by
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    Finset.sum_nonneg (fun k _ => sq_nonneg (B i k)))).mp h
  ext i k
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (B i k))).mp (h1 i (by simp)) k (by simp)
  simpa only [sq_eq_zero_iff,Matrix.zero_apply] using h2

lemma difference_operator (B C : Matrix κ ι ℝ)
    (hB : ∀ x : EuclideanSpace ℝ ι, ‖matrixMap B x‖^2 ≤ ‖x‖^2)
    (hC : ∀ x : EuclideanSpace ℝ ι, ‖matrixMap C x‖^2 ≤ ‖x‖^2) :
    ∀ x : EuclideanSpace ℝ ι, ‖matrixMap (B-C) x‖^2 ≤ 4*‖x‖^2 := by
  intro x
  have hb : ‖matrixMap B x‖ ≤ ‖x‖ := by nlinarith [hB x,norm_nonneg x,norm_nonneg (matrixMap B x)]
  have hc : ‖matrixMap C x‖ ≤ ‖x‖ := by nlinarith [hC x,norm_nonneg x,norm_nonneg (matrixMap C x)]
  rw [matrixMap_sub]
  have h := norm_sub_le (matrixMap B x) (matrixMap C x)
  have h0 := norm_nonneg (matrixMap B x-matrixMap C x)
  nlinarith
end GaussianTail

namespace GaussianChaining
open GaussianTail GridNets

lemma width_power (n : ℕ) : ((1/64:ℝ)^n)^(2/3:ℝ) = ((1/2:ℝ)^n)^4 := by
  rw [show (1/64:ℝ)=(1/2)^6 by norm_num,← pow_mul,← Real.rpow_natCast,← Real.rpow_mul (by norm_num),
    ← pow_mul,← Real.rpow_natCast]
  congr 1
  push_cast
  ring

lemma coordinate_power_bound (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (hab : a ≤ 2*(1/64:ℝ)^n) :
    a^(2/3:ℝ) ≤ 2*((1/2:ℝ)^n)^4 := by
  have h2 : (2:ℝ)^(2/3:ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by norm_num : (2/3:ℝ)≤1)
  calc
    _ ≤ (2*(1/64:ℝ)^n)^(2/3:ℝ) := Real.rpow_le_rpow ha hab (by norm_num)
    _ = (2:ℝ)^(2/3:ℝ)*((1/2:ℝ)^n)^4 := by rw [Real.mul_rpow (by norm_num) (by positivity),width_power]
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 (by positivity)

lemma width_le_quarter (n : ℕ) : (1/64:ℝ)^n ≤ ((1/2:ℝ)^n)^4 := by
  rw [← pow_mul, mul_comm n 4,pow_mul]
  apply pow_le_pow_left₀ (by norm_num)
  norm_num

variable {ι κ I : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype I] [Nonempty I]

noncomputable def netEnd (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (l : ℕ) (i : I) : Matrix κ ι ℝ :=
  B (rep p l i)

noncomputable def netEdge (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) : ℕ → I → Matrix κ ι ℝ
  | 0,i => netEnd B p 0 i
  | l+1,i => netEnd B p (l+1) i-netEnd B p l i

noncomputable def edgeSet (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (l : ℕ) : Finset (Matrix κ ι ℝ) :=
  Finset.univ.image (netEdge B p l)

omit [DecidableEq ι] in
lemma edgeSet_card (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i)) (l : ℕ) :
    (edgeSet B p l).card ≤ 2^(24*(l+1)) := by
  classical
  cases l with
  | zero => exact image_pair_card_le p hp 0 (fun i _ => B i)
  | succ l =>
      change (Finset.univ.image (fun i => B (rep p (l+1) i)-B (rep p l i))).card ≤ _
      simpa only [Nat.add_sub_cancel] using image_pair_card_le p hp (l+1) (fun i k => B i-B k)

lemma adjacent_distance (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i)) (l : ℕ) (i : I) :
    |(p (rep p (l+1) i)).1-(p (rep p l i)).1| ≤ 2*(1/64:ℝ)^l ∧
    |(p (rep p (l+1) i)).2-(p (rep p l i)).2| ≤ 2*(1/64:ℝ)^l := by
  have h1 := rep_distance p hp (l+1) i
  have h2 := rep_distance p hp l i
  have hw : (1/64:ℝ)^(l+1) ≤ (1/64:ℝ)^l := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (by positivity) (by norm_num)
  constructor
  · have ht := abs_sub_le (p (rep p (l+1) i)).1 (p i).1 (p (rep p l i)).1
    rw [abs_sub_comm (p i).1] at ht
    linarith [h1.1,h2.1]
  · have ht := abs_sub_le (p (rep p (l+1) i)).2 (p i).2 (p (rep p l i)).2
    rw [abs_sub_comm (p i).2] at ht
    linarith [h1.2,h2.2]

omit [DecidableEq ι] in
lemma netEdge_variance (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i))
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ)
    (hbase : ∀ i, squareMass (B i) ≤ C*((2:ℝ)^j)^2)
    (hdiff : ∀ i k, squareMass (B i-B k) ≤ C*((2:ℝ)^j)^2*
      (|(p i).1-(p k).1|^(2/3:ℝ)+|(p i).2-(p k).2|))
    (l : ℕ) (i : I) : squareMass (netEdge B p l i) ≤ variance (64*C+1) j l := by
  cases l with
  | zero =>
    apply (hbase _).trans
    dsimp [variance]
    simp only [pow_zero,one_pow,mul_one]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  | succ l =>
    have hd := adjacent_distance p hp l i
    have hh : |(p (rep p (l+1) i)).1-(p (rep p l i)).1|^(2/3:ℝ)+
        |(p (rep p (l+1) i)).2-(p (rep p l i)).2| ≤ 4*((1/2:ℝ)^l)^4 := by
      have h1 := coordinate_power_bound l (abs_nonneg _) hd.1
      have h2 := width_le_quarter l
      linarith [hd.2]
    calc
      _ ≤ C*((2:ℝ)^j)^2*(|(p (rep p (l+1) i)).1-(p (rep p l i)).1|^(2/3:ℝ)+
        |(p (rep p (l+1) i)).2-(p (rep p l i)).2|) := hdiff _ _
      _ ≤ C*((2:ℝ)^j)^2*(4*((1/2:ℝ)^l)^4) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ variance (64*C+1) j (l+1) := by
        dsimp [variance]
        rw [pow_succ (1/2:ℝ) l]
        have hn : 0 ≤ ((2:ℝ)^j)^2*((1/2:ℝ)^l)^4 := by positivity
        nlinarith

lemma netEdge_operator (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ)
    (hop : ∀ i x, ‖matrixMap (B i) x‖^2 ≤ ‖x‖^2) (l : ℕ) (i : I) :
    ∀ x, ‖matrixMap (netEdge B p l i) x‖^2 ≤ 4*‖x‖^2 := by
  cases l with
  | zero => intro x; exact (hop _ x).trans (by nlinarith [sq_nonneg ‖x‖])
  | succ l => exact difference_operator _ _ (hop _) (hop _)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma netEdge_sum (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (i : I) (n : ℕ) :
    ∑ l ∈ Finset.range (n+1), netEdge B p l i = netEnd B p n i := by
  induction n with
  | zero => simp [netEdge]
  | succ n ih => rw [Finset.sum_range_succ,ih,netEdge]; abel

omit [DecidableEq ι] in
lemma eventually_netEnd_eq (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i))
    {C : ℝ} (j : ℕ) (hdiff : ∀ i k, squareMass (B i-B k) ≤ C*((2:ℝ)^j)^2*
      (|(p i).1-(p k).1|^(2/3:ℝ)+|(p i).2-(p k).2|)) :
    ∀ᶠ l : ℕ in atTop, ∀ i, netEnd B p l i = B i := by
  filter_upwards [eventually_rep_eq p hp] with l hl i
  apply sub_eq_zero.mp
  apply squareMass_eq_zero
  apply le_antisymm _ (squareMass_nonneg _)
  have h := hdiff (rep p l i) i
  simpa only [netEnd,hl i, sub_self,abs_zero,Real.zero_rpow (by norm_num : (2/3:ℝ)≠0),add_zero,mul_zero] using h

lemma radius_summable (A : ℝ) (j : ℕ) : Summable (fun l : ℕ => radius A j l) := by
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/2:ℝ)) (by norm_num)).summable
  have h2 := (hasSum_geometric_of_norm_lt_one (ξ := (1/2:ℝ)) (by norm_num)).summable
  have h := (h1.add h2).mul_left (100*(A+1)*(2:ℝ)^j)
  apply h.congr
  intro l
  dsimp [radius]
  ring

lemma netEnd_norm_le (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) {A : ℝ} (hA : 0 ≤ A) (j : ℕ)
    (x : EuclideanSpace ℝ ι)
    (h : ∀ l i, ‖matrixMap (netEdge B p l i) x‖ ≤ radius A j l) (n : ℕ) (i : I) :
    ‖matrixMap (netEnd B p n i) x‖ ≤ 400*(A+1)*(2:ℝ)^j := by
  have hs : matrixMap (netEnd B p n i) x =
      ∑ l ∈ Finset.range (n+1), matrixMap (netEdge B p l i) x := by
    rw [← netEdge_sum B p i n]
    simp only [matrixMap, map_sum, _root_.sum_apply]
  rw [hs]
  calc
    _ ≤ ∑ l ∈ Finset.range (n+1), ‖matrixMap (netEdge B p l i) x‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ Finset.range (n+1), radius A j l := Finset.sum_le_sum fun l _ => h l i
    _ ≤ ∑' l, radius A j l := (radius_summable A j).sum_le_tsum _ (fun l _ => radius_nonneg hA j l)
    _ = _ := radius_sum A j

end GaussianChaining

end

section

open Matrix
open scoped RealInnerProductSpace
namespace GaussianTail
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

omit [DecidableEq κ] in
lemma matrixMap_mul (B : Matrix κ ι ℝ) (C : Matrix ι ν ℝ) (x : EuclideanSpace ℝ ν) :
    matrixMap (B*C) x=matrixMap B (matrixMap C x) := by
  apply WithLp.ofLp_injective
  exact (Matrix.mulVec_mulVec (WithLp.ofLp x) B C).symm

lemma inner_matrixMap (B : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ κ) :
    ⟪matrixMap B x,y⟫=⟪x,matrixMap B.transpose y⟫ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change y.ofLp ⬝ᵥ (B.mulVec x.ofLp) = (B.transpose.mulVec y.ofLp) ⬝ᵥ x.ofLp
  rw [Matrix.dotProduct_mulVec,Matrix.mulVec_transpose]

lemma coisometry_operator (B : Matrix κ ι ℝ) (hB : B*B.transpose=1) :
    ∀ x : EuclideanSpace ℝ ι, ‖matrixMap B x‖^2 ≤ ‖x‖^2 := by
  intro x
  have ht : ∀ y : EuclideanSpace ℝ κ, ‖matrixMap B.transpose y‖=‖y‖ := by
    intro y
    have hh := gram_form B.transpose y
    rw [Matrix.transpose_transpose,hB] at hh
    have he : toEuclideanCLM (𝕜 := ℝ) (1 : Matrix κ κ ℝ) y=y := by
      apply WithLp.ofLp_injective
      exact Matrix.one_mulVec _
    rw [he,real_inner_self_eq_norm_sq] at hh
    nlinarith [norm_nonneg (matrixMap B.transpose y),norm_nonneg y]
  have hi := real_inner_le_norm (x := x) (y := matrixMap B.transpose (matrixMap B x))
  rw [← inner_matrixMap,real_inner_self_eq_norm_sq,ht] at hi
  have hn : ‖matrixMap B x‖ ≤ ‖x‖ := by
    nlinarith [norm_nonneg (matrixMap B x),norm_nonneg x]
  nlinarith [norm_nonneg (matrixMap B x),norm_nonneg x]

end GaussianTail

end

section

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal NNReal BigOperators Topology
namespace GaussianChaining
open GaussianTail GridNets
variable {ι κ I : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype I]

noncomputable def sizeClass (k : ℝ) : ℕ :=
  if hk : 1/4 ≤ k then (exists_nat_pow_near (by linarith : (1:ℝ) ≤ 4*k) (by norm_num : (1:ℝ)<4)).choose else 0

lemma sizeClass_bounds {k : ℝ} (hk : 1/4 ≤ k) :
    ((2:ℝ)^(sizeClass k))^2 ≤ 4*k ∧ k < ((2:ℝ)^(sizeClass k))^2 := by
  unfold sizeClass
  rw [dite_eq_left hk]
  set j := (exists_nat_pow_near (by linarith : (1:ℝ) ≤ 4*k) (by norm_num : (1:ℝ)<4)).choose
  have hj := (exists_nat_pow_near (by linarith : (1:ℝ) ≤ 4*k) (by norm_num : (1:ℝ)<4)).choose_spec
  change (4:ℝ)^j ≤ 4*k ∧ 4*k < 4^(j+1) at hj
  have he : ((2:ℝ)^j)^2 = 4^j := by rw [← pow_mul,mul_comm j 2,pow_mul]; norm_num
  rw [he]
  constructor
  · exact hj.1
  · rw [pow_succ] at hj; linarith [hj.2]

lemma sizeClass_sqrt {k : ℝ} (hk : 1/4 ≤ k) :
    (2:ℝ)^(sizeClass k) ≤ 2*Real.sqrt k := by
  have hs := Real.sq_sqrt (by linarith : 0 ≤ k)
  have hh := (sizeClass_bounds hk).1
  have h0 := Real.sqrt_nonneg k
  have hp : (0:ℝ) ≤ 2^(sizeClass k) := by positivity
  nlinarith

end GaussianChaining

end

section

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace BigOperators
namespace GaussianAR
open GaussianTail GaussianChaining
variable {ι κ I : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype I]

end GaussianAR

end

end OAI
