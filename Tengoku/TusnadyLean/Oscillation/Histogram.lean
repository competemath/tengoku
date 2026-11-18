import Tengoku.Seed.Data.Sym.Card
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Pi
import Tengoku.Seed.Analysis.MeanInequalities
import Tengoku.Seed.Analysis.SpecialFunctions.Exp
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual finite iid laws and the one-layer occupancy estimate. -/
namespace Oscillation
open scoped BigOperators
open Finset
noncomputable section

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def histogram {n : ℕ} (x : Fin n → Ω) : Sym Ω n :=
  ⟨Finset.univ.val.map x, by simp⟩

def histogramCount {n : ℕ} (s : Sym Ω n) (c : Ω) : ℕ :=
  (s : Multiset Ω).count c

def productWeight {n : ℕ} (p : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  ∏ i, p (x i)

omit [DecidableEq Ω] in
/--
@isnad1 id=eq.0h3v.s6.03157d3457b3 from=translated src=- shape=ae2cde1c vocab=a9326a96
-/
lemma sum_productWeight {n : ℕ} (p : Ω → ℝ) :
    ∑ x : Fin n → Ω, productWeight p x = (∑ c, p c) ^ n := by
  simp only [productWeight]
  rw [← Fintype.prod_sum]
  simp

omit [Fintype Ω] in
/--
@isnad1 id=eq.0h4v.s5.e9fbf141d141 from=translated src=- shape=19cd447e vocab=22de5097
-/
lemma histogramCount_eq_card {n : ℕ} (x : Fin n → Ω) (c : Ω) :
    histogramCount (histogram x) c = (Finset.univ.filter (fun i => x i = c)).card := by
  simp only [histogramCount, histogram, Sym.toMultiset, Multiset.count_map]
  simp only [eq_comm]
  rfl

/--
@isnad1 id=eq.0h3v.s5.b49852d3f671 from=translated src=- shape=aed6abd5 vocab=9812a382
-/
lemma histogram_count_sum {n : ℕ} (s : Sym Ω n) : ∑ c, histogramCount s c = n := by
  exact (Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _)).trans s.2

/--
@isnad1 id=eq.0h4v.s6.f3a262ad322a from=translated src=- shape=44d56c7f vocab=80678151
-/
lemma sum_sample_eq_counts {n : ℕ} (x : Fin n → Ω) (f : Ω → ℝ) :
    ∑ i, f (x i) = ∑ c, (histogramCount (histogram x) c : ℝ) * f c := by
  rw [← Finset.sum_fiberwise Finset.univ x (fun i => f (x i))]
  apply Finset.sum_congr rfl
  intro c _
  rw [histogramCount_eq_card]
  calc
    (∑ i ∈ Finset.univ.filter (fun i => x i = c), f (x i)) =
        ∑ i ∈ Finset.univ.filter (fun i => x i = c), f c := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by simp

/--
@isnad1 id=lt.0h4v.s5.112ce3f17e7c from=translated src=- shape=4b3475ef vocab=1f9e4df1
-/
lemma histogramCount_pos_sample {n : ℕ} (x : Fin n → Ω) (i : Fin n) :
    0 < histogramCount (histogram x) (x i) := by
  rw [histogramCount_eq_card]
  exact Finset.card_pos.mpr ⟨i, by simp⟩

/--
@isnad1 id=le.2h2v.s6.a168f67885c6 from=translated src=- shape=2b987b0c vocab=ea11e8b4
-/
lemma prod_le_mean_pow {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (∏ i, z i) ≤ ((∑ i, z i) / n) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin n))
    (fun _ => (1 : ℝ)) z (by simp) (by simpa using hnR) (fun i _ => hz i)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, one_mul] at h
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg (Finset.prod_nonneg fun i _ => hz i) _) h n
  rwa [Real.rpow_inv_natCast_pow (Finset.prod_nonneg fun i _ => hz i) (Nat.ne_of_gt hn)] at hp

def empirical {n : ℕ} (s : Sym Ω n) (c : Ω) : ℝ := histogramCount s c / n

omit [Fintype Ω] in
/--
@isnad1 id=le.0h4v.s4.4c96f1b3b155 from=translated src=- shape=34936494 vocab=85af1532
-/
lemma empirical_nonneg {n : ℕ} (s : Sym Ω n) (c : Ω) : 0 ≤ empirical s c := by
  unfold empirical
  positivity

/--
@isnad1 id=eq.1h3v.s5.26ae8c469ea7 from=translated src=- shape=25fe545b vocab=cb629feb
-/
lemma empirical_total {n : ℕ} (hn : 0 < n) (s : Sym Ω n) : ∑ c, empirical s c = 1 := by
  simp only [empirical, ← Finset.sum_div, ← Nat.cast_sum, histogram_count_sum]
  exact div_self (by exact_mod_cast Nat.ne_of_gt hn)

omit [Fintype Ω] in
/--
@isnad1 id=eq.1h4v.s5.31d9eee1c065 from=translated src=- shape=3f95790b vocab=b0a6b2b2
-/
lemma count_eq_mul_empirical {n : ℕ} (hn : 0 < n) (s : Sym Ω n) (c : Ω) :
    (histogramCount s c : ℝ) = n * empirical s c := by
  unfold empirical
  field_simp

/--
@isnad1 id=eq.2h2v.s5.00810761b569 from=translated src=- shape=a8727d22 vocab=102c45ce
-/
lemma mul_sqrt_div {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    q * Real.sqrt (p / q) = Real.sqrt (p * q) := by
  by_cases hq0 : q = 0
  · simp [hq0]
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 (lt_of_le_of_ne hq (Ne.symm hq0))).ne'
  rw [Real.sqrt_div hp, Real.sqrt_mul hp]
  field_simp
  rw [Real.sq_sqrt hq]
  ring

def affinity {n : ℕ} (p : Ω → ℝ) (s : Sym Ω n) : ℝ :=
  ∑ c, Real.sqrt (p c * empirical s c)

/--
@isnad1 id=le.0h4v.s5.6d7acd631e00 from=translated src=- shape=f2eb5953 vocab=fb1a704e
-/
lemma affinity_nonneg {n : ℕ} (p : Ω → ℝ) (s : Sym Ω n) : 0 ≤ affinity p s :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/--
@isnad1 id=eq.2h4v.s6.e4befa87d3fa from=translated src=- shape=2a126851 vocab=611b2fb6
-/
lemma sample_ratio_mean {n : ℕ} (hn : 0 < n) (p : Ω → ℝ) (hp : ∀ c, 0 ≤ p c)
    (x : Fin n → Ω) :
    (∑ i, Real.sqrt (p (x i) / empirical (histogram x) (x i))) / n =
      affinity p (histogram x) := by
  rw [sum_sample_eq_counts x (fun c => Real.sqrt (p c / empirical (histogram x) c))]
  simp_rw [count_eq_mul_empirical hn]
  simp_rw [mul_assoc, mul_sqrt_div (hp _) (empirical_nonneg _ _)]
  rw [← Finset.mul_sum]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.ne_of_gt hn)

/--
@isnad1 id=le.2h4v.s6.c77da25fc225 from=translated src=- shape=6d7b69c0 vocab=6090386f
-/
lemma productWeight_le_empirical {n : ℕ} (hn : 0 < n) (p : Ω → ℝ) (hp : ∀ c, 0 ≤ p c)
    (x : Fin n → Ω) :
    productWeight p x ≤ productWeight (empirical (histogram x)) x *
      affinity p (histogram x) ^ (2*n) := by
  let q := empirical (histogram x)
  let z := fun i => Real.sqrt (p (x i) / q (x i))
  have hq : ∀ i, 0 < q (x i) := by
    intro i
    exact div_pos (by exact_mod_cast histogramCount_pos_sample x i) (by exact_mod_cast hn)
  have hz := prod_le_mean_pow hn z (fun _ => Real.sqrt_nonneg _)
  have hm : (∑ i, z i) / n = affinity p (histogram x) := sample_ratio_mean hn p hp x
  rw [hm] at hz
  have heq : productWeight p x = productWeight q x * (∏ i, z i)^2 := by
    simp only [productWeight, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    dsimp [z]
    rw [Real.sq_sqrt (div_nonneg (hp _) (hq i).le)]
    exact (mul_div_cancel₀ _ (hq i).ne').symm
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => (hq i).le)
  have hz2 := pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _) hz 2
  simpa [← pow_mul, Nat.mul_comm] using hz2

/-- Probability of one actual histogram, with no multinomial formula assumed.
@isnad1 id=le.2h4v.s7.c20b5cfe31e4 from=translated src=- shape=386f4d9b vocab=7d5d0918
-/
theorem histogram_probability_le {n : ℕ} (hn : 0 < n) (p : Ω → ℝ)
    (hp : ∀ c, 0 ≤ p c) (s : Sym Ω n) :
    (∑ x ∈ Finset.univ.filter (fun x : Fin n → Ω => histogram x = s), productWeight p x)
      ≤ affinity p s ^ (2*n) := by
  let H := Finset.univ.filter (fun x : Fin n → Ω => histogram x = s)
  have hpoint : ∀ x ∈ H, productWeight p x ≤
      productWeight (empirical s) x * affinity p s ^ (2*n) := by
    intro x hx
    have he := (Finset.mem_filter.mp hx).2
    simpa [he] using productWeight_le_empirical hn p hp x
  calc
    _ ≤ ∑ x ∈ H, productWeight (empirical s) x * affinity p s ^ (2*n) :=
      Finset.sum_le_sum hpoint
    _ = (∑ x ∈ H, productWeight (empirical s) x) * affinity p s ^ (2*n) := by
      rw [Finset.sum_mul]
    _ ≤ 1 * affinity p s ^ (2*n) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (affinity_nonneg _ _) _)
      calc
        _ ≤ ∑ x : Fin n → Ω, productWeight (empirical s) x := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro x _ _
          exact Finset.prod_nonneg fun i _ => empirical_nonneg s (x i)
        _ = 1 := by rw [sum_productWeight, empirical_total hn]; simp
    _ = _ := one_mul _

def interiorSum {n M : ℕ} (s : Sym (Option (Fin M)) n) : ℝ :=
  ∑ c : Fin M, Real.sqrt (histogramCount s (some c))

/--
@isnad1 id=le.0h3v.s4.fc208228b70a from=translated src=- shape=0cdb9142 vocab=30721770
-/
lemma interiorSum_nonneg {n M : ℕ} (s : Sym (Option (Fin M)) n) : 0 ≤ interiorSum s :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/--
@isnad1 id=le.1h4v.s5.a31c3bf6c681 from=translated src=- shape=d57815c4 vocab=e6bf1bbb
-/
lemma empirical_le_one {n : ℕ} (hn : 0 < n) (s : Sym Ω n) (c : Ω) : empirical s c ≤ 1 := by
  rw [← empirical_total hn s]
  exact Finset.single_le_sum (fun d _ => empirical_nonneg s d) (Finset.mem_univ c)

/--
@isnad1 id=le.6h5v.s7.c993acb93be2 from=translated src=- shape=fb452846 vocab=def229fc
-/
lemma affinity_le_interior {n M : ℕ} (hn : 0 < n) (hM : 0 < M) {b : ℝ} (_hb : 0 < b)
    (p : Option (Fin M) → ℝ) (hp : ∀ c, 0 ≤ p c)
    (hgood : ∀ c, p (some c) ≤ 1 / M) (hbad : p none ≤ 4/b)
    (s : Sym (Option (Fin M)) n) :
    affinity p s ≤ interiorSum s / Real.sqrt ((n:ℝ)*M) + 2 / Real.sqrt b := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hbad' : Real.sqrt (p none * empirical s none) ≤ 2 / Real.sqrt b := by
    calc
      _ ≤ Real.sqrt ((4:ℝ)/b) := by
        apply Real.sqrt_le_sqrt
        calc
          _ ≤ p none * 1 := mul_le_mul_of_nonneg_left (empirical_le_one hn s none) (hp none)
          _ ≤ _ := by simpa using hbad
      _ = _ := by rw [Real.sqrt_div (by norm_num)]; norm_num
  have hgood' (c : Fin M) : Real.sqrt (p (some c) * empirical s (some c)) ≤
      Real.sqrt (histogramCount s (some c)) / Real.sqrt ((n:ℝ)*M) := by
    calc
      _ ≤ Real.sqrt ((1/(M:ℝ)) * empirical s (some c)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (hgood c) (empirical_nonneg s _))
      _ = Real.sqrt ((histogramCount s (some c):ℝ) / ((n:ℝ)*M)) := by
        congr 1
        unfold empirical
        field_simp
      _ = _ := Real.sqrt_div (by positivity) _
  unfold affinity
  rw [Fintype.sum_option]
  calc
    _ ≤ 2 / Real.sqrt b + ∑ c, Real.sqrt (histogramCount s (some c)) /
          Real.sqrt ((n:ℝ)*M) := add_le_add hbad' (Finset.sum_le_sum fun c _ => hgood' c)
    _ = _ := by rw [← Finset.sum_div]; exact add_comm _ _

/--
@isnad1 id=le.0h2v.s6.b168042527ed from=translated src=- shape=40e95135 vocab=c5ff295b
-/
lemma histogram_card_le (n M : ℕ) :
    Fintype.card (Sym (Option (Fin M)) n) ≤ 2^(n+M) := by
  rw [Sym.card_sym_eq_choose]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Nat.choose_le_two_pow (n+M) n

/--
@isnad1 id=le.1h1v.s6.3fd5f16fca3e from=translated src=- shape=716a5f17 vocab=2446b050
-/
lemma square_exp_neg_le_four {x : ℝ} (hx : 0 ≤ x) :
    (x+2)^2 * Real.exp (-x) ≤ 4 := by
  have hexp := Real.add_one_le_exp (x/2)
  have hx2 : 0 ≤ x+2 := by linarith
  have hsq := pow_le_pow_left₀ hx2 (show x+2 ≤ 2*Real.exp (x/2) by linarith) 2
  have hid : (2*Real.exp (x/2))^2 = 4*Real.exp x := by
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num
    ring
  rw [hid] at hsq
  calc
    _ ≤ (4*Real.exp x) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = 4 := by rw [mul_assoc, ← Real.exp_add]; simp

/--
@isnad1 id=le.4h4v.s7.f75fdce8e51e from=translated src=- shape=02ef2842 vocab=f7c166ae
-/
lemma occupancy_exponential_absorption {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    {b S : ℝ} (hb : 0 < b) (hS : 0 ≤ S) :
    (S / Real.sqrt ((n:ℝ)*M) + 2 / Real.sqrt b)^(2*n) *
      Real.exp (-Real.sqrt (b*n/M)*S) ≤ (4/b)^n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hsn : Real.sqrt (n:ℝ) ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
  have hsm : Real.sqrt (M:ℝ) ≠ 0 := (Real.sqrt_pos.2 hMR).ne'
  have hsb : Real.sqrt b ≠ 0 := (Real.sqrt_pos.2 hb).ne'
  have hsd : Real.sqrt ((n:ℝ)*M) ≠ 0 := (Real.sqrt_pos.2 (mul_pos hnR hMR)).ne'
  let x := S * Real.sqrt b / Real.sqrt ((n:ℝ)*M)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hbase : S / Real.sqrt ((n:ℝ)*M) + 2 / Real.sqrt b = (x+2)/Real.sqrt b := by
    dsimp [x]
    field_simp
  have hrate : Real.sqrt (b*n/M) = (n:ℝ)*Real.sqrt b/Real.sqrt ((n:ℝ)*M) := by
    rw [Real.sqrt_div (mul_nonneg hb.le hnR.le), Real.sqrt_mul hb.le,
      Real.sqrt_mul hnR.le]
    field_simp
    rw [Real.sq_sqrt hnR.le]
  have hexponent : -Real.sqrt (b*n/M)*S = (n:ℝ)*(-x) := by
    rw [hrate]
    dsimp [x]
    ring
  rw [hbase, hexponent, Real.exp_nat_mul, pow_mul, div_pow, Real.sq_sqrt hb.le, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  calc
    (x+2)^2 / b * Real.exp (-x) = ((x+2)^2 * Real.exp (-x))/b := by ring
    _ ≤ 4/b := div_le_div_of_nonneg_right (square_exp_neg_le_four hx) hb.le

/-- The exact one-layer estimate for a product law on M interior buckets plus a boundary bucket.
Only upper bounds on bucket probabilities are needed; the histogram argument is proved above.
@isnad1 id=le.6h4v.s8.15ff207c58e1 from=translated src=- shape=7f1e2532 vocab=98026b08
-/
theorem iid_interior_laplace {n M : ℕ} (hn : 0 < n) (hM : 0 < M) {b : ℝ} (hb : 0 < b)
    (p : Option (Fin M) → ℝ) (hp : ∀ c, 0 ≤ p c)
    (hgood : ∀ c, p (some c) ≤ 1 / M) (hbad : p none ≤ 4/b) :
    (∑ x : Fin n → Option (Fin M), productWeight p x *
      Real.exp (-Real.sqrt (b*n/M) * interiorSum (histogram x)))
      ≤ (2:ℝ)^(n+M) * (4/b)^n := by
  rw [← Finset.sum_fiberwise Finset.univ histogram
    (fun x : Fin n → Option (Fin M) => productWeight p x *
      Real.exp (-Real.sqrt (b*n/M) * interiorSum (histogram x)))]
  have htype (s : Sym (Option (Fin M)) n) :
      (∑ x ∈ Finset.univ.filter (fun x : Fin n → Option (Fin M) => histogram x = s),
        productWeight p x * Real.exp (-Real.sqrt (b*n/M) * interiorSum (histogram x)))
      ≤ (4/b)^n := by
    have heq : (∑ x ∈ Finset.univ.filter (fun x : Fin n → Option (Fin M) => histogram x = s),
        productWeight p x * Real.exp (-Real.sqrt (b*n/M) * interiorSum (histogram x))) =
      (∑ x ∈ Finset.univ.filter (fun x : Fin n → Option (Fin M) => histogram x = s),
        productWeight p x) * Real.exp (-Real.sqrt (b*n/M) * interiorSum s) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    rw [heq]
    calc
      _ ≤ affinity p s ^ (2*n) * Real.exp (-Real.sqrt (b*n/M) * interiorSum s) :=
        mul_le_mul_of_nonneg_right (histogram_probability_le hn p hp s) (Real.exp_pos _).le
      _ ≤ (interiorSum s / Real.sqrt ((n:ℝ)*M) + 2/Real.sqrt b)^(2*n) *
          Real.exp (-Real.sqrt (b*n/M) * interiorSum s) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact pow_le_pow_left₀ (affinity_nonneg p s) (affinity_le_interior hn hM hb p hp hgood hbad s) _
      _ ≤ _ := occupancy_exponential_absorption hn hM hb (interiorSum_nonneg s)
  calc
    _ ≤ ∑ s : Sym (Option (Fin M)) n, (4/b)^n := Finset.sum_le_sum fun s _ => htype s
    _ = (Fintype.card (Sym (Option (Fin M)) n):ℝ) * (4/b)^n := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast histogram_card_le n M

end
end Oscillation
