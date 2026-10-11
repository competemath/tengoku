import Tengoku.OpenaiMath.OAI.NumberTheory.GaussianMoat.BooleanCube

namespace OAI

universe uIota

namespace GaussianMoat
open MeasureTheory ProbabilityTheory
open scoped NNReal

def cubeEquiv : (n : ℕ) → Cube n ≃ (Fin n → Bool)
  | 0 => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => ()
      left_inv := fun x => by cases x; rfl
      right_inv := fun f => by funext i; exact Fin.elim0 i }
  | n+1 => (Equiv.prodCongr (Equiv.refl Bool) (cubeEquiv n)).trans (Fin.consEquiv (fun _ => Bool))

noncomputable def cubeSignEquiv (ι : Type uIota) [Fintype ι] : Cube (Fintype.card ι) ≃ (ι → Bool) :=
  (cubeEquiv (Fintype.card ι)).trans
    (Equiv.arrowCongr (Fintype.equivFin ι).symm (Equiv.refl Bool))

noncomputable def signDist {ι : Type uIota} [Fintype ι] (σ τ : ι → Bool) : ℕ := by
  classical
  exact ∑ i, if σ i = τ i then 0 else 1

theorem cubeEquiv_dist (n : ℕ) (x y : Cube n) :
    signDist (cubeEquiv n x) (cubeEquiv n y) = cubeDist n x y := by
  classical
  induction n with
  | zero => simp [signDist, cubeDist]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    obtain ⟨c,y⟩ := y
    simp only [signDist, Fin.sum_univ_succ, cubeEquiv, Equiv.trans_apply,
      Equiv.prodCongr_apply, Fin.consEquiv_apply, Fin.cons_zero,
      Fin.cons_succ, cubeDist]
    congr 1
    exact ih x y

theorem cubeSignEquiv_dist (ι : Type uIota) [Fintype ι] (x y : Cube (Fintype.card ι)) :
    signDist (cubeSignEquiv ι x) (cubeSignEquiv ι y) = cubeDist (Fintype.card ι) x y := by
  classical
  rw [← cubeEquiv_dist]
  unfold signDist cubeSignEquiv
  simp only [Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.symm_symm]
  exact (Fintype.equivFin ι).sum_comp (fun i => if cubeEquiv (Fintype.card ι) x i =
    cubeEquiv (Fintype.card ι) y i then (0 : ℕ) else 1)

theorem signMeasure_real_singleton {ι : Type uIota} [Fintype ι] (σ : ι → Bool) :
    (signMeasure ι).real {σ} = ((2 : ℝ)^Fintype.card ι)⁻¹ := by
  simp [measureReal_def, signMeasure, Measure.pi_singleton, fairCoin,
    PMF.uniformOfFintype_apply]

open scoped Classical in

theorem signMeasure_real_set {ι : Type uIota} [Fintype ι] (S : Set (ι → Bool)) :
    (signMeasure ι).real S = (∑ σ, if σ ∈ S then (1 : ℝ) else 0) /
      (2 : ℝ)^Fintype.card ι := by
  classical
  have he : S = (↑(Finset.univ.filter (· ∈ S)) : Set (ι → Bool)) := by ext; simp
  conv_lhs => rw [he, ← sum_measureReal_singleton]
  rw [Finset.sum_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : σ ∈ S <;> simp [hσ, signMeasure_real_singleton]

theorem cubeSignEquiv_measure {ι : Type uIota} [Fintype ι] (S : (ι → Bool) → Prop) :
    (signMeasure ι).real {σ | S σ} =
      (cubeSize (fun x => S (cubeSignEquiv ι x)) : ℝ) / (2 : ℝ)^Fintype.card ι := by
  classical
  rw [signMeasure_real_set]
  congr 1
  simp only [Set.mem_ofPred_eq]
  rw [← (cubeSignEquiv ι).sum_comp (fun σ => if S σ then (1 : ℝ) else 0)]
  simp only [cubeSize, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

noncomputable def SplitSieve.extendSigns (s : SplitSieve) (σ : s.primes → Bool) (p : ℕ) : Bool := by
  classical
  exact if hp : p ∈ s.primes then σ ⟨p,hp⟩ else false

@[simp] theorem SplitSieve.extendSigns_mem (s : SplitSieve) (σ : s.primes → Bool)
    (p : ℕ) (hp : p ∈ s.primes) : s.extendSigns σ p = σ ⟨p,hp⟩ := by
  simp [SplitSieve.extendSigns, hp]

noncomputable def SplitSieve.signedProduct (s : SplitSieve) (σ : s.primes → Bool) : GaussianInt :=
  ∏ p ∈ s.primes, signedFactor (s.factor p) (s.extendSigns σ p)

theorem SplitSieve.line_witness_log_lower (s : SplitSieve) (σ : s.primes → Bool)
    {v w : GaussianInt} (hv : PrimitiveDirection v) (hv0 : v ≠ 0) (hw : w ≠ 0)
    (hline : determinant v w = 0) (hdiv : s.signedProduct σ ∣ w)
    {B : ℝ} (hbound : (w.norm : ℝ) ≤ B) :
    Real.log (v.norm : ℝ) / 2 + (∑ p : s.primes, Real.log (p : ℝ)) - Real.log B / 2 ≤
      ∑ p : s.primes, s.lineLog v p (σ p) := by
  classical
  let t := s.primes.filter (fun p => ¬signedFactor (s.factor p) (s.extendSigns σ p) ∣ v)
  have hp (p : ℕ) (hp : p ∈ t) : 0 < (p : ℝ) := by
    exact_mod_cast (s.prime_mem p (Finset.mem_filter.mp hp).1).pos
  have hprod : 0 < ∏ p ∈ t, (p : ℝ) := Finset.prod_pos hp
  have hvpos : 0 < (v.norm : ℝ) := by exact_mod_cast (GaussianInt.norm_pos.mpr hv0)
  have hlo := s.line_witness_norm_lower s.primes (fun _ h => h) (s.extendSigns σ) hv hw hline hdiv
  have hlow : (v.norm : ℝ) * (∏ p ∈ t, (p : ℝ))^2 ≤ B := by
    apply le_trans ?_ hbound
    have hc : ((v.norm * (∏ p ∈ t, (p : ℤ))^2 : ℤ) : ℝ) ≤ (w.norm : ℝ) := by exact_mod_cast hlo
    push_cast at hc
    exact hc
  have hlog := Real.log_le_log (mul_pos hvpos (sq_pos_of_pos hprod)) hlow
  rw [Real.log_mul hvpos.ne' (sq_pos_of_pos hprod).ne', Real.log_pow,
    Real.log_prod (fun p hp' => (hp p hp').ne')] at hlog
  have hsum : (∑ p ∈ t, Real.log (p : ℝ)) =
      (∑ p : s.primes, Real.log (p : ℝ)) - ∑ p : s.primes, s.lineLog v p (σ p) := by
    calc
      _ = ∑ p ∈ s.primes, (Real.log (p : ℝ) - s.lineLog v p (s.extendSigns σ p)) := by
        unfold t
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p hp'
        unfold SplitSieve.lineLog
        split_ifs <;> simp_all
      _ = _ := by
        rw [← Finset.sum_coe_sort s.primes
          (fun p => Real.log (p : ℝ) - s.lineLog v p (s.extendSigns σ p))]
        simp [SplitSieve.extendSigns, Finset.sum_sub_distrib]
  rw [hsum] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [hlog]

def SplitSieve.lineEvent (s : SplitSieve) (Q : Set GaussianInt) (v : GaussianInt)
    (σ : s.primes → Bool) : Prop :=
  ∃ w ∈ Q, w ≠ 0 ∧ determinant v w = 0 ∧ s.signedProduct σ ∣ w

theorem SplitSieve.line_event_tail (s : SplitSieve) {Q : Set GaussianInt}
    {v : GaussianInt} (hv : PrimitiveDirection v) (hv0 : v ≠ 0) {B ε : ℝ}
    (hQ : ∀ w ∈ Q, (w.norm : ℝ) ≤ B) (hε : 0 ≤ ε)
    (hexcess : ε ≤ (∑ p : s.primes, Real.log (p : ℝ)) - Real.log B / 2) :
    (signMeasure s.primes).real {σ | s.lineEvent Q v σ} ≤
      Real.exp (-ε^2 / (2 * ∑ p : s.primes,
        (((‖Real.log (p : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ))) := by
  apply le_trans (measureReal_mono (s₂ := {σ |
    Real.log (v.norm : ℝ) / 2 + ε ≤ ∑ p : s.primes, s.lineLog v p (σ p)}) ?_)
  · exact s.lineLog_tail hv hv0 hε
  · rintro σ ⟨w,hwQ,hw,hline,hd⟩
    have hl := s.line_witness_log_lower σ hv hv0 hw hline hd (hQ w hwQ)
    change Real.log (v.norm : ℝ) / 2 + ε ≤ _
    linarith

open scoped Classical in

noncomputable def SplitSieve.commonProduct (s : SplitSieve) (σ τ : s.primes → Bool) : GaussianInt :=
  ∏ p ∈ s.primes.filter (fun p => s.extendSigns σ p = s.extendSigns τ p),
    signedFactor (s.factor p) (s.extendSigns σ p)

theorem SplitSieve.commonProduct_dvd_left (s : SplitSieve) (σ τ : s.primes → Bool) :
    s.commonProduct σ τ ∣ s.signedProduct σ := by
  classical
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

theorem SplitSieve.commonProduct_comm (s : SplitSieve) (σ τ : s.primes → Bool) :
    s.commonProduct σ τ = s.commonProduct τ σ := by
  classical
  unfold SplitSieve.commonProduct
  apply Finset.prod_congr
  · ext p
    simp only [Finset.mem_filter, eq_comm]
  · intro p hp
    rw [(Finset.mem_filter.mp hp).2]

theorem SplitSieve.commonProduct_dvd_right (s : SplitSieve) (σ τ : s.primes → Bool) :
    s.commonProduct σ τ ∣ s.signedProduct τ := by
  rw [s.commonProduct_comm]
  exact s.commonProduct_dvd_left τ σ

open scoped Classical in
theorem SplitSieve.signDist_eq_card (s : SplitSieve) (σ τ : s.primes → Bool) :
    signDist σ τ = (s.primes.filter (fun p => s.extendSigns σ p ≠ s.extendSigns τ p)).card := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_coe_sort s.primes
    (fun p => if s.extendSigns σ p ≠ s.extendSigns τ p then 1 else 0)]
  unfold signDist
  apply Finset.sum_congr rfl
  intro p _
  simp [SplitSieve.extendSigns]

theorem determinant_zero_trans {u v w : GaussianInt} (hv : v ≠ 0)
    (huv : determinant u v = 0) (hvw : determinant v w = 0) :
    determinant u w = 0 := by
  have hcoord : v.re ≠ 0 ∨ v.im ≠ 0 := by
    contrapose! hv
    ext <;> simp [hv.1, hv.2]
  unfold determinant at *
  rcases hcoord with hr | hi
  · apply (mul_eq_zero.mp (show v.re * (u.re * w.im - u.im * w.re) = 0 by
      nlinarith [congrArg (fun x : ℤ => x * w.re) huv,
        congrArg (fun x : ℤ => u.re * x) hvw])).resolve_left hr
  · apply (mul_eq_zero.mp (show v.im * (u.re * w.im - u.im * w.re) = 0 by
      nlinarith [congrArg (fun x : ℤ => x * w.im) huv,
        congrArg (fun x : ℤ => u.im * x) hvw])).resolve_left hi

@[simp] theorem determinant_self (v : GaussianInt) : determinant v v = 0 := by
  unfold determinant
  ring

theorem determinant_swap (u v : GaussianInt) : determinant u v = -determinant v u := by
  unfold determinant
  ring

def witnessLine (v : GaussianInt) : Set GaussianInt := {w | determinant v w = 0}

theorem witnessLine_eq {v w : GaussianInt} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : determinant v w = 0) : witnessLine v = witnessLine w := by
  ext u
  constructor
  · intro hu
    exact determinant_zero_trans hv (by rw [determinant_swap, hvw, neg_zero]) hu
  · exact determinant_zero_trans hw hvw

def SplitSieve.badSign (s : SplitSieve) (Q : Set GaussianInt) (σ : s.primes → Bool) : Prop :=
  ∃ w ∈ Q, w ≠ 0 ∧ s.signedProduct σ ∣ w

noncomputable def SplitSieve.badWitness (s : SplitSieve) (Q : Set GaussianInt)
    (σ : {σ : s.primes → Bool // s.badSign Q σ}) : GaussianInt := σ.property.choose

theorem SplitSieve.badWitness_spec (s : SplitSieve) (Q : Set GaussianInt)
    (σ : {σ : s.primes → Bool // s.badSign Q σ}) :
    s.badWitness Q σ ∈ Q ∧ s.badWitness Q σ ≠ 0 ∧ s.signedProduct σ.val ∣ s.badWitness Q σ :=
  σ.property.choose_spec

def SplitSieve.badLines (s : SplitSieve) (Q : Set GaussianInt) : Set (Set GaussianInt) :=
  Set.range (fun σ : {σ : s.primes → Bool // s.badSign Q σ} => witnessLine (s.badWitness Q σ))

theorem SplitSieve.badLine_primitive (s : SplitSieve) (Q : Set GaussianInt)
    (L : s.badLines Q) : ∃ v : GaussianInt, PrimitiveDirection v ∧ v ≠ 0 ∧ witnessLine v = L.val := by
  obtain ⟨σ, hσ⟩ := L.property
  have hw := s.badWitness_spec Q σ
  obtain ⟨v,hv,hv0,a,_hanz,ha⟩ := exists_primitive_direction hw.2.1
  refine ⟨v,hv,hv0, ?_⟩
  rw [← hσ]
  apply witnessLine_eq hv0 hw.2.1
  rw [ha]
  unfold determinant
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
  ring

def SplitSieve.lineClass (s : SplitSieve) (Q : Set GaussianInt) (L : s.badLines Q)
    (σ : s.primes → Bool) : Prop :=
  ∃ hσ : s.badSign Q σ, witnessLine (s.badWitness Q ⟨σ,hσ⟩) = L.val

theorem SplitSieve.badSign_iff_class (s : SplitSieve) (Q : Set GaussianInt) (σ : s.primes → Bool) :
    s.badSign Q σ ↔ ∃ L : s.badLines Q, s.lineClass Q L σ := by
  constructor
  · intro hσ
    exact ⟨⟨witnessLine (s.badWitness Q ⟨σ,hσ⟩), ⟨⟨σ,hσ⟩,rfl⟩⟩, hσ, rfl⟩
  · rintro ⟨L,hσ,_⟩
    exact hσ

theorem SplitSieve.lineClass_subset_event (s : SplitSieve) (Q : Set GaussianInt)
    (L : s.badLines Q) {v : GaussianInt} (hvL : witnessLine v = L.val) :
    {σ | s.lineClass Q L σ} ⊆ {σ | s.lineEvent Q v σ} := by
  rintro σ ⟨hσ,hL⟩
  have hw := s.badWitness_spec Q ⟨σ,hσ⟩
  refine ⟨_,hw.1,hw.2.1,?_,hw.2.2⟩
  change s.badWitness Q ⟨σ,hσ⟩ ∈ witnessLine v
  rw [hvL, ← hL]
  exact determinant_self _

theorem cubeSize_exists_le_sum {n : ℕ} {ι : Type uIota} [Fintype ι]
    (S : ι → Cube n → Prop) : cubeSize (fun x => ∃ i, S i x) ≤ ∑ i, cubeSize (S i) := by
  classical
  unfold cubeSize
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : ∃ i, S i x
  · obtain ⟨i, hi⟩ := hx
    rw [ite_eq_left ⟨i,hi⟩]
    have h : (if S i x then 1 else 0) ≤ ∑ j : ι, if S j x then 1 else 0 :=
      Finset.single_le_sum (f := fun j => if S j x then (1 : ℕ) else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa only [ite_eq_left hi] using h
  · simp only [ite_eq_right hx]
    exact Nat.zero_le _

def orientedRectangle (e : ℂ) (R W : ℝ) : Set GaussianInt :=
  {z | |(star e * (z : ℂ)).re| ≤ R ∧ |(star e * (z : ℂ)).im| ≤ W}

theorem rectangle_norm_bound {e : ℂ} (he : ‖e‖ = 1) {R W : ℝ}
    (hW : 0 ≤ W) (hWR : W ≤ R) {z : GaussianInt} (hz : z ∈ orientedRectangle e R W) :
    (z.norm : ℝ) ≤ 2 * R^2 := by
  have hnorm : ‖star e * (z : ℂ)‖ = ‖(z : ℂ)‖ := by
    rw [norm_mul, norm_star, he, one_mul]
  rw [norm_square_complex, ← hnorm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hx : (star e * (z : ℂ)).re ^ 2 ≤ R^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg ((star e * (z : ℂ)).re))
      (hW.trans hWR)).mpr hz.1
  have hy : (star e * (z : ℂ)).im ^ 2 ≤ W^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg ((star e * (z : ℂ)).im)) hW).mpr hz.2
  have hww := (sq_le_sq₀ hW (hW.trans hWR)).mpr hWR
  nlinarith

theorem determinant_rotated (e : ℂ) (he : ‖e‖ = 1) (z w : GaussianInt) :
    (determinant z w : ℝ) =
      (star e * (z : ℂ)).re * (star e * (w : ℂ)).im -
      (star e * (z : ℂ)).im * (star e * (w : ℂ)).re := by
  have hsq : e.re^2 + e.im^2 = 1 := by
    have hh := Complex.normSq_eq_norm_sq e
    rw [he] at hh
    simpa [Complex.normSq_apply, pow_two] using hh
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    ← GaussianInt.intCast_re, ← GaussianInt.intCast_im, determinant, Int.cast_sub, Int.cast_mul]
  nlinarith [congrArg (fun x : ℝ => x * ((z.re : ℝ) * w.im - z.im * w.re)) hsq]

theorem rectangle_determinant_bound {e : ℂ} (he : ‖e‖ = 1) {R W : ℝ}
    (hR : 0 ≤ R) (hW : 0 ≤ W) {z w : GaussianInt}
    (hz : z ∈ orientedRectangle e R W) (hw : w ∈ orientedRectangle e R W) :
    (|determinant z w| : ℝ) ≤ 2*R*W := by
  rw [determinant_rotated e he]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_mul]
  have h1 := mul_le_mul hz.1 hw.2 (abs_nonneg _) hR
  have h2 := mul_le_mul hz.2 hw.1 (abs_nonneg _) hW
  nlinarith

theorem rectangle_cube_growth {r : ℕ} {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/4)
    (hlarge : 1000 ≤ d^3 * r) :
    let h := ⌊d * r / 10⌋₊
    d^3 * r / 5120 ≤ (h : ℝ) * Real.log (1 + (d^2 * r / 64) / ((r : ℝ) * Real.log 2)) := by
  dsimp only
  have hr : 0 < (r : ℝ) := by
    by_contra h
    have hr0 : (r : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hr0, mul_zero] at hlarge
    norm_num at hlarge
  have loglo : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have loghi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlog : 0 < Real.log 2 := lt_of_lt_of_le (by norm_num) loglo
  have hdle : d ≤ 1 := by linarith
  have hsq : d^2 ≤ 1 := by nlinarith
  have hdr : d^3 * r ≤ d * r := by
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hsq)]) hr.le
  have hfloor : d * r / 20 ≤ (⌊d * r / 10⌋₊ : ℝ) := by
    have hh := Nat.lt_floor_add_one (d * r / 10)
    have hdrl : 1000 ≤ d * r := hlarge.trans hdr
    linarith
  have heq : (d^2 * r / 64) / ((r : ℝ) * Real.log 2) = d^2 / (64 * Real.log 2) := by
    field_simp
  let δ := d^2 / (64 * Real.log 2)
  have hδ : 0 ≤ δ := div_nonneg (sq_nonneg _) (by positivity)
  have hδ1 : δ ≤ 1 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hlog)).mpr
    nlinarith
  have hδlo : d^2 / 64 ≤ δ := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hlog)).mpr
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr loghi)]
  have hlogδ : δ/2 ≤ Real.log (1+δ) := by
    apply le_trans ?_ (Real.le_log_one_add_of_nonneg hδ)
    apply (le_div_iff₀ (by linarith : 0 < δ+2)).mpr
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ1)]
  rw [heq]
  change _ ≤ (⌊d * r / 10⌋₊ : ℝ) * Real.log (1+δ)
  have hm := mul_le_mul hfloor hlogδ (by linarith) (Nat.cast_nonneg _)
  have hm' : d^3 * r / 2560 ≤ (d*r/20) * (δ/2) := by
    have := mul_le_mul_of_nonneg_left hδlo (by positivity : 0 ≤ d*r/40)
    nlinarith
  have hnon : 0 ≤ d^3 * r := by positivity
  nlinarith

theorem rectangle_linear_large {r d : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hlarge : 1000 ≤ d^3 * r) : 1000 ≤ d*r := by
  have hs : d^2 ≤ 1 := by nlinarith
  have hc : d^3 ≤ d := by nlinarith [mul_nonneg hd (sub_nonneg.mpr hs)]
  exact hlarge.trans (mul_le_mul_of_nonneg_right hc hr)

theorem rectangle_log_small {r : ℕ} {d t u l : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1/4) (ht : 1/2 ≤ t) (hu : 0 ≤ u) (hutu : u ≤ 2*t)
    (hl : (r : ℝ)*t ≤ l) (hlarge : 1000 ≤ d^3 * r) :
    Real.log 2 + (1-d)*l + (2*⌊d*r/10⌋₊ : ℕ)*u < l := by
  have hdr : 1000 ≤ d*r := rectangle_linear_large (Nat.cast_nonneg _) hd.le (by linarith) hlarge
  have hf : (⌊d*r/10⌋₊ : ℝ) ≤ d*r/10 := Nat.floor_le (by positivity)
  have hm : (2*⌊d*r/10⌋₊ : ℕ)*u ≤ (d*r/5)*(2*t) := by
    push_cast
    apply mul_le_mul (by linarith) hutu hu
    positivity
  have hdl := mul_le_mul_of_nonneg_left hl hd.le
  have hdt : 500 ≤ d*r*t := by
    have hh := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ d*r)
    nlinarith
  have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  nlinarith

theorem rectangle_log_excess {r : ℕ} {d t l : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/4)
    (ht : 1/2 ≤ t) (hl : (r : ℝ)*t ≤ l) (hlarge : 1000 ≤ d^3 * r) :
    d*l/2 ≤ l - ((1-d)*l + Real.log 2/2) := by
  have hdr : 1000 ≤ d*r := rectangle_linear_large (Nat.cast_nonneg _) hd.le (by linarith) hlarge
  have h1 := mul_le_mul_of_nonneg_left hl hd.le
  have h2 := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ d*r)
  have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  nlinarith

theorem rectangle_hoeffding_exponent {r d t l V : ℝ} (hr : 0 < r) (hd : 0 ≤ d)
    (ht : 0 < t) (hl : r*t ≤ l) (hV : 0 < V) (hVup : V ≤ r*t^2) :
    2*(d^2*r/64) ≤ (d*l/2)^2 / (2*V) := by
  have hdl : 0 ≤ d*r*t/2 := by positivity
  have hdl' : d*r*t/2 ≤ d*l/2 := by nlinarith [mul_le_mul_of_nonneg_left hl hd]
  have hs : (d*r*t/2)^2 ≤ (d*l/2)^2 := (sq_le_sq₀ hdl (hdl.trans hdl')).mpr hdl'
  have hden : 0 < 2*r*t^2 := by positivity
  calc
    2*(d^2*r/64) ≤ d^2*r/8 := by nlinarith [mul_nonneg (sq_nonneg d) hr.le]
    _ = (d*r*t/2)^2 / (2*r*t^2) := by field_simp; ring
    _ ≤ (d*l/2)^2 / (2*r*t^2) := div_le_div_of_nonneg_right hs hden.le
    _ ≤ (d*l/2)^2 / (2*V) := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)

theorem SplitSieve.log_period (s : SplitSieve) :
    Real.log (s.period : ℝ) = ∑ p : s.primes, Real.log (p : ℝ) := by
  classical
  unfold SplitSieve.period
  push_cast
  rw [Real.log_prod (fun p hp => by
    exact_mod_cast (s.prime_mem p hp).ne_zero)]
  exact (Finset.sum_coe_sort s.primes (fun p => Real.log (p : ℝ))).symm

noncomputable def SplitSieve.logVariance (s : SplitSieve) : ℝ :=
  ∑ p : s.primes, (((‖Real.log (p : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ)

theorem SplitSieve.logVariance_pos (s : SplitSieve) (hr : 0 < s.primes.card) :
    0 < s.logVariance := by
  classical
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hr
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (s.prime_mem p hp).one_lt)
  apply Finset.sum_pos' (fun _ _ => by positivity)
  refine ⟨⟨p,hp⟩, Finset.mem_univ _, ?_⟩
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos hlog]
  positivity

theorem SplitSieve.logVariance_le (s : SplitSieve) {U : ℝ}
    (hU : 1 ≤ U) (hpU : ∀ p ∈ s.primes, (p : ℝ) ≤ U) :
    s.logVariance ≤ (s.primes.card : ℝ) * (Real.log U / 2)^2 := by
  classical
  calc
    _ ≤ ∑ _p : s.primes, (Real.log U / 2)^2 := by
      apply Finset.sum_le_sum
      intro p _
      have hp : 0 < (p : ℝ) := by exact_mod_cast (s.prime_mem p p.property).pos
      have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (s.prime_mem p p.property).one_le)
      have hle := Real.log_le_log hp (hpU p p.property)
      simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs,
        abs_of_nonneg hlog]
      exact (sq_le_sq₀ (by positivity) (div_nonneg (Real.log_nonneg hU) (by norm_num))).mpr (by linarith)
    _ = _ := by simp [nsmul_eq_mul]

end GaussianMoat

end OAI
