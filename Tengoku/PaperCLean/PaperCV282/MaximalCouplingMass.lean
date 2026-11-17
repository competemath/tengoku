import Tengoku.PaperCLean.PaperCV282.FiniteFieldTotalVariation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The overlap and residual masses of two countable probability laws -/
namespace PaperC.V282.MaximalCouplingMass

open FiniteFieldTotalVariation

noncomputable section

variable {α : Type*}

def overlap (p q : α → ℝ) (x : α) : ℝ := min (p x) (q x)

def residual (p q : α → ℝ) (x : α) : ℝ := p x-overlap p q x

/--
@isnad1 id=le.2h4v.s5.eba2257f1a1b from=translated src=- shape=3f162890 vocab=fe8701fd
-/
theorem overlap_nonneg {p q : α → ℝ} (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) (x : α) :
    0≤overlap p q x := le_min (hp0 x) (hq0 x)

/--
@isnad1 id=le.0h4v.s4.e9211713e9b0 from=translated src=- shape=5ef2c697 vocab=d99068e3
-/
theorem residual_nonneg (p q : α → ℝ) (x : α) : 0≤residual p q x :=
  sub_nonneg.mpr (min_le_left _ _)

/--
@isnad1 id=summable.3h3v.s6.de9ff1b1c4e2 from=translated src=- shape=692e7aa7 vocab=9d337b74
-/
theorem summable_overlap {p q : α → ℝ} (hp : Summable p)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) : Summable (overlap p q) :=
  hp.of_nonneg_of_le (overlap_nonneg hp0 hq0) (fun _ => min_le_left _ _)

/--
@isnad1 id=eq.4h3v.s6.41d2c8772291 from=translated src=- shape=c8dd81ba vocab=1f8a5f6b
-/
theorem variation_eq_one_sub_overlap {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) :
    massTotalVariation p q=1-∑' x,overlap p q x := by
  have ho := summable_overlap hp.summable hp0 hq0
  have hpoint (x : α) : |p x-q x|=p x+q x-2*overlap p q x := by
    unfold overlap
    rcases le_total (p x) (q x) with h|h
    · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  unfold massTotalVariation
  simp_rw [hpoint]
  rw [(hp.summable.add hq.summable).tsum_sub (ho.mul_left 2),
    hp.summable.tsum_add hq.summable,tsum_mul_left,hp.tsum_eq,hq.tsum_eq]
  ring

/--
@isnad1 id=hassum.4h3v.s6.e398d7a072e3 from=translated src=- shape=a23edffc vocab=8e53134a
-/
theorem hasSum_residual {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) :
    HasSum (residual p q) (massTotalVariation p q) := by
  rw [variation_eq_one_sub_overlap hp hq hp0 hq0]
  exact hp.sub (summable_overlap hp.summable hp0 hq0).hasSum

/--
@isnad1 id=eq.5h4v.s6.9440bb05acc5 from=translated src=- shape=47dad637 vocab=8e53134a
-/
theorem residual_eq_zero_of_variation_zero {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) (hzero : massTotalVariation p q=0) (x : α) :
    residual p q x=0 := by
  have hs := hasSum_residual hp hq hp0 hq0
  have hle := hs.summable.le_tsum x (fun j _ => residual_nonneg p q j)
  rw [hs.tsum_eq,hzero] at hle
  exact le_antisymm hle (residual_nonneg p q x)

/--
@isnad1 id=eq.0h4v.s5.d277aeb68f31 from=translated src=- shape=0f668f33 vocab=85a01fdd
-/
theorem residual_product_self (p q : α → ℝ) (x : α) : residual p q x*residual q p x=0 := by
  unfold residual overlap
  rcases le_total (p x) (q x) with h|h
  · simp [min_eq_left h,min_eq_right h]
  · simp [min_eq_right h,min_eq_left h]

/-- The usual diagonal overlap plus the independent product of the disjoint residuals.-/
def couplingMass (p q : α → ℝ) (z : α × α) : ℝ := by
  classical
  exact (if z.1=z.2 then overlap p q z.1 else 0)+
    residual p q z.1*residual q p z.2/massTotalVariation p q

/--
@isnad1 id=le.2h4v.s5.be2ca2cf9d26 from=translated src=- shape=140fabb4 vocab=0b82fe78
-/
theorem couplingMass_nonneg {p q : α → ℝ} (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x)
    (z : α × α) : 0≤couplingMass p q z := by
  classical
  unfold couplingMass
  apply add_nonneg
  · split_ifs
    · exact overlap_nonneg hp0 hq0 _
    · exact le_rfl
  · exact div_nonneg (mul_nonneg (residual_nonneg _ _ _) (residual_nonneg _ _ _))
      (massTotalVariation_nonneg _ _)

/--
@isnad1 id=eq.0h4v.s4.01361a2f7319 from=translated src=- shape=bbf38f34 vocab=af349d77
-/
theorem couplingMass_diagonal (p q : α → ℝ) (x : α) :
    couplingMass p q (x,x)=overlap p q x := by
  classical
  simp [couplingMass,residual_product_self]

/-- Its first marginal is exactly p, including the case of identical laws.
@isnad1 id=hassum.4h4v.s6.5e26b27df656 from=translated src=- shape=210aa375 vocab=4f6a8561
-/
theorem hasSum_couplingMass_row {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) (x : α) :
    HasSum (fun y => couplingMass p q (x,y)) (p x) := by
  classical
  have hr := hasSum_residual hq hp hq0 hp0
  rw [massTotalVariation_comm q p] at hr
  have hd : HasSum (fun y => if x=y then overlap p q x else 0) (overlap p q x) := by
    simpa only [eq_comm] using (hasSum_ite_eq x (overlap p q x))
  have hs := hd.add ((hr.mul_left (residual p q x)).div_const (massTotalVariation p q))
  have he : overlap p q x+residual p q x*massTotalVariation p q/massTotalVariation p q=p x := by
    by_cases hz : massTotalVariation p q=0
    · have hx := residual_eq_zero_of_variation_zero hp hq hp0 hq0 hz x
      simp only [hz,mul_zero,div_zero,add_zero]
      unfold residual at hx
      linarith
    · rw [mul_div_cancel_right₀ _ hz]
      unfold residual
      ring
  rw [he] at hs
  exact hs

/--
@isnad1 id=eq.0h5v.s5.d45c58c86658 from=translated src=- shape=b2992976 vocab=79ccf8c2
-/
theorem couplingMass_swap (p q : α → ℝ) (x y : α) :
    couplingMass p q (x,y)=couplingMass q p (y,x) := by
  classical
  unfold couplingMass overlap
  rw [massTotalVariation_comm q p]
  by_cases h : x=y
  · subst y
    simp [min_comm,mul_comm]
  · simp [h,Ne.symm h,mul_comm]

/--
@isnad1 id=hassum.4h4v.s6.5d8e8f1ad64e from=translated src=- shape=864137ac vocab=4f6a8561
-/
theorem hasSum_couplingMass_column {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) (y : α) :
    HasSum (fun x => couplingMass p q (x,y)) (q y) := by
  simp_rw [couplingMass_swap p q]
  exact hasSum_couplingMass_row hq hp hq0 hp0 y

/-- A genuine probability mass on the countable product space.
@isnad1 id=hassum.4h3v.s6.218fab5c23e2 from=translated src=- shape=64f37f91 vocab=d9fba670
-/
theorem hasSum_couplingMass {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) : HasSum (couplingMass p q) 1 := by
  have hs : Summable (couplingMass p q) := (summable_prod_of_nonneg (couplingMass_nonneg hp0 hq0)).mpr
    ⟨fun x => (hasSum_couplingMass_row hp hq hp0 hq0 x).summable,
      by simpa only [(hasSum_couplingMass_row hp hq hp0 hq0 _).tsum_eq] using hp.summable⟩
  have ht : (∑' z,couplingMass p q z)=1 := by
    rw [hs.tsum_prod]
    simp_rw [(hasSum_couplingMass_row hp hq hp0 hq0 _).tsum_eq]
    exact hp.tsum_eq
  exact ht ▸ hs.hasSum

end
end PaperC.V282.MaximalCouplingMass
