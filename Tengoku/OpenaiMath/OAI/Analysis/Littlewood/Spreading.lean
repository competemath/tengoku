import Tengoku.OpenaiMath.OAI.Analysis.Littlewood.QuadraticTail

namespace OAI

universe uI uE uJ uK

namespace AsymptoticallyMinimalLittlewood
namespace Spreading
noncomputable section
open QuadraticTail MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff FourierTransform SchwartzMap

/-- The uniform stationary-phase bound in the squared, scale-invariant form
needed for every retained spread Fourier coefficient. -/
lemma quadratic_norm_scaled {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1)
    {β : ℝ} (hβ : β≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ T, 0<T → ∀ u : ℝ,
      T*|β| *‖∫ x : ℝ, g x*phase (T*β) u x‖^2 ≤ (1+C/T)^2 := by
  let C := Real.pi / |β| * (∫ ξ : ℝ, ξ^2 * ‖(𝓕⁻ (hg.toSchwartzMap hgs) : 𝓢(ℝ,ℂ)) ξ‖)
  have hC : 0≤C := mul_nonneg (div_nonneg Real.pi_pos.le (abs_nonneg _))
    (integral_nonneg (fun ξ ↦ mul_nonneg (sq_nonneg _) (norm_nonneg _)))
  refine ⟨C,hC,?_⟩
  intro T hT u
  obtain ⟨E,hE,he⟩ := uniform_quadratic_integration g hg hgs hβ hT u
  change ‖E‖≤C/T at hE
  change (∫ x : ℝ, g x*phase (T*β) u x) = _ at he
  have hphase : ‖realPhase (2*Real.pi*(Real.sign β/8-u^2/(2*T*β)))‖ = 1 := by
    exact norm_realPhase _
  have hsqrt : 0<Real.sqrt (T*|β|) := Real.sqrt_pos.mpr (mul_pos hT (abs_pos.mpr hβ))
  have hn : ‖g (u/(T*β))+E‖≤1+C/T :=
    (norm_add_le _ _).trans (add_le_add (hg1 _) hE)
  have hnorm : ‖∫ x : ℝ, g x*phase (T*β) u x‖ =
      ‖g (u/(T*β))+E‖/Real.sqrt (T*|β|) := by
    rw [he,norm_mul,norm_div,hphase,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hsqrt]
    ring
  rw [hnorm,div_pow,Real.sq_sqrt (mul_pos hT (abs_pos.mpr hβ)).le]
  have hc : 0≤1+C/T := by positivity
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  calc
    _ = ‖g (u/(T*β))+E‖^2 := by field_simp
    _ ≤ _ := hn2

variable {I : Type uI} [Fintype I] [DecidableEq I]

def multiBox (B : ℝ) (β : I → ℝ) : Finset (I → ℤ) :=
  Fintype.piFinset (fun i ↦ box B (β i))

def determinant (β : I → ℝ) : ℝ := ∏ i, |β i|

omit [DecidableEq I] in
lemma determinant_pos {β : I → ℝ} (hβ : ∀ i, β i≠0) : 0<determinant β :=
  Finset.prod_pos (fun i _ ↦ abs_pos.mpr (hβ i))

lemma row_mass_le {g : ℝ → ℂ} (hgs : Continuous g) {α : ℝ}
    (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α) (T β : ℝ) :
    (∑ w ∈ box T β, ‖∫ x : ℝ, g x*phase (T*β) w x‖^2) ≤
      ∫ x : ℝ, ‖g x‖^2 := by
  let f : C(UnitAddCircle,ℂ) := ⟨circleChirp g (T*β),circleChirp_continuous hgs hα hs _⟩
  have hp := circle_parseval f
  have hb := hp.summable.sum_le_tsum (box T β) (fun w _ ↦ sq_nonneg _)
  rw [hp.tsum_eq] at hb
  change (∑ w ∈ box T β, ‖fourierCoeff (circleChirp g (T*β)) w‖^2) ≤
    ∫ z : UnitAddCircle, ‖circleChirp g (T*β) z‖^2 ∂AddCircle.haarAddCircle at hb
  simpa only [circleChirp_coefficient hα hs,circleChirp_mass hα hs] using hb

lemma row_mass_tendsto {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : ℝ} (hβ : β≠0) :
    Tendsto (fun T : ℝ ↦ ∑ w ∈ box T β,
      ‖∫ x : ℝ, g x*phase (T*β) w x‖^2) atTop (𝓝 (∫ x : ℝ, ‖g x‖^2)) := by
  obtain ⟨C,hC,h⟩ := row_mass_error hg hgs hg1 hα0 hα hs hβ
  have hi : Tendsto (fun T : ℝ ↦ C/T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub hi) tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT using h T hT
  · exact Eventually.of_forall (fun T ↦ row_mass_le hgs.continuous hα hs T β)

lemma tensor_mass_tendsto {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : I → ℝ} (hβ : ∀ i, β i≠0) :
    Tendsto (fun B : ℝ ↦ ∑ u ∈ multiBox B β,
      ‖∏ i, (∫ x : ℝ, g x*phase (B*β i) (u i) x)‖^2)
      atTop (𝓝 ((∫ x : ℝ, ‖g x‖^2)^(Fintype.card I))) := by
  have he (B : ℝ) : (∑ u ∈ multiBox B β,
      ‖∏ i, (∫ x : ℝ, g x*phase (B*β i) (u i) x)‖^2) =
      ∏ i, (∑ w ∈ box B (β i), ‖∫ x : ℝ, g x*phase (B*β i) w x‖^2) := by
    simp only [norm_prod,← Finset.prod_pow,multiBox]
    exact (Finset.prod_univ_sum (fun i : I ↦ box B (β i))
      (fun (i : I) (w : ℤ) ↦ ‖∫ x : ℝ, g x*phase (B*β i) w x‖^2)).symm
  simp_rw [he]
  simpa using tendsto_finsetProd Finset.univ
    (fun i _ ↦ row_mass_tendsto hg hgs hg1 hα0 hα hs (hβ i))

end
end Spreading
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex

lemma support_pair_sum {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (S : Finset (Fin n → ℤ)) (hp : ∀ s ∈ S, positive n s)
    (hc : ∀ s, s ∈ c.support ↔ s ∈ S ∨ -s ∈ S)
    {E : Type uE} [AddCommMonoid E] (f : (Fin n → ℤ) → E) :
    ∑ s ∈ c.support, f s = ∑ s ∈ S, (f s+f (-s)) := by
  classical
  have hd : Disjoint S (S.image Neg.neg) := by
    rw [Finset.disjoint_left]
    intro s hs hn
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hn
    exact positive_not_neg (hp t ht) (hp _ hs)
  have he : c.support = S ∪ S.image Neg.neg := by
    ext s
    simpa only [Finset.mem_union, Finset.mem_image, neg_eq_iff_eq_neg,
      exists_eq_right] using hc s
  rw [he, Finset.sum_union hd, Finset.sum_image (by
    intro x _ y _ h; exact neg_injective h), Finset.sum_add_distrib]

lemma binary_positive_data {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) :
    ∃ n : ℕ, ∃ S : Finset (Fin n → ℤ), S.Nonempty ∧
      (∀ s ∈ S, positive n s) ∧ ∃ c : (Fin n → ℤ) → ℂ,
      (∀ s ∈ S, c s≠0) ∧
      (∀ x : Fin n → UnitAddCircle,
        (binary n x : ℂ) = (∑ s ∈ S, c s*mFourier s x) +
          conj (∑ s ∈ S, c s*mFourier s x)) ∧
      1-δ ≤ 2*∑ s ∈ S, ‖c s‖^2 ∧ 2*∑ s ∈ S, ‖c s‖^2 ≤ 1 := by
  classical
  obtain ⟨n,hn,he⟩ := exists_binary_energy hδ
  obtain ⟨c,hp,hc⟩ := exists_binary_coefficients n
  obtain ⟨S,hS,hSp⟩ := coefficient_support_pairs c hp hc
  have hm : 2*∑ s ∈ S, ‖c s‖^2 = energy n := by
    rw [← binary_coefficients_energy c hc, support_pair_sum c S hS hSp]
    simp only [binary_coefficients_conj c hc, norm_conj]
    rw [Finset.sum_add_distrib]
    ring
  have hSn : S.Nonempty := by
    by_contra hz
    have hz' : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hz
    rw [hz'] at hm
    simp only [Finset.sum_empty,mul_zero] at hm
    linarith
  refine ⟨n,S,hSn,hS,c,?_,?_,by linarith,by rw [hm]; exact (energy_bounds n).2⟩
  · intro s hs
    exact Finsupp.mem_support_iff.mp ((hSp s).mpr (Or.inl hs))
  · intro x
    rw [hc, support_pair_sum c S hS hSp, Finset.sum_add_distrib]
    congr 1
    simp only [map_sum,map_mul,binary_coefficients_conj c hc,mFourier_neg]

def rowForm {n : ℕ} (s : Fin n → ℤ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ k, (s k : ℝ) • LinearMap.proj k

lemma rowForm_apply {n : ℕ} (s : Fin n → ℤ) (x : Fin n → ℝ) :
    rowForm s x = ∑ k, (s k : ℝ)*x k := by simp [rowForm]

lemma rowForm_injective {n : ℕ} : Function.Injective (@rowForm n) := by
  classical
  intro s t h
  ext k
  have hh := congrArg (fun f : (Fin n → ℝ) →ₗ[ℝ] ℝ ↦ f (Pi.single k 1)) h
  simp [rowForm_apply, Pi.single_apply, mul_ite] at hh
  exact_mod_cast hh

lemma positive_rowForm_ne_zero {n : ℕ} {s : Fin n → ℤ} (hs : positive n s) :
    rowForm s ≠ 0 := by
  intro hz
  apply primitive_ne_zero (positive_primitive hs)
  apply rowForm_injective
  simpa [rowForm] using hz

lemma positive_rowForm_nonparallel {n : ℕ} {s t : Fin n → ℤ}
    (hs : positive n s) (ht : positive n t) (hne : s ≠ t) (c : ℝ) :
    rowForm s ≠ c • rowForm t := by
  classical
  intro he
  apply hne
  apply (positive_parallel_eq hs ht (c := c) ?_).1
  intro k
  have hh := congrArg (fun f : (Fin n → ℝ) →ₗ[ℝ] ℝ ↦ f (Pi.single k 1)) he
  simpa [rowForm_apply, Pi.single_apply, mul_ite] using hh

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

lemma mFourier_norm_apply {J : Type uJ} [Fintype J] (s : J → ℤ)
    (x : J → UnitAddCircle) : ‖mFourier s x‖=1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

lemma mFourier_add_point {J : Type uJ} [Fintype J] (s : J → ℤ)
    (x y : J → UnitAddCircle) : mFourier s (x+y)=mFourier s x*mFourier s y := by
  simp only [mFourier, ContinuousMap.coe_mk,Pi.add_apply,fourier_apply,
    zsmul_add,AddCircle.toCircle_add,Circle.coe_mul,Finset.prod_mul_distrib]

lemma mFourier_real {J : Type uJ} [Fintype J] (s : J → ℤ) (x : J → ℝ) :
    mFourier s (fun j ↦ (x j : UnitAddCircle)) =
      Complex.exp (Complex.I*(2*Real.pi*(∑ j, (s j : ℝ)*x j) : ℝ)) := by
  simp only [mFourier,ContinuousMap.coe_mk,fourier_coe_apply,Complex.ofReal_one,div_one]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_intCast,Complex.ofReal_ofNat,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma phase_tensor_character {n : ℕ} {J : Type uJ} [Fintype J]
    (s : Fin n → ℤ) (b : J → Fin n → ℝ) (B : ℝ) (z : J → ℝ) :
    (∏ j, phase (B*rowForm s (b j)) 0 (z j)) =
      mFourier s (fun k ↦ ((B/2*∑ j, b j k*z j^2 : ℝ) : UnitAddCircle)) := by
  rw [mFourier_real]
  simp only [phase,sub_zero,zero_mul,← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_div,
    Complex.ofReal_ofNat,Complex.ofReal_pow,rowForm_apply]
  push_cast
  simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

lemma tensor_trunc_expand {J : Type uJ} [Fintype J] [DecidableEq J]
    (g : ℝ → ℂ) (B : ℝ) (β : J → ℝ) (z : J → UnitAddCircle) :
    (∏ j, rowTrunc g B (β j) (z j)) =
      ∑ u∈multiBox B β, (∏ j, ∫ x : ℝ, g x*phase (B*β j) (u j) x)*mFourier u z := by
  classical
  simp only [rowTrunc,multiBox,mFourier,ContinuousMap.coe_mk,← Finset.prod_mul_distrib]
  exact Finset.prod_univ_sum _ _

lemma cutoff_power {D : ℕ} {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∃ α : ℝ, 0<α ∧ α<1/2 ∧ tsupport g ⊆ Set.Icc (-α) α) ∧
      (∀ x, 0≤g x ∧ g x≤1) ∧
      1-δ < (∫ x : ℝ, g x^2)^D := by
  have hD : (0:ℝ)<D+1 := by positivity
  let ε : ℝ := δ/(D+1)
  have hε : 0<ε := div_pos hδ hD
  have hε1 : ε<1 := by dsimp [ε]; rw [div_lt_one hD]; have : (0:ℝ)≤D := Nat.cast_nonneg _; linarith
  obtain ⟨g,hgs,hgc,hga,hg,hm⟩ := Cutoff.unit_cutoff hε
  refine ⟨g,hgs,hgc,hga,hg,?_⟩
  have hb := one_add_mul_le_pow (a := -ε) (by linarith : (-2:ℝ)≤-ε) D
  have hp : (1-ε)^D ≤ (∫ x : ℝ, g x^2)^D := pow_le_pow_left₀ (by linarith) hm.le _
  have hi : (D : ℝ)*ε<δ := by dsimp [ε]; rw [← mul_div_assoc, div_lt_iff₀ hD]; nlinarith
  have hh : 1-δ < 1+(D:ℝ)*(-ε) := by linarith
  exact hh.trans_le (hb.trans (by simpa only [sub_eq_add_neg] using hp))

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

structure RawData (I J : Type) [Fintype I] [Fintype J] (δ : ℝ) where
  frequency : I → J → ℤ
  coefficient : I → ℂ
  velocity : J → ℝ
  nonzero : ∀ i, frequency i ≠ 0
  nonparallel : ∀ i i', i≠i' → ∀ t : ℝ,
    ¬∀ j, (frequency i j : ℝ)=t*(frequency i' j : ℝ)
  bounded : ∀ y : J → UnitAddCircle,
    ‖(∑ i, coefficient i*mFourier (frequency i) y)+
      conj (∑ i, coefficient i*mFourier (frequency i) y)‖≤1
  energy : (1-3*δ)^2 ≤ 2*∑ i, ‖coefficient i‖^2
  curvature : ∀ i, (∑ j, (frequency i j : ℝ)*velocity j)≠0
  width : 2*∑ i, |∑ j, (frequency i j : ℝ)*velocity j| < 1
  size : ∀ i, ‖coefficient i‖^2 ≤ ((1+δ)^3/(1-δ))*
    |∑ j, (frequency i j : ℝ)*velocity j|

structure FinitePacket (δ : ℝ) where
  I : Type
  J : Type
  fintypeI : Fintype I
  fintypeJ : Fintype J
  nonemptyI : Nonempty I
  data : @RawData I J fintypeI fintypeJ δ

attribute [instance] FinitePacket.fintypeI FinitePacket.fintypeJ FinitePacket.nonemptyI

lemma mFourier_sum_type {J : Type uJ} {K : Type uK} [Fintype J] [Fintype K]
    (s : J → ℤ) (u : K → ℤ) (x : J ⊕ K → UnitAddCircle) :
    mFourier (Sum.elim s u) x = mFourier s (x ∘ Sum.inl)*mFourier u (x ∘ Sum.inr) := by
  simp only [mFourier,ContinuousMap.coe_mk,Fintype.prod_sum_type,Sum.elim_inl,
    Sum.elim_inr,Function.comp_apply]

lemma spread_numeric_coefficient {δ τ P Δ ρ U V : ℝ}
    (hδ : 0<δ) (hδ1 : δ<1) (hτ : 0<τ) (hP : 0<P) (hρ : 0<ρ)
    (_hU : 0≤U) (hV : 0≤V)
    (hdet : (1-δ)*τ*U/ρ ≤ Δ) (hdisc : P*Δ*V≤(1+δ)^2) :
    U*V/(1+δ)^2 ≤ ((1+δ)^3/(1-δ))*(ρ/(τ*P*(1+δ)^3)) := by
  have hd0 : 0<1-δ := sub_pos.mpr hδ1
  have hd1 : 0<1+δ := by linarith
  have hd2 := mul_le_mul_of_nonneg_right hdet (mul_nonneg hP.le hV)
  have hd3 := mul_le_mul_of_nonneg_left hdisc hρ.le
  have he : ((1-δ)*τ*U/ρ)*(P*V)*ρ=(1-δ)*τ*P*(U*V) := by field_simp
  have hd4 := mul_le_mul_of_nonneg_right hd2 hρ.le
  rw [he] at hd4
  have hraw : (1-δ)*τ*P*(U*V)≤ρ*(1+δ)^2 := by nlinarith only [hd3,hd4]
  have hr : ((1+δ)^3/(1-δ))*(ρ/(τ*P*(1+δ)^3))=ρ/((1-δ)*τ*P) := by
    field_simp
  rw [hr]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd1) (by positivity)).mpr
  nlinarith only [hraw]

lemma spread_numeric_width {δ τ P Δ ρ U L : ℝ}
    (hδ : 0<δ) (hτ : 0<τ) (hP : 0<P) (hρ : 0<ρ)
    (hdet : Δ ≤ (1+δ)*τ*U/ρ) (hcard : L≤(1+δ)*P*Δ) :
    L*(ρ/(τ*P*(1+δ)^3))≤U/(1+δ) := by
  have hd1 : 0<1+δ := by linarith
  have h1 := mul_le_mul_of_nonneg_left hdet (mul_nonneg hd1.le hP.le)
  have h2 := mul_le_mul_of_nonneg_right (hcard.trans h1) hρ.le
  have he : (1+δ)*P*((1+δ)*τ*U/ρ)*ρ=τ*P*(1+δ)^2*U := by field_simp
  rw [he] at h2
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) hd1).mpr
  have hh := mul_le_mul_of_nonneg_right h2 hd1.le
  nlinarith only [hh]

lemma spread_numeric_energy {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1/20) :
    (1-3*δ)^2 ≤ ((1-δ)*(1-2*δ))/(1+δ)^2 := by
  have h1 : 0≤1-3*δ := by linarith
  have h2 : 0≤1-2*δ := by linarith
  have hd : 0<1+δ := by linarith
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  have hh : (1-3*δ)*(1+δ)≤1-2*δ := by nlinarith [sq_nonneg δ]
  have hsq : ((1-3*δ)*(1+δ))^2≤(1-2*δ)^2 := sq_le_sq₀ (mul_nonneg h1 hd.le) h2 |>.mpr hh
  nlinarith [mul_nonneg hδ.le h2]

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

end
end AsymptoticallyMinimalLittlewood.Auxiliary

end OAI
