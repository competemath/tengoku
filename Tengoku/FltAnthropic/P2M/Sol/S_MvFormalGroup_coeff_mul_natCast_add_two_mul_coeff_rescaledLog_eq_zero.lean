import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_BasicV2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvFormalGroup_coeff_mul_natCast_add_two_mul_coeff_rescaledLog_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvFormalGroup_coeff_mul_natCast_add_two_mul_coeff_rescaledLog_eq_zero

set_option autoImplicit false

universe u

namespace S17QH

open MvPowerSeries

section Cong

variable {S : Type*} [CommRing S] {σ : Type*}

def Cong (n : ℕ) (f g : MvPowerSeries σ S) : Prop := ∀ m : σ →₀ ℕ, m.degree ≤ n → coeff m f = coeff m g

namespace Cong

variable {n : ℕ} {f g h : MvPowerSeries σ S}

/--
@isnad1 id=cong.0h4v.s4.06f605d5fd68 from=translated src=- shape=a1045736 vocab=c3c42a38
-/
theorem refl (f : MvPowerSeries σ S) : Cong n f f := fun _ _ => rfl

/--
@isnad1 id=cong.1h7v.s6.eb6d9fbe77f5 from=translated src=- shape=6d5120ab vocab=b23ec497
-/
theorem sum {ι : Type*} (s : Finset ι) {F G : ι → MvPowerSeries σ S} (h : ∀ i ∈ s, Cong n (F i) (G i)) :
    Cong n (∑ i ∈ s, F i) (∑ i ∈ s, G i) := fun m hm => by
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi m hm

/--
@isnad1 id=cong.2h7v.s6.af3bc6305673 from=translated src=- shape=e6b07aac vocab=fb7603e8
-/
theorem mul {f' g' : MvPowerSeries σ S} (h₁ : Cong n f g) (h₂ : Cong n f' g') : Cong n (f * f') (g * g') := by
  classical
  intro m hm
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  have h1 : x.1.degree ≤ n := by
    have := congrArg Finsupp.degree hx'; rw [map_add] at this; omega
  have h2 : x.2.degree ≤ n := by
    have := congrArg Finsupp.degree hx'; rw [map_add] at this; omega
  rw [h₁ _ h1, h₂ _ h2]

/--
@isnad1 id=iff.0h5v.s6.8344bb418bed from=translated src=- shape=eb211e68 vocab=274abdf1
-/
theorem iff_le_order : Cong n f g ↔ ((n + 1 : ℕ) : ℕ∞) ≤ (f - g).order := by
  constructor
  · intro h
    exact nat_le_order fun m hm => by rw [map_sub, h m (by omega), sub_self]
  · intro h m hm
    have := coeff_of_lt_order (d := m) (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le hm) h)
    rwa [map_sub, sub_eq_zero] at this

/--
@isnad1 id=cong.3h7v.s7.aac6538e2ff6 from=translated src=- shape=35c73d5c vocab=14e75edc
-/
theorem substLeft {τ : Type*} {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (hfg : Cong n f g) : Cong n (subst a f) (subst a g) := by
  rw [iff_le_order] at hfg ⊢
  rw [← subst_sub ha]
  refine hfg.trans ((le_mul_of_one_le_left (by simp) ?_).trans (le_order_subst ha _))
  refine le_iInf fun i => nat_le_order fun d hd => ?_
  have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
  rw [this, coeff_zero_eq_constantCoeff_apply, ha0]

end Cong

/--
@isnad1 id=le.1h5v.s7.b4a1f5dd1a0a from=translated src=- shape=2a9ec3de vocab=e2d079bc
-/
theorem card_le_order_prod {ι : Type*} (s : Finset ι) (u : ι → MvPowerSeries σ S)
    (hu : ∀ i ∈ s, constantCoeff (u i) = 0) : (s.card : ℕ∞) ≤ (∏ i ∈ s, u i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one, add_comm]
    refine le_trans (add_le_add ?_ (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))) le_order_mul
    refine nat_le_order fun d hd => ?_
    have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
    rw [this, coeff_zero_eq_constantCoeff_apply, hu a (Finset.mem_insert_self a s)]

/--
@isnad1 id=cong.3h6v.s8.a5664ed486b6 from=translated src=- shape=c3a45e9e vocab=e30ddab1
-/
theorem Cong.prod_of_cong_one {ι : Type*} (s : Finset ι) (u v : ι → MvPowerSeries σ S)
    (hu : ∀ i ∈ s, constantCoeff (u i) = 0) (hv : ∀ i ∈ s, constantCoeff (v i) = 0)
    (h : ∀ i ∈ s, Cong 1 (u i) (v i)) : Cong s.card (∏ i ∈ s, u i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact Cong.refl _
  | insert a s ha ih =>
    have hu' := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hv' := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have ih' := ih hu' hv' fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Cong.iff_le_order,
      show u a * ∏ i ∈ s, u i - v a * ∏ i ∈ s, v i =
        (u a - v a) * ∏ i ∈ s, u i + v a * (∏ i ∈ s, u i - ∏ i ∈ s, v i) by ring]
    refine le_trans ?_ min_order_le_add
    refine le_min ?_ ?_
    ·
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (u a - v a).order := by
        have := (Cong.iff_le_order).1 (h a (Finset.mem_insert_self a s)); exact_mod_cast this
      have h2 := card_le_order_prod s u hu'
      calc ((s.card + 1 + 1 : ℕ) : ℕ∞) = (2 : ℕ) + (s.card : ℕ∞) := by push_cast; ring
        _ ≤ (u a - v a).order + (∏ i ∈ s, u i).order := add_le_add h1 h2
        _ ≤ _ := le_order_mul
    ·
      have h1 : ((1 : ℕ) : ℕ∞) ≤ (v a).order := nat_le_order fun d hd => by
        have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
        rw [this, coeff_zero_eq_constantCoeff_apply, hv a (Finset.mem_insert_self a s)]
      have h2 : ((s.card + 1 : ℕ) : ℕ∞) ≤ (∏ i ∈ s, u i - ∏ i ∈ s, v i).order := (Cong.iff_le_order).1 ih'
      calc ((s.card + 1 + 1 : ℕ) : ℕ∞) = (1 : ℕ) + ((s.card + 1 : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ (v a).order + (∏ i ∈ s, u i - ∏ i ∈ s, v i).order := add_le_add h1 h2
        _ ≤ _ := le_order_mul

/--
@isnad1 id=eq.0h5v.s7.d93526c2d5c7 from=translated src=- shape=c8161bc4 vocab=c23edcbd
-/
theorem finsuppProd_eq_prod_sigma {ι : Type*} (d : ι →₀ ℕ) (F : ι → MvPowerSeries σ S) :
    (d.prod fun i e => F i ^ e) = ∏ x ∈ d.support.sigma (fun i => Finset.range (d i)), F x.1 := by
  rw [Finsupp.prod, Finset.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Finset.prod_const, Finset.card_range]

/--
@isnad1 id=eq.0h2v.s7.e5a9a74c9238 from=translated src=- shape=a53c6678 vocab=db4b390d
-/
theorem card_sigma_range {ι : Type*} (d : ι →₀ ℕ) : (d.support.sigma fun i => Finset.range (d i)).card = d.degree := by
  rw [Finset.card_sigma, Finsupp.degree_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.card_range _

/--
@isnad1 id=cong.4h7v.s9.82aa808accd3 from=translated src=- shape=a144a9cf vocab=0c3a3c43
-/
theorem Cong.aeval_of_isHomogeneous {τ : Type*} {N : ℕ} (P : MvPolynomial τ S) (hP : P.IsHomogeneous N)
    (a b : τ → MvPowerSeries σ S) (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (hab : ∀ i, Cong 1 (a i) (b i)) :
    Cong N (MvPolynomial.aeval a P : MvPowerSeries σ S) (MvPolynomial.aeval b P) := by
  classical
  have key : ∀ d ∈ P.support, Cong N (d.prod fun i e => a i ^ e) (d.prod fun i e => b i ^ e) := by
    intro d hd
    have hdeg : d.degree = N := by
      have := hP (MvPolynomial.mem_support_iff.1 hd)
      rw [Finsupp.degree_eq_weight_one]
      simpa [Pi.one_def] using this
    rw [finsuppProd_eq_prod_sigma, finsuppProd_eq_prod_sigma, ← hdeg, ← card_sigma_range d]
    exact Cong.prod_of_cong_one _ _ _ (fun x _ => ha x.1) (fun x _ => hb x.1) (fun x _ => hab x.1)
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum]
  refine Cong.sum _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  exact (Cong.refl _).mul (key d hd)

end Cong

section Pieces

variable {S : Type*} [CommRing S] {σ : Type*}

section Fin
variable [Fintype σ]

open Classical in

noncomputable def lowDeg (σ : Type*) [Fintype σ] (N : ℕ) : Finset (σ →₀ ℕ) :=
  ((Fintype.piFinset fun _ : σ => Finset.range (N + 1)).image fun f => Finsupp.equivFunOnFinite.symm f).filter
    fun n => n.degree ≤ N

/--
@isnad1 id=iff.0h3v.s7.85ce399b4767 from=translated src=- shape=ccbf4f66 vocab=10ec4b35
-/
theorem mem_lowDeg {N : ℕ} (n : σ →₀ ℕ) : n ∈ lowDeg σ N ↔ n.degree ≤ N := by
  classical
  rw [lowDeg, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨Finset.mem_image.2 ⟨fun s => n s, Fintype.mem_piFinset.2 fun s => Finset.mem_range.2
      (Nat.lt_succ_of_le ((Finsupp.le_degree s n).trans h)), ?_⟩, h⟩
    ext s; simp

private noncomputable def _root_.S17QH.homogPart (N : ℕ) (g : MvPowerSeries σ S) : MvPolynomial σ S :=
  ∑ m ∈ (lowDeg σ N).filter (fun m => m.degree = N), MvPolynomial.monomial m (coeff m g)

export _root_.S17QH (homogPart)
/--
@isnad1 id=eq.0h5v.s8.5a3e15d157be from=translated src=- shape=04825eaf vocab=12f9c36f
-/
theorem coeff_homogPart (N : ℕ) (g : MvPowerSeries σ S) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (homogPart N g) = if m.degree = N then coeff m g else 0 := by
  classical
  rw [homogPart, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, mem_lowDeg]
  by_cases h : m.degree = N
  · rw [ite_eq_left ⟨h.le, h⟩, ite_eq_left h]
  · rw [ite_eq_right (fun h' => h h'.2), ite_eq_right h]

/--
@isnad1 id=ishomoge.0h4v.s4.01ac86e42cc1 from=translated src=- shape=3f23cdbe vocab=8a5b910f
-/
theorem isHomogeneous_homogPart (N : ℕ) (g : MvPowerSeries σ S) : (homogPart N g).IsHomogeneous N := by
  classical
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun m hm => ?_
  exact MvPolynomial.isHomogeneous_monomial _ (Finset.mem_filter.1 hm).2

end Fin

/--
@isnad1 id=ex.1h2v.s7.744e2e49167b from=translated src=- shape=bdf8b0dd vocab=dbf5d1eb
-/
theorem exists_eq_single_of_degree_eq_one {m : σ →₀ ℕ} (hm : m.degree = 1) : ∃ u, m = Finsupp.single u 1 := by
  classical
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  obtain ⟨u, hu⟩ := Finsupp.support_nonempty_iff.2 hm0
  have hu1 : m u = 1 := by
    have h1 := Finsupp.le_degree u m
    have h2 := Finsupp.mem_support_iff.1 hu
    omega
  refine ⟨u, ?_⟩
  have hle : Finsupp.single u 1 ≤ m := Finsupp.single_le_iff.2 hu1.ge
  have hrest : m - Finsupp.single u 1 = 0 := by
    apply (Finsupp.degree_eq_zero_iff _).1
    have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
    rw [map_add, Finsupp.degree_single, hm] at this
    omega
  have := tsub_add_cancel_of_le hle
  rw [hrest, zero_add] at this
  exact this.symm

/--
@isnad1 id=iff.0h4v.s9.d42b5157d6b6 from=translated src=- shape=65c39a5d vocab=aaa0edbe
-/
theorem Cong.one_iff {f g : MvPowerSeries σ S} :
    Cong 1 f g ↔ constantCoeff f = constantCoeff g ∧ ∀ u, coeff (Finsupp.single u 1) f = coeff (Finsupp.single u 1) g := by
  constructor
  · intro h
    exact ⟨by rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]; exact h 0 (by simp),
      fun u => h _ (by rw [Finsupp.degree_single])⟩
  · rintro ⟨h0, h1⟩ m hm
    rcases Nat.lt_or_ge m.degree 1 with hlt | hge
    · have : m = 0 := (Finsupp.degree_eq_zero_iff m).1 (by omega)
      rw [this, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, h0]
    · obtain ⟨u, rfl⟩ := exists_eq_single_of_degree_eq_one (m := m) (by omega)
      exact h1 u

end Pieces

section Main

variable {𝓞 : Type u} [CommRing 𝓞] {d : ℕ}

noncomputable def muJ (j : Fin d) : (Fin d ⊕ Fin d) →₀ ℕ :=
  Finsupp.single (Sum.inl j) 1 + Finsupp.single (Sum.inr j) 1

/--
@isnad1 id=eq.0h2v.s7.cfb5f39d321f from=translated src=- shape=980d18b5 vocab=79a171ef
-/
theorem degree_muJ (j : Fin d) : (muJ (d := d) j).degree = 2 := by
  rw [muJ, map_add, Finsupp.degree_single, Finsupp.degree_single]

/--
@isnad1 id=eq.0h3v.s6.7d843d3743a6 from=translated src=- shape=47e25cdb vocab=25b5a611
-/
theorem muJ_inl (j s : Fin d) : muJ (d := d) j (Sum.inl s) = if s = j then 1 else 0 := by
  classical
  simp only [muJ, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, Sum.inl.injEq, reduceCtorEq, ite_false, add_zero]
  by_cases h : j = s
  · subst h; simp
  · simp [h, Ne.symm h]

/--
@isnad1 id=eq.0h3v.s6.5156a24bd913 from=translated src=- shape=47e25cdb vocab=b6f44ba9
-/
theorem muJ_inr (j s : Fin d) : muJ (d := d) j (Sum.inr s) = if s = j then 1 else 0 := by
  classical
  simp only [muJ, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, Sum.inr.injEq, reduceCtorEq, ite_false, zero_add]
  by_cases h : j = s
  · subst h; simp
  · simp [h, Ne.symm h]

end Main

section MainBC

variable {𝓞 : Type u} [CommRing 𝓞] {d : ℕ}

/--
@isnad1 id=ex.1h2v.s7.cdcfd97b9552 from=translated src=- shape=6f4c3987 vocab=ab09b3d7
-/
theorem exists_eq_single_add_single_of_degree_eq_two {σ : Type*} {m : σ →₀ ℕ} (hm : m.degree = 2) :
    ∃ a b, m = Finsupp.single a 1 + Finsupp.single b 1 := by
  classical
  have hne : m ≠ 0 := by rintro rfl; simp at hm
  obtain ⟨a, ha⟩ : ∃ a, m a ≠ 0 := by
    by_contra h; push Not at h; exact hne (Finsupp.ext h)
  set m' := m - Finsupp.single a 1 with hm'
  have hmm' : Finsupp.single a 1 + m' = m := by
    ext s
    simp only [hm', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
    split_ifs with hs
    · subst hs; omega
    · omega
  have hdeg : m'.degree = 1 := by
    have := congrArg Finsupp.degree hmm'
    rw [map_add, Finsupp.degree_single, hm] at this
    omega
  obtain ⟨b, hb⟩ := exists_eq_single_of_degree_eq_one hdeg
  exact ⟨a, b, by rw [← hmm', hb]⟩

/--
@isnad1 id=eq.0h5v.s9.ecd80f4eef88 from=translated src=- shape=6cd18e82 vocab=ceb54f60
-/
theorem coeff_muJ_XY_mul_XY (j a b : Fin d) :
    coeff (muJ j) (((X (Sum.inl a) + X (Sum.inr a)) * (X (Sum.inl b) + X (Sum.inr b)) :
      MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) = if a = j ∧ b = j then 2 else 0 := by
  classical
  have hX : ∀ x : Fin d ⊕ Fin d, (X x : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) = monomial (Finsupp.single x 1) 1 :=
    fun x => rfl
  simp only [hX, add_mul, mul_add, monomial_mul_monomial, one_mul, map_add, coeff_monomial]

  have hev : ∀ (x y z : Fin d ⊕ Fin d), ((Finsupp.single x 1 + Finsupp.single y 1 : (Fin d ⊕ Fin d) →₀ ℕ) z) =
      (if x = z then 1 else 0) + (if y = z then 1 else 0) := fun x y z => by
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  have hmu : ∀ z : Fin d ⊕ Fin d, (muJ (d := d) j) z = (if Sum.inl j = z then 1 else 0) + (if Sum.inr j = z then 1 else 0) :=
    fun z => by simp only [muJ, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  have key : ∀ x y : Fin d ⊕ Fin d, (muJ j = Finsupp.single x 1 + Finsupp.single y 1) ↔
      ((x = Sum.inl j ∧ y = Sum.inr j) ∨ (x = Sum.inr j ∧ y = Sum.inl j)) := by
    intro x y
    constructor
    · intro h
      have e1 := congrArg (fun f : (Fin d ⊕ Fin d) →₀ ℕ => f (Sum.inl j)) h
      have e2 := congrArg (fun f : (Fin d ⊕ Fin d) →₀ ℕ => f (Sum.inr j)) h
      have e3 := congrArg (fun f : (Fin d ⊕ Fin d) →₀ ℕ => f x) h
      simp only [hev, hmu] at e1 e2 e3
      simp only [ite_true] at e1 e2 e3
      by_cases hx1 : x = Sum.inl j
      · subst hx1
        left; refine ⟨rfl, ?_⟩
        by_cases hy : y = Sum.inr j
        · exact hy
        · exfalso; rw [ite_eq_right hy] at e2; simp at e2
      · by_cases hx2 : x = Sum.inr j
        · subst hx2
          right; refine ⟨rfl, ?_⟩
          by_cases hy : y = Sum.inl j
          · exact hy
          · exfalso; rw [ite_eq_right hy] at e1; simp at e1
        · exfalso
          rw [ite_eq_right (Ne.symm hx1), ite_eq_right (Ne.symm hx2)] at e3
          split_ifs at e3 <;> omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rfl
      · rw [muJ, add_comm]
  simp only [key]
  by_cases ha : a = j <;> by_cases hb : b = j
  · subst ha; subst hb; simp; norm_num
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]

/--
@isnad1 id=eq.1h4v.s9.7810a135bf3b from=translated src=- shape=c3ef0439 vocab=8d9684f5
-/
theorem coeff_muJ_prod_XY_pow' (j : Fin d) (m : Fin d →₀ ℕ) (hm : m.degree = 2) :
    coeff (muJ j) (m.prod fun s e => ((X (Sum.inl s) + X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) ^ e) =
      if m = Finsupp.single j 2 then 2 else 0 := by
  classical
  obtain ⟨a, b, rfl⟩ := exists_eq_single_add_single_of_degree_eq_two hm
  rw [Finsupp.prod_add_index' (h := fun s e => ((X (Sum.inl s) + X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) ^ e)
    (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  rw [Finsupp.prod_single_index (h := fun s e => ((X (Sum.inl s) + X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) ^ e) (pow_zero _),
    Finsupp.prod_single_index (h := fun s e => ((X (Sum.inl s) + X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) ^ e) (pow_zero _),
    pow_one, pow_one, coeff_muJ_XY_mul_XY]
  congr 1
  apply propext
  constructor
  · rintro ⟨rfl, rfl⟩; rw [← Finsupp.single_add]
  · intro h
    have h1 := congrArg (fun f => f a) h
    have h2 := congrArg (fun f => f b) h
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, ite_true] at h1 h2
    constructor
    · by_contra hx
      rw [ite_eq_right (Ne.symm hx)] at h1
      split_ifs at h1 <;> omega
    · by_contra hy
      rw [ite_eq_right (Ne.symm hy)] at h2
      split_ifs at h2 <;> omega

/--
@isnad1 id=eq.2h6v.s8.6a3e08d2dabb from=translated src=- shape=b4a98a46 vocab=cf10cf0e
-/
theorem coeff_subst_X_comp_eq_zero {σ τ : Type*} {e : σ → τ} (he : Function.Injective e) (g : MvPowerSeries σ 𝓞)
    (μ : τ →₀ ℕ) (hμ : ∀ d' : σ →₀ ℕ, d'.mapDomain e ≠ μ) :
    coeff μ (subst (fun s => (X (e s) : MvPowerSeries τ 𝓞)) g) = 0 := by
  classical
  have ha : HasSubst (fun s => (X (e s) : MvPowerSeries τ 𝓞)) := by
    refine ⟨fun s => by rw [constantCoeff_X]; exact IsNilpotent.zero, fun d' => ?_⟩
    apply Set.Subsingleton.finite
    intro s₁ h₁ s₂ h₂
    simp only [Set.mem_ofPred_eq, coeff_X] at h₁ h₂
    split_ifs at h₁ h₂ with e₁ e₂
    · rw [e₁] at e₂; exact he (Finsupp.single_left_injective one_ne_zero e₂)
    all_goals simp_all
  have hmono : ∀ d' : σ →₀ ℕ, (d'.prod fun s k => (X (e s) : MvPowerSeries τ 𝓞) ^ k) = monomial (d'.mapDomain e) 1 := by
    intro d'
    rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_mapDomain_index_inj he]
  rw [coeff_subst ha]
  refine finsum_eq_zero_of_forall_eq_zero fun d' => ?_
  rw [hmono, coeff_monomial, ite_eq_right (Ne.symm (hμ d')), smul_zero]

/--
@isnad1 id=ne.0h3v.s5.83c3244ffef1 from=translated src=- shape=5adc5b06 vocab=c66733ba
-/
theorem muJ_not_mapDomain_inl (j : Fin d) (d' : Fin d →₀ ℕ) : d'.mapDomain Sum.inl ≠ muJ j := by
  intro h
  have := congrArg (fun f => f (Sum.inr j)) h
  simp only [muJ_inr, ite_true] at this
  rw [Finsupp.mapDomain_of_notMem_range] at this
  · exact zero_ne_one this
  · rintro ⟨x, hx⟩; cases hx

/--
@isnad1 id=ne.0h3v.s5.d6eff41bee41 from=translated src=- shape=5adc5b06 vocab=113952ee
-/
theorem muJ_not_mapDomain_inr (j : Fin d) (d' : Fin d →₀ ℕ) : d'.mapDomain Sum.inr ≠ muJ j := by
  intro h
  have := congrArg (fun f => f (Sum.inl j)) h
  simp only [muJ_inl, ite_true] at this
  rw [Finsupp.mapDomain_of_notMem_range] at this
  · exact zero_ne_one this
  · rintro ⟨x, hx⟩; cases hx

variable (p : ℕ) [Fact p.Prime]

/--
@isnad1 id=eq.6h8v.s10.d431a0e8e019 from=translated src=- shape=5c901ef2 vocab=0851fc54
-/
theorem mainγ (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (F : MvFormalGroup d 𝓞)
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (i j : Fin d) :
    (F.toPowerSeries i).coeff (muJ j) * (p : 𝓞) + 2 * (φ i).coeff (Finsupp.single j 2) = 0 := by
  classical
  have hsub : HasSubst Fp := hasSubst_of_constantCoeff_zero hFp0

  have hc1 : ∀ s, Cong 1 (Fp s) (X (Sum.inl s) + X (Sum.inr s)) := by
    intro s
    rw [Cong.one_iff]
    refine ⟨by rw [hFp0, map_add, constantCoeff_X, constantCoeff_X, add_zero], ?_⟩
    intro x
    have h := hFp s (Finsupp.single x 1) (by simp)
    rw [Finsupp.degree_single, pow_one, mul_comm ((p:𝓞))] at h
    rw [(mul_cancel_right_mem_nonZeroDivisors hp).1 h, map_add, coeff_X, coeff_X]
    rcases x with k | k
    · rw [F.coeff_single_inl]
      by_cases h : s = k
      · subst h; simp [Finsupp.single_eq_single_iff]
      · simp [Finsupp.single_eq_single_iff, h, Ne.symm h]
    · rw [F.coeff_single_inr]
      by_cases h : s = k
      · subst h; simp [Finsupp.single_eq_single_iff]
      · simp [Finsupp.single_eq_single_iff, h, Ne.symm h]

  set H : MvPolynomial (Fin d) 𝓞 := homogPart 2 (φ i) with hH
  have hc2 : Cong 2 (φ i) (X i + (H : MvPowerSeries (Fin d) 𝓞)) := by
    intro m hm
    have hHm : coeff m (H : MvPowerSeries (Fin d) 𝓞) = if m.degree = 2 then coeff m (φ i) else 0 := by
      rw [MvPolynomial.coeff_coe, coeff_homogPart]
    have hXm : coeff m (X i : MvPowerSeries (Fin d) 𝓞) = if m = Finsupp.single i 1 then 1 else 0 := coeff_X _ _
    rw [map_add, hHm, hXm]
    by_cases h2 : m.degree = 2
    · rw [ite_eq_left h2, ite_eq_right, zero_add]
      intro h; rw [h, Finsupp.degree_single] at h2; omega
    · rw [ite_eq_right h2, add_zero]
      by_cases h1 : m.degree = 1
      · obtain ⟨u, rfl⟩ := exists_eq_single_of_degree_eq_one h1
        have := congrArg (fun M => M i u) hφ1
        simp only [MvFormalGroup.linearPart, Matrix.of_apply, Matrix.one_apply] at this
        rw [this]
        by_cases hiu : i = u
        · subst hiu; simp
        · rw [ite_eq_right hiu, ite_eq_right]; intro h; exact hiu (Finsupp.single_left_injective one_ne_zero h).symm
      · have h0 : m.degree = 0 := by omega
        have : m = 0 := (Finsupp.degree_eq_zero_iff m).1 h0
        subst this
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ0, ite_eq_right]
        intro h; have := congrArg Finsupp.degree h; simp at this

  have hL1 : Cong 2 (subst Fp (φ i)) (Fp i + (MvPolynomial.aeval Fp H : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) := by
    have := Cong.substLeft (n := 2) hsub hFp0 hc2
    rwa [subst_add hsub, subst_X hsub, subst_coe (a := Fp) H] at this
  have hXY0 : ∀ s, constantCoeff ((X (Sum.inl s) + X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) = 0 :=
    fun s => by rw [map_add, constantCoeff_X, constantCoeff_X, add_zero]
  have hL2 : Cong 2 (MvPolynomial.aeval Fp H : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
      (MvPolynomial.aeval (fun s => (X (Sum.inl s) + X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) H) :=
    Cong.aeval_of_isHomogeneous H (isHomogeneous_homogPart _ _) _ _ hFp0 hXY0 hc1

  have hcoefH : coeff (muJ j)
      (MvPolynomial.aeval (fun s => (X (Sum.inl s) + X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) H) =
      2 * (φ i).coeff (Finsupp.single j 2) := by
    have hterm : ∀ m : Fin d →₀ ℕ, m.degree = 2 →
        coeff (muJ j) (MvPolynomial.aeval
          (fun s => (X (Sum.inl s) + X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))
          (MvPolynomial.monomial m (MvPolynomial.coeff m H))) =
        MvPolynomial.coeff m H * (if m = Finsupp.single j 2 then 2 else 0) := by
      intro m hm
      rw [MvPolynomial.aeval_monomial, ← MvPowerSeries.c_eq_algebraMap, coeff_C_mul, coeff_muJ_prod_XY_pow' j m hm]
    rw [H.as_sum, map_sum, map_sum, Finset.sum_eq_single (Finsupp.single j 2)]
    · rw [hterm _ (Finsupp.degree_single _ _), ite_eq_left rfl, hH, coeff_homogPart, ite_eq_left (Finsupp.degree_single _ _),
        mul_comm]
    · intro m hm hne
      have hdeg : m.degree = 2 := by
        have := isHomogeneous_homogPart 2 (φ i) (MvPolynomial.mem_support_iff.1 (hH ▸ hm))
        rw [Finsupp.degree_eq_weight_one]
        simpa [Pi.one_def] using this
      rw [hterm m hdeg, ite_eq_right hne, mul_zero]
    · intro hnot
      rw [MvPolynomial.notMem_support_iff.1 hnot, map_zero, map_zero, map_zero]

  have hRHS : coeff (muJ j) (subst (fun s => (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
      subst (fun s => (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i)) = 0 := by
    rw [map_add, coeff_subst_X_comp_eq_zero Sum.inl_injective _ _ (muJ_not_mapDomain_inl j),
      coeff_subst_X_comp_eq_zero Sum.inr_injective _ _ (muJ_not_mapDomain_inr j), add_zero]
  have hLHS : coeff (muJ j) (subst Fp (φ i)) = coeff (muJ j) (Fp i) + 2 * (φ i).coeff (Finsupp.single j 2) := by
    rw [hL1 (muJ j) (degree_muJ j).le, map_add, hL2 (muJ j) (degree_muJ j).le, hcoefH]
  have hFpμ : coeff (muJ j) (Fp i) * (p : 𝓞) = (p : 𝓞) ^ 2 * (F.toPowerSeries i).coeff (muJ j) := by
    rw [← degree_muJ j]
    exact hFp i (muJ j) (by
      intro h; have := congrArg Finsupp.degree h; rw [degree_muJ] at this; simp at this)
  have h0 : coeff (muJ j) (Fp i) + 2 * (φ i).coeff (Finsupp.single j 2) = 0 := by
    rw [← hLHS, hφF, hRHS]
  have h1 : (p : 𝓞) * ((F.toPowerSeries i).coeff (muJ j) * (p : 𝓞) + 2 * (φ i).coeff (Finsupp.single j 2)) =
      (p : 𝓞) * 0 := by
    rw [mul_zero]
    calc (p : 𝓞) * ((F.toPowerSeries i).coeff (muJ j) * (p : 𝓞) + 2 * (φ i).coeff (Finsupp.single j 2))
        = (p : 𝓞) ^ 2 * (F.toPowerSeries i).coeff (muJ j) + (2 * (φ i).coeff (Finsupp.single j 2)) * (p : 𝓞) := by ring
      _ = (coeff (muJ j) (Fp i) + 2 * (φ i).coeff (Finsupp.single j 2)) * (p : 𝓞) := by rw [← hFpμ]; ring
      _ = 0 := by rw [h0, zero_mul]
  exact (mul_cancel_left_mem_nonZeroDivisors hp).1 h1

end MainBC

end S17QH

open MvPowerSeries in

/--
@isnad1 id=eq.6h8v.s10.88091c337397 from=translated src=- shape=5274cedc vocab=874df06f
-/
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {d : ℕ} (F : MvFormalGroup d 𝓞)
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (i j : Fin d) :
    (F.toPowerSeries i).coeff (Finsupp.single (Sum.inl j) 1 + Finsupp.single (Sum.inr j) 1) * (p : 𝓞) +
      2 * (φ i).coeff (Finsupp.single j 2) = 0 :=
  S17QH.mainγ p hp F Fp hFp hFp0 φ hφ0 hφ1 hφF i j
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
