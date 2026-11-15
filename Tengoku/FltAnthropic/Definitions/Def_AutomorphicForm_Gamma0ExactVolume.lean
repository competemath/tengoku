import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_FundamentalDomainExactVolume
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory Set ModularGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups Pointwise ENNReal Modular

namespace FLT.Gamma0ExactVolume

open FLT.Gamma0FundamentalSet FLT.HyperbolicMeasure FLT.FundamentalDomainExactVolume
  FLT.FundamentalDomainVolume

/--
@isnad1 id=eq.1h1v.s6.eeb3573d5870 from=translated src=- shape=92d73063 vocab=5f957b62
-/
theorem volume_eq_zero_of_image_null {s : Set ℍ}
    (h : volume ((↑) '' s : Set ℂ) = 0) : volume s = 0 := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  exact setLIntegral_measure_zero _ _ h

/--
@isnad1 id=eq.0h1v.s5.80badf53c6ca from=translated src=- shape=1ce78f50 vocab=85c84c3e
-/
theorem volume_re_eq_zero (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have hset : {z : ℂ | z.re = c} =
      Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ (Set.univ : Set ℝ)) := by
    ext z
    simp [Set.mem_prod]
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet)]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod, Real.volume_singleton, zero_mul]

/--
@isnad1 id=eq.0h0v.s6.67da817e6a3b from=translated src=- shape=6b5123b1 vocab=dbcd3726
-/
theorem volume_normSq_eq_one : volume {z : ℂ | Complex.normSq z = 1} = 0 := by
  have hsub : {z : ℂ | Complex.normSq z = 1} ⊆ Metric.sphere (0 : ℂ) 1 := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    simp only [Metric.mem_sphere, dist_zero_right]
    nlinarith [Complex.normSq_eq_norm_sq z, norm_nonneg z]
  exact measure_mono_null hsub (Measure.addHaar_sphere volume 0 1)

/--
@isnad1 id=eq.0h0v.s5.c067926517cd from=translated src=- shape=300ac5b9 vocab=56501074
-/
theorem volume_fd_diff_fdo : volume (𝒟 \ 𝒟ᵒ) = 0 := by
  apply volume_eq_zero_of_image_null
  apply measure_mono_null (t := {z : ℂ | Complex.normSq z = 1} ∪
    ({z : ℂ | z.re = 1 / 2} ∪ {z : ℂ | z.re = -(1 / 2)}))
  · rintro w ⟨z, ⟨⟨hn, hr⟩, hz⟩, rfl⟩
    simp only [ModularGroup.fdo, Set.mem_ofPred_eq, not_and_or, not_lt] at hz
    rcases hz with hz | hz
    · exact Or.inl (le_antisymm hz hn)
    · right
      have : |z.re| = 1 / 2 := le_antisymm hr hz
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mp this with h | h
      · exact Or.inl (by simp only [Set.mem_ofPred_eq, UpperHalfPlane.coe_re]; exact h)
      · exact Or.inr (by simp only [Set.mem_ofPred_eq, UpperHalfPlane.coe_re]; exact h)
  · refine measure_union_null volume_normSq_eq_one (measure_union_null ?_ ?_) <;>
      exact volume_re_eq_zero _

/--
@isnad1 id=eq.0h0v.s5.4ae735c082db from=translated src=- shape=b6077ce3 vocab=d789a82d
-/
theorem volume_fdo_eq_volume_fd : volume 𝒟ᵒ = volume 𝒟 := by
  refine le_antisymm (measure_mono ModularGroup.fdo_subset_fd) ?_
  calc volume 𝒟 = volume (𝒟ᵒ ∪ 𝒟 \ 𝒟ᵒ) := by
        rw [Set.union_sdiff_cancel ModularGroup.fdo_subset_fd]
    _ ≤ volume 𝒟ᵒ + volume (𝒟 \ 𝒟ᵒ) := measure_union_le _ _
    _ = volume 𝒟ᵒ := by rw [volume_fd_diff_fdo, add_zero]

/--
@isnad1 id=le.0h1v.s8.0433ba6460cf from=translated src=- shape=81ffe492 vocab=2055ba57
-/
theorem volume_gammaFundamentalSet_le (Γ : Subgroup SL(2, ℤ)) [Finite (SL(2, ℤ) ⧸ Γ)] :
    volume (gammaFundamentalSet Γ) ≤ Nat.card (SL(2, ℤ) ⧸ Γ) • volume 𝒟 := by
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  calc volume (gammaFundamentalSet Γ)
      = volume (⋃ q : SL(2, ℤ) ⧸ Γ, (Quotient.out q)⁻¹ • 𝒟) := rfl
    _ ≤ ∑' q : SL(2, ℤ) ⧸ Γ, volume ((Quotient.out q)⁻¹ • 𝒟) := measure_iUnion_le _
    _ = Nat.card (SL(2, ℤ) ⧸ Γ) • volume 𝒟 := by
        simp_rw [FLT.HyperbolicMeasure.volume_smul_sl2z]
        rw [tsum_eq_sum (s := Finset.univ) (fun i hi => absurd (Finset.mem_univ i) hi),
          Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

/--
@isnad1 id=pairwise.1h1v.s9.87656ad75823 from=translated src=- shape=b7f0aee0 vocab=9de943bc
-/
theorem pairwise_disjoint_inv_smul_fdo (Γ : Subgroup SL(2, ℤ)) (hΓ : -1 ∈ Γ) :
    Pairwise (Function.onFun Disjoint
      fun q : SL(2, ℤ) ⧸ Γ => (Quotient.out q)⁻¹ • (𝒟ᵒ : Set ℍ)) := by
  intro q q' hqq'
  rw [Function.onFun, Set.disjoint_left]
  rintro z hz hz'
  rw [Set.mem_inv_smul_set_iff] at hz hz'
  have key : (Quotient.out q' * (Quotient.out q)⁻¹) • (Quotient.out q • z) ∈ 𝒟ᵒ := by
    rwa [mul_smul, inv_smul_smul]
  rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo hz key with h | h
  ·
    exact hqq' (by rw [← Quotient.out_eq q, ← Quotient.out_eq q', mul_inv_eq_one.mp h])
  ·
    apply hqq'
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    refine Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)
    rw [mul_inv_eq_iff_eq_mul.mp h, neg_one_mul, mul_neg, inv_mul_cancel]
    exact hΓ

/--
@isnad1 id=le.1h1v.s9.f1f2c88d5fe1 from=translated src=- shape=05a95120 vocab=26d0fece
-/
theorem nsmul_volume_fd_le (Γ : Subgroup SL(2, ℤ)) (hΓ : -1 ∈ Γ) [Finite (SL(2, ℤ) ⧸ Γ)] :
    Nat.card (SL(2, ℤ) ⧸ Γ) • volume 𝒟 ≤ volume (gammaFundamentalSet Γ) := by
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  have hsub : (⋃ q : SL(2, ℤ) ⧸ Γ, (Quotient.out q)⁻¹ • (𝒟ᵒ : Set ℍ)) ⊆
      gammaFundamentalSet Γ :=
    Set.iUnion_mono fun q => Set.smul_set_mono ModularGroup.fdo_subset_fd
  calc Nat.card (SL(2, ℤ) ⧸ Γ) • volume 𝒟
      = ∑' q : SL(2, ℤ) ⧸ Γ, volume ((Quotient.out q)⁻¹ • (𝒟ᵒ : Set ℍ)) := by
        simp_rw [FLT.HyperbolicMeasure.volume_smul_sl2z, volume_fdo_eq_volume_fd]
        rw [tsum_eq_sum (s := Finset.univ) (fun i hi => absurd (Finset.mem_univ i) hi),
          Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
    _ = volume (⋃ q : SL(2, ℤ) ⧸ Γ, (Quotient.out q)⁻¹ • (𝒟ᵒ : Set ℍ)) :=
        (measure_iUnion (pairwise_disjoint_inv_smul_fdo Γ hΓ)
          (fun _ => (ModularGroup.isOpen_fdo.smul _).measurableSet)).symm
    _ ≤ volume (gammaFundamentalSet Γ) := measure_mono hsub

/--
@isnad1 id=eq.1h1v.s9.a7f4718bd9cb from=translated src=- shape=6956442c vocab=8f34f88c
-/
theorem volume_gammaFundamentalSet_eq (Γ : Subgroup SL(2, ℤ)) (hΓ : -1 ∈ Γ)
    [Finite (SL(2, ℤ) ⧸ Γ)] :
    volume (gammaFundamentalSet Γ) = Nat.card (SL(2, ℤ) ⧸ Γ) • volume 𝒟 :=
  le_antisymm (volume_gammaFundamentalSet_le Γ) (nsmul_volume_fd_le Γ hΓ)

/--
@isnad1 id=eq.1h1v.s9.84954ff2bb36 from=translated src=- shape=9f78aa5c vocab=160f2343
-/
theorem volume_gammaFundamentalSet_eq_ofReal (Γ : Subgroup SL(2, ℤ)) (hΓ : -1 ∈ Γ)
    [Finite (SL(2, ℤ) ⧸ Γ)] :
    volume (gammaFundamentalSet Γ) =
      Nat.card (SL(2, ℤ) ⧸ Γ) • ENNReal.ofReal (Real.pi / 3) := by
  rw [volume_gammaFundamentalSet_eq Γ hΓ, FLT.FundamentalDomainExactVolume.volume_fd_eq]

/--
@isnad1 id=mem.0h1v.s8.dd309ee66a53 from=translated src=- shape=47a2a55e vocab=3a18f723
-/
theorem neg_one_mem_Gamma0_all (N : ℕ) : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
  rw [Gamma0_mem]
  simp

/--
@isnad1 id=eq.0h1v.s7.065f458863fd from=translated src=- shape=6ec09994 vocab=647e5aea
-/
theorem volume_gamma0_eq (N : ℕ) [NeZero N] :
    haveI : Finite (SL(2, ℤ) ⧸ Gamma0 N) := FLT.SiegelSetCover.finite_quotient_gamma0 N
    volume (gammaFundamentalSet (Gamma0 N)) =
      Nat.card (SL(2, ℤ) ⧸ Gamma0 N) • ENNReal.ofReal (Real.pi / 3) := by
  haveI : Finite (SL(2, ℤ) ⧸ Gamma0 N) := FLT.SiegelSetCover.finite_quotient_gamma0 N
  exact volume_gammaFundamentalSet_eq_ofReal (Gamma0 N) (neg_one_mem_Gamma0_all N)

/--
@isnad1 id=eq.0h0v.s7.cc7f7c1c827e from=translated src=- shape=f9cdd9f4 vocab=69fb18e4
-/
theorem gate_top_two_routes :
    volume (gammaFundamentalSet (⊤ : Subgroup SL(2, ℤ))) = ENNReal.ofReal (Real.pi / 3) := by
  haveI : Subsingleton (SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ))) :=
    QuotientGroup.subsingleton_quotient_top
  haveI : Finite (SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ))) := Finite.of_subsingleton
  rw [volume_gammaFundamentalSet_eq_ofReal ⊤ (Subgroup.mem_top _),
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩, one_smul]

/--
@isnad1 id=eq.0h0v.s7.cc7f7c1c827e from=translated src=- shape=f9cdd9f4 vocab=69fb18e4
-/
theorem gate_top_committed_route :
    volume (gammaFundamentalSet (⊤ : Subgroup SL(2, ℤ))) = ENNReal.ofReal (Real.pi / 3) := by
  rw [FLT.Gamma0FundamentalSet.gate_volume_top_eq]
  exact FLT.FundamentalDomainExactVolume.volume_fd_eq

/--
@isnad1 id=ne.0h0v.s6.328f3a29bb0b from=translated src=- shape=30713882 vocab=7dc45353
-/
theorem gate_count_load_bearing : (2 : ℕ) • volume 𝒟 ≠ (1 : ℕ) • volume 𝒟 := by
  rw [one_smul, two_nsmul]
  intro h
  exact FLT.FundamentalDomainVolume.volume_fd_pos.ne'
    ((ENNReal.add_right_inj FLT.FundamentalDomainVolume.volume_fd_lt_top.ne).mp
      (h.trans (add_zero _).symm))

/--
@isnad1 id=eq.0h0v.s5.336dfdc52be6 from=translated src=- shape=1ee3fad9 vocab=8d10a5fe
-/
theorem gate_compl_fdo_volume_top : volume ((Set.univ : Set ℍ) \ 𝒟ᵒ) = ⊤ := by
  by_contra h
  have hlt : volume ((Set.univ : Set ℍ) \ 𝒟ᵒ) < ⊤ := lt_top_iff_ne_top.mpr h
  have : volume (Set.univ : Set ℍ) < ⊤ := by
    calc volume (Set.univ : Set ℍ) = volume ((Set.univ \ 𝒟ᵒ) ∪ (𝒟ᵒ : Set ℍ)) := by
          rw [Set.sdiff_union_of_subset (Set.subset_univ _)]
      _ ≤ volume ((Set.univ : Set ℍ) \ 𝒟ᵒ) + volume (𝒟ᵒ : Set ℍ) := measure_union_le _ _
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hlt, lt_of_le_of_lt
          (measure_mono ModularGroup.fdo_subset_fd)
          FLT.FundamentalDomainVolume.volume_fd_lt_top⟩
  exact absurd FLT.HyperbolicMeasure.volume_univ_eq_top this.ne

/--
@isnad1 id=lt.0h1v.s5.58bc1256f7bb from=translated src=- shape=1584ff9e vocab=432b6d29
-/
theorem gate_no_regression_lt_top (N : ℕ) [NeZero N] :
    volume (gammaFundamentalSet (Gamma0 N)) < ⊤ := by
  haveI : Finite (SL(2, ℤ) ⧸ Gamma0 N) := FLT.SiegelSetCover.finite_quotient_gamma0 N
  rw [volume_gamma0_eq N, nsmul_eq_mul]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ENNReal.ofReal_lt_top

/--
@isnad1 id=and.0h1v.s8.562ac3bae492 from=translated src=- shape=69bd6b04 vocab=f4b83c3b
-/
theorem gate_rhs_ne_zero_ne_top (N : ℕ) [NeZero N] :
    haveI : Finite (SL(2, ℤ) ⧸ Gamma0 N) := FLT.SiegelSetCover.finite_quotient_gamma0 N
    (Nat.card (SL(2, ℤ) ⧸ Gamma0 N) • ENNReal.ofReal (Real.pi / 3) ≠ 0) ∧
      (Nat.card (SL(2, ℤ) ⧸ Gamma0 N) • ENNReal.ofReal (Real.pi / 3) ≠ ⊤) := by
  haveI : Finite (SL(2, ℤ) ⧸ Gamma0 N) := FLT.SiegelSetCover.finite_quotient_gamma0 N
  constructor
  · rw [← volume_gamma0_eq N]
    exact (FLT.Gamma0FundamentalSet.volume_gammaFundamentalSet_pos (Gamma0 N)).ne'
  · rw [← volume_gamma0_eq N]
    exact (gate_no_regression_lt_top N).ne

end FLT.Gamma0ExactVolume
