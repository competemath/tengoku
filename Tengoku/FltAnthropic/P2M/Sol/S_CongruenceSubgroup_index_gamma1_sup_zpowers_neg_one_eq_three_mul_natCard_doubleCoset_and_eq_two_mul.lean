import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CongruenceSubgroup_index_gamma1_sup_zpowers_neg_one_eq_three_mul_natCard_doubleCoset_and_eq_two_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CongruenceSubgroup_index_gamma1_sup_zpowers_neg_one_eq_three_mul_natCard_doubleCoset_and_eq_two_mul

set_option autoImplicit false

open scoped MatrixGroups

namespace DCCount

section General

variable {G : Type*} [Group G] (Γ K : Subgroup G)

noncomputable def dcMap :
    DoubleCoset.Quotient (Γ : Set G) (K : Set G) × K → _root_.Quotient (QuotientGroup.rightRel Γ) :=
  fun qk => Quotient.mk'' (qk.1.out * (qk.2 : G))

/--
@isnad1 id=eq.0h5v.s7.522082c1c803 from=translated src=- shape=dbe3843d vocab=d10e2dd6
-/
theorem dcMap_apply (q : DoubleCoset.Quotient (Γ : Set G) (K : Set G)) (k : K) :
    dcMap Γ K (q, k) = Quotient.mk'' (q.out * (k : G)) := rfl

/--
@isnad1 id=surjecti.0h3v.s6.325441c58527 from=translated src=- shape=5b1c8198 vocab=75ef8ca2
-/
theorem dcMap_surjective : Function.Surjective (dcMap Γ K) := by
  intro x
  refine Quotient.inductionOn' x (fun g => ?_)
  obtain ⟨h, k, hh, hk, he⟩ := DoubleCoset.mk_out_eq_mul Γ K g
  refine ⟨(DoubleCoset.mk Γ K g, ⟨k⁻¹, K.inv_mem hk⟩), ?_⟩
  rw [dcMap_apply]
  refine Quotient.sound' (QuotientGroup.rightRel_apply.mpr ?_)
  rw [he]
  have : g * (h * g * k * k⁻¹)⁻¹ = h⁻¹ := by group
  rw [this]
  exact Γ.inv_mem hh

/--
@isnad1 id=injectiv.1h3v.s7.ba21a583f7f1 from=translated src=- shape=c9ab2fcb vocab=b5354056
-/
theorem dcMap_injective (hfree : ∀ g : G, ∀ k ∈ K, g * k * g⁻¹ ∈ Γ → k = 1) :
    Function.Injective (dcMap Γ K) := by
  rintro ⟨q₁, k₁⟩ ⟨q₂, k₂⟩ h
  rw [dcMap_apply, dcMap_apply] at h
  have h' : (q₂.out * (k₂ : G)) * (q₁.out * (k₁ : G))⁻¹ ∈ Γ :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact' h)
  have hq : DoubleCoset.mk Γ K q₁.out = DoubleCoset.mk Γ K q₂.out :=
    (DoubleCoset.eq Γ K _ _).2 ⟨(q₂.out * (k₂ : G)) * (q₁.out * (k₁ : G))⁻¹, h', (k₁ : G) * (k₂ : G)⁻¹,
      K.mul_mem k₁.2 (K.inv_mem k₂.2), by group⟩
  rw [DoubleCoset.out_eq', DoubleCoset.out_eq'] at hq
  subst hq
  have h'' : q₁.out * ((k₂ : G) * (k₁ : G)⁻¹) * q₁.out⁻¹ ∈ Γ := by
    simpa only [mul_inv_rev, mul_assoc] using h'
  have hk : (k₂ : G) * (k₁ : G)⁻¹ = 1 := hfree q₁.out _ (K.mul_mem k₂.2 (K.inv_mem k₁.2)) h''
  rw [mul_inv_eq_one] at hk
  rw [Subtype.ext hk]

/--
@isnad1 id=eq.1h3v.s7.6c57a99bd936 from=translated src=- shape=e3bf38d6 vocab=9ec81bd5
-/
theorem index_eq_natCard_doubleCoset_mul (hfree : ∀ g : G, ∀ k ∈ K, g * k * g⁻¹ ∈ Γ → k = 1) :
    Γ.index = Nat.card (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) * Nat.card K :=
  calc Γ.index = Nat.card (G ⧸ Γ) := rfl
    _ = Nat.card (_root_.Quotient (QuotientGroup.rightRel Γ)) :=
        Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ).symm
    _ = Nat.card (DoubleCoset.Quotient (Γ : Set G) (K : Set G) × K) :=
        Nat.card_congr (Equiv.ofBijective (dcMap Γ K)
          ⟨dcMap_injective Γ K hfree, dcMap_surjective Γ K⟩).symm
    _ = _ := Nat.card_prod _ _

/--
@isnad1 id=ex.3h4v.s6.87c844fc738b from=translated src=- shape=006a53dc vocab=ef190579
-/
theorem exists_pow_eq_of_mem_zpowers {x y : G} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1)
    (hy : y ∈ Subgroup.zpowers x) : ∃ r : ℕ, r < m ∧ x ^ r = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h0 : 0 ≤ k % (m : ℤ) := Int.emod_nonneg k (by exact_mod_cast hm.ne')
  have h1 : k % (m : ℤ) < m := Int.emod_lt_of_pos k (by exact_mod_cast hm)
  refine ⟨(k % (m : ℤ)).toNat, by omega, ?_⟩
  rw [zpow_eq_zpow_emod' k hx, ← zpow_natCast, Int.toNat_of_nonneg h0]

end General

open Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup

/--
@isnad1 id=eq.0h2v.s8.de0755c6e285 from=translated src=- shape=5b1ea536 vocab=ff003392
-/
theorem trace_conj (g k : SL(2, ℤ)) :
    Matrix.trace ((g * k * g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      Matrix.trace (k : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [mul_assoc, coe_mul, Matrix.trace_mul_comm, ← coe_mul, mul_assoc, inv_mul_cancel, mul_one]

/--
@isnad1 id=eq.1h2v.s8.5869adec541d from=translated src=- shape=d2a60c93 vocab=6faf1166
-/
theorem trace_mod_of_mem_Gamma1 {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) :
    ((Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℤ) : ℤ) : ZMod M) = 2 := by
  rw [Gamma1_mem] at hγ
  rw [Matrix.trace_fin_two, Int.cast_add, hγ.1, hγ.2.1]
  norm_num

/--
@isnad1 id=not.3h3v.s8.1ac8287cf261 from=translated src=- shape=ca8a012e vocab=c91be2a9
-/
theorem not_mem_Gamma1_of_trace {M : ℕ} (hM : 5 ≤ M) {γ : SL(2, ℤ)} (t : ℤ)
    (ht : Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℤ) = t) (ht' : t = 0 ∨ t = 1 ∨ t = -1 ∨ t = -2) :
    γ ∉ Gamma1 M := by
  intro hγ
  have h := trace_mod_of_mem_Gamma1 hγ
  rw [ht, show (2 : ZMod M) = ((2 : ℤ) : ZMod M) by norm_num, ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have hpos : (0 : ℤ) < 2 - t := by rcases ht' with rfl | rfl | rfl | rfl <;> norm_num
  have hle := Int.le_of_dvd hpos h
  have hM' : (5 : ℤ) ≤ M := by exact_mod_cast hM
  rcases ht' with rfl | rfl | rfl | rfl <;> omega

/--
@isnad1 id=not.1h1v.s8.b5368c719a65 from=translated src=- shape=225021a0 vocab=8c8c9eb3
-/
theorem neg_one_not_mem_Gamma1 {M : ℕ} (hM : 5 ≤ M) : (-1 : SL(2, ℤ)) ∉ Gamma1 M :=
  not_mem_Gamma1_of_trace hM (-2)
    (by rw [coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.trace_neg, Matrix.trace_one, Fintype.card_fin]; norm_num)
    (by norm_num)

/--
@isnad1 id=eq.0h0v.s8.44beaf9a967c from=translated src=- shape=323e5004 vocab=d7d6fd83
-/
theorem S_sq : ModularGroup.S ^ 2 = (-1 : SL(2, ℤ)) :=
  Subtype.ext (by rw [coe_pow, pow_two, S_mul_S_eq, coe_neg, Matrix.SpecialLinearGroup.coe_one])

/--
@isnad1 id=eq.0h0v.s7.788b3cb52685 from=translated src=- shape=be816c72 vocab=dfc9fd34
-/
theorem S_pow_four : ModularGroup.S ^ 4 = (1 : SL(2, ℤ)) := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, S_sq, neg_one_sq]

/--
@isnad1 id=eq.0h0v.s8.82e717330943 from=translated src=- shape=405f5f4c vocab=24c3c1a5
-/
theorem coe_ST : ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
    !![0, -1; 1, 1] := by
  rw [coe_mul, coe_S, coe_T, Matrix.mul_fin_two]
  norm_num

/--
@isnad1 id=eq.0h0v.s9.8b4a2b75de3e from=translated src=- shape=3c7ce8ad vocab=7bd1ffd8
-/
theorem coe_ST_sq : (((ModularGroup.S * ModularGroup.T) ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
    !![-1, -1; 1, 0] := by
  rw [coe_pow, coe_ST, pow_two, Matrix.mul_fin_two]
  norm_num

/--
@isnad1 id=eq.0h0v.s8.0d563df832ed from=translated src=- shape=abdbf034 vocab=2328d14f
-/
theorem ST_pow_three : (ModularGroup.S * ModularGroup.T) ^ 3 = (-1 : SL(2, ℤ)) := by
  apply Subtype.ext
  rw [pow_succ, coe_mul, coe_ST_sq, coe_ST, coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/--
@isnad1 id=eq.0h0v.s8.f26f42acbc01 from=translated src=- shape=5cc1983f vocab=9a2d3578
-/
theorem ST_pow_six : (ModularGroup.S * ModularGroup.T) ^ 6 = (1 : SL(2, ℤ)) := by
  rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, ST_pow_three, neg_one_sq]

/--
@isnad1 id=iff.0h1v.s9.de82b1350b71 from=translated src=- shape=9ab80b74 vocab=10f8d285
-/
theorem mem_zpowers_neg_one_iff {x : SL(2, ℤ)} :
    x ∈ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro hx
    obtain ⟨r, hr, rfl⟩ := exists_pow_eq_of_mem_zpowers (m := 2) (by norm_num) neg_one_sq hx
    interval_cases r
    · exact Or.inl (pow_zero _)
    · exact Or.inr (pow_one _)
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

/--
@isnad1 id=normal.0h0v.s7.0e0371bc12d3 from=translated src=- shape=20adafaa vocab=67149b4c
-/
theorem zpowers_neg_one_normal : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal :=
  ⟨fun n hn g => by
    rw [mem_zpowers_neg_one_iff] at hn
    rw [mem_zpowers_neg_one_iff]
    rcases hn with rfl | rfl
    · exact Or.inl (by group)
    · exact Or.inr (by rw [mul_neg_one, neg_mul, mul_inv_cancel])⟩

/--
@isnad1 id=eq.1h1v.s8.04710c0deae8 from=translated src=- shape=6b944e59 vocab=8abbc1d9
-/
theorem relIndex_Gamma1_sup {M : ℕ} (hM : 5 ≤ M) :
    (Gamma1 M).relIndex (Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) = 2 := by
  haveI := zpowers_neg_one_normal
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨-1, Subgroup.mem_sup_right (Subgroup.mem_zpowers _), fun b hb => ?_⟩
  rw [Subgroup.mem_sup_of_normal_right] at hb
  obtain ⟨γ, hγ, z, hz, rfl⟩ := hb
  rw [mem_zpowers_neg_one_iff] at hz
  rcases hz with rfl | rfl
  · refine Or.inr ⟨by rwa [mul_one], fun h => neg_one_not_mem_Gamma1 hM ?_⟩
    have := (Gamma1 M).mul_mem ((Gamma1 M).inv_mem hγ) h
    rwa [mul_one, inv_mul_cancel_left] at this
  · refine Or.inl ⟨by rwa [mul_neg_one, mul_neg_one, neg_neg], fun h => neg_one_not_mem_Gamma1 hM ?_⟩
    have := (Gamma1 M).mul_mem ((Gamma1 M).inv_mem hγ) h
    rwa [inv_mul_cancel_left] at this

/--
@isnad1 id=eq.1h1v.s9.0742c6b4b977 from=translated src=- shape=eb57d881 vocab=d8b3839a
-/
theorem index_Gamma1_eq {M : ℕ} (hM : 5 ≤ M) :
    (Gamma1 M).index = 2 * (Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  have h := Subgroup.relIndex_mul_index (H := Gamma1 M)
    (K := Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) le_sup_left
  rw [relIndex_Gamma1_sup hM] at h
  exact h.symm

/--
@isnad1 id=eq.3h3v.s9.ce9cd1cd8191 from=translated src=- shape=47d87715 vocab=aa4e822e
-/
theorem free_S {M : ℕ} (hM : 5 ≤ M) (g : SL(2, ℤ)) (k : SL(2, ℤ))
    (hk : k ∈ Subgroup.zpowers ModularGroup.S) (hmem : g * k * g⁻¹ ∈ Gamma1 M) : k = 1 := by
  obtain ⟨r, hr, rfl⟩ := exists_pow_eq_of_mem_zpowers (m := 4) (by norm_num) S_pow_four hk
  interval_cases r
  · exact pow_zero _
  · exact absurd hmem (not_mem_Gamma1_of_trace hM 0
      (by rw [trace_conj, pow_one, coe_S, Matrix.trace_fin_two_of]; norm_num) (by norm_num))
  · exact absurd hmem (not_mem_Gamma1_of_trace hM (-2)
      (by rw [trace_conj, S_sq, coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.trace_neg, Matrix.trace_one, Fintype.card_fin]
          norm_num) (by norm_num))
  · exact absurd hmem (not_mem_Gamma1_of_trace hM 0
      (by rw [trace_conj, pow_succ, S_sq, neg_one_mul, coe_neg, Matrix.trace_neg, coe_S,
            Matrix.trace_fin_two_of]; norm_num) (by norm_num))

/--
@isnad1 id=eq.3h3v.s9.87db59039b3d from=translated src=- shape=faf916a6 vocab=c5dbac1f
-/
theorem free_ST {M : ℕ} (hM : 5 ≤ M) (g : SL(2, ℤ)) (k : SL(2, ℤ))
    (hk : k ∈ Subgroup.zpowers (ModularGroup.S * ModularGroup.T)) (hmem : g * k * g⁻¹ ∈ Gamma1 M) :
    k = 1 := by
  obtain ⟨r, hr, rfl⟩ := exists_pow_eq_of_mem_zpowers (m := 6) (by norm_num) ST_pow_six hk
  interval_cases r
  · exact pow_zero _
  · exact absurd hmem (not_mem_Gamma1_of_trace hM 1
      (by rw [trace_conj, pow_one, coe_ST, Matrix.trace_fin_two_of]; norm_num) (by norm_num))
  · exact absurd hmem (not_mem_Gamma1_of_trace hM (-1)
      (by rw [trace_conj, coe_ST_sq, Matrix.trace_fin_two_of]; norm_num) (by norm_num))
  · exact absurd hmem (not_mem_Gamma1_of_trace hM (-2)
      (by rw [trace_conj, ST_pow_three, coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.trace_neg, Matrix.trace_one,
            Fintype.card_fin]; norm_num) (by norm_num))
  · exact absurd hmem (not_mem_Gamma1_of_trace hM (-1)
      (by rw [trace_conj, pow_succ, ST_pow_three, neg_one_mul, coe_neg, Matrix.trace_neg, coe_ST,
            Matrix.trace_fin_two_of]; norm_num) (by norm_num))
  · exact absurd hmem (not_mem_Gamma1_of_trace hM 1
      (by rw [trace_conj, show (5 : ℕ) = 3 + 2 from rfl, pow_add, ST_pow_three, neg_one_mul, coe_neg,
            Matrix.trace_neg, coe_ST_sq, Matrix.trace_fin_two_of]; norm_num) (by norm_num))

/--
@isnad1 id=eq.0h0v.s8.809bf447c2bf from=translated src=- shape=4b866bb0 vocab=09c54a7a
-/
theorem natCard_zpowers_S : Nat.card (Subgroup.zpowers ModularGroup.S) = 4 := by
  rw [Nat.card_zpowers]
  refine (orderOf_eq_iff (by norm_num)).2 ⟨S_pow_four, fun m hm hm0 h => ?_⟩
  interval_cases m
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    rw [pow_one, coe_S, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    rw [S_sq, coe_neg, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    rw [pow_succ, S_sq, neg_one_mul, coe_neg, coe_S, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'

/--
@isnad1 id=eq.0h0v.s8.53f4ff487554 from=translated src=- shape=bcdee477 vocab=8a76411d
-/
theorem natCard_zpowers_ST : Nat.card (Subgroup.zpowers (ModularGroup.S * ModularGroup.T)) = 6 := by
  rw [Nat.card_zpowers]
  refine (orderOf_eq_iff (by norm_num)).2 ⟨ST_pow_six, fun m hm hm0 h => ?_⟩
  interval_cases m
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    rw [pow_one, coe_ST, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1) h
    rw [coe_ST_sq, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    rw [ST_pow_three, coe_neg, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    rw [pow_succ, ST_pow_three, neg_one_mul, coe_neg, coe_ST, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1) h
    rw [show (5 : ℕ) = 3 + 2 from rfl, pow_add, ST_pow_three, neg_one_mul, coe_neg, coe_ST_sq, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'

end DCCount

open DCCount in
/--
@isnad1 id=and.1h1v.s10.dd76336be290 from=translated src=- shape=f5e087fb vocab=c672c921
-/
theorem solution
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) :
    (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
        3 * Nat.card (DoubleCoset.Quotient
          (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
          (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set SL(2, ℤ))) ∧
      (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
        2 * Nat.card (DoubleCoset.Quotient
          (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
          (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ))) := by
  have h2 := index_Gamma1_eq hM
  have hST := index_eq_natCard_doubleCoset_mul (CongruenceSubgroup.Gamma1 M)
    (Subgroup.zpowers (ModularGroup.S * ModularGroup.T)) (free_ST hM)
  have hS := index_eq_natCard_doubleCoset_mul (CongruenceSubgroup.Gamma1 M)
    (Subgroup.zpowers ModularGroup.S) (free_S hM)
  rw [natCard_zpowers_ST] at hST
  rw [natCard_zpowers_S] at hS
  constructor <;> omega
