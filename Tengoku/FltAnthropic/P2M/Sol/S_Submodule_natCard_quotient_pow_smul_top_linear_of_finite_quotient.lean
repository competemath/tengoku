import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Submodule_natCard_quotient_pow_smul_top_linear_of_finite_quotient.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Submodule_natCard_quotient_pow_smul_top_linear_of_finite_quotient

set_option autoImplicit false

namespace P2MHilbertSamuel

open Submodule

variable {R : Type*} [CommRing R] (I : Ideal R) (X : Type*) [AddCommGroup X] [Module R X]

abbrev F (m : ℕ) : Submodule R X := I ^ m • (⊤ : Submodule R X)

/--
@isnad1 id=eq.0h3v.s6.f349abdeed53 from=translated src=- shape=c526b4f1 vocab=ad426938
-/
theorem F_zero : F I X 0 = ⊤ := by
  show I ^ 0 • (⊤ : Submodule R X) = ⊤
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]

/--
@isnad1 id=eq.0h4v.s7.d6c5e2601972 from=translated src=- shape=1ef07ef3 vocab=ed768075
-/
theorem F_succ (m : ℕ) : F I X (m + 1) = I • F I X m := by
  show I ^ (m + 1) • (⊤ : Submodule R X) = I • (I ^ m • ⊤)
  rw [pow_succ', Submodule.mul_smul]

/--
@isnad1 id=antitone.0h3v.s6.285b8e51dd3b from=translated src=- shape=874b3736 vocab=847d2d26
-/
theorem F_antitone : Antitone (fun m => F I X m) := by
  intro m n hmn
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)

variable [IsNoetherianRing R] (q : ℕ) (hRq : Finite (R ⧸ Ideal.span {(q : R)})) (hqI : (q : R) ∈ I)
  [Module.Finite R X]

omit [IsNoetherianRing R] in
include hRq hqI in
/--
@isnad1 id=finite.2h3v.s6.614faa794ac4 from=translated src=- shape=786b3cdb vocab=1c530b59
-/
theorem finite_quotient_ideal : Finite (R ⧸ I) := by
  have hle : Ideal.span {(q : R)} ≤ I := by rw [Ideal.span_le]; simpa using hqI
  exact Finite.of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)

include hRq hqI in

/--
@isnad1 id=finite.2h5v.s7.59c0fe9f1c0b from=translated src=- shape=56f65840 vocab=14536a81
-/
theorem finite_quotient_F (m : ℕ) : Finite (X ⧸ F I X m) := by
  haveI : Finite (R ⧸ I) := finite_quotient_ideal I q hRq hqI
  induction m with
  | zero =>
    rw [F_zero]
    exact Finite.of_subsingleton
  | succ m ih =>
    rw [F_succ]
    haveI := ih
    exact Submodule.finite_quotient_smul I (IsNoetherian.noetherian _)

include hRq hqI in
/--
@isnad1 id=ne.2h5v.s7.855588b1f537 from=translated src=- shape=0cb3bca8 vocab=055d3800
-/
theorem index_F_ne_zero (m : ℕ) : (F I X m).toAddSubgroup.index ≠ 0 := by
  have hfin : Finite (X ⧸ (F I X m).toAddSubgroup) := finite_quotient_F I X q hRq hqI m
  rw [AddSubgroup.index_eq_card]
  exact Nat.card_pos.ne'

omit [IsNoetherianRing R] [Module.Finite R X] in

/--
@isnad1 id=eq.0h3v.s6.266414725985 from=translated src=- shape=cec25e64 vocab=306acb23
-/
theorem natCard_quotient_eq_index (N : Submodule R X) : Nat.card (X ⧸ N) = N.toAddSubgroup.index := by
  rw [AddSubgroup.index_eq_card]; rfl

omit [IsNoetherianRing R] [Module.Finite R X] in

/--
@isnad1 id=eq.0h4v.s7.3512db17aa5e from=translated src=- shape=9882d281 vocab=ec053eb7
-/
theorem index_F_succ (m : ℕ) :
    (F I X (m + 1)).toAddSubgroup.index
      = (F I X (m + 1)).toAddSubgroup.relIndex (F I X m).toAddSubgroup * (F I X m).toAddSubgroup.index := by
  rw [AddSubgroup.relIndex_mul_index]
  exact Submodule.toAddSubgroup_mono (F_antitone I X (Nat.le_succ m))

end P2MHilbertSamuel

namespace P2MHilbertSamuel

open Submodule

variable {R : Type*} [CommRing R] (I : Ideal R) (X : Type*) [AddCommGroup X] [Module R X]

abbrev K (n : ℕ) : AddSubgroup ↥(F I X n).toAddSubgroup :=
  (F I X (n + 1)).toAddSubgroup.addSubgroupOf (F I X n).toAddSubgroup

abbrev Mg (n : ℕ) : Type _ := ↥(F I X n).toAddSubgroup ⧸ K I X n

/--
@isnad1 id=eq.0h4v.s6.081c3ac08d5a from=translated src=- shape=a1ff9351 vocab=627c26bd
-/
theorem relIndex_eq_card (n : ℕ) :
    (F I X (n + 1)).toAddSubgroup.relIndex (F I X n).toAddSubgroup = Nat.card (Mg I X n) := by
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card]

variable (q : ℕ) (hqI : (q : R) ∈ I)

include hqI in

/--
@isnad1 id=eq.1h6v.s8.8614bd1eb91f from=translated src=- shape=93a17ddd vocab=0cc098e0
-/
theorem q_smul_eq_zero (n : ℕ) (y : Mg I X n) : q • y = 0 := by
  induction y using QuotientAddGroup.induction_on with
  | H x =>
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    show (q • x).1 ∈ (F I X (n + 1)).toAddSubgroup
    have hx : x.1 ∈ F I X n := x.2
    have : ((q : R) • x.1) ∈ F I X (n + 1) := by
      rw [F_succ]; exact Submodule.smul_mem_smul hqI hx
    simpa [Nat.cast_smul_eq_nsmul] using this

private noncomputable def _root_.P2MHilbertSamuel.zmodModule (n : ℕ) : Module (ZMod q) (Mg I X n) :=
  AddCommGroup.zmodModule (q_smul_eq_zero I X q hqI n)

export _root_.P2MHilbertSamuel (zmodModule)

noncomputable def d (n : ℕ) : ℕ :=
  letI := zmodModule I X q hqI n
  Module.finrank (ZMod q) (Mg I X n)

variable [Fact q.Prime] [IsNoetherianRing R] (hRq : Finite (R ⧸ Ideal.span {(q : R)})) [Module.Finite R X]

include hqI hRq in
/--
@isnad1 id=finite.2h5v.s7.352f424d12b7 from=translated src=- shape=4ff604e6 vocab=f94e4de9
-/
theorem finite_Mg (n : ℕ) : Finite (Mg I X n) := by
  have hfin : Finite (X ⧸ (F I X (n + 1)).toAddSubgroup) := finite_quotient_F I X q hRq hqI (n + 1)
  have hne : (F I X (n + 1)).toAddSubgroup.index ≠ 0 := index_F_ne_zero I X q hRq hqI (n + 1)
  rw [index_F_succ] at hne
  have hrel : (F I X (n + 1)).toAddSubgroup.relIndex (F I X n).toAddSubgroup ≠ 0 := fun h => hne (by rw [h, zero_mul])
  rw [relIndex_eq_card] at hrel
  exact Nat.finite_of_card_ne_zero hrel

include hqI hRq in

/--
@isnad1 id=eq.2h5v.s7.bb45e760e9d1 from=translated src=- shape=d7d3b37e vocab=bee4ffce
-/
theorem card_Mg (n : ℕ) : Nat.card (Mg I X n) = q ^ d I X q hqI n := by
  letI := zmodModule I X q hqI n
  haveI := finite_Mg I X q hqI hRq n
  haveI : Module.Finite (ZMod q) (Mg I X n) := Module.Finite.of_finite
  show Nat.card (Mg I X n) = q ^ Module.finrank (ZMod q) (Mg I X n)
  rw [Module.natCard_eq_pow_finrank (K := ZMod q) (V := Mg I X n), Nat.card_zmod]

include hqI hRq in

/--
@isnad1 id=eq.2h5v.s7.4ddaef27b111 from=translated src=- shape=7090e60c vocab=6c90b6f3
-/
theorem index_F_eq (m : ℕ) :
    (F I X m).toAddSubgroup.index = q ^ (∑ k ∈ Finset.range m, d I X q hqI k) := by
  induction m with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, pow_zero, F_zero]
    simp
  | succ m ih =>
    rw [index_F_succ, relIndex_eq_card, card_Mg I X q hqI hRq, ih, Finset.sum_range_succ, pow_add, mul_comm]

include hqI hRq in
/--
@isnad1 id=eq.2h5v.s7.b1550f928772 from=translated src=- shape=ace5c908 vocab=2c019f4a
-/
theorem natCard_quotient_F_eq (m : ℕ) :
    Nat.card (X ⧸ F I X m) = q ^ (∑ k ∈ Finset.range m, d I X q hqI k) := by
  rw [natCard_quotient_eq_index, index_F_eq I X q hqI hRq]

/--
@isnad1 id=ex.1h3v.s6.50546fab74a8 from=translated src=- shape=40da656b vocab=02f13830
-/
theorem sandwich_of_eventually_const (dd : ℕ → ℕ) (e n₀ : ℕ) (h : ∀ n, n₀ ≤ n → dd n = e) :
    ∃ C : ℕ, ∀ m : ℕ, (∑ k ∈ Finset.range m, dd k) ≤ m * e + C ∧ m * e ≤ (∑ k ∈ Finset.range m, dd k) + C := by
  refine ⟨(∑ k ∈ Finset.range n₀, dd k) + n₀ * e, fun m => ?_⟩
  rcases Nat.lt_or_ge m n₀ with hm | hm
  · constructor
    · calc (∑ k ∈ Finset.range m, dd k) ≤ ∑ k ∈ Finset.range n₀, dd k :=
            Finset.sum_le_sum_of_subset (Finset.range_mono hm.le)
        _ ≤ _ := by nlinarith
    · have := Nat.mul_le_mul_right e hm.le
      omega
  · have hsplit : (∑ k ∈ Finset.range m, dd k) = (∑ k ∈ Finset.range n₀, dd k) + (m - n₀) * e := by
      have : m = n₀ + (m - n₀) := by omega
      conv_lhs => rw [this, Finset.sum_range_add]
      congr 1
      rw [Finset.sum_congr rfl (fun k _ => h (n₀ + k) (Nat.le_add_right _ _)), Finset.sum_const, Finset.card_range,
        smul_eq_mul]
    rw [hsplit]
    constructor
    · nlinarith [Nat.sub_le m n₀]
    · have : (m - n₀) * e + n₀ * e = m * e := by rw [← Nat.add_mul, Nat.sub_add_cancel hm]
      set P := (m - n₀) * e
      set Q := n₀ * e
      set T := m * e
      omega

end P2MHilbertSamuel

namespace P2MHilbertSamuel

def Δ (g : ℕ → ℤ) : ℕ → ℤ := fun n => g (n + 1) - g n

/--
@isnad1 id=eq.0h2v.s5.ca0423a02d94 from=translated src=- shape=6f8ff08b vocab=a8d92232
-/
theorem Δ_apply (g : ℕ → ℤ) (n : ℕ) : Δ g n = g (n + 1) - g n := rfl

/--
@isnad1 id=eq.0h2v.s5.e6331796e5a0 from=translated src=- shape=a91df714 vocab=3e64e5f3
-/
theorem Δ_sub (g₁ g₂ : ℕ → ℤ) : Δ (g₁ - g₂) = Δ g₁ - Δ g₂ := by
  funext n; simp only [Δ, Pi.sub_apply]; ring

/--
@isnad1 id=eq.0h1v.s5.f53979e3871c from=translated src=- shape=ecf696ea vocab=5f18bac5
-/
theorem Δ_neg (g : ℕ → ℤ) : Δ (-g) = -Δ g := by
  funext n; simp only [Δ, Pi.neg_apply]; ring

/--
@isnad1 id=eq.0h3v.s6.1f10a1e812ff from=translated src=- shape=1ca4cc32 vocab=0d46d1ce
-/
theorem iterΔ_sub (k : ℕ) (g₁ g₂ : ℕ → ℤ) : Δ^[k] (g₁ - g₂) = Δ^[k] g₁ - Δ^[k] g₂ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      Δ_sub]

/--
@isnad1 id=eq.0h2v.s5.ce3dd279ff3f from=translated src=- shape=79187880 vocab=1fb0cf7c
-/
theorem iterΔ_neg (k : ℕ) (g : ℕ → ℤ) : Δ^[k] (-g) = -Δ^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Δ_neg]

/--
@isnad1 id=le.1h3v.s5.33dce8d090de from=translated src=- shape=5d683742 vocab=dcd34835
-/
theorem le_of_one_le_Δ (g : ℕ → ℤ) (N : ℕ) (h : ∀ n, N ≤ n → 1 ≤ Δ g n) (k : ℕ) :
    g N + k ≤ g (N + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h (N + k) (Nat.le_add_right N k)
    rw [Δ_apply] at hk
    have e : N + (k + 1) = N + k + 1 := rfl
    rw [e]; push_cast; linarith

/--
@isnad1 id=ex.1h2v.s5.cc609d82acca from=translated src=- shape=d6e1973a vocab=a33a793c
-/
theorem eventually_le_of_one_le_Δ (g : ℕ → ℤ) (hg : ∃ N, ∀ n, N ≤ n → 1 ≤ Δ g n) (B : ℤ) :
    ∃ N, ∀ n, N ≤ n → B ≤ g n := by
  obtain ⟨N, hN⟩ := hg
  refine ⟨N + (B - g N).toNat, fun n hn => ?_⟩
  have key := le_of_one_le_Δ g N hN (n - N)
  have hnN : N + (n - N) = n := by omega
  rw [hnN] at key
  have h1 : B - g N ≤ ((B - g N).toNat : ℤ) := Int.self_le_toNat _
  have h2 : ((B - g N).toNat : ℤ) ≤ ((n - N : ℕ) : ℤ) := by
    exact_mod_cast (show (B - g N).toNat ≤ n - N by omega)
  linarith

/--
@isnad1 id=ex.1h2v.s6.32558b295906 from=translated src=- shape=47ce6c0c vocab=aa825e38
-/
theorem eventually_one_le_Δ_of_iter (g : ℕ → ℤ) (j : ℕ)
    (h : ∃ N, ∀ n, N ≤ n → 1 ≤ Δ^[j + 1] g n) : ∃ N, ∀ n, N ≤ n → 1 ≤ Δ g n := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    apply ih
    have h' : ∃ N, ∀ n, N ≤ n → 1 ≤ Δ (Δ^[j + 1] g) n := by
      simpa only [Function.iterate_succ_apply'] using h
    exact eventually_le_of_one_le_Δ _ h' 1

/--
@isnad1 id=ex.1h1v.s5.d8dcf1be0b7a from=translated src=- shape=e4cf51cb vocab=a33a793c
-/
theorem eventually_const_of_Δ_eq_zero (g : ℕ → ℤ) (h : ∃ N, ∀ n, N ≤ n → Δ g n = 0) :
    ∃ c : ℤ, ∃ N : ℕ, ∀ n, N ≤ n → g n = c := by
  obtain ⟨N, hN⟩ := h
  refine ⟨g N, N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := hN (N + k) (Nat.le_add_right N k)
    rw [Δ_apply] at hk
    have e : N + (k + 1) = N + k + 1 := rfl
    rw [e]; linarith [ih]

/--
@isnad1 id=ex.3h3v.s6.48f243520533 from=translated src=- shape=0004bde3 vocab=cbfe64e5
-/
theorem eventually_const_of_iterΔ_eq_zero (h : ℕ → ℤ) (c : ℕ) (h0 : ∀ n, 0 ≤ h n)
    (hsum : ∀ m : ℕ, (∑ k ∈ Finset.range m, h k) ≤ c * m)
    (s : ℕ) (hs : ∃ N, ∀ n, N ≤ n → Δ^[s] h n = 0) :
    ∃ e : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → h n = e := by

  have noGrow : ¬ ∃ N, ∀ n, N ≤ n → 1 ≤ Δ h n := by
    intro hg
    obtain ⟨M, hM⟩ := eventually_le_of_one_le_Δ h hg (2 * c + 1)
    have hM1 : ∀ n, M + 1 ≤ n → (2 * c + 1 : ℤ) ≤ h n := fun n hn => hM n (by omega)
    have hs2 := hsum ((M + 1) + (M + 1))
    rw [Finset.sum_range_add] at hs2
    have hA : 0 ≤ ∑ k ∈ Finset.range (M + 1), h k := Finset.sum_nonneg fun k _ => h0 k
    have hB : ((M + 1 : ℕ) : ℤ) * (2 * c + 1) ≤ ∑ k ∈ Finset.range (M + 1), h ((M + 1) + k) := by
      have := Finset.card_nsmul_le_sum (Finset.range (M + 1)) (fun k => h ((M + 1) + k)) (2 * c + 1)
        (fun k _ => hM1 ((M + 1) + k) (Nat.le_add_right _ _))
      simpa [Finset.card_range, nsmul_eq_mul] using this
    push_cast at hs2 hB
    nlinarith

  have noGrowNeg : ¬ ∃ N, ∀ n, N ≤ n → 1 ≤ Δ (-h) n := by
    intro hg
    obtain ⟨M, hM⟩ := eventually_le_of_one_le_Δ (-h) hg 1
    have h1 := hM M le_rfl
    simp only [Pi.neg_apply] at h1
    linarith [h0 M]

  have Q : ∀ k, (∃ N, ∀ n, N ≤ n → Δ^[k + 1] h n = 0) → ∃ N, ∀ n, N ≤ n → Δ h n = 0 := by
    intro k
    induction k with
    | zero => intro hk; simpa using hk
    | succ k ih =>
      intro hk
      have hk' : ∃ N, ∀ n, N ≤ n → Δ (Δ^[k + 1] h) n = 0 := by
        simpa only [Function.iterate_succ_apply'] using hk
      obtain ⟨cst, N, hN⟩ := eventually_const_of_Δ_eq_zero _ hk'
      rcases lt_trichotomy cst 0 with hneg | hzero | hpos
      · exact absurd (eventually_one_le_Δ_of_iter (-h) k
          ⟨N, fun n hn => by rw [iterΔ_neg, Pi.neg_apply, hN n hn]; omega⟩) noGrowNeg
      · exact ih ⟨N, fun n hn => by rw [hN n hn, hzero]⟩
      · exact absurd (eventually_one_le_Δ_of_iter h k ⟨N, fun n hn => by rw [hN n hn]; omega⟩) noGrow

  have hΔ : ∃ N, ∀ n, N ≤ n → Δ h n = 0 := by
    cases s with
    | zero =>
      obtain ⟨N, hN⟩ := hs
      refine ⟨N, fun n hn => ?_⟩
      have a := hN n hn
      have b := hN (n + 1) (by omega)
      simp only [Function.iterate_zero, id] at a b
      rw [Δ_apply, a, b]; rfl
    | succ k => exact Q k hs
  obtain ⟨cst, N, hN⟩ := eventually_const_of_Δ_eq_zero h hΔ
  refine ⟨cst.toNat, N, fun n hn => ?_⟩
  rw [hN n hn, Int.toNat_of_nonneg]
  rw [← hN N le_rfl]; exact h0 N

end P2MHilbertSamuel

namespace P2MHilbertSamuel

open Submodule

universe u

noncomputable def lc (q : ℕ) (V : Type*) : ℤ := (Nat.log q (Nat.card V) : ℤ)

/--
@isnad1 id=eq.2h3v.s5.55d3d3606b6c from=translated src=- shape=542cee2f vocab=dbe6c6b9
-/
theorem lc_eq {q : ℕ} (hq : 1 < q) {V : Type*} {k : ℕ} (h : Nat.card V = q ^ k) : lc q V = k := by
  simp [lc, h, Nat.log_pow hq]

/--
@isnad1 id=and.3h4v.s6.ea4ef273d73f from=translated src=- shape=bd107a68 vocab=c4451730
-/
theorem lc_of_card_mul {q : ℕ} (hq : q.Prime) {M A B : Type*} (hM : ∃ k, Nat.card M = q ^ k)
    (h : Nat.card M = Nat.card A * Nat.card B) :
    (∃ k, Nat.card A = q ^ k) ∧ (∃ k, Nat.card B = q ^ k) ∧ lc q M = lc q A + lc q B := by
  obtain ⟨k, hk⟩ := hM
  have hA : Nat.card A ∣ q ^ k := ⟨Nat.card B, by rw [← hk, h]⟩
  have hB : Nat.card B ∣ q ^ k := ⟨Nat.card A, by rw [← hk, h, mul_comm]⟩
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hq).1 hA
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hq).1 hB
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
  have hab : q ^ k = q ^ (a + b) := by rw [pow_add, ← ha, ← hb, ← h, hk]
  have := Nat.pow_right_injective hq.two_le hab
  rw [lc_eq hq.one_lt hk, lc_eq hq.one_lt ha, lc_eq hq.one_lt hb, this]; push_cast; rfl

def consFam {A : Type*} [CommRing A] (V : ℕ → Type u) [∀ n, AddCommGroup (V n)] [∀ n, Module A (V n)]
    (W₀ : Submodule A (V 0)) (W : ∀ m, Submodule A (V (m + 1))) : ∀ n, Submodule A (V n)
  | 0 => W₀
  | m + 1 => W m

/--
@isnad1 id=ex.4h5v.s11.642eaaa81f84 from=translated src=- shape=8cdd6618 vocab=dd240edd
-/
theorem hilbertSerre (A : Type*) [CommRing A] (q : ℕ) (hq : q.Prime) (s : ℕ) :
    ∀ (V : ℕ → Type u) [∀ n, AddCommGroup (V n)] [∀ n, Module A (V n)] [∀ n, Finite (V n)]
      (f : Fin s → ∀ n, V n →ₗ[A] V (n + 1)),
      (∀ n, ∃ k, Nat.card (V n) = q ^ k) →
      (∀ i j n (x : V n), f i (n + 1) (f j n x) = f j (n + 1) (f i n x)) →
      (∀ W : ∀ n, Submodule A (V n), (∀ i n, (W n).map (f i n) ≤ W (n + 1)) →
          ∃ n₁, ∀ n, n₁ ≤ n → W (n + 1) ≤ ⨆ i, (W n).map (f i n)) →
      ∃ N, ∀ n, N ≤ n → Δ^[s] (fun n => lc q (V n)) n = 0 := by
  induction s with
  | zero =>
    intro V _ _ _ f hcard hcomm hnoeth
    obtain ⟨n₁, h₁⟩ := hnoeth (fun n => ⊤) (fun i => i.elim0)
    refine ⟨n₁ + 1, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have htop : (⊤ : Submodule A (V (m + 1))) ≤ ⊥ := by
      have := h₁ m (by omega)
      rwa [iSup_of_empty] at this
    have hsub : Subsingleton (V (m + 1)) := ⟨fun x y => by
      have hx : x ∈ (⊥ : Submodule A (V (m + 1))) := htop Submodule.mem_top
      have hy : y ∈ (⊥ : Submodule A (V (m + 1))) := htop Submodule.mem_top
      rw [Submodule.mem_bot] at hx hy
      rw [hx, hy]⟩
    have hc : Nat.card (V (m + 1)) = q ^ 0 := by
      rw [pow_zero]; exact Nat.card_of_subsingleton (0 : V (m + 1))
    simp only [Function.iterate_zero, id]
    rw [lc_eq hq.one_lt hc]; rfl
  | succ s ih =>
    intro V _ _ _ f hcard hcomm hnoeth

    let g : ∀ n, V n →ₗ[A] V (n + 1) := f (Fin.last s)
    let f' : Fin s → ∀ n, V n →ₗ[A] V (n + 1) := fun i => f i.castSucc
    have hcomm' : ∀ (i : Fin s) n (x : V n), g (n + 1) (f' i n x) = f' i (n + 1) (g n x) :=
      fun i n x => hcomm (Fin.last s) i.castSucc n x

    let K : ∀ n, Submodule A (V n) := fun n => LinearMap.ker (g n)
    have hKmap : ∀ (i : Fin s) n, ∀ x ∈ K n, f' i n x ∈ K (n + 1) := by
      intro i n x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hcomm', hx, map_zero]
    let fK : Fin s → ∀ n, K n →ₗ[A] K (n + 1) := fun i n => (f' i n).restrict (hKmap i n)

    let Rg : ∀ n, Submodule A (V (n + 1)) := fun n => LinearMap.range (g n)
    have hRmap : ∀ (i : Fin s) n, Rg n ≤ (Rg (n + 1)).comap (f' i (n + 1)) := by
      rintro i n _ ⟨x, rfl⟩
      exact ⟨f' i n x, hcomm' i n x⟩
    let fC : Fin s → ∀ n, (V (n + 1) ⧸ Rg n) →ₗ[A] (V (n + 2) ⧸ Rg (n + 1)) :=
      fun i n => Submodule.mapQ (Rg n) (Rg (n + 1)) (f' i (n + 1)) (hRmap i n)
    haveI : ∀ n, Finite (V (n + 1) ⧸ Rg n) := fun n =>
      Finite.of_surjective _ (Submodule.Quotient.mk_surjective (Rg n))

    have cardVK : ∀ n, Nat.card (V n) = Nat.card (Rg n) * Nat.card (K n) := fun n => by
      rw [Submodule.card_eq_card_quotient_mul_card (K n),
        Nat.card_congr (LinearMap.quotKerEquivRange (g n)).toEquiv, mul_comm]
    have cardVC : ∀ n, Nat.card (V (n + 1)) = Nat.card (Rg n) * Nat.card (V (n + 1) ⧸ Rg n) :=
      fun n => Submodule.card_eq_card_quotient_mul_card (Rg n)
    have factK := fun n => lc_of_card_mul hq (hcard n) (cardVK n)
    have factC := fun n => lc_of_card_mul hq (hcard (n + 1)) (cardVC n)

    have HK := ih (fun n => K n) fK (fun n => (factK n).2.1)
      (fun i j n x => by ext; exact hcomm i.castSucc j.castSucc n x) (by
        intro W hW
        let W' : ∀ n, Submodule A (V n) := fun n => (W n).map (K n).subtype
        have hW' : ∀ i n, (W' n).map (f i n) ≤ W' (n + 1) := by
          intro i n
          induction i using Fin.lastCases with
          | last =>
            rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
            have h0 : f (Fin.last s) n ((K n).subtype x) = 0 := LinearMap.mem_ker.1 x.2
            rw [h0]; exact zero_mem _
          | cast j =>
            rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
            exact ⟨fK j n x, hW j n ⟨x, hx, rfl⟩, rfl⟩
        obtain ⟨n₁, h₁⟩ := hnoeth W' hW'
        refine ⟨n₁, fun n hn => ?_⟩
        intro x hx
        have hx' : (x : V (n + 1)) ∈ W' (n + 1) := ⟨x, hx, rfl⟩
        have step := h₁ n hn hx'
        have hle : (⨆ i, (W' n).map (f i n)) ≤ (⨆ j, (W n).map (fK j n)).map (K (n + 1)).subtype := by
          refine iSup_le fun i => ?_
          induction i using Fin.lastCases with
          | last =>
            rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
            have h0 : f (Fin.last s) n ((K n).subtype x) = 0 := LinearMap.mem_ker.1 x.2
            rw [h0]; exact zero_mem _
          | cast j =>
            rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
            exact ⟨fK j n x, Submodule.mem_iSup_of_mem j ⟨x, hx, rfl⟩, rfl⟩
        obtain ⟨y, hy, hyx⟩ := hle step
        have : y = x := Subtype.ext hyx
        rw [← this]; exact hy)

    have HC := ih (fun n => V (n + 1) ⧸ Rg n) fC (fun n => (factC n).2.1)
      (fun i j n x => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        exact congrArg Submodule.Quotient.mk (hcomm i.castSucc j.castSucc (n + 1) x)) (by
        intro W hW
        let W' : ∀ n, Submodule A (V n) := consFam V ⊥ (fun m => (W m).comap (Rg m).mkQ)
        have W'_zero : W' 0 = ⊥ := rfl
        have W'_succ : ∀ m, W' (m + 1) = (W m).comap (Rg m).mkQ := fun m => rfl
        have hW' : ∀ i n, (W' n).map (f i n) ≤ W' (n + 1) := by
          intro i n
          cases n with
          | zero => rw [W'_zero, Submodule.map_bot]; exact bot_le
          | succ m =>
            rw [W'_succ, W'_succ, Submodule.map_le_iff_le_comap]
            intro x hx
            simp only [Submodule.mem_comap, Submodule.mkQ_apply] at hx ⊢
            induction i using Fin.lastCases with
            | last =>
              have h0 : (Submodule.Quotient.mk (f (Fin.last s) (m + 1) x) : V (m + 2) ⧸ Rg (m + 1)) = 0 :=
                (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
              rw [h0]; exact zero_mem _
            | cast j => exact hW j m ⟨Submodule.Quotient.mk x, hx, rfl⟩
        obtain ⟨n₁, h₁⟩ := hnoeth W' hW'
        refine ⟨n₁, fun n hn => ?_⟩
        intro c hc
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
        have hx : x ∈ W' (n + 2) := by rw [W'_succ]; exact hc
        have step := h₁ (n + 1) (by omega) hx
        have hle : (⨆ i, (W' (n + 1)).map (f i (n + 1)))
            ≤ (⨆ j, (W n).map (fC j n)).comap (Rg (n + 1)).mkQ := by
          refine iSup_le fun i => ?_
          rw [Submodule.map_le_iff_le_comap]
          intro y hy
          rw [W'_succ] at hy
          simp only [Submodule.mem_comap, Submodule.mkQ_apply] at hy ⊢
          induction i using Fin.lastCases with
          | last =>
            have h0 : (Submodule.Quotient.mk (f (Fin.last s) (n + 1) y) : V (n + 2) ⧸ Rg (n + 1)) = 0 :=
              (Submodule.Quotient.mk_eq_zero _).2 ⟨y, rfl⟩
            rw [h0]; exact zero_mem _
          | cast j => exact Submodule.mem_iSup_of_mem j ⟨Submodule.Quotient.mk y, hy, rfl⟩
        exact hle step)

    obtain ⟨NK, hNK⟩ := HK
    obtain ⟨NC, hNC⟩ := HC
    refine ⟨max NK NC, fun n hn => ?_⟩
    have hΔ : Δ (fun n => lc q (V n)) = (fun n => lc q (V (n + 1) ⧸ Rg n)) - (fun n => lc q (K n)) := by
      funext n
      simp only [Δ, Pi.sub_apply]
      rw [(factK n).2.2, (factC n).2.2]; ring
    rw [Function.iterate_succ_apply, hΔ, iterΔ_sub, Pi.sub_apply, hNC n (le_of_max_le_right hn),
      hNK n (le_of_max_le_left hn), sub_self]

end P2MHilbertSamuel

namespace P2MHilbertSamuel

open Submodule Pointwise

universe u v

variable {R : Type u} [CommRing R] (I : Ideal R) (X : Type v) [AddCommGroup X] [Module R X]

abbrev Fsub (n : ℕ) : Submodule R ↥(F I X n) := (F I X (n + 1)).comap (F I X n).subtype

abbrev Gr (n : ℕ) : Type v := ↥(F I X n) ⧸ Fsub I X n

def mulF {x : R} (hx : x ∈ I) (n : ℕ) : ↥(F I X n) →ₗ[R] ↥(F I X (n + 1)) :=
  (LinearMap.lsmul R X x).restrict fun y hy => by
    rw [F_succ]; exact Submodule.smul_mem_smul hx hy

/--
@isnad1 id=eq.1h6v.s9.2efc770999a6 from=translated src=- shape=cfe0c4f5 vocab=cb6534e5
-/
theorem mulF_coe {x : R} (hx : x ∈ I) (n : ℕ) (y : ↥(F I X n)) :
    ((mulF I X hx n y : ↥(F I X (n + 1))) : X) = x • (y : X) := rfl

def grMul {x : R} (hx : x ∈ I) (n : ℕ) : Gr I X n →ₗ[R] Gr I X (n + 1) :=
  (Fsub I X n).mapQ (Fsub I X (n + 1)) (mulF I X hx n) fun y hy => by
    change ((mulF I X hx n y : ↥(F I X (n + 1))) : X) ∈ F I X (n + 1 + 1)
    rw [mulF_coe, F_succ]
    exact Submodule.smul_mem_smul hx hy

/--
@isnad1 id=eq.1h6v.s11.7bdf5abef9f9 from=translated src=- shape=0dd2666b vocab=4ef09e2f
-/
theorem grMul_mk {x : R} (hx : x ∈ I) (n : ℕ) (y : ↥(F I X n)) :
    grMul I X hx n (Submodule.Quotient.mk y) = Submodule.Quotient.mk (mulF I X hx n y) := rfl

/--
@isnad1 id=eq.2h7v.s12.8eaf38644d7f from=translated src=- shape=a9ae9516 vocab=88f8f921
-/
theorem grMul_comm {x y : R} (hx : x ∈ I) (hy : y ∈ I) (n : ℕ) (z : Gr I X n) :
    grMul I X hx (n + 1) (grMul I X hy n z) = grMul I X hy (n + 1) (grMul I X hx n z) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  simp only [grMul_mk]
  congr 1
  apply Subtype.ext
  simp only [mulF_coe]
  exact smul_comm x y (z : X)

/--
@isnad1 id=eq.0h4v.s5.c65fd7a8ddb8 from=translated src=- shape=d41ef7bd vocab=dd530248
-/
theorem card_Gr_eq (n : ℕ) : Nat.card (Gr I X n) = Nat.card (Mg I X n) := rfl

/--
@isnad1 id=surjecti.0h4v.s10.2b05f80f65c2 from=translated src=- shape=32fa2152 vocab=30b2f052
-/
theorem grMul_surjective_principal (r : R) (n : ℕ) :
    Function.Surjective (grMul (Ideal.span {r}) X (Ideal.mem_span_singleton_self r) n) := by
  intro c
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  have hz : (z : X) ∈ r • F (Ideal.span {r}) X n := by
    rw [← Submodule.ideal_span_singleton_smul, ← F_succ]; exact z.2
  obtain ⟨w, hw, hwz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
  refine ⟨Submodule.Quotient.mk ⟨w, hw⟩, ?_⟩
  rw [grMul_mk]
  congr 1
  exact Subtype.ext hwz

def liftSub (n : ℕ) (W : Submodule R (Gr I X n)) : Submodule R X :=
  (W.comap (Fsub I X n).mkQ).map (F I X n).subtype

/--
@isnad1 id=iff.0h6v.s11.40a744e13b26 from=translated src=- shape=157beb59 vocab=e404eb75
-/
theorem mem_liftSub_iff (n : ℕ) (W : Submodule R (Gr I X n)) (z : ↥(F I X n)) :
    (z : X) ∈ liftSub I X n W ↔ (Fsub I X n).mkQ z ∈ W := by
  constructor
  · rintro ⟨z', hz', hzz⟩
    have : z' = z := Subtype.ext hzz
    rw [← this]; exact hz'
  · intro h; exact ⟨z, h, rfl⟩

/--
@isnad1 id=le.0h5v.s8.163abddb818b from=translated src=- shape=75d732cf vocab=59c0af73
-/
theorem liftSub_le (n : ℕ) (W : Submodule R (Gr I X n)) : liftSub I X n W ≤ F I X n := by
  rintro _ ⟨y, -, rfl⟩; exact y.2

/--
@isnad1 id=le.0h5v.s8.8082d99d2071 from=translated src=- shape=38d50eb4 vocab=bdbe8754
-/
theorem le_liftSub (n : ℕ) (W : Submodule R (Gr I X n)) : F I X (n + 1) ≤ liftSub I X n W := by
  intro z hz
  have hz' : z ∈ F I X n := F_antitone I X (Nat.le_succ n) hz
  have h0 : (Fsub I X n).mkQ ⟨z, hz'⟩ = 0 := (Submodule.Quotient.mk_eq_zero (Fsub I X n)).2 hz
  exact (mem_liftSub_iff I X n W ⟨z, hz'⟩).2 (by rw [h0]; exact zero_mem _)

/--
@isnad1 id=le.3h8v.s11.5e79fc288ec7 from=translated src=- shape=05ab09e1 vocab=878666d2
-/
theorem smul_liftSub_le {s : ℕ} (x : Fin s → R) (hxI : Ideal.span (Set.range x) = I) (hx : ∀ i, x i ∈ I)
    (n : ℕ) (W : Submodule R (Gr I X n)) (T : Submodule R (Gr I X (n + 1)))
    (h : ∀ i, W.map (grMul I X (hx i) n) ≤ T) : I • liftSub I X n W ≤ liftSub I X (n + 1) T := by
  rw [Submodule.smul_le]
  intro r hr m hm
  obtain ⟨y, hy, rfl⟩ := hm
  rw [← hxI] at hr
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hr
  · rintro _ ⟨i, rfl⟩
    refine ⟨mulF I X (hx i) n y, ?_, rfl⟩
    show (Fsub I X (n + 1)).mkQ (mulF I X (hx i) n y) ∈ T
    exact h i ⟨(Fsub I X n).mkQ y, hy, rfl⟩
  · rw [zero_smul]; exact zero_mem _
  · intro a b _ _ ha hb; rw [add_smul]; exact add_mem ha hb
  · intro a b _ hb; rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ a hb

/--
@isnad1 id=ex.3h6v.s12.98504c2c95bb from=translated src=- shape=a8d9cc3b vocab=f4a92b1f
-/
theorem noeth_Gr [IsNoetherianRing R] [Module.Finite R X] {s : ℕ} (x : Fin s → R)
    (hxI : Ideal.span (Set.range x) = I) (hx : ∀ i, x i ∈ I)
    (W : ∀ n, Submodule R (Gr I X n))
    (hW : ∀ i n, (W n).map (grMul I X (hx i) n) ≤ W (n + 1)) :
    ∃ n₁, ∀ n, n₁ ≤ n → W (n + 1) ≤ ⨆ i, (W n).map (grMul I X (hx i) n) := by
  let Nf : I.Filtration X :=
    ⟨fun n => liftSub I X n (W n), fun n => (liftSub_le I X (n + 1) (W (n + 1))).trans (le_liftSub I X n (W n)),
      fun n => smul_liftSub_le I X x hxI hx n (W n) (W (n + 1)) fun i => hW i n⟩
  have hle : Nf ≤ I.stableFiltration ⊤ := fun n => liftSub_le I X n (W n)
  obtain ⟨n₀, hn₀⟩ := (I.stableFiltration_stable ⊤).of_le hle
  refine ⟨n₀, fun n hn => ?_⟩
  intro c hc
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  have hz : (z : X) ∈ Nf.N (n + 1) := (mem_liftSub_iff I X (n + 1) (W (n + 1)) z).2 hc
  rw [← hn₀ n hn] at hz
  have hT := smul_liftSub_le I X x hxI hx n (W n) (⨆ i, (W n).map (grMul I X (hx i) n))
    (fun i => le_iSup (fun i => (W n).map (grMul I X (hx i) n)) i) hz
  exact (mem_liftSub_iff I X (n + 1) _ z).1 hT

section assembly

variable (q : ℕ) [Fact q.Prime] [IsNoetherianRing R] (hRq : Finite (R ⧸ Ideal.span {(q : R)}))
  (hqI : (q : R) ∈ I) [Module.Finite R X]

include hRq hqI in
/--
@isnad1 id=finite.2h5v.s7.9b912355c51c from=translated src=- shape=47f96f51 vocab=eba5848e
-/
theorem finite_Gr (n : ℕ) : Finite (Gr I X n) := by
  haveI : Finite (X ⧸ F I X (n + 1)) := finite_quotient_F I X q hRq hqI (n + 1)
  refine Finite.of_injective ((Fsub I X n).mapQ (F I X (n + 1)) (F I X n).subtype le_rfl) ?_
  intro a b h
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at h
  rw [Submodule.Quotient.eq]
  show ((a - b : ↥(F I X n)) : X) ∈ F I X (n + 1)
  simpa using h

include hRq in

/--
@isnad1 id=le.1h4v.s7.ac978ee55e4b from=translated src=- shape=bc0d47ab vocab=82369bdf
-/
theorem d_principal_le (k : ℕ) :
    d (Ideal.span {(q : R)}) X q (Ideal.mem_span_singleton_self _) k
      ≤ d (Ideal.span {(q : R)}) X q (Ideal.mem_span_singleton_self _) 0 := by
  set J : Ideal R := Ideal.span {(q : R)}
  have hqJ : (q : R) ∈ J := Ideal.mem_span_singleton_self _
  have hq : 1 < q := (Fact.out : q.Prime).one_lt
  have hcard : ∀ k, Nat.card (Gr J X k) ≤ Nat.card (Gr J X 0) := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      haveI := finite_Gr J X q hRq hqJ k
      exact (Nat.card_le_card_of_surjective _ (grMul_surjective_principal X (q : R) k)).trans ih
  have := hcard k
  rw [card_Gr_eq, card_Gr_eq, card_Mg J X q hqJ hRq, card_Mg J X q hqJ hRq] at this
  exact (Nat.pow_le_pow_iff_right hq).1 this

include hRq hqI in

/--
@isnad1 id=le.2h5v.s7.adbbad1f3904 from=translated src=- shape=23c43bb5 vocab=334becdf
-/
theorem sum_d_le (m : ℕ) :
    (∑ k ∈ Finset.range m, d I X q hqI k)
      ≤ m * d (Ideal.span {(q : R)}) X q (Ideal.mem_span_singleton_self _) 0 := by
  set J : Ideal R := Ideal.span {(q : R)}
  have hqJ : (q : R) ∈ J := Ideal.mem_span_singleton_self _
  have hq : 1 < q := (Fact.out : q.Prime).one_lt
  have hJI : J ≤ I := by rw [Ideal.span_le]; simpa using hqI

  have hle : F J X m ≤ F I X m := Submodule.smul_mono_left (Ideal.pow_right_mono hJI m)
  have hdvd : Nat.card (X ⧸ F I X m) ∣ Nat.card (X ⧸ F J X m) := by
    rw [natCard_quotient_eq_index, natCard_quotient_eq_index]
    exact AddSubgroup.index_dvd_of_le (Submodule.toAddSubgroup_mono hle)
  have hne : Nat.card (X ⧸ F J X m) ≠ 0 := by
    rw [natCard_quotient_eq_index]; exact index_F_ne_zero J X q hRq hqJ m
  have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  rw [natCard_quotient_F_eq I X q hqI hRq, natCard_quotient_F_eq J X q hqJ hRq, Nat.pow_le_pow_iff_right hq] at h1
  refine h1.trans ?_
  calc (∑ k ∈ Finset.range m, d J X q hqJ k) ≤ ∑ k ∈ Finset.range m, d J X q hqJ 0 :=
        Finset.sum_le_sum fun k _ => d_principal_le X q hRq k
    _ = m * d J X q hqJ 0 := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

include hRq in

/--
@isnad1 id=ex.2h4v.s7.ec1621aacb88 from=translated src=- shape=f4502fcc vocab=0150f528
-/
theorem d_eventually_const : ∃ e N : ℕ, ∀ n, N ≤ n → d I X q hqI n = e := by
  have hq : q.Prime := Fact.out
  obtain ⟨s, x, hxI⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian I)
  have hx : ∀ i, x i ∈ I := fun i => hxI ▸ Submodule.subset_span ⟨i, rfl⟩
  haveI := fun n => finite_Gr I X q hRq hqI n
  have HS := hilbertSerre R q hq s (fun n => Gr I X n) (fun i n => grMul I X (hx i) n)
    (fun n => ⟨d I X q hqI n, by rw [card_Gr_eq, card_Mg I X q hqI hRq]⟩)
    (fun i j n z => grMul_comm I X (hx i) (hx j) n z) (noeth_Gr I X x hxI hx)
  have hlc : (fun n => lc q (Gr I X n)) = fun n => (d I X q hqI n : ℤ) :=
    funext fun n => lc_eq hq.one_lt (by rw [card_Gr_eq, card_Mg I X q hqI hRq])
  rw [hlc] at HS
  obtain ⟨e, N, hN⟩ := eventually_const_of_iterΔ_eq_zero (fun n => (d I X q hqI n : ℤ))
    (d (Ideal.span {(q : R)}) X q (Ideal.mem_span_singleton_self _) 0) (fun n => by positivity)
    (fun m => by
      have h1 : ((∑ k ∈ Finset.range m, d I X q hqI k : ℕ) : ℤ)
          ≤ ((m * d (Ideal.span {(q : R)}) X q (Ideal.mem_span_singleton_self _) 0 : ℕ) : ℤ) := by
        exact_mod_cast sum_d_le I X q hRq hqI m
      simpa [mul_comm] using h1) s HS
  exact ⟨e, N, fun n hn => by exact_mod_cast hN n hn⟩

end assembly

end P2MHilbertSamuel

/--
@isnad1 id=ex.2h4v.s9.d4f2b05063f1 from=translated src=- shape=79765b18 vocab=beeb6af0
-/
theorem solution
    (R : Type*) [CommRing R] [IsNoetherianRing R] (q : ℕ) [Fact q.Prime]
    (hRq : Finite (R ⧸ Ideal.span {(q : R)}))
    (I : Ideal R) (hqI : (q : R) ∈ I)
    (X : Type*) [AddCommGroup X] [Module R X] [Module.Finite R X] :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card (X ⧸ (I ^ m • (⊤ : Submodule R X))) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card (X ⧸ (I ^ m • (⊤ : Submodule R X))) * q ^ C := by
  obtain ⟨e, N, hN⟩ := P2MHilbertSamuel.d_eventually_const I X q hRq hqI
  obtain ⟨C, hC⟩ := P2MHilbertSamuel.sandwich_of_eventually_const _ e N hN
  refine ⟨e, C, fun m => ?_⟩
  have hq : 1 ≤ q := (Fact.out : q.Prime).one_lt.le
  rw [show (I ^ m • (⊤ : Submodule R X)) = P2MHilbertSamuel.F I X m from rfl,
    P2MHilbertSamuel.natCard_quotient_F_eq I X q hqI hRq m, ← pow_add]
  exact ⟨Nat.pow_le_pow_right hq (hC m).1, Nat.pow_le_pow_right hq (hC m).2⟩
