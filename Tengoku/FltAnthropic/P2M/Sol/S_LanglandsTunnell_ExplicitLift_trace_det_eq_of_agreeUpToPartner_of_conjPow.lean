import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_Lift48
import Tengoku.FltAnthropic.Definitions.Def_TaylorWiles_Primes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_ExplicitLift_trace_det_eq_of_agreeUpToPartner_of_conjPow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_ExplicitLift_trace_det_eq_of_agreeUpToPartner_of_conjPow

set_option autoImplicit false

namespace P2mOctCompare

open FLT.ExplicitLift LanglandsTunnell.Lift48 Matrix

def Hex (k : Mat) : Prop := det2 k = 1 ∧ (tr2 k = 1 ∨ tr2 k = -1)

scoped instance : DecidablePred Hex := fun k =>
  inferInstanceAs (Decidable (det2 k = 1 ∧ (tr2 k = 1 ∨ tr2 k = -1)))

def inv2 (p : Mat) : Mat := det2 p • !![p 1 1, -(p 0 1); -(p 1 0), p 0 0]

/--
@isnad1 id=and.1h1v.s8.174337e15207 from=translated src=- shape=d74f5f39 vocab=12239c9f
-/
theorem K48_inv2 : ∀ k ∈ K48, k * inv2 k = 1 ∧ inv2 k * k = 1 := by decide

/--
@isnad1 id=eq.2h1v.s6.134f686fb694 from=translated src=- shape=384e3f6b vocab=4e533b6b
-/
theorem K48_hex_pw6 : ∀ k ∈ K48, Hex k → pw k 6 = 1 := by decide

/--
@isnad1 id=or.3h2v.s8.a79b7f3c6c89 from=translated src=- shape=77128330 vocab=138c9b24
-/
theorem K48_hex_powers : ∀ k ∈ K48, Hex k → ∀ j ∈ List.range 6,
    (Hex (pw k j) ∧ tr2 (pw k j) = -((-tr2 k) ^ j)) ∨
      (¬ Hex (pw k j) ∧ tr2 (pw k j) = 2 * (-tr2 k) ^ j) := by
  decide

/--
@isnad1 id=and.3h1v.s8.b031ecb8fd5f from=translated src=- shape=60677b98 vocab=a30ae137
-/
theorem K48_hex_sq : ∀ k ∈ K48, Hex k → tr2 k = 1 → Hex (k * k) ∧ tr2 (k * k) = -1 := by decide

/--
@isnad1 id=ex.3h1v.s8.3e08d725b09b from=translated src=- shape=bcbc843a vocab=5cf30701
-/
theorem K48_hex_witness : ∀ k ∈ K48, Hex k → tr2 k = -1 →
    ∃ p ∈ K48, pw (k * (p * k * inv2 p)) 2 = -1 := by decide

/--
@isnad1 id=and.0h0v.s7.7af8937b466b from=translated src=- shape=c226f899 vocab=c41b49b4
-/
theorem neg_one_facts : ¬ Hex (-1) ∧ tr2 (-1 : Mat) = -2 := by decide

/--
@isnad1 id=eq.1h1v.s7.6b458dd28e0e from=translated src=- shape=f9a21da6 vocab=0cc3e0e2
-/
theorem hex_neg_tr_pow_six (k : Mat) (hk : Hex k) : (-tr2 k) ^ 6 = 1 := by
  rcases hk.2 with h | h <;> rw [h] <;> decide

section MatrixLemmas

variable {F : Type} [Field F] [CharZero F]

/--
@isnad1 id=eq.1h4v.s9.921f05719fea from=translated src=- shape=cdd9e1fd vocab=2eff0a1c
-/
theorem pow_scalar_add_nilpotent (x : F) (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N = 0) (m : ℕ) :
    (x • (1 : Matrix (Fin 2) (Fin 2) F) + N) ^ (m + 1) =
      (x ^ (m + 1)) • (1 : Matrix (Fin 2) (Fin 2) F) + (((m : F) + 1) * x ^ m) • N := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, Matrix.mul_smul, one_mul, mul_one, smul_smul,
      smul_mul_assoc, hN, smul_zero, add_zero]
    match_scalars <;> ring

theorem eq_scalar_of_isOfFinOrder (A : Matrix (Fin 2) (Fin 2) F) (hA : IsOfFinOrder A) (x : F)
    (htr : A.trace = 2 * x) (hdet : A.det = x ^ 2) : A = x • (1 : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨m₀, hm₀, hAm⟩ := isOfFinOrder_iff_pow_eq_one.1 hA
  obtain ⟨m, rfl⟩ : ∃ m, m₀ = m + 1 := ⟨m₀ - 1, (Nat.sub_add_cancel hm₀).symm⟩
  set N : Matrix (Fin 2) (Fin 2) F := A - x • 1 with hNdef
  have hAN : A = x • 1 + N := by rw [hNdef]; abel
  have hN : N * N = 0 := by
    have hCH := Matrix.sq_eq_trace_smul_sub_det_smul_one A
    rw [htr, hdet] at hCH
    have : N * N = A ^ 2 - (2 * x) • A + (x ^ 2) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [hNdef]
      simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul, sq]
      module
    rw [this, hCH]; module
  have hpow := pow_scalar_add_nilpotent x N hN m
  rw [← hAN, hAm] at hpow

  have hmulN : N = (x ^ (m + 1)) • N := by
    have := congrArg (· * N) hpow
    simp only [one_mul, add_mul, smul_mul_assoc, hN, smul_zero, add_zero] at this
    exact this
  by_cases hxm : x ^ (m + 1) = 1
  · rw [hxm, one_smul] at hpow
    have h2 : (((m : F) + 1) * x ^ m) • N = 0 :=
      add_left_cancel (hpow.symm.trans (add_zero _).symm)
    have hx0 : x ≠ 0 := by
      rintro rfl; rw [zero_pow (Nat.succ_ne_zero m)] at hxm; exact zero_ne_one hxm
    have hcoef : ((m : F) + 1) * x ^ m ≠ 0 :=
      mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero m) (pow_ne_zero _ hx0)
    rcases smul_eq_zero.1 h2 with h | h
    · exact absurd h hcoef
    · rw [hAN, h, add_zero]
  · have h2 : (x ^ (m + 1) - 1) • N = 0 := by rw [sub_smul, one_smul, ← hmulN, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · exact absurd (sub_eq_zero.1 h) hxm
    · rw [hAN, h, add_zero]

omit [CharZero F] in

/--
@isnad1 id=and.2h6v.s9.fb7699703358 from=translated src=- shape=14fb6e7d vocab=f07e63fd
-/
theorem trace_det_pow_transport {R : Type} [CommRing R] (ι : R →+* F)
    (A : Matrix (Fin 2) (Fin 2) R) (B : Matrix (Fin 2) (Fin 2) F)
    (htr : B.trace = ι A.trace) (hdet : B.det = ι A.det) (n : ℕ) :
    (B ^ n).trace = ι (A ^ n).trace ∧ (B ^ n).det = ι (A ^ n).det := by
  refine ⟨?_, by rw [Matrix.det_pow, Matrix.det_pow, map_pow, hdet]⟩
  induction n using Nat.twoStepInduction with
  | zero => rw [pow_zero, pow_zero, Matrix.trace_one, Matrix.trace_one, map_natCast]
  | one => simpa using htr
  | more k ih0 ih1 =>
    rw [Matrix.trace_pow_add_two, Matrix.trace_pow_add_two, ih0, ih1, htr, hdet]
    simp only [map_sub, map_mul]

end MatrixLemmas

section Compare

variable {G : Type} [Group G] {F : Type} [Field F] [CharZero F]
  (ι : ℤ√(-2) →+* F)
  (M : G →* Matrix (Fin 2) (Fin 2) (ℤ√(-2)))
  (hM : ∀ g, M g ∈ Submonoid.closure ({Slift, Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2)))))
  (hMsurj : ∀ k ∈ Submonoid.closure ({Slift, Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2)))),
      ∃ g, M g = k)
  (r : G →* Matrix (Fin 2) (Fin 2) F)
  (hfin : ∀ g, IsOfFinOrder (r g))
  (S : Set G)
  (hS : ∀ φ ∈ S, (r φ).det = ι (M φ).det ∧
      ((r φ).trace = ι (M φ).trace ∨
        ((M φ).det = 1 ∧ ((M φ).trace = 1 ∨ (M φ).trace = -1) ∧
          (r φ).trace = -2 * ι (M φ).trace)))
  (hcover : ∀ σ : G, ∃ φ ∈ S, ∃ g : G, ∃ n : ℕ,
      r σ = r (g * φ ^ n * g⁻¹) ∧ M σ = M (g * φ ^ n * g⁻¹))

include hM in
/--
@isnad1 id=mem.1h3v.s10.732b072ec2ad from=translated src=- shape=4b608e86 vocab=fe5deee8
-/
theorem M_mem_K48 (g : G) : M g ∈ K48 := (mem_closure_iff_mem_K48 _).1 (hM g)

omit [CharZero F] in
/--
@isnad1 id=eq.0h4v.s9.f7c5fe3dec9a from=translated src=- shape=af28d4da vocab=281c08d7
-/
theorem r_mul_inv (g : G) : r g * r g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]

omit [CharZero F] in
/--
@isnad1 id=eq.0h4v.s9.49d85b146fd5 from=translated src=- shape=6dace1a9 vocab=281c08d7
-/
theorem r_inv_mul (g : G) : r g⁻¹ * r g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]

/--
@isnad1 id=eq.0h3v.s9.9520947c6889 from=translated src=- shape=8fad5992 vocab=f21825bf
-/
theorem M_mul_inv (g : G) : M g * M g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]

/--
@isnad1 id=eq.0h3v.s9.af3d692e834b from=translated src=- shape=d057b693 vocab=f21825bf
-/
theorem M_inv_mul (g : G) : M g⁻¹ * M g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]

omit [CharZero F] in
/--
@isnad1 id=eq.0h5v.s9.93b042c19d10 from=translated src=- shape=c007ad71 vocab=27d1fc1f
-/
theorem r_conj_trace (g : G) (X : Matrix (Fin 2) (Fin 2) F) :
    (r g * X * r g⁻¹).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, r_inv_mul, one_mul]

omit [CharZero F] in
/--
@isnad1 id=eq.0h5v.s9.6c92dac02438 from=translated src=- shape=c007ad71 vocab=a7cec13a
-/
theorem r_conj_det (g : G) (X : Matrix (Fin 2) (Fin 2) F) :
    (r g * X * r g⁻¹).det = X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (r g).det, mul_assoc, ← Matrix.det_mul,
    r_mul_inv, Matrix.det_one, mul_one]

/--
@isnad1 id=eq.0h4v.s10.f0b943bb8bf7 from=translated src=- shape=01998743 vocab=da6885be
-/
theorem M_conj_trace (g : G) (X : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) :
    (M g * X * M g⁻¹).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, M_inv_mul, one_mul]

/--
@isnad1 id=eq.0h4v.s10.c987725f13dc from=translated src=- shape=01998743 vocab=b62cfa03
-/
theorem M_conj_det (g : G) (X : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) :
    (M g * X * M g⁻¹).det = X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (M g).det, mul_assoc, ← Matrix.det_mul,
    M_mul_inv, Matrix.det_one, mul_one]

/--
@isnad1 id=iff.0h1v.s8.6a3a69ab758c from=translated src=- shape=b42fad1c vocab=ab7f33b8
-/
theorem hex_iff (k : Mat) : Hex k ↔ k.det = 1 ∧ (k.trace = 1 ∨ k.trace = -1) := by
  rw [Hex, det2_eq_det, tr2_eq_trace]

/--
@isnad1 id=iff.0h4v.s9.58e96f23adff from=translated src=- shape=f36af73a vocab=5a6ca57b
-/
theorem hex_conj (g : G) (X : Mat) : Hex (M g * X * M g⁻¹) ↔ Hex X := by
  rw [hex_iff, hex_iff, M_conj_trace, M_conj_det]

include hM in

/--
@isnad1 id=eq.1h3v.s10.156302566c21 from=translated src=- shape=c0b851f3 vocab=33a9eb14
-/
theorem M_inv_eq_inv2 (g : G) : M g⁻¹ = inv2 (M g) := by
  have h := (K48_inv2 (M g) (M_mem_K48 M hM g)).1
  calc M g⁻¹ = M g⁻¹ * (M g * inv2 (M g)) := by rw [h, mul_one]
    _ = inv2 (M g) := by rw [← mul_assoc, M_inv_mul, one_mul]

def Good (σ : G) : Prop := (r σ).trace = ι (M σ).trace ∧ (r σ).det = ι (M σ).det

def Bad (σ : G) : Prop :=
  ∃ c : ℤ√(-2), (c = 1 ∨ c = -1) ∧ r σ = ι c • (1 : Matrix (Fin 2) (Fin 2) F) ∧
    Hex (M σ) ∧ (M σ).trace = -c

include hM hfin hS hcover in

/--
@isnad1 id=or.4h7v.s12.eb5aaa8d1d55 from=translated src=- shape=bc4228ad vocab=8a9f012c
-/
theorem good_or_bad (σ : G) : Good ι M r σ ∨ Bad ι M r σ := by
  obtain ⟨φ, hφS, g, n, hrσ, hMσ⟩ := hcover σ
  obtain ⟨hdetφ, hφ⟩ := hS φ hφS
  have hrσ' : r σ = r g * r φ ^ n * r g⁻¹ := by rw [hrσ, map_mul, map_mul, map_pow]
  have hMσ' : M σ = M g * M φ ^ n * M g⁻¹ := by rw [hMσ, map_mul, map_mul, map_pow]
  rcases hφ with htrφ | ⟨hdet1, htr1, htrφ⟩
  ·
    left
    obtain ⟨htrn, hdetn⟩ := trace_det_pow_transport ι (M φ) (r φ) htrφ hdetφ n
    refine ⟨?_, ?_⟩
    · rw [hrσ', hMσ', r_conj_trace, M_conj_trace, htrn]
    · rw [hrσ', hMσ', r_conj_det, M_conj_det, hdetn]
  ·
    set k : Mat := M φ with hk
    have hkK : k ∈ K48 := M_mem_K48 M hM φ
    have hkhex : Hex k := (hex_iff k).2 ⟨hdet1, htr1⟩
    set c : ℤ√(-2) := -k.trace with hc
    have hc1 : c = 1 ∨ c = -1 := by
      rcases htr1 with h | h
      · right; rw [hc, h]
      · left; rw [hc, h, neg_neg]
    have hcsq : c ^ 2 = 1 := by rcases hc1 with h | h <;> rw [h] <;> norm_num
    have hrφ : r φ = ι c • (1 : Matrix (Fin 2) (Fin 2) F) := by
      apply eq_scalar_of_isOfFinOrder (r φ) (hfin φ)
      · rw [htrφ, hc, map_neg]; ring
      · rw [hdetφ, hdet1, ← map_pow, hcsq]
    have hrσc : r σ = ι (c ^ n) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [hrσ', hrφ, smul_pow, one_pow, Matrix.mul_smul, mul_one, Matrix.smul_mul, r_mul_inv,
        map_pow]

    have hk6 : k ^ 6 = 1 := by rw [← pw_eq_pow]; exact K48_hex_pw6 k hkK hkhex
    have hc6 : c ^ 6 = 1 := by
      have := hex_neg_tr_pow_six k hkhex; rwa [tr2_eq_trace] at this
    set j : ℕ := n % 6 with hj
    have hjlt : j < 6 := Nat.mod_lt _ (by norm_num)
    have hkn : k ^ n = k ^ j := by
      conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul, hk6, one_pow, one_mul]
    have hcn : c ^ n = c ^ j := by
      conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul, hc6, one_pow, one_mul]
    have htab := K48_hex_powers k hkK hkhex j (List.mem_range.2 hjlt)
    rw [pw_eq_pow, tr2_eq_trace, tr2_eq_trace, ← hc, ← hkn, ← hcn] at htab

    have hMσtr : (M σ).trace = (k ^ n).trace := by rw [hMσ', M_conj_trace]
    have hMσdet : (M σ).det = 1 := by rw [hMσ', M_conj_det, Matrix.det_pow, hdet1, one_pow]
    have hrσdet : (r σ).det = 1 := by
      rw [hrσc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← map_pow, ← pow_mul,
        mul_comm, pow_mul, hcsq, one_pow, map_one]
    have hrσtr : (r σ).trace = ι (2 * c ^ n) := by
      rw [hrσc, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, map_mul, smul_eq_mul,
        map_ofNat, mul_comm, Nat.cast_ofNat]
    rcases htab with ⟨hhexj, htrj⟩ | ⟨-, htrj⟩
    ·
      right
      refine ⟨c ^ n, ?_, hrσc, ?_, ?_⟩
      · rw [hcn]
        rcases hc1 with h | h
        · left; rw [h, one_pow]
        · rw [h]; exact (neg_one_pow_eq_or (R := ℤ√(-2)) j)
      · rw [hMσ', hex_conj]; exact hhexj
      · rw [hMσtr, htrj]
    ·
      left
      exact ⟨by rw [hrσtr, hMσtr, htrj], by rw [hrσdet, hMσdet, map_one]⟩

include hM hMsurj hfin hS hcover in

/--
@isnad1 id=false.8h7v.s12.fa73c8edf630 from=translated src=- shape=469f3ee4 vocab=c721c3c5
-/
theorem not_bad_one (σ : G) (hr : r σ = 1) (hhex : Hex (M σ)) (htr : (M σ).trace = -1) : False := by
  set m : Mat := M σ with hm
  have hmK : m ∈ K48 := M_mem_K48 M hM σ
  obtain ⟨p, hpK, hp⟩ := K48_hex_witness m hmK hhex (by rw [tr2_eq_trace]; exact htr)
  obtain ⟨η, hη⟩ := hMsurj p ((mem_closure_iff_mem_K48 p).2 hpK)
  have hηinv : M η⁻¹ = inv2 p := by rw [M_inv_eq_inv2 M hM η, hη]
  set τ : G := σ * (η * σ * η⁻¹) with hτ
  have hrτ : r τ = 1 := by
    rw [hτ, map_mul, map_mul, map_mul, hr, one_mul, mul_one, r_mul_inv]
  have hMτ2 : M (τ ^ 2) = -1 := by
    rw [map_pow, hτ, map_mul, map_mul, map_mul, hη, hηinv, ← hm, ← pw_eq_pow, hp]
  have hrτ2 : r (τ ^ 2) = 1 := by rw [map_pow, hrτ, one_pow]
  rcases good_or_bad ι M hM r hfin S hS hcover (τ ^ 2) with ⟨hgtr, -⟩ | ⟨c, -, -, hhex', -⟩
  · rw [hrτ2, hMτ2, Matrix.trace_one, Fintype.card_fin, ← tr2_eq_trace, neg_one_facts.2,
      map_neg, map_ofNat] at hgtr
    norm_num at hgtr
  · rw [hMτ2] at hhex'
    exact neg_one_facts.1 hhex'

include hM hMsurj hfin hS hcover in
/--
@isnad1 id=not.5h7v.s12.e87d34311877 from=translated src=- shape=5b78438b vocab=1c776568
-/
theorem not_bad (σ : G) : ¬ Bad ι M r σ := by
  rintro ⟨c, hc, hr, hhex, htr⟩
  rcases hc with rfl | rfl
  · rw [map_one, one_smul] at hr
    exact not_bad_one ι M hM hMsurj r hfin S hS hcover σ hr hhex htr
  ·
    have hmK : M σ ∈ K48 := M_mem_K48 M hM σ
    have hsq := K48_hex_sq (M σ) hmK hhex (by rw [tr2_eq_trace, htr, neg_neg])
    refine not_bad_one ι M hM hMsurj r hfin S hS hcover (σ ^ 2) ?_ ?_ ?_
    · rw [map_pow, hr, smul_pow, one_pow, ← map_pow]; norm_num
    · rw [map_pow, pow_two]; exact hsq.1
    · rw [map_pow, pow_two, ← tr2_eq_trace]; exact hsq.2

include hM hMsurj hfin hS hcover in
/--
@isnad1 id=good.5h7v.s12.1c56283ae084 from=translated src=- shape=af1ea83d vocab=22939f8d
-/
theorem good (σ : G) : Good ι M r σ :=
  (good_or_bad ι M hM r hfin S hS hcover σ).resolve_right (not_bad ι M hM hMsurj r hfin S hS hcover σ)

end Compare

end P2mOctCompare
open scoped _root_.P2MW.S_LanglandsTunnell_ExplicitLift_trace_det_eq_of_agreeUpToPartner_of_conjPow.P2mOctCompare

/--
@isnad1 id=and.5h7v.s12.ba37258a09f1 from=translated src=- shape=aab75261 vocab=4827b1eb
-/
theorem solution
    {G : Type} [Group G] {F : Type} [Field F] [CharZero F]
    (ι : ℤ√(-2) →+* F)
    (M : G →* Matrix (Fin 2) (Fin 2) (ℤ√(-2)))
    (hM : ∀ g, M g ∈ Submonoid.closure
      ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2)))))
    (hMsurj : ∀ k ∈ Submonoid.closure
      ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2)))),
      ∃ g, M g = k)
    (r : G →* Matrix (Fin 2) (Fin 2) F)
    (hfin : ∀ g, IsOfFinOrder (r g))
    (S : Set G)
    (hS : ∀ φ ∈ S, (r φ).det = ι (M φ).det ∧
      ((r φ).trace = ι (M φ).trace ∨
        ((M φ).det = 1 ∧ ((M φ).trace = 1 ∨ (M φ).trace = -1) ∧
          (r φ).trace = -2 * ι (M φ).trace)))
    (hcover : ∀ σ : G, ∃ φ ∈ S, ∃ g : G, ∃ n : ℕ,
      r σ = r (g * φ ^ n * g⁻¹) ∧ M σ = M (g * φ ^ n * g⁻¹))
    (σ : G) :
    (r σ).trace = ι (M σ).trace ∧ (r σ).det = ι (M σ).det :=
  P2mOctCompare.good ι M hM hMsurj r hfin S hS hcover σ
