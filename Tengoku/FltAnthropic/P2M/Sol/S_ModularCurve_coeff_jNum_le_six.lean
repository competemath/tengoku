import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_coeff_jNum_le_six.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_coeff_jNum_le_six

set_option autoImplicit false

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace ModularCurve
export _root_.ModularCurve (eisenstein4 etaProd dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv jNum)
open _root_.ModularCurve

namespace JCoeff

variable {R : Type*} [CommRing R]

def LowCoeffs (f : R⟦X⟧) (L : List R) : Prop :=
  ∀ i : ℕ, i < L.length → coeff i f = L.getD i 0

def conv (L M : List R) : List R :=
  (List.range (min L.length M.length)).map
    fun k => ((List.range (k + 1)).map fun i => L.getD i 0 * M.getD (k - i) 0).sum

/--
@isnad1 id=eq.0h3v.s4.3db188f57ee4 from=translated src=- shape=a02d4823 vocab=55961621
-/
theorem length_conv (L M : List R) : (conv L M).length = min L.length M.length := by
  simp [conv]

/--
@isnad1 id=eq.0h3v.s5.f5fbf8c4d590 from=translated src=- shape=782819ee vocab=98dcbbb1
-/
theorem finset_sum_range_eq_list_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

/--
@isnad1 id=eq.1h4v.s7.665f3a08f23d from=translated src=- shape=7c8c2526 vocab=07a51cb8
-/
theorem getD_conv (L M : List R) {k : ℕ} (hk : k < min L.length M.length) :
    (conv L M).getD k 0 = ∑ i ∈ Finset.range (k + 1), L.getD i 0 * M.getD (k - i) 0 := by
  rw [conv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp [finset_sum_range_eq_list_sum]

/--
@isnad1 id=lowcoeff.2h5v.s5.c2318e3e4159 from=translated src=- shape=4507ac17 vocab=1d09b363
-/
theorem LowCoeffs.mul {f g : R⟦X⟧} {L M : List R} (hf : LowCoeffs f L) (hg : LowCoeffs g M) :
    LowCoeffs (f * g) (conv L M) := by
  intro k hk
  rw [length_conv] at hk
  rw [getD_conv L M hk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [hf i (by omega), hg (k - i) (by omega)]

/--
@isnad1 id=lowcoeff.2h4v.s4.7aee6bb9bf83 from=translated src=- shape=c3d02c23 vocab=ec8451a5
-/
theorem LowCoeffs.congr {f : R⟦X⟧} {L M : List R} (hf : LowCoeffs f L) (h : L = M) : LowCoeffs f M :=
  h ▸ hf

/--
@isnad1 id=lowcoeff.0h2v.s5.6cd2eb153792 from=translated src=- shape=33626707 vocab=53ff0554
-/
theorem LowCoeffs.one (n : ℕ) : LowCoeffs (1 : R⟦X⟧) (1 :: List.replicate n 0) := by
  intro i hi
  rcases i with _ | i
  · simp
  · simp only [List.length_cons, List.length_replicate] at hi
    rw [coeff_one, ite_eq_right (Nat.succ_ne_zero i), List.getD_eq_getElem?_getD]
    simp [show i < n by omega]

/--
@isnad1 id=lowcoeff.1h3v.s7.e2a32a1e37a8 from=translated src=- shape=0426690e vocab=fc9dc599
-/
theorem LowCoeffs.one_sub_X_pow (m n : ℕ) (hm : 0 < m) :
    LowCoeffs (1 - X ^ m : R⟦X⟧) ((List.range n).map fun i => if i = 0 then 1 else if i = m then -1 else 0) := by
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some, map_sub, coeff_one, coeff_X_pow]
  by_cases h0 : i = 0
  · subst h0; simp [hm.ne]
  · simp [h0]
    split_ifs <;> simp

/--
@isnad1 id=dvd.2h4v.s6.661caa7ebcdf from=translated src=- shape=3f7c47b9 vocab=02c152e6
-/
theorem LowCoeffs.X_pow_dvd_sub {f g : R⟦X⟧} {L : List R} (hf : LowCoeffs f L) (hg : LowCoeffs g L) :
    (X : R⟦X⟧) ^ L.length ∣ f - g := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, hf m hm, hg m hm, sub_self]

/--
@isnad1 id=lowcoeff.5h4v.s7.7eede437ac78 from=translated src=- shape=13a97ba9 vocab=0f934ef6
-/
theorem LowCoeffs.invOfUnit {u : R⟦X⟧} {L V : List R} (hu : LowCoeffs u L) (hV : V.length = L.length)
    (hc : constantCoeff u = 1) (hconv : conv L V = 1 :: List.replicate (L.length - 1) 0)
    (hpos : 0 < L.length) :
    LowCoeffs (u.invOfUnit 1) V := by
  set w := u.invOfUnit 1 with hw
  have huw : u * w = 1 := PowerSeries.mul_invOfUnit u 1 (by rw [hc]; rfl)

  set Vp : R⟦X⟧ := PowerSeries.mk fun i => V.getD i 0 with hVp
  have hVpL : LowCoeffs Vp V := fun i _ => by simp [hVp, coeff_mk]
  have h1 : LowCoeffs (u * Vp) (1 :: List.replicate (L.length - 1) 0) :=
    (hu.mul hVpL).congr (by rw [hconv])
  have h1' : LowCoeffs (1 : R⟦X⟧) (1 :: List.replicate (L.length - 1) 0) := LowCoeffs.one _
  have hdvd : (X : R⟦X⟧) ^ L.length ∣ u * Vp - 1 := by
    have := h1.X_pow_dvd_sub h1'
    simpa [Nat.sub_add_cancel hpos] using this
  have hdvd' : (X : R⟦X⟧) ^ L.length ∣ Vp - w := by
    have : Vp - w = w * (u * Vp - 1) := by
      calc Vp - w = (u * w) * Vp - w * 1 := by rw [huw, one_mul, mul_one]
        _ = w * (u * Vp - 1) := by ring
    rw [this]
    exact Dvd.dvd.mul_left hdvd w
  rw [X_pow_dvd_iff] at hdvd'
  intro i hi
  have := hdvd' i (by omega)
  rw [map_sub, sub_eq_zero] at this
  rw [← this]
  exact hVpL i hi

/--
@isnad1 id=lowcoeff.2h5v.s6.4b6a2262c7fb from=translated src=- shape=3630ffa4 vocab=7fb3753f
-/
theorem LowCoeffs.pow_succ {f : R⟦X⟧} {L M : List R} {n : ℕ} (hn : LowCoeffs (f ^ n) M) (hf : LowCoeffs f L) :
    LowCoeffs (f ^ (n + 1)) (conv M L) := by
  rw [_root_.pow_succ]; exact hn.mul hf

end JCoeff

open JCoeff

section Eta

/--
@isnad1 id=eq.2h3v.s8.a541f1691740 from=translated src=- shape=8e14e22b vocab=acbe09ce
-/
theorem coeff_prod_one_sub_X_pow_of_le (T : Finset ℕ) (K : ℕ) (hT : ∀ b ∈ T, K ≤ b) (k : ℕ) (hk : k ≤ K) :
    coeff k (∏ b ∈ T, (1 - (X : ℤ⟦X⟧) ^ (b + 1))) = coeff k (1 : ℤ⟦X⟧) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, sub_mul, one_mul, map_sub, ih (fun b hb => hT b (Finset.mem_insert_of_mem hb))]
    have : coeff k ((X : ℤ⟦X⟧) ^ (a + 1) * ∏ b ∈ T, (1 - (X : ℤ⟦X⟧) ^ (b + 1))) = 0 := by
      rw [coeff_X_pow_mul']
      have : ¬ a + 1 ≤ k := by have := hT a (Finset.mem_insert_self a T); omega
      rw [ite_eq_right this]
    rw [this, sub_zero]

/--
@isnad1 id=eq.1h2v.s8.5aa4df077a50 from=translated src=- shape=351cc475 vocab=67dd9af0
-/
theorem coeff_etaProd_eq_coeff_prod_range (K k : ℕ) (hk : k ≤ K) :
    coeff k etaProd = coeff k (∏ n ∈ Finset.range K, (1 - (X : ℤ⟦X⟧) ^ (n + 1))) := by
  classical
  have hmul := PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ
  have hprod : HasProd (fun n => 1 - (X : ℤ⟦X⟧) ^ (n + 1)) etaProd := hmul.hasProd

  have hlim : Filter.Tendsto (fun s : Finset ℕ => coeff k (∏ b ∈ s, (1 - (X : ℤ⟦X⟧) ^ (b + 1))))
      Filter.atTop (nhds (coeff k etaProd)) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℤ k).tendsto _).comp hprod

  have hev : ∀ᶠ s : Finset ℕ in Filter.atTop,
      coeff k (∏ b ∈ s, (1 - (X : ℤ⟦X⟧) ^ (b + 1)))
        = coeff k (∏ n ∈ Finset.range K, (1 - (X : ℤ⟦X⟧) ^ (n + 1))) := by
    rw [Filter.eventually_atTop]
    refine ⟨Finset.range K, fun s hs => ?_⟩
    rw [← Finset.prod_sdiff hs, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Finset.sum_eq_single 0]
    · rw [coeff_prod_one_sub_X_pow_of_le (s \ Finset.range K) K (fun b hb => by
          simp only [Finset.mem_sdiff, Finset.mem_range, not_lt] at hb; exact hb.2) 0 (Nat.zero_le _)]
      simp
    · intro i hi hi0
      rw [coeff_prod_one_sub_X_pow_of_le (s \ Finset.range K) K (fun b hb => by
          simp only [Finset.mem_sdiff, Finset.mem_range, not_lt] at hb; exact hb.2) i
          (by rw [Finset.mem_range] at hi; omega)]
      rw [coeff_one, ite_eq_right hi0, zero_mul]
    · intro h; simp at h
  have hlim2 : Filter.Tendsto (fun s : Finset ℕ => coeff k (∏ b ∈ s, (1 - (X : ℤ⟦X⟧) ^ (b + 1))))
      Filter.atTop (nhds (coeff k (∏ n ∈ Finset.range K, (1 - (X : ℤ⟦X⟧) ^ (n + 1))))) :=
    tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hev)
  exact tendsto_nhds_unique hlim hlim2

/--
@isnad1 id=lowcoeff.0h0v.s5.c684aed351b3 from=translated src=- shape=f80f79de vocab=c98f946d
-/
theorem lowCoeffs_etaProd : LowCoeffs etaProd [1, -1, -1, 0, 0, 1, 0] := by

  have hP : LowCoeffs (∏ n ∈ Finset.range 7, (1 - (X : ℤ⟦X⟧) ^ (n + 1))) [1, -1, -1, 0, 0, 1, 0] := by
    have f := fun m (hm : 0 < m) => LowCoeffs.one_sub_X_pow (R := ℤ) m 7 hm
    have h1 : LowCoeffs (∏ n ∈ Finset.range 1, (1 - (X : ℤ⟦X⟧) ^ (n + 1))) [1, -1, 0, 0, 0, 0, 0] := by
      rw [Finset.prod_range_one]; exact (f 1 (by norm_num)).congr (by decide)
    have h2 := (h1.mul (f 2 (by norm_num))).congr (M := [1, -1, -1, 1, 0, 0, 0]) (by decide)
    rw [← Finset.prod_range_succ] at h2
    have h3 := (h2.mul (f 3 (by norm_num))).congr (M := [1, -1, -1, 0, 1, 1, -1]) (by decide)
    rw [← Finset.prod_range_succ] at h3
    have h4 := (h3.mul (f 4 (by norm_num))).congr (M := [1, -1, -1, 0, 0, 2, 0]) (by decide)
    rw [← Finset.prod_range_succ] at h4
    have h5 := (h4.mul (f 5 (by norm_num))).congr (M := [1, -1, -1, 0, 0, 1, 1]) (by decide)
    rw [← Finset.prod_range_succ] at h5
    have h6 := (h5.mul (f 6 (by norm_num))).congr (M := [1, -1, -1, 0, 0, 1, 0]) (by decide)
    rw [← Finset.prod_range_succ] at h6
    have h7 := (h6.mul (f 7 (by norm_num))).congr (M := [1, -1, -1, 0, 0, 1, 0]) (by decide)
    rw [← Finset.prod_range_succ] at h7
    exact h7
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rw [coeff_etaProd_eq_coeff_prod_range 7 i (by omega)]
  exact hP i (by simpa using hi)

/--
@isnad1 id=lowcoeff.0h0v.s6.f0465c9c95a5 from=translated src=- shape=8781e66f vocab=7a5dac75
-/
theorem lowCoeffs_dedekindEtaUnit : LowCoeffs dedekindEtaUnit [1, -24, 252, -1472, 4830, -6048, -16744] := by
  have e1 := lowCoeffs_etaProd
  have e2 := (e1.mul e1).congr (M := [1, -2, -1, 2, 1, 2, -2]) (by decide)
  have e4 := (e2.mul e2).congr (M := [1, -4, 2, 8, -5, -4, -10]) (by decide)
  have e8 := (e4.mul e4).congr (M := [1, -8, 20, 0, -70, 64, 56]) (by decide)
  have e16 := (e8.mul e8).congr (M := [1, -16, 104, -320, 260, 1248, -3712]) (by decide)
  have e24 := (e16.mul e8).congr (M := [1, -24, 252, -1472, 4830, -6048, -16744]) (by decide)
  have : dedekindEtaUnit = (((etaProd * etaProd) * (etaProd * etaProd)) * ((etaProd * etaProd) * (etaProd * etaProd)))
      * ((((etaProd * etaProd) * (etaProd * etaProd)) * ((etaProd * etaProd) * (etaProd * etaProd))))
      * (((etaProd * etaProd) * (etaProd * etaProd)) * ((etaProd * etaProd) * (etaProd * etaProd))) := by
    rw [dedekindEtaUnit]; ring

  have h24 : dedekindEtaUnit = ((((etaProd * etaProd) * (etaProd * etaProd)) * ((etaProd * etaProd) * (etaProd * etaProd))) *
      (((etaProd * etaProd) * (etaProd * etaProd)) * ((etaProd * etaProd) * (etaProd * etaProd)))) *
      (((etaProd * etaProd) * (etaProd * etaProd)) * ((etaProd * etaProd) * (etaProd * etaProd))) := by
    rw [dedekindEtaUnit]; ring
  rw [h24]
  exact e24

/--
@isnad1 id=lowcoeff.0h0v.s5.50e9bc806bff from=translated src=- shape=f34727e0 vocab=b36cfef5
-/
theorem lowCoeffs_dedekindEtaUnitInv : LowCoeffs dedekindEtaUnitInv [1, 24, 324, 3200, 25650, 176256, 1073720] := by
  refine lowCoeffs_dedekindEtaUnit.invOfUnit (by rfl) constantCoeff_dedekindEtaUnit (by decide) (by decide)

/--
@isnad1 id=lowcoeff.0h0v.s5.9152e5afa46b from=translated src=- shape=f34727e0 vocab=66ca6f0b
-/
theorem lowCoeffs_eisenstein4 : LowCoeffs eisenstein4 [1, 240, 2160, 6720, 17520, 30240, 60480] := by
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  simp only [eisenstein4, coeff_mk]
  interval_cases i <;> decide

/--
@isnad1 id=lowcoeff.0h0v.s5.23a2ef8697f0 from=translated src=- shape=f34727e0 vocab=d6bbf85d
-/
theorem lowCoeffs_jNum : LowCoeffs jNum [1, 744, 196884, 21493760, 864299970, 20245856256, 333202640600] := by
  have h4 := lowCoeffs_eisenstein4
  have h42 := (h4.mul h4).congr (M := [1, 480, 61920, 1050240, 7926240, 37500480, 135480960]) (by decide)
  have h43 := (h42.mul h4).congr (M := [1, 720, 179280, 16954560, 396974160, 4632858720, 34413301440]) (by decide)
  have hj := (h43.mul lowCoeffs_dedekindEtaUnitInv).congr
    (M := [1, 744, 196884, 21493760, 864299970, 20245856256, 333202640600]) (by decide)
  have : jNum = eisenstein4 * eisenstein4 * eisenstein4 * dedekindEtaUnitInv := by rw [jNum]; ring
  rw [this]; exact hj

/--
@isnad1 id=and.0h0v.s9.c43d0dea2bd7 from=translated src=- shape=2b2ec391 vocab=3e9021a8
-/
theorem coeff_jNum_le_six' :
    coeff 0 jNum = 1 ∧ coeff 1 jNum = 744 ∧ coeff 2 jNum = 196884 ∧ coeff 3 jNum = 21493760 ∧
      coeff 4 jNum = 864299970 ∧ coeff 5 jNum = 20245856256 ∧ coeff 6 jNum = 333202640600 := by
  have h := lowCoeffs_jNum
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide)⟩

end Eta

end ModularCurve

open _root_.ModularCurve open _root_.P2MW.S_ModularCurve_coeff_jNum_le_six.ModularCurve open _root_.Polynomial

/--
@isnad1 id=and.0h0v.s9.c43d0dea2bd7 from=translated src=- shape=2b2ec391 vocab=3e9021a8
-/
theorem solution :
    PowerSeries.coeff 0 jNum = 1 ∧ PowerSeries.coeff 1 jNum = 744 ∧ PowerSeries.coeff 2 jNum = 196884 ∧
      PowerSeries.coeff 3 jNum = 21493760 ∧ PowerSeries.coeff 4 jNum = 864299970 ∧
      PowerSeries.coeff 5 jNum = 20245856256 ∧ PowerSeries.coeff 6 jNum = 333202640600 :=
  ModularCurve.coeff_jNum_le_six'
