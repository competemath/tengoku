import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PhiGen
import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots
import Tengoku.Seed.RingTheory.Polynomial.Cyclotomic.Basic
import Tengoku.Seed.RingTheory.PowerSeries.Expand

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_StarBank_deltaNorm.lean`: wrote out 10 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 4 `p2m_export`, 4 `p2m_open`, 2 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_StarBank_deltaNorm

set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology

open _root_.ModularCurve

namespace ModularCurve
export _root_.ModularCurve (qTwist qTwist_coeff qTwist_single qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single etaProd constantCoeff_etaProd ofPowerSeries_coeff_of_neg)
namespace W1
open _root_.ModularCurve

/--
@isnad1 id=eq.0h3v.s9.933aa3e501fc from=translated src=- shape=570521cc vocab=8729b528
-/
theorem qTwist_ofPowerSeries {R : Type*} [CommRing R] (u : Rˣ) (f : PowerSeries R) :
    qTwist u (HahnSeries.ofPowerSeries ℤ R f) =
      HahnSeries.ofPowerSeries ℤ R (PowerSeries.rescale (u : R) f) := by
  ext k
  rw [qTwist_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_rescale, zpow_natCast, Units.val_pow_eq_pow_val]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, mul_zero]

/--
@isnad1 id=eq.0h3v.s9.59c44386f30d from=translated src=- shape=d05b2b85 vocab=9f6a54b0
-/
theorem qExpand_ofPowerSeries {R : Type*} [CommRing R] (N : ℕ) [NeZero N] (f : PowerSeries R) :
    qExpand R N (HahnSeries.ofPowerSeries ℤ R f) =
      HahnSeries.ofPowerSeries ℤ R (PowerSeries.expand N (NeZero.ne N) f) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul]
    rcases le_or_gt 0 m with hm | hm
    · lift m to ℕ using hm
      rw [HahnSeries.ofPowerSeries_apply_coeff,
        show ((N : ℤ) * ((m : ℕ) : ℤ) : ℤ) = ((N * m : ℕ) : ℤ) by push_cast; ring,
        HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_expand_mul]
    · have hneg : (N : ℤ) * m < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) hm
      rw [ofPowerSeries_coeff_of_neg _ hm, ofPowerSeries_coeff_of_neg _ hneg]
  · rw [qExpand_coeff_of_not_dvd N _ hk]
    rcases le_or_gt 0 k with hk0 | hk0
    · lift k to ℕ using hk0
      rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_expand_of_not_dvd]
      exact fun h => hk (Int.natCast_dvd_natCast.2 h)
    · rw [ofPowerSeries_coeff_of_neg _ hk0]

/--
@isnad1 id=continuo.1h3v.s7.27c680204007 from=translated src=- shape=18450056 vocab=f094d2de
-/
theorem continuous_of_coeff {R S : Type*} [Semiring R] [Semiring S] [TopologicalSpace R]
    [TopologicalSpace S] (g : PowerSeries R → PowerSeries S)
    (h : ∀ d, Continuous fun φ => PowerSeries.coeff d (g φ)) : Continuous g :=
  continuous_iff_continuousAt.2 fun φ =>
    (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto S g (nhds φ) (g φ)).2 fun d =>
      (h d).continuousAt

/--
@isnad1 id=continuo.1h3v.s6.a873c74740f8 from=translated src=- shape=1aa6b859 vocab=c2dc096a
-/
theorem continuous_map {R S : Type*} [Semiring R] [Semiring S] [TopologicalSpace R]
    [TopologicalSpace S] (f : R →+* S) (hf : Continuous f) :
    Continuous (PowerSeries.map f : PowerSeries R → PowerSeries S) :=
  continuous_of_coeff _ fun d => by
    simp only [PowerSeries.coeff_map]
    exact hf.comp (PowerSeries.WithPiTopology.continuous_coeff R d)

/--
@isnad1 id=continuo.0h2v.s6.26692bec06bd from=translated src=- shape=976576e9 vocab=add2bae1
-/
theorem continuous_rescale {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (a : R) : Continuous (PowerSeries.rescale a : PowerSeries R → PowerSeries R) :=
  continuous_of_coeff _ fun d => by
    simp only [PowerSeries.coeff_rescale]
    exact (continuous_of_discreteTopology (f := fun x : R => a ^ d * x)).comp
      (PowerSeries.WithPiTopology.continuous_coeff R d)

/--
@isnad1 id=continuo.1h2v.s7.290fc71521b1 from=translated src=- shape=8d3b455e vocab=9bd88799
-/
theorem continuous_expand {R : Type*} [CommRing R] [TopologicalSpace R] (N : ℕ) (hN : N ≠ 0) :
    Continuous (PowerSeries.expand N hN : PowerSeries R → PowerSeries R) :=
  continuous_of_coeff _ fun d => by
    simp only [PowerSeries.coeff_expand]
    split_ifs
    · exact PowerSeries.WithPiTopology.continuous_coeff R _
    · exact continuous_const

/--
@isnad1 id=multipli.1h2v.s7.82b620e886f5 from=translated src=- shape=9b8dbd5e vocab=7a9ebb85
-/
theorem multipliable_of_X_pow_dvd {R : Type*} [CommRing R] [TopologicalSpace R]
    (u : ℕ → PowerSeries R) (h : ∀ n, (PowerSeries.X : PowerSeries R) ^ (n + 1) ∣ u n - 1) :
    Multipliable u := by
  have hu : u = fun n => 1 + (u n - 1) := funext fun n => by ring
  rw [hu]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩
  intro m hm
  have hle : ((m + 1 : ℕ) : ℕ∞) ≤ (u m - 1).order :=
    PowerSeries.nat_le_order _ _ fun i hi => PowerSeries.X_pow_dvd_iff.1 (h m) i hi
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le hm) hle

/--
@isnad1 id=eq.0h1v.s7.58bcb3abeb76 from=translated src=- shape=846db7c4 vocab=69924a33
-/
theorem map_etaProd_eq_tprod (K : Type*) [CommRing K] [TopologicalSpace K] [T2Space K] :
    PowerSeries.map (Int.castRingHom K) etaProd =
      ∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.X ^ (n + 1)) := by
  rw [etaProd, (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).map_tprod
    (PowerSeries.map (Int.castRingHom K)) (continuous_map _ continuous_of_discreteTopology)]
  exact tprod_congr fun n => by rw [map_sub, map_one, map_pow, PowerSeries.map_X]

/--
@isnad1 id=eq.0h2v.s8.d439681b06a0 from=translated src=- shape=ed73665d vocab=9fa77189
-/
theorem rescale_tprod_one_sub_X_pow {K : Type*} [CommRing K] [TopologicalSpace K]
    [DiscreteTopology K] (a : K) :
    PowerSeries.rescale a (∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.X ^ (n + 1))) =
      ∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.C (a ^ (n + 1)) * PowerSeries.X ^ (n + 1)) := by
  rw [(PowerSeries.WithPiTopology.multipliable_one_sub_X_pow K).map_tprod (PowerSeries.rescale a)
    (continuous_rescale a)]
  exact tprod_congr fun n => by
    rw [map_sub, map_one, map_pow, PowerSeries.rescale_X, mul_pow, ← map_pow]

/--
@isnad1 id=eq.1h2v.s8.3c49280f4c79 from=translated src=- shape=269a6210 vocab=99bca1a0
-/
theorem expand_tprod_one_sub_X_pow {K : Type*} [CommRing K] [TopologicalSpace K] [T2Space K]
    (N : ℕ) (hN : N ≠ 0) :
    PowerSeries.expand N hN (∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.X ^ (n + 1))) =
      ∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.X ^ (N * (n + 1))) := by
  rw [(PowerSeries.WithPiTopology.multipliable_one_sub_X_pow K).map_tprod (PowerSeries.expand N hN)
    (continuous_expand N hN)]
  exact tprod_congr fun n => by rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]

/--
@isnad1 id=eq.1h4v.s8.b8b493de522e from=translated src=- shape=607c7a9d vocab=59ae2a12
-/
theorem prod_one_sub_root_mul {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] {μ : K}
    (hμ : IsPrimitiveRoot μ p) (Y : PowerSeries K) :
    ∏ b ∈ Finset.range p, ((1 : PowerSeries K) - PowerSeries.C (μ ^ b) * Y) = 1 - Y ^ p := by
  classical
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (PowerSeries.C : K → PowerSeries K) := fun a b hab => by
    simpa using congrArg PowerSeries.constantCoeff hab
  have hμ' : IsPrimitiveRoot (PowerSeries.C μ) p := hμ.map_of_injective hinj
  have h := hμ'.pow_sub_pow_eq_prod_sub_mul 1 Y hp.pos
  rw [one_pow] at h
  rw [h]
  have hset : Polynomial.nthRootsFinset p (1 : PowerSeries K) =
      (Finset.range p).image fun b => PowerSeries.C μ ^ b := by
    ext x
    rw [Polynomial.mem_nthRootsFinset hp.pos, Finset.mem_image]
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := hμ'.eq_pow_of_pow_eq_one hx
      exact ⟨i, Finset.mem_range.2 hi, rfl⟩
    · rintro ⟨i, -, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, hμ'.pow_eq_one, one_pow]
  rw [hset, Finset.prod_image fun i hi j hj hij =>
    hμ'.pow_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij]
  exact Finset.prod_congr rfl fun b _ => by rw [map_pow]

/--
@isnad1 id=eq.1h4v.s8.f87cb4daadad from=translated src=- shape=80cb434e vocab=e74ffd92
-/
theorem prod_twist_factor {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (m : ℕ) :
    ∏ b ∈ Finset.range p,
        ((1 : PowerSeries K) - PowerSeries.C ((ζ ^ b) ^ m) * PowerSeries.X ^ m) =
      if p ∣ m then ((1 : PowerSeries K) - PowerSeries.X ^ m) ^ p
      else (1 : PowerSeries K) - PowerSeries.X ^ (p * m) := by
  have hp : p.Prime := Fact.out
  split_ifs with hd
  · obtain ⟨k, rfl⟩ := hd
    rw [Finset.prod_congr rfl fun b _ => show
        (1 : PowerSeries K) - PowerSeries.C ((ζ ^ b) ^ (p * k)) * PowerSeries.X ^ (p * k) =
          1 - PowerSeries.X ^ (p * k) by
      rw [← pow_mul, mul_left_comm b p k, pow_mul, hζ.pow_eq_one, one_pow, map_one, one_mul],
      Finset.prod_const, Finset.card_range]
  · have hμ : IsPrimitiveRoot (ζ ^ m) p :=
      hζ.pow_of_coprime m (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hd))
    rw [Finset.prod_congr rfl fun b _ => show
        (1 : PowerSeries K) - PowerSeries.C ((ζ ^ b) ^ m) * PowerSeries.X ^ m =
          1 - PowerSeries.C ((ζ ^ m) ^ b) * PowerSeries.X ^ m by rw [← pow_mul, mul_comm b m, pow_mul],
      prod_one_sub_root_mul hμ, ← pow_mul, mul_comm m p]

def uFam (K : Type*) [CommRing K] (k n : ℕ) : PowerSeries K := 1 - PowerSeries.X ^ (k * (n + 1))

def hFam (K : Type*) [CommRing K] (p n : ℕ) : PowerSeries K :=
  if p ∣ n + 1 then 1 else 1 - PowerSeries.X ^ (p * (n + 1))

def gFam (K : Type*) [CommRing K] (p n : ℕ) : PowerSeries K :=
  if p ∣ n + 1 then (1 - PowerSeries.X ^ (n + 1)) ^ p else 1

def g'Fam (K : Type*) [CommRing K] (p n : ℕ) : PowerSeries K :=
  if p ∣ n + 1 then 1 - PowerSeries.X ^ (p * (n + 1)) else 1

def cFam (K : Type*) [CommRing K] (p n : ℕ) : PowerSeries K :=
  if p ∣ n + 1 then (1 - PowerSeries.X ^ (n + 1)) ^ p else 1 - PowerSeries.X ^ (p * (n + 1))

/--
@isnad1 id=eq.0h3v.s5.c7b666c35606 from=translated src=- shape=9a362019 vocab=21c6ea45
-/
theorem cFam_eq (K : Type*) [CommRing K] (p n : ℕ) : cFam K p n = hFam K p n * gFam K p n := by
  unfold cFam hFam gFam
  split_ifs <;> ring

/--
@isnad1 id=eq.0h3v.s5.88d2a25e0cb6 from=translated src=- shape=9a362019 vocab=dba737a3
-/
theorem uFam_eq (K : Type*) [CommRing K] (p n : ℕ) : uFam K p n = hFam K p n * g'Fam K p n := by
  unfold uFam hFam g'Fam
  split_ifs <;> ring

/--
@isnad1 id=le.1h2v.s5.71c4e5b59a4e from=translated src=- shape=99724977 vocab=923b6325
-/
theorem one_le_index {p : ℕ} (hp : 0 < p) (m : ℕ) : 1 ≤ p * (m + 1) :=
  Nat.one_le_iff_ne_zero.2 (mul_ne_zero hp.ne' (Nat.succ_ne_zero m))

/--
@isnad1 id=injectiv.1h1v.s5.708c80dbb9d3 from=translated src=- shape=43e46bc2 vocab=dcd65c7e
-/
theorem index_injective {p : ℕ} (hp : 0 < p) : Function.Injective fun m : ℕ => p * (m + 1) - 1 := by
  intro a b hab
  have h := (tsub_left_inj (one_le_index hp a) (one_le_index hp b)).1 hab
  have h' := Nat.eq_of_mul_eq_mul_left hp h
  omega

/--
@isnad1 id=le.1h3v.s6.b843433c61b0 from=translated src=- shape=e331f7b5 vocab=ecbc1925
-/
theorem mulSupport_subset_range {K : Type*} [CommRing K] {p : ℕ} (F : ℕ → PowerSeries K)
    (hF : ∀ n, ¬ p ∣ n + 1 → F n = 1) :
    Function.mulSupport F ⊆ Set.range fun m : ℕ => p * (m + 1) - 1 := by
  intro n hn
  rw [Function.mem_mulSupport] at hn
  by_cases hd : p ∣ n + 1
  · obtain ⟨k, hk⟩ := hd
    cases k with
    | zero => simp at hk
    | succ m => exact ⟨m, (Nat.eq_sub_of_add_eq hk).symm⟩
  · exact absurd (hF n hd) hn

section Multipliable

variable (K : Type*) [CommRing K] [TopologicalSpace K]

/--
@isnad1 id=multipli.1h2v.s5.1c88fb7d999e from=translated src=- shape=c6995b21 vocab=71e8cfc0
-/
theorem multipliable_uFam {k : ℕ} (hk : 0 < k) : Multipliable (uFam K k) :=
  multipliable_of_X_pow_dvd _ fun n => by
    rw [uFam, sub_sub_cancel_left, dvd_neg]
    exact pow_dvd_pow _ (Nat.le_mul_of_pos_left _ hk)

/--
@isnad1 id=multipli.1h2v.s5.fbc9662518dc from=translated src=- shape=c6995b21 vocab=2dc43e2f
-/
theorem multipliable_hFam {p : ℕ} (hp : 0 < p) : Multipliable (hFam K p) :=
  multipliable_of_X_pow_dvd _ fun n => by
    unfold hFam
    split_ifs
    · simp
    · rw [sub_sub_cancel_left, dvd_neg]
      exact pow_dvd_pow _ (Nat.le_mul_of_pos_left _ hp)

/--
@isnad1 id=multipli.0h2v.s4.ca66441969e6 from=translated src=- shape=3bff0faa vocab=0b0ef4b9
-/
theorem multipliable_gFam (p : ℕ) : Multipliable (gFam K p) :=
  multipliable_of_X_pow_dvd _ fun n => by
    unfold gFam
    split_ifs
    · have h1 : (PowerSeries.X : PowerSeries K) ^ (n + 1) ∣ (1 - PowerSeries.X ^ (n + 1)) - 1 :=
        ⟨-1, by ring⟩
      have h2 := sub_dvd_pow_sub_pow ((1 : PowerSeries K) - PowerSeries.X ^ (n + 1)) 1 p
      rw [one_pow] at h2
      exact h1.trans h2
    · simp

/--
@isnad1 id=multipli.1h2v.s5.a19e0424d38c from=translated src=- shape=c6995b21 vocab=8b75a498
-/
theorem multipliable_g'Fam {p : ℕ} (hp : 0 < p) : Multipliable (g'Fam K p) :=
  multipliable_of_X_pow_dvd _ fun n => by
    unfold g'Fam
    split_ifs
    · rw [sub_sub_cancel_left, dvd_neg]
      exact pow_dvd_pow _ (Nat.le_mul_of_pos_left _ hp)
    · simp

end Multipliable

section Topological

variable (K : Type*) [CommRing K] [TopologicalSpace K] [DiscreteTopology K]

/--
@isnad1 id=eq.1h2v.s6.68af410bf415 from=translated src=- shape=d9eac666 vocab=0965e0e3
-/
theorem tprod_gFam {p : ℕ} (hp : 0 < p) : ∏' n, gFam K p n = (∏' n, uFam K p n) ^ p := by
  have hsupp := mulSupport_subset_range (gFam K p) fun n hd => by
    unfold gFam; rw [ite_eq_right hd]
  rw [← (index_injective hp).tprod_eq hsupp, ← (multipliable_uFam K hp).tprod_pow]
  exact tprod_congr fun m => by
    show gFam K p (p * (m + 1) - 1) = uFam K p m ^ p
    unfold gFam uFam
    rw [Nat.sub_add_cancel (one_le_index hp m), ite_eq_left (dvd_mul_right p (m + 1))]

omit [DiscreteTopology K] in

/--
@isnad1 id=eq.1h2v.s6.88b287ed0e1a from=translated src=- shape=02d3576d vocab=fd93daeb
-/
theorem tprod_g'Fam {p : ℕ} (hp : 0 < p) : ∏' n, g'Fam K p n = ∏' n, uFam K (p * p) n := by
  have hsupp := mulSupport_subset_range (g'Fam K p) fun n hd => by
    unfold g'Fam; rw [ite_eq_right hd]
  rw [← (index_injective hp).tprod_eq hsupp]
  exact tprod_congr fun m => by
    show g'Fam K p (p * (m + 1) - 1) = uFam K (p * p) m
    unfold g'Fam uFam
    rw [Nat.sub_add_cancel (one_le_index hp m), ite_eq_left (dvd_mul_right p (m + 1)), mul_assoc]

/--
@isnad1 id=eq.1h2v.s7.88ce26134515 from=translated src=- shape=00df2e53 vocab=cc8a71f7
-/
theorem regroup {p : ℕ} (hp : 0 < p) :
    (∏' n, cFam K p n) * (∏' n, uFam K (p * p) n) = (∏' n, uFam K p n) ^ (p + 1) := by
  have hc : ∏' n, cFam K p n = (∏' n, hFam K p n) * ∏' n, gFam K p n := by
    rw [← (multipliable_hFam K hp).tprod_mul (multipliable_gFam K p)]
    exact tprod_congr fun n => cFam_eq K p n
  have hu : ∏' n, uFam K p n = (∏' n, hFam K p n) * ∏' n, g'Fam K p n := by
    rw [← (multipliable_hFam K hp).tprod_mul (multipliable_g'Fam K hp)]
    exact tprod_congr fun n => uFam_eq K p n
  rw [hc, tprod_gFam K hp, ← tprod_g'Fam K hp]
  calc (∏' n, hFam K p n) * (∏' n, uFam K p n) ^ p * ∏' n, g'Fam K p n
      = (∏' n, uFam K p n) ^ p * ((∏' n, hFam K p n) * ∏' n, g'Fam K p n) := by ring
    _ = (∏' n, uFam K p n) ^ (p + 1) := by rw [← hu, pow_succ]

end Topological

/--
@isnad1 id=eq.1h3v.s9.0e4378a0ea34 from=translated src=- shape=80709eac vocab=4a783e1a
-/
theorem etaNorm_powerSeries {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    (∏ b ∈ Finset.range p,
        PowerSeries.rescale (ζ ^ b) (PowerSeries.map (Int.castRingHom K) etaProd)) *
      PowerSeries.expand (p * p) (mul_ne_zero (NeZero.ne p) (NeZero.ne p))
        (PowerSeries.map (Int.castRingHom K) etaProd) =
    PowerSeries.expand p (NeZero.ne p) (PowerSeries.map (Int.castRingHom K) etaProd) ^ (p + 1) := by
  letI : TopologicalSpace K := ⊥
  haveI : DiscreteTopology K := ⟨rfl⟩
  have hp : p.Prime := Fact.out
  have hmult : ∀ b ∈ Finset.range p, Multipliable fun n : ℕ =>
      (1 : PowerSeries K) - PowerSeries.C ((ζ ^ b) ^ (n + 1)) * PowerSeries.X ^ (n + 1) :=
    fun b _ => multipliable_of_X_pow_dvd _ fun n => ⟨-PowerSeries.C ((ζ ^ b) ^ (n + 1)), by ring⟩
  rw [map_etaProd_eq_tprod K, expand_tprod_one_sub_X_pow, expand_tprod_one_sub_X_pow,
    Finset.prod_congr rfl fun b _ => rescale_tprod_one_sub_X_pow (ζ ^ b),
    ← Multipliable.tprod_finsetProd hmult, tprod_congr fun n => prod_twist_factor hζ (n + 1)]
  exact regroup K hp.pos

end ModularCurve.W1

namespace ModularCurve export _root_.ModularCurve (qTwist qTwist_coeff qTwist_single qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single etaProd constantCoeff_etaProd ofPowerSeries_coeff_of_neg) namespace StarBank end ModularCurve.StarBank
open scoped _root_.ModularCurve in

private theorem ModularCurve.StarBank.etaNorm {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    (∏ b ∈ Finset.range p,
        qTwist (ζ ^ b) (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd))) *
      qExpand K (p * p) (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd)) =
    qExpand K p (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd)) ^
      (p + 1) := by
  rw [ModularCurve.W1.qExpand_ofPowerSeries, ModularCurve.W1.qExpand_ofPowerSeries,
    Finset.prod_congr rfl fun b _ => ModularCurve.W1.qTwist_ofPowerSeries (ζ ^ b) _,
    ← map_prod, ← map_mul, ← map_pow]
  simp only [Units.val_pow_eq_pow_val]
  exact congrArg _ (ModularCurve.W1.etaNorm_powerSeries hζ)

namespace ModularCurve
export _root_.ModularCurve (qTwist qTwist_coeff qTwist_single qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single etaProd constantCoeff_etaProd ofPowerSeries_coeff_of_neg)
namespace W1
open _root_.ModularCurve

/--
@isnad1 id=eq.0h3v.s8.8872e7fd5be4 from=translated src=- shape=39abe6ff vocab=cac129aa
-/
theorem prod_single_one {K : Type*} [CommRing K] (s : Finset ℕ) (x : ℕ → K) :
    ∏ b ∈ s, HahnSeries.single (1 : ℤ) (x b) = HahnSeries.single (s.card : ℤ) (∏ b ∈ s, x b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, HahnSeries.single_mul_single,
      Finset.card_insert_of_notMem ha, Nat.cast_succ, add_comm (1 : ℤ)]

/--
@isnad1 id=eq.1h6v.s11.61d99d45eccc from=translated src=- shape=a0979976 vocab=af7d2a91
-/
theorem delta_bookkeeping {K : Type*} [Field K] (p : ℕ) (ε : K) (PT V1 V2 : LaurentSeries K)
    (hN : PT * V2 = V1 ^ (p + 1)) :
    HahnSeries.single (p : ℤ) ε * PT ^ 24 * (HahnSeries.single ((p * p : ℕ) : ℤ) (1 : K) * V2 ^ 24) =
      HahnSeries.C ε * (HahnSeries.single (p : ℤ) (1 : K) * V1 ^ 24) ^ (p + 1) := by
  have hs : HahnSeries.single (p : ℤ) ε * HahnSeries.single ((p * p : ℕ) : ℤ) (1 : K) =
      HahnSeries.C ε * HahnSeries.single (p : ℤ) (1 : K) ^ (p + 1) := by
    rw [HahnSeries.single_mul_single, HahnSeries.single_pow, HahnSeries.C_apply,
      HahnSeries.single_mul_single, mul_one, one_pow, mul_one,
      show (0 : ℤ) + (p + 1) • ((p : ℕ) : ℤ) = ((p : ℕ) : ℤ) + ((p * p : ℕ) : ℤ) by
        rw [nsmul_eq_mul]; push_cast; ring]
  calc HahnSeries.single (p : ℤ) ε * PT ^ 24 *
        (HahnSeries.single ((p * p : ℕ) : ℤ) (1 : K) * V2 ^ 24)
      = (HahnSeries.single (p : ℤ) ε * HahnSeries.single ((p * p : ℕ) : ℤ) (1 : K)) *
          (PT * V2) ^ 24 := by ring
    _ = HahnSeries.C ε * (HahnSeries.single (p : ℤ) (1 : K) * V1 ^ 24) ^ (p + 1) := by
        rw [hN, hs]; ring

end ModularCurve.W1

open scoped _root_.ModularCurve in

private theorem ModularCurve.StarBank.deltaNorm {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    (∏ b ∈ Finset.range p, qTwist (ζ ^ b)
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) *
      qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
    HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) *
      qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^
        (p + 1) := by
  have hN := ModularCurve.StarBank.etaNorm p ζ hζ
  have hT : ∀ b ∈ Finset.range p,
      qTwist (ζ ^ b) (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
        HahnSeries.single (1 : ℤ) ((ζ ^ b : Kˣ) : K) *
          qTwist (ζ ^ b)
            (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd)) ^ 24 :=
    fun b _ => by rw [map_mul, map_pow, qTwist_single, zpow_one, mul_one]
  rw [Finset.prod_congr rfl hT, Finset.prod_mul_distrib, Finset.prod_pow,
    ModularCurve.W1.prod_single_one, Finset.card_range, ← Units.coe_prod, map_mul, map_pow,
    qExpand_single, mul_one, map_mul, map_pow, qExpand_single, mul_one]
  exact ModularCurve.W1.delta_bookkeeping p _ _ _ _ hN

namespace ModularCurve
export _root_.ModularCurve (qTwist qTwist_coeff qTwist_single qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single etaProd constantCoeff_etaProd ofPowerSeries_coeff_of_neg)
namespace W1
open _root_.ModularCurve

end ModularCurve.W1

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_StarBank_deltaNorm.ModularCurve in

/--
@isnad1 id=eq.1h3v.s11.65f4d9b25eec from=translated src=- shape=71a6e502 vocab=4ba5fd84
-/
theorem solution {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    (∏ b ∈ Finset.range p, qTwist (ζ ^ b)
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) *
      qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
    HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) *
      qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^
        (p + 1) :=
  ModularCurve.StarBank.deltaNorm p ζ hζ

