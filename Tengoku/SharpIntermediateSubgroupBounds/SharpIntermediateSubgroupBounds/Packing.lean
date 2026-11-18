import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds.Escape
import Tengoku.Seed.Algebra.Order.BigOperators.GroupWithZero.Finset
import Tengoku.Seed.Data.Nat.Log
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Order
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Packing relative generating tuples

Raw tuples attached to distinct generated subgroups are disjoint.  Packing
them into the ambient tuple space converts relative escape into the
bandwise moment inequality and its cardinality corollaries.
-/

namespace SharpIntermediateSubgroupBounds

open scoped BigOperators

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

local instance packingSubgroupDecidableEq : DecidableEq (Subgroup G) := Classical.decEq _

/--
@isnad1 id=finite.0h1v.s3.55a88c868bab from=translated src=- shape=9499e9bc vocab=8ca526be
-/
local instance subgroupFinite : Finite (Subgroup G) :=
  Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective

/-- All intermediate subgroups above `H`.-/
def interval (H : Subgroup G) : Type u :=
  {K : Subgroup G // H ≤ K}

/-- The `r`-th multiplicative band in base `q`.-/
def band (H : Subgroup G) (q r : ℕ) : Type u :=
  {K : Subgroup G // H ≤ K ∧ q ^ r ≤ H.relIndex K ∧
    H.relIndex K < q ^ (r + 1)}

/-- The layer of intermediate subgroups having one fixed relative index.-/
def layer (H : Subgroup G) (m : ℕ) : Type u :=
  {K : Subgroup G // H ≤ K ∧ H.relIndex K = m}

instance intervalFintype (H : Subgroup G) : Fintype (interval H) := by
  letI : Finite (interval H) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

instance bandFintype (H : Subgroup G) (q r : ℕ) : Fintype (band H q r) := by
  letI : Finite (band H q r) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

instance layerFintype (H : Subgroup G) (m : ℕ) : Fintype (layer H m) := by
  letI : Finite (layer H m) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

instance rawRelGenFintype (H K : Subgroup G) (r : ℕ) :
    Fintype (RawRelGen H K r) := by
  letI : Finite (RawRelGen H K r) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- Forget the generated subgroup and retain only the raw tuple.-/
def packedRawMap (H : Subgroup G) (q r : ℕ) :
    (Σ K : band H q r, RawRelGen H K.1 r) → (Fin r → G) :=
  fun z => z.2.1

/--
@isnad1 id=injectiv.0h4v.s7.e9520423d58c from=translated src=- shape=65e733c4 vocab=3457b6fa
-/
theorem packedRawMap_injective (H : Subgroup G) (q r : ℕ) :
    Function.Injective (packedRawMap H q r) := by
  rintro ⟨K, x⟩ ⟨L, y⟩ hxy
  have htuple : x.1 = y.1 := hxy
  have hKLval : K.1 = L.1 := by
    rw [← x.2.2, ← y.2.2, htuple]
  have hKL : K = L := Subtype.ext hKLval
  subst L
  have hxy' : x = y := Subtype.ext htuple
  subst y
  rfl

/-- The raw relative-generating tuples for all targets in one band pack
injectively into the ambient tuple space.
@isnad1 id=le.0h4v.s7.c480b66dc66b from=translated src=- shape=22a736b6 vocab=07644e5a
-/
theorem packed_raw_card_bound (H : Subgroup G) (q r : ℕ) :
    (∑ K : band H q r, Nat.card (RawRelGen H K.1 r)) ≤ Nat.card G ^ r := by
  have hcard := Fintype.card_le_of_injective (packedRawMap H q r)
    (packedRawMap_injective H q r)
  rw [Fintype.card_sigma, Fintype.card_congr (Equiv.refl (Fin r → G))] at hcard
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin] using hcard

/-- Relative escape for one member of a `q`-band, allowing any
`2 ≤ q ≤ minFac [G:H]`.
@isnad1 id=le.3h5v.s8.7ccc119bddef from=translated src=- shape=b8fa3f65 vocab=b9b0598a
-/
theorem band_relative_escape_raw {H : Subgroup G} (hn : 1 < H.index)
    {q r : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (K : band H q r) :
    gammaQ q r * (Nat.card K.1 : ℚ) ^ r ≤
      (Nat.card (RawRelGen H K.1 r) : ℚ) := by
  have hupper : H.relIndex K.1 < H.index.minFac ^ (r + 1) :=
    K.2.2.2.trans_le (pow_le_pow_left' hqp _)
  apply le_trans
    (mul_le_mul_of_nonneg_right (gammaQ_mono_base hq hqp) (by positivity))
  exact relative_escape_raw hn K.2.1 hupper

/-- Summed raw-tuple escape bound before cancellation of `|H|^r`.
@isnad1 id=le.3h4v.s7.393100c207c4 from=translated src=- shape=b417a9bb vocab=68a02bb9
-/
theorem band_raw_sum_bound {H : Subgroup G} (hn : 1 < H.index)
    {q r : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) :
    gammaQ q r *
        (∑ K : band H q r, (Nat.card K.1 : ℚ) ^ r) ≤
      (Nat.card G : ℚ) ^ r := by
  calc
    gammaQ q r * (∑ K : band H q r, (Nat.card K.1 : ℚ) ^ r) =
        ∑ K : band H q r,
          gammaQ q r * (Nat.card K.1 : ℚ) ^ r := by
      rw [Finset.mul_sum]
    _ ≤ ∑ K : band H q r,
        (Nat.card (RawRelGen H K.1 r) : ℚ) :=
      Finset.sum_le_sum fun K _ => band_relative_escape_raw hn hq hqp K
    _ ≤ (Nat.card G : ℚ) ^ r := by
      exact_mod_cast packed_raw_card_bound H q r

/-- The bandwise moment theorem (Theorem 1.3), over the exact field `ℚ`.
The parameterized form includes the least-prime choice and the universal
choice `q = 2`.
@isnad1 id=le.3h4v.s7.c633de1e5bca from=translated src=- shape=2ad052d9 vocab=39871122
-/
theorem bandwise_moment {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) (r : ℕ) :
    gammaQ q r *
        (∑ K : band H q r, (H.relIndex K.1 : ℚ) ^ r) ≤
      (H.index : ℚ) ^ r := by
  have hraw := band_raw_sum_bound hn hq hqp (r := r)
  have hsum :
      (∑ K : band H q r, (Nat.card K.1 : ℚ) ^ r) =
        (Nat.card H : ℚ) ^ r *
          (∑ K : band H q r, (H.relIndex K.1 : ℚ) ^ r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro K hK
    rw [← card_mul_relIndex K.2.1, Nat.cast_mul, mul_pow]
  have hGcard : Nat.card H * H.index = Nat.card G := H.card_mul_index
  have hGpow :
      (Nat.card G : ℚ) ^ r =
        (Nat.card H : ℚ) ^ r * (H.index : ℚ) ^ r := by
    rw [← hGcard, Nat.cast_mul, mul_pow]
  have hHpos : (0 : ℚ) < (Nat.card H : ℚ) ^ r :=
    pow_pos (Nat.cast_pos.mpr Nat.card_pos) _
  apply le_of_mul_le_mul_left _ hHpos
  calc
    (Nat.card H : ℚ) ^ r *
          (gammaQ q r *
            (∑ K : band H q r, (H.relIndex K.1 : ℚ) ^ r)) =
        gammaQ q r *
          (∑ K : band H q r, (Nat.card K.1 : ℚ) ^ r) := by
      rw [hsum]
      ring
    _ ≤ (Nat.card G : ℚ) ^ r := hraw
    _ = (Nat.card H : ℚ) ^ r * (H.index : ℚ) ^ r := hGpow

/-- Denominator-cleared natural-number form of the bandwise moment
theorem.
@isnad1 id=le.3h4v.s7.16b79daa953b from=translated src=- shape=39672fe4 vocab=a97c355d
-/
theorem bandwise_moment_nat {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) (r : ℕ) :
    gammaNum q r *
        (∑ K : band H q r, H.relIndex K.1 ^ r) ≤
      gammaDen q r * H.index ^ r := by
  have hdenPos : 0 < gammaDen q r := pow_pos (by omega) _
  have h := bandwise_moment hn hq hqp r
  rw [gammaQ] at h
  have hqRat :
      (gammaNum q r : ℚ) *
          (∑ K : band H q r, H.relIndex K.1 ^ r) ≤
        (gammaDen q r : ℚ) * (H.index : ℚ) ^ r := by
    calc
      (gammaNum q r : ℚ) *
            (∑ K : band H q r, H.relIndex K.1 ^ r) =
          (gammaDen q r : ℚ) *
            ((gammaNum q r : ℚ) / gammaDen q r *
              (∑ K : band H q r,
                (H.relIndex K.1 : ℚ) ^ r)) := by
        simp only [Nat.cast_sum, Nat.cast_pow]
        field_simp
      _ ≤ (gammaDen q r : ℚ) * (H.index : ℚ) ^ r :=
        mul_le_mul_of_nonneg_left h (by positivity)
  exact_mod_cast hqRat

/-- Every term in a band contributes at least `q^(r^2)` to its `r`-th
moment.
@isnad1 id=le.0h4v.s7.ce919cbe87a6 from=translated src=- shape=dd79b576 vocab=c6750af4
-/
theorem band_card_mul_pow_le_moment (H : Subgroup G) (q r : ℕ) :
    Nat.card (band H q r) * q ^ (r * r) ≤
      ∑ K : band H q r, H.relIndex K.1 ^ r := by
  have hsum : (∑ _K : band H q r, q ^ (r * r)) ≤
      ∑ K : band H q r, H.relIndex K.1 ^ r := by
    apply Finset.sum_le_sum
    intro K hK
    change q ^ (r * r) ≤ H.relIndex K.1 ^ r
    rw [pow_mul]
    exact pow_le_pow_left' K.2.2.1 _
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card (band H q r) * q ^ (r * r) =
        ∑ _K : band H q r, q ^ (r * r) := by
      simp [Nat.mul_comm]
    _ ≤ ∑ K : band H q r, H.relIndex K.1 ^ r := hsum

/-- Denominator-cleared band-cardinality bound (Corollary 3.1).
@isnad1 id=le.3h4v.s6.3230b867230b from=translated src=- shape=4607e0ef vocab=cf943cb7
-/
theorem band_card_bound_nat {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) (r : ℕ) :
    gammaNum q r * (Nat.card (band H q r) * q ^ (r * r)) ≤
      gammaDen q r * H.index ^ r := by
  exact (Nat.mul_le_mul_left _ (band_card_mul_pow_le_moment H q r)).trans
    (bandwise_moment_nat hn hq hqp r)

/-- Division form of the band-cardinality bound.
@isnad1 id=le.3h4v.s6.50f2dd25485e from=translated src=- shape=73f51af4 vocab=629e9a15
-/
theorem band_card_bound {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) (r : ℕ) :
    (Nat.card (band H q r) : ℚ) ≤
      (H.index : ℚ) ^ r /
        (gammaQ q r * (q : ℚ) ^ (r * r)) := by
  have hmass := band_card_mul_pow_le_moment H q r
  have hmoment := bandwise_moment hn hq hqp r
  have hgamma : 0 < gammaQ q r := gammaQ_pos hq
  have hqpow : (0 : ℚ) < (q : ℚ) ^ (r * r) := by positivity
  apply (le_div_iff₀ (mul_pos hgamma hqpow)).2
  calc
    (Nat.card (band H q r) : ℚ) *
          (gammaQ q r * (q : ℚ) ^ (r * r)) =
        gammaQ q r *
          ((Nat.card (band H q r) : ℚ) * (q : ℚ) ^ (r * r)) := by
      ring
    _ ≤ gammaQ q r *
          (∑ K : band H q r, (H.relIndex K.1 : ℚ) ^ r) := by
      apply mul_le_mul_of_nonneg_left _ hgamma.le
      exact_mod_cast hmass
    _ ≤ (H.index : ℚ) ^ r := hmoment

/-- The zeroth band contains only its bottom subgroup.
@isnad1 id=eq.2h4v.s7.12b4a30c7cec from=translated src=- shape=83797935 vocab=a2197690
-/
theorem band_zero_eq_bottom {H : Subgroup G} {q : ℕ}
    (hq : 1 < q) (hqp : q ≤ H.index.minFac) (K : band H q 0) :
    K.1 = H := by
  by_contra hne
  have hlt : H < K.1 := lt_of_le_of_ne K.2.1 (Ne.symm hne)
  have hmin : H.index.minFac ≤ H.relIndex K.1 :=
    minFac_le_relIndex_of_lt (le_refl H) hlt
  have hupper : H.relIndex K.1 < q := by
    simpa using K.2.2.2
  omega

/-- Any two members of the zeroth band coincide.
@isnad1 id=eq.2h5v.s6.b644ac4cca57 from=translated src=- shape=8e897020 vocab=5dbd9c9e
-/
theorem band_zero_subsingleton {H : Subgroup G} {q : ℕ}
    (hq : 1 < q) (hqp : q ≤ H.index.minFac) (K L : band H q 0) :
    K = L := by
  apply Subtype.ext
  rw [band_zero_eq_bottom hq hqp K, band_zero_eq_bottom hq hqp L]

/-- The zeroth band has cardinality exactly one.
@isnad1 id=eq.2h3v.s5.c91fbbe3267c from=translated src=- shape=957b493b vocab=162016d9
-/
theorem band_zero_card_eq_one {H : Subgroup G} {q : ℕ}
    (hq : 1 < q) (hqp : q ≤ H.index.minFac) :
    Nat.card (band H q 0) = 1 := by
  let b : band H q 0 := ⟨H, le_rfl, by simp, by simpa using hq⟩
  let e : band H q 0 ≃ PUnit.{u + 1} :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => b
      left_inv := fun K => (band_zero_subsingleton hq hqp K b).symm
      right_inv := by intro z; cases z; rfl }
  rw [Nat.card_congr e]
  simp

/-- Canonical band containing an intermediate subgroup.-/
def intervalToBandSigma (H : Subgroup G) (q : ℕ) (hn : 1 < H.index)
    (hq : 1 < q) :
    interval H → Σ r : Fin (Nat.log q H.index + 1), band H q r.1 :=
  fun K => by
    let m := H.relIndex K.1
    have hm0 : m ≠ 0 := by
      letI : H.IsFiniteRelIndex K.1 := H.isFiniteRelIndex_of_finiteIndex
      exact Subgroup.relIndex_ne_zero
    have hmn : m ≤ H.index :=
      Nat.le_of_dvd (by omega) (H.relIndex_dvd_index_of_le K.2)
    have hrle : Nat.log q m ≤ Nat.log q H.index := Nat.log_mono_right hmn
    let r : Fin (Nat.log q H.index + 1) :=
      ⟨Nat.log q m, Nat.lt_succ_of_le hrle⟩
    exact ⟨r, ⟨K.1, K.2, Nat.pow_log_le_self q hm0,
      Nat.lt_pow_succ_log_self hq m⟩⟩

/-- Forget the band index.-/
def bandSigmaToInterval (H : Subgroup G) (q : ℕ) :
    (Σ r : Fin (Nat.log q H.index + 1), band H q r.1) → interval H :=
  fun z => ⟨z.2.1, z.2.2.1⟩

/--
@isnad1 id=eq.2h4v.s5.9515376d6939 from=translated src=- shape=2047074d vocab=862f2223
-/
@[simp]
theorem bandSigmaToInterval_intervalToBandSigma (H : Subgroup G) (q : ℕ)
    (hn : 1 < H.index) (hq : 1 < q) (K : interval H) :
    bandSigmaToInterval H q (intervalToBandSigma H q hn hq K) = K := by
  apply Subtype.ext
  rfl

/--
@isnad1 id=injectiv.2h3v.s6.e42ea0c0e703 from=translated src=- shape=d28db933 vocab=419fe8df
-/
theorem intervalToBandSigma_injective (H : Subgroup G) (q : ℕ)
    (hn : 1 < H.index) (hq : 1 < q) :
    Function.Injective (intervalToBandSigma H q hn hq) := by
  intro K L h
  have := congrArg (bandSigmaToInterval H q) h
  simpa using this

/-- Every intermediate subgroup lies in a unique band through
`floor(log_q [G:H])`.
@isnad1 id=existsun.2h4v.s7.ee6bf023011e from=translated src=- shape=85a04cfa vocab=69a93bf9
-/
theorem intermediate_unique_band (H : Subgroup G) (q : ℕ)
    (hn : 1 < H.index) (hq : 1 < q) (K : interval H) :
    ∃! r : Fin (Nat.log q H.index + 1),
      q ^ (r : ℕ) ≤ H.relIndex K.1 ∧
        H.relIndex K.1 < q ^ ((r : ℕ) + 1) := by
  let m := H.relIndex K.1
  have hm0 : m ≠ 0 := by
    letI : H.IsFiniteRelIndex K.1 := H.isFiniteRelIndex_of_finiteIndex
    exact Subgroup.relIndex_ne_zero
  have hmn : m ≤ H.index :=
    Nat.le_of_dvd (by omega) (H.relIndex_dvd_index_of_le K.2)
  have hrle : Nat.log q m ≤ Nat.log q H.index := Nat.log_mono_right hmn
  refine ⟨⟨Nat.log q m, Nat.lt_succ_of_le hrle⟩, ?_, ?_⟩
  · exact ⟨Nat.pow_log_le_self q hm0, Nat.lt_pow_succ_log_self hq m⟩
  · intro r hr
    apply Fin.ext
    exact (Nat.log_eq_of_pow_le_of_lt_pow hr.1 hr.2).symm

/-- Exact finite sum appearing in the interval bound.-/
def finiteUQ (n q : ℕ) : ℚ :=
  ∑ r : Fin (Nat.log q n + 1),
    (n : ℚ) ^ (r : ℕ) /
      (gammaQ q (r : ℕ) * (q : ℚ) ^ ((r : ℕ) * (r : ℕ)))

/-- Finite `U` bound for the whole interval.
@isnad1 id=le.3h3v.s6.973f38ffaa0b from=translated src=- shape=8ebeb6d1 vocab=69fd52db
-/
theorem finiteU_bound {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) :
    (Nat.card (interval H) : ℚ) ≤ finiteUQ H.index q := by
  have hcardNat : Fintype.card (interval H) ≤
      Fintype.card (Σ r : Fin (Nat.log q H.index + 1), band H q r.1) :=
    Fintype.card_le_of_injective (intervalToBandSigma H q hn hq)
      (intervalToBandSigma_injective H q hn hq)
  have hcard : (Nat.card (interval H) : ℚ) ≤
      ∑ r : Fin (Nat.log q H.index + 1),
        (Nat.card (band H q (r : ℕ)) : ℚ) := by
    rw [Nat.card_eq_fintype_card]
    simp_rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_sigma] at hcardNat
    exact_mod_cast hcardNat
  calc
    (Nat.card (interval H) : ℚ) ≤
        ∑ r : Fin (Nat.log q H.index + 1),
          (Nat.card (band H q (r : ℕ)) : ℚ) := hcard
    _ ≤ ∑ r : Fin (Nat.log q H.index + 1),
        (H.index : ℚ) ^ (r : ℕ) /
          (gammaQ q (r : ℕ) *
            (q : ℚ) ^ ((r : ℕ) * (r : ℕ))) :=
      Finset.sum_le_sum fun r _ => band_card_bound hn hq hqp (r : ℕ)
    _ = finiteUQ H.index q := rfl

/-- Forgetful packing map for one exact-index layer.-/
def packedLayerRawMap (H : Subgroup G) (m r : ℕ) :
    (Σ K : layer H m, RawRelGen H K.1 r) → (Fin r → G) :=
  fun z => z.2.1

/--
@isnad1 id=injectiv.0h4v.s6.67bffb32a507 from=translated src=- shape=208448ea vocab=015faeef
-/
theorem packedLayerRawMap_injective (H : Subgroup G) (m r : ℕ) :
    Function.Injective (packedLayerRawMap H m r) := by
  rintro ⟨K, x⟩ ⟨L, y⟩ hxy
  have htuple : x.1 = y.1 := hxy
  have hKLval : K.1 = L.1 := by
    rw [← x.2.2, ← y.2.2, htuple]
  have hKL : K = L := Subtype.ext hKLval
  subst L
  have hxy' : x = y := Subtype.ext htuple
  subst y
  rfl

/--
@isnad1 id=le.0h4v.s6.3afcc6a8a5a5 from=translated src=- shape=96ebfadd vocab=af98cd45
-/
theorem packed_layer_raw_card_bound (H : Subgroup G) (m r : ℕ) :
    (∑ K : layer H m, Nat.card (RawRelGen H K.1 r)) ≤ Nat.card G ^ r := by
  have hcard := Fintype.card_le_of_injective (packedLayerRawMap H m r)
    (packedLayerRawMap_injective H m r)
  rw [Fintype.card_sigma, Fintype.card_congr (Equiv.refl (Fin r → G))] at hcard
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin] using hcard

/--
@isnad1 id=le.4h6v.s7.c047a95b0444 from=translated src=- shape=2bc24708 vocab=eff01df1
-/
theorem layer_relative_escape_raw {H : Subgroup G} (hn : 1 < H.index)
    {q r m : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (hmi : m < q ^ (r + 1)) (K : layer H m) :
    gammaQ q r * (Nat.card K.1 : ℚ) ^ r ≤
      (Nat.card (RawRelGen H K.1 r) : ℚ) := by
  have hupper : H.relIndex K.1 < H.index.minFac ^ (r + 1) := by
    rw [K.2.2]
    exact hmi.trans_le (pow_le_pow_left' hqp _)
  apply le_trans
    (mul_le_mul_of_nonneg_right (gammaQ_mono_base hq hqp) (by positivity))
  exact relative_escape_raw hn K.2.1 hupper

/--
@isnad1 id=le.4h5v.s7.f5d0f6ee5a3e from=translated src=- shape=fecbd8d9 vocab=b73d300c
-/
theorem layer_raw_sum_bound {H : Subgroup G} (hn : 1 < H.index)
    {q r m : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (hmi : m < q ^ (r + 1)) :
    gammaQ q r *
        (∑ K : layer H m, (Nat.card K.1 : ℚ) ^ r) ≤
      (Nat.card G : ℚ) ^ r := by
  calc
    gammaQ q r * (∑ K : layer H m, (Nat.card K.1 : ℚ) ^ r) =
        ∑ K : layer H m,
          gammaQ q r * (Nat.card K.1 : ℚ) ^ r := by
      rw [Finset.mul_sum]
    _ ≤ ∑ K : layer H m,
        (Nat.card (RawRelGen H K.1 r) : ℚ) :=
      Finset.sum_le_sum fun K _ => layer_relative_escape_raw hn hq hqp hmi K
    _ ≤ (Nat.card G : ℚ) ^ r := by
      exact_mod_cast packed_layer_raw_card_bound H m r

/-- Rational layer bound retaining the exact index `m`.
@isnad1 id=le.4h5v.s7.ade7f881e59c from=translated src=- shape=a2aede51 vocab=163f94f8
-/
theorem layer_card_moment {H : Subgroup G} (hn : 1 < H.index)
    {q r m : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (hmi : m < q ^ (r + 1)) :
    gammaQ q r * (Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r ≤
      (H.index : ℚ) ^ r := by
  have hraw := layer_raw_sum_bound hn hq hqp hmi
  have hsum :
      (∑ K : layer H m, (Nat.card K.1 : ℚ) ^ r) =
        (Nat.card H : ℚ) ^ r *
          (∑ K : layer H m, (H.relIndex K.1 : ℚ) ^ r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro K hK
    rw [← card_mul_relIndex K.2.1, Nat.cast_mul, mul_pow]
  have hlayerSum :
      (∑ K : layer H m, (H.relIndex K.1 : ℚ) ^ r) =
        (Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r := by
    calc
      (∑ K : layer H m, (H.relIndex K.1 : ℚ) ^ r) =
          ∑ _K : layer H m, (m : ℚ) ^ r := by
        apply Finset.sum_congr rfl
        intro K hK
        rw [K.2.2]
      _ = (Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r := by
        simp [Nat.card_eq_fintype_card]
  have hGcard : Nat.card H * H.index = Nat.card G := H.card_mul_index
  have hGpow :
      (Nat.card G : ℚ) ^ r =
        (Nat.card H : ℚ) ^ r * (H.index : ℚ) ^ r := by
    rw [← hGcard, Nat.cast_mul, mul_pow]
  have hHpos : (0 : ℚ) < (Nat.card H : ℚ) ^ r :=
    pow_pos (Nat.cast_pos.mpr Nat.card_pos) _
  apply le_of_mul_le_mul_left _ hHpos
  calc
    (Nat.card H : ℚ) ^ r *
          (gammaQ q r * (Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r) =
        gammaQ q r *
          (∑ K : layer H m, (Nat.card K.1 : ℚ) ^ r) := by
      rw [hsum, hlayerSum]
      ring
    _ ≤ (Nat.card G : ℚ) ^ r := hraw
    _ = (Nat.card H : ℚ) ^ r * (H.index : ℚ) ^ r := hGpow

/-- Denominator-cleared exact layer bound (Corollary 3.1).
@isnad1 id=le.4h5v.s7.bff0cbd94b6d from=translated src=- shape=6f21d81f vocab=fb996e13
-/
theorem layer_card_bound_nat {H : Subgroup G} (hn : 1 < H.index)
    {q r m : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (hmi : m < q ^ (r + 1)) :
    gammaNum q r * (Nat.card (layer H m) * m ^ r) ≤
      gammaDen q r * H.index ^ r := by
  have hdenPos : 0 < gammaDen q r := pow_pos (by omega) _
  have h := layer_card_moment hn hq hqp hmi
  rw [gammaQ] at h
  have hqRat :
      (gammaNum q r : ℚ) *
          ((Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r) ≤
        (gammaDen q r : ℚ) * (H.index : ℚ) ^ r := by
    calc
      (gammaNum q r : ℚ) *
            ((Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r) =
          (gammaDen q r : ℚ) *
            ((gammaNum q r : ℚ) / gammaDen q r *
              (Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r) := by
        field_simp
      _ ≤ (gammaDen q r : ℚ) * (H.index : ℚ) ^ r :=
        mul_le_mul_of_nonneg_left h (by positivity)
  exact_mod_cast hqRat

/-- Literal division form of the exact-layer clause of Corollary 3.1.
The hypotheses place the fixed index `m` in band `r`.
@isnad1 id=le.5h5v.s7.0fdf278474dc from=translated src=- shape=75013c4a vocab=5033cd6c
-/
theorem layer_card_bound {H : Subgroup G} (hn : 1 < H.index)
    {q r m : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (hlo : q ^ r ≤ m) (hhi : m < q ^ (r + 1)) :
    (Nat.card (layer H m) : ℚ) ≤
      (H.index : ℚ) ^ r /
        (gammaQ q r * (m : ℚ) ^ r) := by
  have hmPos : 0 < m := lt_of_lt_of_le (pow_pos (by omega) r) hlo
  have hdenPos : (0 : ℚ) < gammaQ q r * (m : ℚ) ^ r :=
    mul_pos (gammaQ_pos hq) (pow_pos (Nat.cast_pos.mpr hmPos) _)
  apply (le_div_iff₀ hdenPos).2
  calc
    (Nat.card (layer H m) : ℚ) *
          (gammaQ q r * (m : ℚ) ^ r) =
        gammaQ q r * (Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r := by
      ring
    _ ≤ (H.index : ℚ) ^ r := layer_card_moment hn hq hqp hhi

/-! ## The elementary generating bound -/

/-- The free right `H^r`-translation of one relative generating tuple.-/
def rawHTranslate {H K : Subgroup G} {r : ℕ} (hHK : H ≤ K)
    (x : RawRelGen H K r) : (Fin r → H) → RawRelGen H K r :=
  fun h => ⟨fun i => x.1 i * (h i : G),
    fun i => K.mul_mem (x.2.1 i) (hHK (h i).2), by
      rw [generatedFrom_mul_right H x.1 h, x.2.2]⟩

/--
@isnad1 id=injectiv.1h5v.s6.7ba8118d1994 from=translated src=- shape=6b8a588b vocab=a3f013fe
-/
theorem rawHTranslate_injective {H K : Subgroup G} {r : ℕ}
    (hHK : H ≤ K) (x : RawRelGen H K r) :
    Function.Injective (rawHTranslate hHK x) := by
  intro h k heq
  funext i
  apply Subtype.ext
  have hi := congrFun (congrArg Subtype.val heq) i
  exact mul_left_cancel hi

/-- A single relative generating tuple yields `|H|^r` distinct raw tuples.
@isnad1 id=le.1h5v.s6.882b79a602da from=translated src=- shape=75674bc6 vocab=0b688a38
-/
theorem cardH_pow_le_rawRelGen {H K : Subgroup G} {r : ℕ}
    (hHK : H ≤ K) (x : RawRelGen H K r) :
    Nat.card H ^ r ≤ Nat.card (RawRelGen H K r) := by
  letI : Fintype H := Fintype.ofFinite H
  have hcard := Fintype.card_le_of_injective (rawHTranslate hHK x)
    (rawHTranslate_injective hHK x)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simpa only [Fintype.card_fun, Fintype.card_fin] using hcard

/--
@isnad1 id=nonempty.0h4v.s4.9f2f41e4852e from=translated src=- shape=818cc01b vocab=fa98665c
-/
theorem escapePath_nonempty (K : Subgroup G) (r : ℕ) (s : EscapeState K) :
    Nonempty (EscapePath K r s) := by
  induction r generalizing s with
  | zero => exact ⟨PUnit.unit⟩
  | succ r ih =>
      obtain ⟨x⟩ := escapeChoiceNonempty K s
      obtain ⟨z⟩ := ih (escapeNext K s x)
      exact ⟨escapeCons K x z⟩

/-- Every intermediate subgroup has a relative generating tuple whose
length is `floor(log₂ [G:H])`.-/
def elementaryRawTuple (H : Subgroup G) (hn : 1 < H.index)
    (K : interval H) :
    RawRelGen H K.1 (Nat.log 2 H.index) := by
  let r := Nat.log 2 H.index
  let z : EscapePath K.1 r ⟨H, K.2⟩ :=
    Classical.choice (escapePath_nonempty K.1 r ⟨H, K.2⟩)
  have hmle : H.relIndex K.1 ≤ H.index :=
    Nat.le_of_dvd (by omega) (H.relIndex_dvd_index_of_le K.2)
  have hnlt : H.index < 2 ^ (r + 1) := by
    exact Nat.lt_pow_succ_log_self (by omega) H.index
  have hp2 : 2 ≤ H.index.minFac :=
    (Nat.minFac_prime (by omega : H.index ≠ 1)).two_le
  have hupper : H.relIndex K.1 < H.index.minFac ^ (r + 1) :=
    (hmle.trans_lt hnlt).trans_le (pow_le_pow_left' hp2 _)
  exact ⟨escapeTuple K.1 z, escapeTuple_mem K.1 z, by
    rw [← escapeEnd_eq_generatedFrom K.1 K.2 z]
    exact escapeEnd_eq_target K.2 hupper z⟩

/-- Raw tuples for all intermediate targets pack into the ambient tuple
space.-/
def packedIntervalRawMap (H : Subgroup G) (r : ℕ) :
    (Σ K : interval H, RawRelGen H K.1 r) → (Fin r → G) :=
  fun z => z.2.1

/--
@isnad1 id=injectiv.0h3v.s6.9675301a346a from=translated src=- shape=980665e1 vocab=0b34ee29
-/
theorem packedIntervalRawMap_injective (H : Subgroup G) (r : ℕ) :
    Function.Injective (packedIntervalRawMap H r) := by
  rintro ⟨K, x⟩ ⟨L, y⟩ hxy
  have htuple : x.1 = y.1 := hxy
  have hKLval : K.1 = L.1 := by
    rw [← x.2.2, ← y.2.2, htuple]
  have hKL : K = L := Subtype.ext hKLval
  subst L
  have hxy' : x = y := Subtype.ext htuple
  subst y
  rfl

/--
@isnad1 id=le.0h3v.s6.b4e54ec288ca from=translated src=- shape=e043d33a vocab=54889cb0
-/
theorem packed_interval_raw_card_bound (H : Subgroup G) (r : ℕ) :
    (∑ K : interval H, Nat.card (RawRelGen H K.1 r)) ≤ Nat.card G ^ r := by
  have hcard := Fintype.card_le_of_injective (packedIntervalRawMap H r)
    (packedIntervalRawMap_injective H r)
  rw [Fintype.card_sigma, Fintype.card_congr (Equiv.refl (Fin r → G))] at hcard
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin] using hcard

/-- The elementary generating-set estimate from the introduction.
@isnad1 id=le.1h2v.s5.081652fb9fa5 from=translated src=- shape=e9cdb1f9 vocab=424eb388
-/
theorem elementary_interval_bound {H : Subgroup G} (hn : 1 < H.index) :
    Nat.card (interval H) ≤ H.index ^ Nat.log 2 H.index := by
  let r := Nat.log 2 H.index
  have heach : ∀ K : interval H,
      Nat.card H ^ r ≤ Nat.card (RawRelGen H K.1 r) := fun K =>
    cardH_pow_le_rawRelGen K.2 (elementaryRawTuple H hn K)
  have hlower : Nat.card (interval H) * Nat.card H ^ r ≤
      ∑ K : interval H, Nat.card (RawRelGen H K.1 r) := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card (interval H) * Nat.card H ^ r =
          ∑ _K : interval H, Nat.card H ^ r := by
        simp
      _ ≤ ∑ K : interval H, Nat.card (RawRelGen H K.1 r) :=
        Finset.sum_le_sum fun K _ => heach K
  have hpack := packed_interval_raw_card_bound H r
  have htotal := hlower.trans hpack
  have hGcard : Nat.card H * H.index = Nat.card G := H.card_mul_index
  have hGpow : Nat.card G ^ r = Nat.card H ^ r * H.index ^ r := by
    rw [← hGcard, mul_pow]
  rw [hGpow] at htotal
  change Nat.card (interval H) ≤ H.index ^ r
  exact Nat.le_of_mul_le_mul_left (c := Nat.card H ^ r)
    (by simpa [Nat.mul_comm] using htotal)
    (pow_pos Nat.card_pos _)

/-- The interval above the top subgroup is a singleton.
@isnad1 id=eq.0h1v.s4.3a624031c56d from=translated src=- shape=ce6accb4 vocab=327077c7
-/
theorem interval_top_card_eq_one :
    Nat.card (interval (⊤ : Subgroup G)) = 1 := by
  let e : interval (⊤ : Subgroup G) ≃ PUnit.{u + 1} :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ⟨⊤, le_rfl⟩
      left_inv := by
        intro K
        apply Subtype.ext
        exact (top_unique K.2).symm
      right_inv := by intro z; cases z; rfl }
  rw [Nat.card_congr e]
  simp

/-- All-index form of the elementary generating bound, including the
degenerate index-one interval.
@isnad1 id=le.0h2v.s5.6411766e9317 from=translated src=- shape=871276c3 vocab=38e44abd
-/
theorem elementary_interval_bound_all (H : Subgroup G) :
    Nat.card (interval H) ≤ H.index ^ Nat.log 2 H.index := by
  by_cases hn : 1 < H.index
  · exact elementary_interval_bound hn
  · have hpos : 0 < H.index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hi : H.index = 1 := by omega
    have htop : H = ⊤ := Subgroup.index_eq_one.mp hi
    subst H
    rw [interval_top_card_eq_one]
    simp

/-! ## Removing the two endpoints -/

/-- Strict intermediate subgroups.-/
def strictIntermediate (H : Subgroup G) : Type u :=
  {K : Subgroup G // H < K ∧ K < ⊤}

instance strictIntermediateFintype (H : Subgroup G) :
    Fintype (strictIntermediate H) := by
  letI : Finite (strictIntermediate H) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

def intervalStrictEncode (H : Subgroup G) (K : interval H) :
    strictIntermediate H ⊕ Bool :=
  if hKH : K.1 = H then Sum.inr false
  else if hKG : K.1 = ⊤ then Sum.inr true
  else Sum.inl ⟨K.1, lt_of_le_of_ne K.2 (Ne.symm hKH),
    lt_of_le_of_ne le_top hKG⟩

def intervalStrictDecode (H : Subgroup G) :
    strictIntermediate H ⊕ Bool → interval H
  | Sum.inl K => ⟨K.1, K.2.1.le⟩
  | Sum.inr false => ⟨H, le_rfl⟩
  | Sum.inr true => ⟨⊤, le_top⟩

/--
@isnad1 id=eq.0h3v.s5.25699ab2a48b from=translated src=- shape=42333f9b vocab=c878969c
-/
theorem intervalStrictDecode_encode (H : Subgroup G) (K : interval H) :
    intervalStrictDecode H (intervalStrictEncode H K) = K := by
  by_cases hKH : K.1 = H
  · rw [intervalStrictEncode, dite_eq_left hKH]
    change (⟨H, le_rfl⟩ : interval H) = K
    exact Subtype.ext hKH.symm
  · by_cases hKG : K.1 = ⊤
    · rw [intervalStrictEncode, dite_eq_right hKH, dite_eq_left hKG]
      change (⟨⊤, le_top⟩ : interval H) = K
      exact Subtype.ext hKG.symm
    · rw [intervalStrictEncode, dite_eq_right hKH, dite_eq_right hKG]
      rfl

/--
@isnad1 id=eq.1h3v.s5.2d8123c39037 from=translated src=- shape=90f4f4ed vocab=55353628
-/
theorem intervalStrictEncode_decode (H : Subgroup G) (hHt : H < ⊤)
    (z : strictIntermediate H ⊕ Bool) :
    intervalStrictEncode H (intervalStrictDecode H z) = z := by
  cases z with
  | inl K =>
      have hKH : K.1 ≠ H := K.2.1.ne'
      have hKG : K.1 ≠ ⊤ := K.2.2.ne
      change (if hKH' : K.1 = H then Sum.inr false
        else if hKG' : K.1 = ⊤ then Sum.inr true
        else Sum.inl ⟨K.1, lt_of_le_of_ne K.2.1.le (Ne.symm hKH'),
          lt_of_le_of_ne le_top hKG'⟩) = Sum.inl K
      rw [dite_eq_right hKH, dite_eq_right hKG]
      congr
  | inr b =>
      cases b
      · simp [intervalStrictEncode, intervalStrictDecode]
      · simp [intervalStrictEncode, intervalStrictDecode, hHt.ne.symm]

/-- The interval splits as its strict interior together with its two
distinct endpoints.-/
def intervalStrictEquiv (H : Subgroup G) (hHt : H < ⊤) :
    interval H ≃ strictIntermediate H ⊕ Bool where
  toFun := intervalStrictEncode H
  invFun := intervalStrictDecode H
  left_inv := intervalStrictDecode_encode H
  right_inv := intervalStrictEncode_decode H hHt

/--
@isnad1 id=eq.1h2v.s5.b16d370cae49 from=translated src=- shape=b629ff0f vocab=70c844d9
-/
theorem strictIntermediate_card_add_two (H : Subgroup G) (hHt : H < ⊤) :
    Nat.card (strictIntermediate H) + 2 = Nat.card (interval H) := by
  letI : Fintype (strictIntermediate H ⊕ Bool) := inferInstance
  have hcard := Fintype.card_congr (intervalStrictEquiv H hHt)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simpa using hcard.symm

/--
@isnad1 id=eq.1h2v.s5.e35a49547b85 from=translated src=- shape=0dcec05b vocab=1103e63a
-/
theorem strictIntermediate_card_eq_sub_two (H : Subgroup G) (hHt : H < ⊤) :
    Nat.card (strictIntermediate H) = Nat.card (interval H) - 2 := by
  have h := strictIntermediate_card_add_two H hHt
  omega

end

end SharpIntermediateSubgroupBounds
