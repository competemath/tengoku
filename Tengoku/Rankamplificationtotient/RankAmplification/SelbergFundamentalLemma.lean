import Tengoku.Rankamplificationtotient.RankAmplification.BFPSTwoAffineSelberg
import Tengoku.Rankamplificationtotient.RankAmplification.BFPSTotientWeight
import Tengoku.Rankamplificationtotient.RankAmplification.MertensComparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The finite Selberg minimizer and the remaining analytic endpoints Mathlib diagonalizes the `Λ²` Selberg main term but stops before constructing and estimating the minimizing weights. -/

namespace RankAmplification

open Finset Nat ArithmeticFunction
open scoped BigOperators Nat.Prime ArithmeticFunction.Moebius

noncomputable section

namespace BFPSTwoAffine

/-! ## Exact comparison of the BFPS local product with one base Mertens product -/

/-- The direct (rather than reciprocal) Mertens product.-/
def directMertensProduct (z : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE z, (1 - (p : ℝ)⁻¹)

/--
@isnad1 id=lt.1h1v.s5.fde657d08f2a from=translated src=- shape=fb5031f0 vocab=8fde40d2
-/
theorem directMertensFactor_pos {p : ℕ} (hp : p.Prime) :
    0 < 1 - (p : ℝ)⁻¹ := by
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))

/--
@isnad1 id=lt.0h1v.s3.babac3ee37a2 from=translated src=- shape=b9369acb vocab=1f21e814
-/
theorem directMertensProduct_pos (z : ℕ) : 0 < directMertensProduct z := by
  unfold directMertensProduct
  exact Finset.prod_pos fun p hp ↦
    directMertensFactor_pos (Nat.prime_of_mem_primesLE hp)

/-- Embed the ordinary harmonic interval into the `z`-smooth Euler-product carrier.-/
def harmonicSmoothEmbedding (z : ℕ) :
    {n : ℕ // n ∈ Finset.Icc 1 z} ↪ (z + 1).smoothNumbers where
  toFun := fun n ↦ ⟨n.1, isSmooth_iff_mem_smoothNumbers_succ.mp ⟨by
    exact Nat.ne_of_gt (Finset.mem_Icc.mp n.2).1
  , by
    intro p hp
    have hpd : p ∣ n.1 := Nat.dvd_of_mem_primeFactors hp
    exact (Nat.le_of_dvd
      (Nat.zero_lt_of_lt (Finset.mem_Icc.mp n.2).1) hpd).trans
        (Finset.mem_Icc.mp n.2).2⟩⟩
  inj' := fun a b hab ↦ Subtype.ext <| congrArg
    (fun q : (z + 1).smoothNumbers ↦ (q : ℕ)) hab

/-- Euler's elementary observation: the reciprocal prime product contains the harmonic sum.
@isnad1 id=le.0h1v.s3.20f1b51b36e5 from=translated src=- shape=0a9af14d vocab=99babdf0
-/
theorem harmonic_le_mertensProduct (z : ℕ) :
    ((harmonic z : ℚ) : ℝ) ≤ mertensProduct z := by
  let e := harmonicSmoothEmbedding z
  let A : Finset ((z + 1).smoothNumbers) := Finset.univ.map e
  have hsmooth := (summable_and_hasSum_smooth_reciprocals z).2
  have hle : (∑ n ∈ A, ((n.1 : ℝ)⁻¹)) ≤ mertensProduct z := by
    calc
      (∑ n ∈ A, ((n.1 : ℝ)⁻¹)) ≤
          ∑' n : (z + 1).smoothNumbers, ((n.1 : ℝ)⁻¹) :=
        hsmooth.summable.sum_le_tsum A
          (fun n _ ↦ inv_nonneg.mpr (Nat.cast_nonneg n.1))
      _ = mertensProduct z := hsmooth.tsum_eq
  have hfinite :
      (∑ n ∈ Finset.Icc 1 z, ((n : ℝ)⁻¹)) =
        ∑ n : {n : ℕ // n ∈ Finset.Icc 1 z}, ((n.1 : ℝ)⁻¹) := by
    rw [← Finset.sum_attach, Finset.attach_eq_univ]
  have hmap :
      (∑ n : {n : ℕ // n ∈ Finset.Icc 1 z}, ((n.1 : ℝ)⁻¹)) =
        ∑ n ∈ A, ((n.1 : ℝ)⁻¹) := by
    change (∑ n : {n : ℕ // n ∈ Finset.Icc 1 z}, ((n.1 : ℝ)⁻¹)) =
      ∑ n ∈ Finset.univ.map e, ((n.1 : ℝ)⁻¹)
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro n _hn
    rfl
  calc
    ((harmonic z : ℚ) : ℝ) =
        ∑ n ∈ Finset.Icc 1 z, ((n : ℝ)⁻¹) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]
    _ = ∑ n : {n : ℕ // n ∈ Finset.Icc 1 z}, ((n.1 : ℝ)⁻¹) := hfinite
    _ = ∑ n ∈ A, ((n.1 : ℝ)⁻¹) := hmap
    _ ≤ mertensProduct z := hle

/--
@isnad1 id=eq.0h1v.s3.ab9007240292 from=translated src=- shape=6b4ab8ce vocab=e11d85ee
-/
theorem mertensProduct_eq_inv_directMertensProduct (z : ℕ) :
    mertensProduct z = (directMertensProduct z)⁻¹ := by
  unfold mertensProduct directMertensProduct
  rw [Finset.prod_inv_distrib]

/--
@isnad1 id=eq.0h1v.s3.6d15244e1817 from=translated src=- shape=6b4ab8ce vocab=e11d85ee
-/
theorem directMertensProduct_eq_inv_mertensProduct (z : ℕ) :
    directMertensProduct z = (mertensProduct z)⁻¹ := by
  rw [mertensProduct_eq_inv_directMertensProduct]
  simp

/-- Fully unconditional elementary direct-product decay.
@isnad1 id=le.1h1v.s5.ef33ef6f86d3 from=translated src=- shape=2b0e15f3 vocab=5c46c09f
-/
theorem directMertensProduct_le_inv_log_add_one
    {z : ℕ} (hz : 1 ≤ z) :
    directMertensProduct z ≤ (Real.log ((z + 1 : ℕ) : ℝ))⁻¹ := by
  have hlogPos : 0 < Real.log ((z + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z + 1 by omega))
  have hlogHarm : Real.log ((z + 1 : ℕ) : ℝ) ≤
      ((harmonic z : ℚ) : ℝ) := log_add_one_le_harmonic z
  have hHarmPos : 0 < ((harmonic z : ℚ) : ℝ) :=
    hlogPos.trans_le hlogHarm
  rw [directMertensProduct_eq_inv_mertensProduct]
  exact ((inv_le_inv₀ (mertensProduct_pos z) hHarmPos).mpr
      (harmonic_le_mertensProduct z)).trans
    ((inv_le_inv₀ hHarmPos hlogPos).mpr hlogHarm)

/--
@isnad1 id=eq.1h2v.s5.129df7a9ccef from=translated src=- shape=2510f828 vocab=8828003e
-/
theorem localDensity_apply_prime {m p : ℕ} (hp : p.Prime) :
    localDensity m p = ((if p ∣ m then 1 else 2 : ℕ) : ℝ) / p := by
  rw [localDensity, shiftedBadResidueCount_prime hp]

/-! The composite-modulus root count is a finite CRT fact, not an analytic premise. -/

/-- Shifted roots represented directly in `ZMod`.-/
def shiftedRootType (m d : ℕ) :=
  {q : ZMod d // shiftedProductMod m d q = 0}

noncomputable instance shiftedRootTypeFintype (m d : ℕ) [NeZero d] :
    Fintype (shiftedRootType m d) := by
  classical
  unfold shiftedRootType
  infer_instance

/--
@isnad1 id=eq.0h2v.s4.b8b3e1da9fb0 from=translated src=- shape=d0a0227f vocab=ea921812
-/
theorem shiftedBadResidueCount_eq_card_shiftedRootType
    (m d : ℕ) [NeZero d] :
    shiftedBadResidueCount m d = Fintype.card (shiftedRootType m d) := by
  let e : Fin d ≃ ZMod d := (ZMod.finEquiv d).toEquiv
  have he (t : Fin d) :
      t ∈ shiftedBadResidueSet m d ↔
        shiftedProductMod m d (e t) = 0 := by
    rw [mem_shiftedBadResidueSet,
      ← shiftedProductMod_natCast_eq_zero_iff_dvd m d t.val]
    have hfin : (ZMod.finEquiv d) t = (t.val : ZMod d) := by
      cases d with
      | zero => exact Fin.elim0 t
      | succ d =>
          change t = (t.val : ZMod (d + 1))
          exact (ZMod.natCast_zmod_val (n := d + 1) t).symm
    change shiftedProductMod m d (t.val : ZMod d) = 0 ↔
      shiftedProductMod m d ((ZMod.finEquiv d) t) = 0
    rw [hfin]
  let rootEquiv :
      {t // t ∈ shiftedBadResidueSet m d} ≃ shiftedRootType m d :=
    e.subtypeEquiv he
  calc
    shiftedBadResidueCount m d =
        Fintype.card {t // t ∈ shiftedBadResidueSet m d} := by
      rw [shiftedBadResidueCount, Fintype.card_coe]
    _ = Fintype.card (shiftedRootType m d) := Fintype.card_congr rootEquiv

/--
@isnad1 id=eq.1h4v.s10.b63d448ddaaa from=translated src=- shape=6d559d7e vocab=ba8094fc
-/
theorem shiftedProductMod_chineseRemainder
    {m a b : ℕ} (hab : a.Coprime b) (q : ZMod (a * b)) :
    ZMod.chineseRemainder hab (shiftedProductMod m (a * b) q) =
      (shiftedProductMod m a (ZMod.chineseRemainder hab q).1,
        shiftedProductMod m b (ZMod.chineseRemainder hab q).2) := by
  simp [shiftedProductMod]
  apply Prod.ext <;> rfl

/-- Chinese-remainder equivalence between shifted roots modulo coprime factors.-/
@[nolint defsWithUnderscore]
noncomputable def shiftedRootType_mulEquiv
    (m : ℕ) {a b : ℕ} (hab : a.Coprime b) :
    shiftedRootType m (a * b) ≃
      shiftedRootType m a × shiftedRootType m b := by
  let e := (ZMod.chineseRemainder hab).toEquiv
  change {q : ZMod (a * b) // shiftedProductMod m (a * b) q = 0} ≃
    {q : ZMod a // shiftedProductMod m a q = 0} ×
      {q : ZMod b // shiftedProductMod m b q = 0}
  let rootEquiv :
      {q : ZMod (a * b) // shiftedProductMod m (a * b) q = 0} ≃
        {q : ZMod a × ZMod b //
          shiftedProductMod m a q.1 = 0 ∧
            shiftedProductMod m b q.2 = 0} :=
    e.subtypeEquiv fun q ↦ by
      rw [← (ZMod.chineseRemainder hab).map_eq_zero_iff,
        shiftedProductMod_chineseRemainder]
      simp only [Prod.mk_eq_zero]
      rfl
  exact rootEquiv.trans (Equiv.subtypeProdEquivProd
    (p := fun q : ZMod a ↦ shiftedProductMod m a q = 0)
    (q := fun q : ZMod b ↦ shiftedProductMod m b q = 0))

/--
@isnad1 id=eq.3h3v.s5.3d934deabf93 from=translated src=- shape=152c656c vocab=5e0e723b
-/
theorem shiftedBadResidueCount_mul_of_coprime
    (m : ℕ) {a b : ℕ} (hab : a.Coprime b) (ha : a ≠ 0) (hb : b ≠ 0) :
    shiftedBadResidueCount m (a * b) =
      shiftedBadResidueCount m a * shiftedBadResidueCount m b := by
  letI : NeZero a := ⟨ha⟩
  letI : NeZero b := ⟨hb⟩
  letI : NeZero (a * b) := ⟨Nat.mul_ne_zero ha hb⟩
  rw [shiftedBadResidueCount_eq_card_shiftedRootType,
    shiftedBadResidueCount_eq_card_shiftedRootType,
    shiftedBadResidueCount_eq_card_shiftedRootType]
  exact (Fintype.card_congr (shiftedRootType_mulEquiv m hab)).trans
    (Fintype.card_prod _ _)

/--
@isnad1 id=eq.0h1v.s4.715e289dd8bf from=translated src=- shape=1d838610 vocab=daa84f70
-/
@[simp]
theorem shiftedBadResidueCount_zero (m : ℕ) :
    shiftedBadResidueCount m 0 = 0 := by
  simp [shiftedBadResidueCount, shiftedBadResidueSet]

/--
@isnad1 id=eq.0h1v.s4.80f4c8f09d9d from=translated src=- shape=1d838610 vocab=daa84f70
-/
@[simp]
theorem shiftedBadResidueCount_one (m : ℕ) :
    shiftedBadResidueCount m 1 = 1 := by
  simp [shiftedBadResidueCount, shiftedBadResidueSet]

/-- The root count as a genuine multiplicative arithmetic function.-/
def shiftedRootCount (m : ℕ) : ArithmeticFunction ℕ where
  toFun d := shiftedBadResidueCount m d
  map_zero' := shiftedBadResidueCount_zero m

/--
@isnad1 id=eq.0h2v.s4.aa2559b0db30 from=translated src=- shape=95236941 vocab=4d8c456c
-/
@[simp]
theorem shiftedRootCount_apply (m d : ℕ) :
    shiftedRootCount m d = shiftedBadResidueCount m d := rfl

/--
@isnad1 id=ismultip.0h1v.s2.a123b819b571 from=translated src=- shape=6da4ece3 vocab=79c8a405
-/
theorem shiftedRootCount_isMultiplicative (m : ℕ) :
    (shiftedRootCount m).IsMultiplicative := by
  constructor
  · simp
  · intro a b hab
    simp only [shiftedRootCount_apply]
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    exact shiftedBadResidueCount_mul_of_coprime m hab ha hb

/--
@isnad1 id=eq.1h2v.s4.285cfdaaf4d5 from=translated src=- shape=2b30bba8 vocab=21a10b15
-/
theorem prod_primeFactors_shiftedBadResidueCount
    {m d : ℕ} (hsq : Squarefree d) :
    ∏ p ∈ d.primeFactors, shiftedBadResidueCount m p =
      shiftedBadResidueCount m d := by
  change (∏ p ∈ d.primeFactors, shiftedRootCount m p) = shiftedRootCount m d
  rw [← (shiftedRootCount_isMultiplicative m).map_prod_of_subset_primeFactors
    d d.primeFactors subset_rfl,
    Nat.prod_primeFactors_of_squarefree hsq]

/-- On squarefree moduli the sieve density is exactly the CRT root count divided by the modulus.
@isnad1 id=eq.2h2v.s5.1a6d85ad3b3b from=translated src=- shape=a1dc134f vocab=1b0eecdd
-/
theorem sieveDensity_eq_shiftedBadResidueCount_div
    {m d : ℕ} (hd : d ≠ 0) (hsq : Squarefree d) :
    sieveDensity m d = (shiftedBadResidueCount m d : ℝ) / d := by
  rw [sieveDensity, ArithmeticFunction.prodPrimeFactors_apply hd]
  simp only [localDensity, Finset.prod_div_distrib]
  rw [← Nat.cast_prod, ← Nat.cast_prod,
    prod_primeFactors_shiftedBadResidueCount hsq,
    Nat.prod_primeFactors_of_squarefree hsq]

/-- Exact squarefree-modulus remainder formula underlying paper (9.2).
@isnad1 id=eq.3h4v.s6.dc16774b95f4 from=translated src=- shape=4c574dd8 vocab=e9ab1fbb
-/
theorem boundingSieve_rem_eq_excess_sub_fraction
    {m R z d : ℕ} (hm : Even m) (hd : 0 < d) (hsq : Squarefree d) :
    (boundingSieve m R z hm).rem d =
      (residueExcessCount m R d : ℝ) -
        (shiftedBadResidueCount m d : ℝ) * (R % d : ℕ) / d := by
  rw [boundingSieve_rem_eq_floor_add_excess hm hd,
    sieveDensity_eq_shiftedBadResidueCount_div hd.ne' hsq]
  have hR : (R : ℝ) = (d : ℝ) * (R / d : ℕ) + (R % d : ℕ) := by
    exact_mod_cast (Nat.mod_add_div R d).symm.trans (by omega)
  rw [hR]
  have hdCast : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  ring

/--
@isnad1 id=le.3h4v.s5.f510487ecf4b from=translated src=- shape=7fe74a01 vocab=2d87439b
-/
theorem abs_boundingSieve_rem_le_shiftedBadResidueCount
    {m R z d : ℕ} (hm : Even m) (hd : 0 < d) (hsq : Squarefree d) :
    |(boundingSieve m R z hm).rem d| ≤ shiftedBadResidueCount m d := by
  rw [boundingSieve_rem_eq_excess_sub_fraction hm hd hsq]
  have hdCast : 0 < (d : ℝ) := by exact_mod_cast hd
  have hcount0 : 0 ≤ (shiftedBadResidueCount m d : ℝ) := by positivity
  have hexcess0 : 0 ≤ (residueExcessCount m R d : ℝ) := by positivity
  have hexcessLe : (residueExcessCount m R d : ℝ) ≤
      shiftedBadResidueCount m d := residueExcessCount_cast_le m R d
  have hfrac : ((R % d : ℕ) : ℝ) / d ≤ 1 := by
    rw [div_le_one hdCast]
    exact_mod_cast (Nat.mod_lt R hd).le
  have hterm0 : 0 ≤
      (shiftedBadResidueCount m d : ℝ) * (R % d : ℕ) / d := by
    positivity
  have htermLe :
      (shiftedBadResidueCount m d : ℝ) * (R % d : ℕ) / d ≤
        shiftedBadResidueCount m d := by
    calc
      (shiftedBadResidueCount m d : ℝ) * (R % d : ℕ) / d =
          (shiftedBadResidueCount m d : ℝ) *
            (((R % d : ℕ) : ℝ) / d) := by ring
      _ ≤ (shiftedBadResidueCount m d : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hfrac hcount0
      _ = shiftedBadResidueCount m d := by ring
  rw [abs_le]
  constructor <;> linarith

/--
@isnad1 id=le.1h2v.s5.2a64193ee8f6 from=translated src=- shape=54fa885b vocab=b9a5b5ad
-/
theorem shiftedBadResidueCount_le_two_pow_card_primeFactors
    {m d : ℕ} (hsq : Squarefree d) :
    shiftedBadResidueCount m d ≤ 2 ^ d.primeFactors.card := by
  rw [← prod_primeFactors_shiftedBadResidueCount hsq]
  calc
    (∏ p ∈ d.primeFactors, shiftedBadResidueCount m p) ≤
        ∏ _p ∈ d.primeFactors, 2 := by
      gcongr with p hp
      exact shiftedBadResidueCount_le_two
        (Nat.prime_of_mem_primeFactors hp)
    _ = 2 ^ d.primeFactors.card := by simp

/-- The completely explicit paper remainder bound `|r_d| ≤ 2^ω(d)`.
@isnad1 id=le.3h4v.s6.f59b6669f9e3 from=translated src=- shape=47536734 vocab=530ae6f6
-/
theorem abs_boundingSieve_rem_le_two_pow_card_primeFactors
    {m R z d : ℕ} (hm : Even m) (hd : 0 < d) (hsq : Squarefree d) :
    |(boundingSieve m R z hm).rem d| ≤
      ((2 ^ d.primeFactors.card : ℕ) : ℝ) := by
  exact (abs_boundingSieve_rem_le_shiftedBadResidueCount hm hd hsq).trans
    (by exact_mod_cast shiftedBadResidueCount_le_two_pow_card_primeFactors hsq)

/-- The correction at a prime dividing `m`; it is one at every other prime.-/
def multiplierCorrectionFactor (m p : ℕ) : ℝ :=
  if p ∣ m then (1 - (p : ℝ)⁻¹)⁻¹ else 1

/--
@isnad1 id=le.1h2v.s4.b385b28e6c87 from=translated src=- shape=30e226e4 vocab=14398c85
-/
theorem one_le_multiplierCorrectionFactor {m p : ℕ} (hp : p.Prime) :
    1 ≤ multiplierCorrectionFactor m p := by
  unfold multiplierCorrectionFactor
  split_ifs
  · exact one_le_primeEulerFactor hp
  · exact le_rfl

/--
@isnad1 id=le.1h2v.s4.319d78cf06d5 from=translated src=- shape=30e226e4 vocab=14398c85
-/
theorem multiplierCorrectionFactor_nonneg {m p : ℕ} (hp : p.Prime) :
    0 ≤ multiplierCorrectionFactor m p :=
  zero_le_one.trans (one_le_multiplierCorrectionFactor hp)

/-- Pointwise local comparison.
@isnad1 id=le.1h2v.s6.53a51984c7db from=translated src=- shape=f2f57d2f vocab=b542fcf8
-/
theorem one_sub_localDensity_le_base_sq_mul_correction
    {m p : ℕ} (hp : p.Prime) :
    1 - localDensity m p ≤
      (1 - (p : ℝ)⁻¹) ^ 2 * multiplierCorrectionFactor m p := by
  rw [localDensity_apply_prime hp]
  unfold multiplierCorrectionFactor
  by_cases hpm : p ∣ m
  · simp only [ite_eq_left hpm, Nat.cast_one]
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hfactor : 1 - (p : ℝ)⁻¹ ≠ 0 :=
      (directMertensFactor_pos hp).ne'
    field_simp [hfactor]
    rfl
  · simp only [ite_eq_right hpm, Nat.cast_ofNat]
    have hpR0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hinv0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hpR0.le
    simp only [mul_one, div_eq_mul_inv]
    nlinarith [sq_nonneg ((p : ℝ)⁻¹)]

/--
@isnad1 id=le.1h2v.s4.c346e1a53c81 from=translated src=- shape=8786dcb6 vocab=1e39f9e7
-/
theorem localSieveProduct_nonneg {m z : ℕ} (hm : Even m) :
    0 ≤ localSieveProduct m z := by
  unfold localSieveProduct
  apply Finset.prod_nonneg
  intro p hpz
  have hp := Nat.prime_of_mem_primesLE hpz
  have hcount := shiftedBadResidueCount_lt_prime_of_even hm hp
  unfold localDensity
  rw [sub_nonneg, div_le_one (by exact_mod_cast hp.pos)]
  exact_mod_cast hcount.le

/--
@isnad1 id=le.0h2v.s5.1187753ca59f from=translated src=- shape=1b51f02d vocab=744b6280
-/
theorem localSieveProduct_le_base_sq_mul_corrections (m z : ℕ) :
    localSieveProduct m z ≤
      directMertensProduct z ^ 2 *
        ∏ p ∈ Nat.primesLE z, multiplierCorrectionFactor m p := by
  unfold localSieveProduct directMertensProduct
  calc
    (∏ p ∈ Nat.primesLE z, (1 - localDensity m p)) ≤
        ∏ p ∈ Nat.primesLE z,
          ((1 - (p : ℝ)⁻¹) ^ 2 * multiplierCorrectionFactor m p) := by
      apply Finset.prod_le_prod
      · intro p hpz
        have hp := Nat.prime_of_mem_primesLE hpz
        have hlocal : 0 ≤ 1 - localDensity m p := by
          rw [localDensity_apply_prime hp]
          by_cases hpm : p ∣ m
          · rw [ite_eq_left hpm]
            norm_num
            have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
            have hpRone : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
            exact (inv_le_one₀ hpRpos).2 hpRone
          · rw [ite_eq_right hpm]
            norm_num
            have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
            have hpRTwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
            exact (div_le_one hpRpos).2 hpRTwo
        exact hlocal
      · intro p hpz
        exact one_sub_localDensity_le_base_sq_mul_correction
          (Nat.prime_of_mem_primesLE hpz)
    _ = (∏ p ∈ Nat.primesLE z, (1 - (p : ℝ)⁻¹)) ^ 2 *
        ∏ p ∈ Nat.primesLE z, multiplierCorrectionFactor m p := by
      rw [Finset.prod_mul_distrib, ← Finset.prod_pow]

/--
@isnad1 id=le.1h2v.s4.2ed3d8117b2b from=translated src=- shape=57fa2794 vocab=c5099d10
-/
theorem correctionProduct_le_totientEulerWeight
    {m z : ℕ} (hm : m ≠ 0) :
    (∏ p ∈ Nat.primesLE z, multiplierCorrectionFactor m p) ≤
      totientEulerWeight m := by
  classical
  have hrewrite :
      (∏ p ∈ Nat.primesLE z, multiplierCorrectionFactor m p) =
        ∏ p ∈ (Nat.primesLE z).filter (· ∣ m),
          (1 - (p : ℝ)⁻¹)⁻¹ := by
    symm
    rw [Finset.prod_filter]
    rfl
  rw [hrewrite, totientEulerWeight]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primesLE hpData.1, hpData.2, hm⟩
  · intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact (primeEulerFactor_pos
      (Nat.prime_of_mem_primesLE hpData.1)).le
  · intro p hp _
    exact one_le_primeEulerFactor (Nat.prime_of_mem_primeFactors hp)

/-- Exact finite local-product reduction with the paper's singular factor.
@isnad1 id=le.1h2v.s5.82e95d4cd28d from=translated src=- shape=c7b811b3 vocab=89fbb6f9
-/
theorem localSieveProduct_le_directMertens_sq_mul_totientWeight
    {m z : ℕ} (hm : m ≠ 0) :
    localSieveProduct m z ≤
      directMertensProduct z ^ 2 * totientWeight m := by
  have hcorrection :
      (∏ p ∈ Nat.primesLE z, multiplierCorrectionFactor m p) ≤
        totientWeight m := by
    rw [totientWeight_eq_eulerWeight hm]
    exact correctionProduct_le_totientEulerWeight hm
  exact (localSieveProduct_le_base_sq_mul_corrections m z).trans
    (mul_le_mul_of_nonneg_left hcorrection
      (sq_nonneg _))

/-- Smallest analytic Mertens input needed after the exact local comparison.-/
def DirectMertensProductUpperBound (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ R, 3 ≤ R → directMertensProduct (cutoff R) ≤ C / Real.log R

/-- A flexible elementary condition covering power-like sieve cutoffs.-/
def CutoffLogLowerBound (cutoff : ℕ → ℕ) (c : ℝ) : Prop :=
  ∀ R, 3 ≤ R →
    1 ≤ cutoff R ∧
      c * Real.log R ≤ Real.log ((cutoff R + 1 : ℕ) : ℝ)

/--
@isnad1 id=directme.2h2v.s4.ffe753fbd54c from=translated src=- shape=ab055a1b vocab=cb0c3c5b
-/
theorem directMertensProductUpperBound_of_cutoffLogLowerBound
    {cutoff : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hcut : CutoffLogLowerBound cutoff c) :
    DirectMertensProductUpperBound cutoff c⁻¹ := by
  intro R hR
  have hRlog : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hdata := hcut R hR
  have hcutLog : 0 < Real.log (((cutoff R) + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < cutoff R + 1 by omega))
  have hcLog : 0 < c * Real.log (R : ℝ) := mul_pos hc hRlog
  calc
    directMertensProduct (cutoff R) ≤
        (Real.log (((cutoff R) + 1 : ℕ) : ℝ))⁻¹ :=
      directMertensProduct_le_inv_log_add_one hdata.1
    _ ≤ (c * Real.log (R : ℝ))⁻¹ :=
      (inv_le_inv₀ hcutLog hcLog).mpr hdata.2
    _ = c⁻¹ / Real.log R := by
      simp only [mul_inv_rev, div_eq_mul_inv]
      ring

/-- In particular, any cutoff dominating `R` has constant one.
@isnad1 id=directme.1h1v.s5.b73802b23f6b from=translated src=- shape=b9993c2f vocab=abf7a98b
-/
theorem directMertensProductUpperBound_of_le
    {cutoff : ℕ → ℕ}
    (hcut : ∀ R, 3 ≤ R → R ≤ cutoff R) :
    DirectMertensProductUpperBound cutoff 1 := by
  have hlog : CutoffLogLowerBound cutoff 1 := by
    intro R hR
    have hcR := hcut R hR
    refine ⟨by omega, ?_⟩
    simp only [one_mul]
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show R ≤ cutoff R + 1 by omega)
  simpa using directMertensProductUpperBound_of_cutoffLogLowerBound
    (cutoff := cutoff) (c := 1) (by norm_num) hlog

/--
@isnad1 id=directme.0h0v.s3.4af8a4fba95c from=translated src=- shape=a212a91e vocab=6e5af276
-/
theorem directMertensProductUpperBound_id :
    DirectMertensProductUpperBound id 1 := by
  apply directMertensProductUpperBound_of_le
  intro R _hR
  exact le_rfl

/-- One base Mertens bound supplies the squared, singular-factor BFPS product estimate.
@isnad1 id=mertensl.2h2v.s5.6b2681358f1a from=translated src=- shape=8d7b6e56 vocab=908025ab
-/
theorem mertensLocalProductUpperBound_of_directMertens
    {cutoff : ℕ → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hM : DirectMertensProductUpperBound cutoff C) :
    MertensLocalProductUpperBound cutoff (C ^ 2) := by
  intro m R hm _hmEven hR
  have hm0 : m ≠ 0 := by omega
  have hlog : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hbase0 : 0 ≤ directMertensProduct (cutoff R) :=
    (directMertensProduct_pos _).le
  have hupper0 : 0 ≤ C / Real.log R := div_nonneg hC hlog.le
  have hsq : directMertensProduct (cutoff R) ^ 2 ≤
      (C / Real.log R) ^ 2 := by
    nlinarith [hM R hR]
  calc
    localSieveProduct m (cutoff R) ≤
        directMertensProduct (cutoff R) ^ 2 * totientWeight m :=
      localSieveProduct_le_directMertens_sq_mul_totientWeight hm0
    _ ≤ (C / Real.log R) ^ 2 * totientWeight m :=
      mul_le_mul_of_nonneg_right hsq (by unfold totientWeight; positivity)
    _ = C ^ 2 / Real.log R ^ 2 * ((m : ℝ) / (m.totient : ℝ)) := by
      unfold totientWeight
      ring

/--
@isnad1 id=mertensl.2h2v.s5.8323fcaeb2e3 from=translated src=- shape=5f84d8bf vocab=8e65c3fe
-/
theorem mertensLocalProductUpperBound_of_cutoffLogLowerBound
    {cutoff : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hcut : CutoffLogLowerBound cutoff c) :
    MertensLocalProductUpperBound cutoff ((c⁻¹) ^ 2) :=
  mertensLocalProductUpperBound_of_directMertens (inv_nonneg.mpr hc.le)
    (directMertensProductUpperBound_of_cutoffLogLowerBound hc hcut)

/--
@isnad1 id=mertensl.0h0v.s3.7c0aaa0fcfbb from=translated src=- shape=a212a91e vocab=7d2bb458
-/
theorem mertensLocalProductUpperBound_id :
    MertensLocalProductUpperBound id 1 := by
  simpa using mertensLocalProductUpperBound_of_directMertens
    (C := 1) (by norm_num) directMertensProductUpperBound_id

end BFPSTwoAffine

namespace SelbergFundamental

/-! ## The finite diagonal minimizer The cutoff is written as `l² ≤ level`, which is equivalent to the customary `l ≤ √level` and avoids introducing square roots into the finite algebra. -/

/-- Divisors retained in the finite Selberg variational problem.-/
def truncatedDivisors (s : SelbergSieve) : Finset ℕ :=
  s.prodPrimes.divisors.filter fun l ↦ (l : ℝ) ^ 2 ≤ s.level

/--
@isnad1 id=iff.0h2v.s5.ff12f1561a96 from=translated src=- shape=13b56ff5 vocab=69b32ab3
-/
@[simp]
theorem mem_truncatedDivisors {s : SelbergSieve} {l : ℕ} :
    l ∈ truncatedDivisors s ↔
      l ∣ s.prodPrimes ∧ (l : ℝ) ^ 2 ≤ s.level := by
  simp [truncatedDivisors, BoundingSieve.prodPrimes_ne_zero]

/--
@isnad1 id=mem.0h1v.s4.2ff4d6f46270 from=translated src=- shape=51e469f9 vocab=c1133796
-/
theorem one_mem_truncatedDivisors (s : SelbergSieve) :
    1 ∈ truncatedDivisors s := by
  rw [mem_truncatedDivisors]
  exact ⟨one_dvd _, by simpa using s.one_le_level⟩

/-- The denominator in the optimal diagonal Selberg main term.-/
def truncatedMass (s : SelbergSieve) : ℝ :=
  ∑ l ∈ truncatedDivisors s, s.selbergTerms l

/--
@isnad1 id=lt.0h1v.s3.349e665d897e from=translated src=- shape=b9369acb vocab=464f9a02
-/
theorem truncatedMass_pos (s : SelbergSieve) : 0 < truncatedMass s := by
  have hle : s.selbergTerms 1 ≤ truncatedMass s := by
    unfold truncatedMass
    exact Finset.single_le_sum
      (fun l hl ↦ (s.selbergTerms_pos (mem_truncatedDivisors.mp hl).1).le)
      (one_mem_truncatedDivisors s)
  exact (s.selbergTerms_pos (one_dvd _)).trans_le hle

/--
@isnad1 id=eq.0h1v.s4.9d32267b9930 from=translated src=- shape=08c74d6c vocab=c8015201
-/
@[simp]
theorem selbergTerms_one (s : BoundingSieve) : s.selbergTerms 1 = 1 := by
  rw [BoundingSieve.selbergTerms_apply, s.nu_mult.map_one]
  simp

/--
@isnad1 id=le.0h1v.s3.d3f99ec8ab2a from=translated src=- shape=b9369acb vocab=ced6dfda
-/
theorem one_le_truncatedMass (s : SelbergSieve) : 1 ≤ truncatedMass s := by
  rw [← selbergTerms_one s.toBoundingSieve]
  unfold truncatedMass
  exact Finset.single_le_sum
    (fun l hl ↦ (s.selbergTerms_pos (mem_truncatedDivisors.mp hl).1).le)
    (one_mem_truncatedDivisors s)

/--
@isnad1 id=le.0h1v.s4.c13d3badd9ab from=translated src=- shape=562e4a6d vocab=5d20b937
-/
theorem truncatedMass_inv_le_one (s : SelbergSieve) :
    (truncatedMass s)⁻¹ ≤ 1 :=
  (inv_le_one₀ (truncatedMass_pos s)).mpr (one_le_truncatedMass s)

/-- Optimal diagonal coordinates.-/
def minimizingDiagonal (s : SelbergSieve) (l : ℕ) : ℝ :=
  if l ∈ truncatedDivisors s then
    (μ l : ℝ) * s.selbergTerms l / truncatedMass s
  else 0

/--
@isnad1 id=eq.1h2v.s5.5a505224a7dd from=translated src=- shape=fac3d5e8 vocab=0ae47db1
-/
theorem cast_moebius_sq_eq_one_of_dvd
    {s : BoundingSieve} {l : ℕ} (hl : l ∣ s.prodPrimes) :
    (μ l : ℝ) ^ 2 = 1 := by
  exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
    (s.squarefree_of_dvd_prodPrimes hl)

/--
@isnad1 id=eq.0h1v.s5.4bf3324050ac from=translated src=- shape=53c57535 vocab=5d84f021
-/
theorem minimizingDiagonal_normalized (s : SelbergSieve) :
    ∑ l ∈ s.prodPrimes.divisors,
        (μ l : ℝ) * minimizingDiagonal s l = 1 := by
  have hmass : truncatedMass s ≠ 0 := (truncatedMass_pos s).ne'
  calc
    (∑ l ∈ s.prodPrimes.divisors,
        (μ l : ℝ) * minimizingDiagonal s l) =
        ∑ l ∈ truncatedDivisors s,
          (μ l : ℝ) *
            ((μ l : ℝ) * s.selbergTerms l / truncatedMass s) := by
      simp only [minimizingDiagonal, truncatedDivisors]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l hl
      have hlData := Nat.mem_divisors.mp hl
      simp [hlData]
    _ = ∑ l ∈ truncatedDivisors s,
          s.selbergTerms l / truncatedMass s := by
      apply Finset.sum_congr rfl
      intro l hl
      calc
        (μ l : ℝ) *
            ((μ l : ℝ) * s.selbergTerms l / truncatedMass s) =
            (μ l : ℝ) ^ 2 * s.selbergTerms l / truncatedMass s := by ring
        _ = s.selbergTerms l / truncatedMass s := by
          rw [cast_moebius_sq_eq_one_of_dvd
            (mem_truncatedDivisors.mp hl).1, one_mul]
    _ = 1 := by
      rw [← Finset.sum_div, ← truncatedMass, div_self hmass]

/--
@isnad1 id=eq.0h1v.s6.5b7ce47bb9c4 from=translated src=- shape=c4926bee vocab=9b1a0f29
-/
theorem minimizingDiagonal_objective (s : SelbergSieve) :
    ∑ l ∈ s.prodPrimes.divisors,
        (s.selbergTerms l)⁻¹ * minimizingDiagonal s l ^ 2 =
      (truncatedMass s)⁻¹ := by
  have hmass : truncatedMass s ≠ 0 := (truncatedMass_pos s).ne'
  calc
    (∑ l ∈ s.prodPrimes.divisors,
        (s.selbergTerms l)⁻¹ * minimizingDiagonal s l ^ 2) =
        ∑ l ∈ truncatedDivisors s,
          (s.selbergTerms l)⁻¹ *
            (((μ l : ℝ) * s.selbergTerms l / truncatedMass s) ^ 2) := by
      simp only [minimizingDiagonal, truncatedDivisors]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l hl
      have hlData := Nat.mem_divisors.mp hl
      simp [hlData]
    _ = ∑ l ∈ truncatedDivisors s,
          s.selbergTerms l / truncatedMass s ^ 2 := by
      apply Finset.sum_congr rfl
      intro l hl
      have hterm : s.selbergTerms l ≠ 0 :=
        (s.selbergTerms_pos (mem_truncatedDivisors.mp hl).1).ne'
      calc
        (s.selbergTerms l)⁻¹ *
            (((μ l : ℝ) * s.selbergTerms l / truncatedMass s) ^ 2) =
            (μ l : ℝ) ^ 2 * s.selbergTerms l /
              truncatedMass s ^ 2 := by
          field_simp
        _ = s.selbergTerms l / truncatedMass s ^ 2 := by
          rw [cast_moebius_sq_eq_one_of_dvd
            (mem_truncatedDivisors.mp hl).1, one_mul]
    _ = (truncatedMass s)⁻¹ := by
      rw [← Finset.sum_div, ← truncatedMass]
      field_simp

/-- The exact finite minimization inequality (Engel's form of Cauchy--Schwarz).
@isnad1 id=le.1h2v.s6.ad11f5c244b6 from=translated src=- shape=e346dffd vocab=0ab51146
-/
theorem minimizingDiagonal_is_minimal
    (s : SelbergSieve) (y : ℕ → ℝ)
    (hy : ∑ l ∈ truncatedDivisors s, (μ l : ℝ) * y l = 1) :
    (truncatedMass s)⁻¹ ≤
      ∑ l ∈ truncatedDivisors s, (s.selbergTerms l)⁻¹ * y l ^ 2 := by
  have hCS := Finset.sq_sum_div_le_sum_sq_div
    (truncatedDivisors s) (fun l ↦ (μ l : ℝ) * y l)
    (fun l hl ↦ s.selbergTerms_pos (mem_truncatedDivisors.mp hl).1)
  rw [hy, one_pow, ← truncatedMass] at hCS
  calc
    (truncatedMass s)⁻¹ = 1 / truncatedMass s := by rw [one_div]
    _ ≤ ∑ l ∈ truncatedDivisors s,
        ((μ l : ℝ) * y l) ^ 2 / s.selbergTerms l := hCS
    _ = ∑ l ∈ truncatedDivisors s,
        (s.selbergTerms l)⁻¹ * y l ^ 2 := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [mul_pow, cast_moebius_sq_eq_one_of_dvd
        (mem_truncatedDivisors.mp hl).1]
      ring

/-! ## Realizing diagonal coordinates by actual Selberg weights -/

/-- Möbius inversion after reversing the divisor lattice of `P`.-/
def reverseMobiusTransform (P : ℕ) (y : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ) * y (P / x.2)

/--
@isnad1 id=eq.1h3v.s5.b7a87a3c1bfc from=translated src=- shape=f4d9f444 vocab=eed3e0a4
-/
theorem sum_reverseMobiusTransform
    (P : ℕ) (y : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, reverseMobiusTransform P y d = y (P / n) := by
  exact ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ) (f := reverseMobiusTransform P y)
    (g := fun k ↦ y (P / k))).mpr (by intro k hk; rfl)) n hn

/--
@isnad1 id=eq.2h2v.s5.8e5a03e297da from=translated src=- shape=b8cb44fe vocab=05e82d40
-/
theorem div_divisor_complement
    {P d : ℕ} (hP : P ≠ 0) (hd : d ∣ P) : P / (P / d) = d := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hd)
  have hdle : d ≤ P := Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hd
  have hquot : 0 < P / d := Nat.div_pos hdle hd0
  apply (Nat.div_eq_iff_eq_mul_left hquot (Nat.div_dvd_of_dvd hd)).mpr
  exact (Nat.mul_div_cancel' hd).symm

/--
@isnad1 id=eq.3h3v.s6.f0ccdb9896b7 from=translated src=- shape=da17c3c9 vocab=a2e7c113
-/
theorem div_quotient_divisor_complement
    {P d a : ℕ} (hP : P ≠ 0) (hd : d ∣ P) (ha : a ∣ P / d) :
    P / ((P / d) / a) = d * a := by
  have hQpos : 0 < P / d := by
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hd)
      (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hd))
  have ha0 : 0 < a :=
    Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hQpos.ne' ha)
  have hquot : 0 < (P / d) / a :=
    Nat.div_pos (Nat.le_of_dvd hQpos ha) ha0
  have hquotDvd : (P / d) / a ∣ P :=
    (Nat.div_dvd_of_dvd ha).trans (Nat.div_dvd_of_dvd hd)
  apply (Nat.div_eq_iff_eq_mul_left hquot hquotDvd).mpr
  calc
    P = d * (P / d) := (Nat.mul_div_cancel' hd).symm
    _ = d * (a * ((P / d) / a)) := by rw [Nat.mul_div_cancel' ha]
    _ = (d * a) * ((P / d) / a) := by ring

/-- The inverse zeta transform, divided by the local density, producing genuine `λ_d` weights.-/
def weightFromDiagonal (s : BoundingSieve) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  if _hd : d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * reverseMobiusTransform s.prodPrimes y (s.prodPrimes / d)
  else 0

/--
@isnad1 id=eq.1h3v.s5.e73f30e05ada from=translated src=- shape=d5331850 vocab=a0c62822
-/
theorem weightFromDiagonal_apply_of_dvd
    {s : BoundingSieve} {y : ℕ → ℝ} {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    s.nu d * weightFromDiagonal s y d =
      reverseMobiusTransform s.prodPrimes y (s.prodPrimes / d) := by
  rw [weightFromDiagonal, dite_eq_left hd]
  field_simp [s.nu_ne_zero hd]

/--
@isnad1 id=iff.2h3v.s5.ce45edba2fee from=translated src=- shape=5e7d3062 vocab=05e82d40
-/
theorem divisor_complement_condition
    {P l d : ℕ} (hl : l ∣ P) (hd : d ∣ P) :
    l ∣ P / d ↔ d ∣ P / l := by
  rw [Nat.dvd_div_iff_mul_dvd hd, Nat.dvd_div_iff_mul_dvd hl,
    Nat.mul_comm]

/-- The constructed weights have exactly the prescribed diagonal coordinates.
@isnad1 id=eq.1h3v.s6.bf5bba5b39f3 from=translated src=- shape=0bd63d55 vocab=2edf27f6
-/
theorem diagonalCoordinate_weightFromDiagonal
    (s : BoundingSieve) (y : ℕ → ℝ) {l : ℕ}
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then s.nu d * weightFromDiagonal s y d else 0) = y l := by
  have hP : s.prodPrimes ≠ 0 := s.prodPrimes_ne_zero
  have hl0 : 0 < l := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hl)
  have hlle : l ≤ s.prodPrimes := Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl
  have hquotPos : 0 < s.prodPrimes / l := Nat.div_pos hlle hl0
  calc
    (∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then s.nu d * weightFromDiagonal s y d else 0) =
        ∑ d ∈ s.prodPrimes.divisors,
          if l ∣ d then
            reverseMobiusTransform s.prodPrimes y (s.prodPrimes / d)
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs with hld
      · exact weightFromDiagonal_apply_of_dvd (Nat.dvd_of_mem_divisors hd)
      · rfl
    _ = ∑ d ∈ s.prodPrimes.divisors,
          if l ∣ s.prodPrimes / d then
            reverseMobiusTransform s.prodPrimes y d
          else 0 := by
      rw [← Nat.sum_div_divisors s.prodPrimes
        (fun d ↦ if l ∣ d then
          reverseMobiusTransform s.prodPrimes y (s.prodPrimes / d) else 0)]
      apply Finset.sum_congr rfl
      intro d hd
      rw [div_divisor_complement hP (Nat.dvd_of_mem_divisors hd)]
    _ = ∑ d ∈ s.prodPrimes.divisors,
          if d ∣ s.prodPrimes / l then
            reverseMobiusTransform s.prodPrimes y d
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hiff := divisor_complement_condition hl
        (Nat.dvd_of_mem_divisors hd)
      by_cases h : l ∣ s.prodPrimes / d
      · have hdvd := hiff.mp h
        simp [h, hdvd]
      · have hndvd : ¬d ∣ s.prodPrimes / l := fun hdvd ↦ h (hiff.mpr hdvd)
        simp [h, hndvd]
    _ = ∑ d ∈ (s.prodPrimes / l).divisors,
          reverseMobiusTransform s.prodPrimes y d := by
      rw [← Finset.sum_filter,
        Nat.divisors_filter_dvd_of_dvd hP (Nat.div_dvd_of_dvd hl)]
    _ = y (s.prodPrimes / (s.prodPrimes / l)) :=
      sum_reverseMobiusTransform s.prodPrimes y hquotPos
    _ = y l := by rw [div_divisor_complement hP hl]

/--
@isnad1 id=eq.0h2v.s5.25abe3690a1c from=translated src=- shape=4025173e vocab=a9512214
-/
theorem reverseMobiusTransform_prodPrimes
    (s : BoundingSieve) (y : ℕ → ℝ) :
    reverseMobiusTransform s.prodPrimes y s.prodPrimes =
      ∑ l ∈ s.prodPrimes.divisors, (μ l : ℝ) * y l := by
  unfold reverseMobiusTransform
  calc
    (∑ x ∈ s.prodPrimes.divisorsAntidiagonal,
        (μ x.1 : ℝ) * y (s.prodPrimes / x.2)) =
        ∑ l ∈ s.prodPrimes.divisors,
          (μ l : ℝ) * y (s.prodPrimes / (s.prodPrimes / l)) :=
      Nat.sum_divisorsAntidiagonal
        (fun l q ↦ (μ l : ℝ) * y (s.prodPrimes / q))
    _ = ∑ l ∈ s.prodPrimes.divisors, (μ l : ℝ) * y l := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [div_divisor_complement s.prodPrimes_ne_zero
        (Nat.dvd_of_mem_divisors hl)]

/--
@isnad1 id=eq.2h3v.s6.7e682bcaa9c2 from=translated src=- shape=e101f1c2 vocab=1b688d02
-/
theorem reverseMobiusTransform_divisor
    {P d : ℕ} (hP : P ≠ 0) (hd : d ∣ P) (y : ℕ → ℝ) :
    reverseMobiusTransform P y (P / d) =
      ∑ a ∈ (P / d).divisors, (μ a : ℝ) * y (d * a) := by
  unfold reverseMobiusTransform
  calc
    (∑ x ∈ (P / d).divisorsAntidiagonal,
        (μ x.1 : ℝ) * y (P / x.2)) =
        ∑ a ∈ (P / d).divisors,
          (μ a : ℝ) * y (P / ((P / d) / a)) :=
      Nat.sum_divisorsAntidiagonal
        (fun a q ↦ (μ a : ℝ) * y (P / q))
    _ = ∑ a ∈ (P / d).divisors, (μ a : ℝ) * y (d * a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [div_quotient_divisor_complement hP hd
        (Nat.dvd_of_mem_divisors ha)]

/-- The actual minimizing Selberg weights obtained from the optimal diagonal coordinates.-/
def minimizingWeight (s : SelbergSieve) : ℕ → ℝ :=
  weightFromDiagonal s.toBoundingSieve (minimizingDiagonal s)

/--
@isnad1 id=eq.0h1v.s4.d53d2ae1b812 from=translated src=- shape=59ae2d96 vocab=ccd86e65
-/
theorem minimizingWeight_one (s : SelbergSieve) :
    minimizingWeight s 1 = 1 := by
  rw [minimizingWeight, weightFromDiagonal, dite_eq_left (one_dvd _),
    s.nu_mult.map_one, inv_one, one_mul, Nat.div_one,
    reverseMobiusTransform_prodPrimes]
  exact minimizingDiagonal_normalized s

/--
@isnad1 id=eq.1h2v.s4.be00fae157bd from=translated src=- shape=16b11ef8 vocab=0f03893b
-/
theorem minimizingWeight_eq_zero_of_not_dvd
    {s : SelbergSieve} {d : ℕ} (hd : ¬d ∣ s.prodPrimes) :
    minimizingWeight s d = 0 := by
  simp [minimizingWeight, weightFromDiagonal, hd]

/-- The constructed minimizing weights have the standard Selberg support `d² ≤ level`.
@isnad1 id=eq.2h2v.s5.b417e8875250 from=translated src=- shape=2b55c763 vocab=73e5964a
-/
theorem minimizingWeight_eq_zero_of_level_lt_sq
    {s : SelbergSieve} {d : ℕ} (hd : d ∣ s.prodPrimes)
    (hlevel : s.level < (d : ℝ) ^ 2) :
    minimizingWeight s d = 0 := by
  rw [minimizingWeight, weightFromDiagonal, dite_eq_left hd,
    reverseMobiusTransform_divisor s.prodPrimes_ne_zero hd]
  have hd0 : 0 < d :=
    Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd)
  have hzero : ∀ a ∈ (s.prodPrimes / d).divisors,
      minimizingDiagonal s (d * a) = 0 := by
    intro a ha
    have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
    have hdaNat : d ≤ d * a := by
      calc
        d = d * 1 := by omega
        _ ≤ d * a := Nat.mul_le_mul_left d (by omega)
    have hda : (d : ℝ) ≤ (d * a : ℕ) := by exact_mod_cast hdaNat
    have hdR0 : 0 ≤ (d : ℝ) := by positivity
    have hdaR0 : 0 ≤ ((d * a : ℕ) : ℝ) := by positivity
    have hnot : d * a ∉ truncatedDivisors s := by
      intro hmem
      have hsquare := (mem_truncatedDivisors.mp hmem).2
      nlinarith
    rw [minimizingDiagonal, ite_eq_right hnot]
  have hsum :
      (∑ a ∈ (s.prodPrimes / d).divisors,
        (μ a : ℝ) * minimizingDiagonal s (d * a)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [hzero a ha, mul_zero]
  rw [hsum, mul_zero]

/--
@isnad1 id=eq.1h2v.s4.205938cc6598 from=translated src=- shape=5423264f vocab=b184ab5c
-/
theorem minimizingWeight_eq_zero_of_not_mem_truncated
    {s : SelbergSieve} {d : ℕ} (hd : d ∉ truncatedDivisors s) :
    minimizingWeight s d = 0 := by
  by_cases hdP : d ∣ s.prodPrimes
  · apply minimizingWeight_eq_zero_of_level_lt_sq hdP
    exact lt_of_not_ge fun hsq ↦ hd (mem_truncatedDivisors.mpr ⟨hdP, hsq⟩)
  · exact minimizingWeight_eq_zero_of_not_dvd hdP

/-- Consequently the associated `Λ²` coefficient vanishes above the Selberg level.
@isnad1 id=eq.1h2v.s4.31236fb3fe52 from=translated src=- shape=5a4e76b1 vocab=2ef0b8da
-/
theorem lambdaSquared_minimizingWeight_eq_zero_of_level_lt
    {s : SelbergSieve} {n : ℕ} (hn : s.level < (n : ℝ)) :
    BoundingSieve.lambdaSquared (minimizingWeight s) n = 0 := by
  unfold BoundingSieve.lambdaSquared
  apply Finset.sum_eq_zero
  intro d₁ hd₁
  apply Finset.sum_eq_zero
  intro d₂ hd₂
  split_ifs with heq
  · by_cases h₁ : d₁ ∈ truncatedDivisors s
    · by_cases h₂ : d₂ ∈ truncatedDivisors s
      · have hd₁Data := mem_truncatedDivisors.mp h₁
        have hd₂Data := mem_truncatedDivisors.mp h₂
        have hd₁Pos : 0 < d₁ := Nat.pos_of_ne_zero
          (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd₁Data.1)
        have hd₂Pos : 0 < d₂ := Nat.pos_of_ne_zero
          (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd₂Data.1)
        have hnleNat : n ≤ d₁ * d₂ := by
          rw [heq]
          exact Nat.lcm_le_mul hd₁Pos hd₂Pos
        have hnle : (n : ℝ) ≤ (d₁ : ℝ) * d₂ := by
          exact_mod_cast hnleNat
        have hd₁Nonneg : 0 ≤ (d₁ : ℝ) := by positivity
        have hd₂Nonneg : 0 ≤ (d₂ : ℝ) := by positivity
        have hmul : (d₁ : ℝ) * d₂ ≤ s.level := by
          nlinarith [sq_nonneg ((d₁ : ℝ) - d₂)]
        exfalso
        linarith
      · rw [minimizingWeight_eq_zero_of_not_mem_truncated h₂,
          mul_zero]
    · rw [minimizingWeight_eq_zero_of_not_mem_truncated h₁,
        zero_mul]
  · rfl

/-- The error term is exactly supported on divisors at most the Selberg level.
@isnad1 id=eq.0h1v.s6.726744ad98c5 from=translated src=- shape=368aed3e vocab=b294efa4
-/
theorem errSum_lambdaSquared_minimizingWeight_eq_level_restriction
    (s : SelbergSieve) :
    s.errSum (BoundingSieve.lambdaSquared (minimizingWeight s)) =
      ∑ d ∈ s.prodPrimes.divisors,
        if (d : ℝ) ≤ s.level then
          |BoundingSieve.lambdaSquared (minimizingWeight s) d| * |s.rem d|
        else 0 := by
  unfold BoundingSieve.errSum
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hlevel : (d : ℝ) ≤ s.level
  · rw [ite_eq_left hlevel]
  · rw [ite_eq_right hlevel,
      lambdaSquared_minimizingWeight_eq_zero_of_level_lt (lt_of_not_ge hlevel),
      abs_zero, zero_mul]

/-- Named finite remainder carrier after the exact support reduction.-/
def levelRestrictedRemainder (s : SelbergSieve) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors,
    if (d : ℝ) ≤ s.level then
      |BoundingSieve.lambdaSquared (minimizingWeight s) d| * |s.rem d|
    else 0

/--
@isnad1 id=eq.0h1v.s3.35a1b068a94f from=translated src=- shape=dcf98fb0 vocab=c732de81
-/
theorem errSum_lambdaSquared_minimizingWeight_eq_levelRestrictedRemainder
    (s : SelbergSieve) :
    s.errSum (BoundingSieve.lambdaSquared (minimizingWeight s)) =
      levelRestrictedRemainder s := by
  rw [levelRestrictedRemainder]
  exact errSum_lambdaSquared_minimizingWeight_eq_level_restriction s

/--
@isnad1 id=eq.1h2v.s6.1f8073992c83 from=translated src=- shape=56e20ec9 vocab=097b4918
-/
theorem diagonalCoordinate_minimizingWeight
    (s : SelbergSieve) {l : ℕ} (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then s.nu d * minimizingWeight s d else 0) =
      minimizingDiagonal s l := by
  exact diagonalCoordinate_weightFromDiagonal s.toBoundingSieve
    (minimizingDiagonal s) hl

/-- Mathlib's diagonalization evaluated at the exact finite minimizer.
@isnad1 id=eq.0h1v.s3.e25dd8e219b8 from=translated src=- shape=caf1d0a7 vocab=b7fbb602
-/
theorem mainSum_lambdaSquared_minimizingWeight (s : SelbergSieve) :
    s.mainSum (BoundingSieve.lambdaSquared (minimizingWeight s)) =
      (truncatedMass s)⁻¹ := by
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  calc
    (∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors,
          if l ∣ d then s.nu d * minimizingWeight s d else 0) ^ 2) =
        ∑ l ∈ s.prodPrimes.divisors,
          (s.selbergTerms l)⁻¹ * minimizingDiagonal s l ^ 2 := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [diagonalCoordinate_minimizingWeight s
        (Nat.dvd_of_mem_divisors hl)]
    _ = (truncatedMass s)⁻¹ := minimizingDiagonal_objective s

/-- Exact finite Selberg upper bound.
@isnad1 id=le.0h1v.s5.ee508c6a1f0a from=translated src=- shape=a2197522 vocab=5c035b99
-/
theorem siftedSum_le_minimizing_main_add_error (s : SelbergSieve) :
    s.siftedSum ≤
      s.totalMass * (truncatedMass s)⁻¹ +
        s.errSum (BoundingSieve.lambdaSquared (minimizingWeight s)) := by
  calc
    s.siftedSum ≤
        s.totalMass * s.mainSum
          (BoundingSieve.lambdaSquared (minimizingWeight s)) +
          s.errSum (BoundingSieve.lambdaSquared (minimizingWeight s)) :=
      s.siftedSum_le_mainSum_errSum_of_upperMoebius _
        (BoundingSieve.upperMoebius_lambdaSquared _ (minimizingWeight_one s))
    _ = s.totalMass * (truncatedMass s)⁻¹ +
          s.errSum (BoundingSieve.lambdaSquared (minimizingWeight s)) := by
      rw [mainSum_lambdaSquared_minimizingWeight]

end SelbergFundamental

namespace BFPSTwoAffine

/-! ## BFPS specialization and the two irreducible analytic estimates -/

/-- The concrete BFPS sieve at level `(max 1 z)²`.-/
def minimizingSelbergSieve (m R z : ℕ) (hm : Even m) : SelbergSieve :=
  selbergSieve m R z hm (((max 1 z : ℕ) : ℝ) ^ 2) (by
    have h : (1 : ℝ) ≤ (max 1 z : ℕ) := by
      exact_mod_cast Nat.le_max_left 1 z
    nlinarith)

/--
@isnad1 id=eq.2h3v.s5.1cfd7aa6d9f0 from=translated src=- shape=8206deb7 vocab=2f25f573
-/
@[simp]
theorem minimizingSelbergSieve_level_of_one_le
    {m R z : ℕ} (hm : Even m) (hz : 1 ≤ z) :
    (minimizingSelbergSieve m R z hm).level = (z : ℝ) ^ 2 := by
  change (((max 1 z : ℕ) : ℝ) ^ 2) = (z : ℝ) ^ 2
  rw [max_eq_right hz]

/--
@isnad1 id=eq.1h3v.s4.12436acafde1 from=translated src=- shape=a64e85f7 vocab=4736a633
-/
@[simp]
theorem minimizingSelbergSieve_totalMass
    (m R z : ℕ) (hm : Even m) :
    (minimizingSelbergSieve m R z hm).totalMass = R := rfl

/--
@isnad1 id=eq.3h4v.s5.c99490c5aaa2 from=translated src=- shape=99f8da7d vocab=a7ff095c
-/
theorem minimizingWeight_eq_zero_of_cutoff_lt
    {m R z d : ℕ} (hm : Even m) (hz : 1 ≤ z) (hzd : z < d) :
    SelbergFundamental.minimizingWeight
      (minimizingSelbergSieve m R z hm) d = 0 := by
  apply SelbergFundamental.minimizingWeight_eq_zero_of_not_mem_truncated
  intro hmem
  have hsquare := (SelbergFundamental.mem_truncatedDivisors.mp hmem).2
  rw [minimizingSelbergSieve_level_of_one_le hm hz] at hsquare
  have hcast : (z : ℝ) < d := by exact_mod_cast hzd
  have hz0 : 0 ≤ (z : ℝ) := by positivity
  have hd0 : 0 ≤ (d : ℝ) := by positivity
  nlinarith

/--
@isnad1 id=eq.3h4v.s5.43c04d6fa0be from=translated src=- shape=202d9524 vocab=c79fb379
-/
theorem lambdaSquared_minimizingWeight_eq_zero_of_cutoff_sq_lt
    {m R z n : ℕ} (hm : Even m) (hz : 1 ≤ z) (hn : z ^ 2 < n) :
    BoundingSieve.lambdaSquared
      (SelbergFundamental.minimizingWeight
        (minimizingSelbergSieve m R z hm)) n = 0 := by
  apply SelbergFundamental.lambdaSquared_minimizingWeight_eq_zero_of_level_lt
  rw [minimizingSelbergSieve_level_of_one_le hm hz]
  exact_mod_cast hn

/-- Purely combinatorial remainder majorant after the exact CRT estimate `|r_d| ≤ 2^ω(d)`.-/
def minimizingWeightRemainderMajorant
    (m R z : ℕ) (hm : Even m) : ℝ :=
  let s := minimizingSelbergSieve m R z hm
  ∑ d ∈ s.prodPrimes.divisors,
    if (d : ℝ) ≤ s.level then
      |BoundingSieve.lambdaSquared
          (SelbergFundamental.minimizingWeight s) d| *
        ((2 ^ d.primeFactors.card : ℕ) : ℝ)
    else 0

/--
@isnad1 id=le.1h3v.s4.f9bc68998ed9 from=translated src=- shape=f0542c85 vocab=7b2ea7cf
-/
theorem levelRestrictedRemainder_le_minimizingWeightRemainderMajorant
    (m R z : ℕ) (hm : Even m) :
    SelbergFundamental.levelRestrictedRemainder
        (minimizingSelbergSieve m R z hm) ≤
      minimizingWeightRemainderMajorant m R z hm := by
  let s := minimizingSelbergSieve m R z hm
  change SelbergFundamental.levelRestrictedRemainder s ≤
    minimizingWeightRemainderMajorant m R z hm
  unfold SelbergFundamental.levelRestrictedRemainder
  change (∑ d ∈ s.prodPrimes.divisors,
      if (d : ℝ) ≤ s.level then
        |BoundingSieve.lambdaSquared
            (SelbergFundamental.minimizingWeight s) d| * |s.rem d|
      else 0) ≤
    ∑ d ∈ s.prodPrimes.divisors,
      if (d : ℝ) ≤ s.level then
        |BoundingSieve.lambdaSquared
            (SelbergFundamental.minimizingWeight s) d| *
          ((2 ^ d.primeFactors.card : ℕ) : ℝ)
      else 0
  apply Finset.sum_le_sum
  intro d hdMem
  by_cases hlevel : (d : ℝ) ≤ s.level
  · rw [ite_eq_left hlevel, ite_eq_left hlevel]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hdDvd : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hdMem
    have hdPos : 0 < d := Nat.pos_of_ne_zero
      (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdDvd)
    have hdSquarefree : Squarefree d :=
      Squarefree.squarefree_of_dvd hdDvd s.prodPrimes_squarefree
    exact abs_boundingSieve_rem_le_two_pow_card_primeFactors
      hm hdPos hdSquarefree
  · rw [ite_eq_right hlevel, ite_eq_right hlevel]

/-- Remaining lower bound for the truncated Selberg denominator, expressed in the natural local-product scale.-/
def TruncatedMassLocalProductUpperBound
    (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ m R, 2 ≤ m → ∀ hm : Even m, 3 ≤ R →
    (SelbergFundamental.truncatedMass
      (minimizingSelbergSieve m R (cutoff R) hm))⁻¹ ≤
        C * localSieveProduct m (cutoff R)

/-- Remaining weighted remainder estimate for the explicitly constructed minimizing weights.-/
def MinimizingRemainderLocalProductUpperBound
    (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ m R, 2 ≤ m → ∀ hm : Even m, 3 ≤ R →
    let s := minimizingSelbergSieve m R (cutoff R) hm
    s.errSum (BoundingSieve.lambdaSquared
      (SelbergFundamental.minimizingWeight s)) ≤
        C * R * localSieveProduct m (cutoff R)

/-- Equivalent, more explicit endpoint involving only divisors `d ≤ level`.-/
def LevelRestrictedRemainderLocalProductUpperBound
    (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ m R, 2 ≤ m → ∀ hm : Even m, 3 ≤ R →
    let s := minimizingSelbergSieve m R (cutoff R) hm
    SelbergFundamental.levelRestrictedRemainder s ≤
      C * R * localSieveProduct m (cutoff R)

/-- Smallest remainder endpoint after all exact CRT and support reductions: it contains only the explicit minimizing weights and the elementary factor `2^ω(d)`.-/
def CombinatorialRemainderLocalProductUpperBound
    (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ m R, 2 ≤ m → ∀ hm : Even m, 3 ≤ R →
    minimizingWeightRemainderMajorant m R (cutoff R) hm ≤
      C * R * localSieveProduct m (cutoff R)

/--
@isnad1 id=levelres.1h2v.s3.2df65f4cad93 from=translated src=- shape=723b5712 vocab=28e932a3
-/
theorem levelRestrictedRemainderLocalProductUpperBound_of_combinatorial
    {cutoff : ℕ → ℕ} {C : ℝ}
    (hrem : CombinatorialRemainderLocalProductUpperBound cutoff C) :
    LevelRestrictedRemainderLocalProductUpperBound cutoff C := by
  intro m R hm hmEven hR
  exact (levelRestrictedRemainder_le_minimizingWeightRemainderMajorant
    m R (cutoff R) hmEven).trans (hrem m R hm hmEven hR)

/--
@isnad1 id=minimizi.1h2v.s3.5720330d4712 from=translated src=- shape=723b5712 vocab=177ea67e
-/
theorem minimizingRemainderLocalProductUpperBound_of_levelRestricted
    {cutoff : ℕ → ℕ} {C : ℝ}
    (hrem : LevelRestrictedRemainderLocalProductUpperBound cutoff C) :
    MinimizingRemainderLocalProductUpperBound cutoff C := by
  intro m R hm hmEven hR
  let s := minimizingSelbergSieve m R (cutoff R) hmEven
  change s.errSum (BoundingSieve.lambdaSquared
    (SelbergFundamental.minimizingWeight s)) ≤
      C * R * localSieveProduct m (cutoff R)
  rw [SelbergFundamental.errSum_lambdaSquared_minimizingWeight_eq_levelRestrictedRemainder]
  exact hrem m R hm hmEven hR

/-- The exact target `SelbergFundamentalLemmaUpperBound` follows from precisely the denominator and remainder estimates above; all Selberg-weight algebra has already been discharged.
@isnad1 id=selbergf.2h3v.s4.fa08a489a49b from=translated src=- shape=1ac400c4 vocab=7d681436
-/
theorem selbergFundamentalLemmaUpperBound_of_mass_and_remainder
    {cutoff : ℕ → ℕ} {Cmass Crem : ℝ}
    (hmass : TruncatedMassLocalProductUpperBound cutoff Cmass)
    (hrem : MinimizingRemainderLocalProductUpperBound cutoff Crem) :
    SelbergFundamentalLemmaUpperBound cutoff (Cmass + Crem) := by
  intro m R hm hmEven hR
  let s := minimizingSelbergSieve m R (cutoff R) hmEven
  have hfinite :=
    SelbergFundamental.siftedSum_le_minimizing_main_add_error s
  have hsMass : s.totalMass = (R : ℝ) := by rfl
  have hmass' := hmass m R hm hmEven hR
  have hrem' := hrem m R hm hmEven hR
  change s.siftedSum ≤
    (Cmass + Crem) * R * localSieveProduct m (cutoff R)
  calc
    s.siftedSum ≤
        (R : ℝ) *
            (SelbergFundamental.truncatedMass s)⁻¹ +
          s.errSum (BoundingSieve.lambdaSquared
            (SelbergFundamental.minimizingWeight s)) := by
      rw [hsMass] at hfinite
      exact hfinite
    _ ≤ (R : ℝ) *
          (Cmass * localSieveProduct m (cutoff R)) +
        Crem * R * localSieveProduct m (cutoff R) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmass' (by positivity)) hrem'
    _ = (Cmass + Crem) * R * localSieveProduct m (cutoff R) := by ring

/--
@isnad1 id=selbergf.2h3v.s4.72bc15923313 from=translated src=- shape=1ac400c4 vocab=f794fd4e
-/
theorem selbergFundamentalLemmaUpperBound_of_mass_and_levelRestrictedRemainder
    {cutoff : ℕ → ℕ} {Cmass Crem : ℝ}
    (hmass : TruncatedMassLocalProductUpperBound cutoff Cmass)
    (hrem : LevelRestrictedRemainderLocalProductUpperBound cutoff Crem) :
    SelbergFundamentalLemmaUpperBound cutoff (Cmass + Crem) :=
  selbergFundamentalLemmaUpperBound_of_mass_and_remainder hmass
    (minimizingRemainderLocalProductUpperBound_of_levelRestricted hrem)

/--
@isnad1 id=selbergf.2h3v.s4.de5b803abd92 from=translated src=- shape=1ac400c4 vocab=6a78b5be
-/
theorem selbergFundamentalLemmaUpperBound_of_mass_and_combinatorialRemainder
    {cutoff : ℕ → ℕ} {Cmass Crem : ℝ}
    (hmass : TruncatedMassLocalProductUpperBound cutoff Cmass)
    (hrem : CombinatorialRemainderLocalProductUpperBound cutoff Crem) :
    SelbergFundamentalLemmaUpperBound cutoff (Cmass + Crem) :=
  selbergFundamentalLemmaUpperBound_of_mass_and_levelRestrictedRemainder hmass
    (levelRestrictedRemainderLocalProductUpperBound_of_combinatorial hrem)

end BFPSTwoAffine

namespace AffinePrimePair

/-! ## Compatibility with the fixed two-affine-form sieve -/

variable (L : AffinePrimePair)

/-- The affine-form sieve at the same canonical finite level `(max 1 z)²`.-/
def minimizingAffineSelbergSieve (R z : ℕ) : SelbergSieve :=
  L.affineSelbergSieve R z (((max 1 z : ℕ) : ℝ) ^ 2) (by
    have h : (1 : ℝ) ≤ (max 1 z : ℕ) := by
      exact_mod_cast Nat.le_max_left 1 z
    nlinarith)

/--
@isnad1 id=eq.0h3v.s4.ae4191a7f61f from=translated src=- shape=e14ff061 vocab=7e0c81bb
-/
@[simp]
theorem minimizingAffineSelbergSieve_totalMass (R z : ℕ) :
    (L.minimizingAffineSelbergSieve R z).totalMass = R := rfl

/-- Denominator estimate in the exact `R / log² R` scale used by Lemma 9.5.-/
def TruncatedMassLogSquaredUpperBound
    (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ R : ℕ, 3 ≤ R →
    (R : ℝ) * (SelbergFundamental.truncatedMass
      (L.minimizingAffineSelbergSieve R (cutoff R)))⁻¹ ≤
        C * logSquaredScale R

/-- Remainder estimate for the explicit minimizing affine Selberg weights.-/
def MinimizingRemainderLogSquaredUpperBound
    (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ R : ℕ, 3 ≤ R →
    let s := L.minimizingAffineSelbergSieve R (cutoff R)
    s.errSum (BoundingSieve.lambdaSquared
      (SelbergFundamental.minimizingWeight s)) ≤
        C * logSquaredScale R

/-- The same finite minimizer discharges the algebraic part of `AffinePrimePair.DimensionTwoSelbergUpperBound`.
@isnad1 id=dimensio.2h4v.s5.7971c659b060 from=translated src=- shape=0c0bf93b vocab=5053cf0f
-/
theorem dimensionTwoSelbergUpperBound_of_mass_and_remainder
    {cutoff : ℕ → ℕ} {Cmass Crem : ℝ}
    (hmass : L.TruncatedMassLogSquaredUpperBound cutoff Cmass)
    (hrem : L.MinimizingRemainderLogSquaredUpperBound cutoff Crem) :
    L.DimensionTwoSelbergUpperBound cutoff (Cmass + Crem) := by
  intro R hR
  let s := L.minimizingAffineSelbergSieve R (cutoff R)
  have hfinite :=
    SelbergFundamental.siftedSum_le_minimizing_main_add_error s
  have hsMass : s.totalMass = (R : ℝ) := by rfl
  have hmass' := hmass R hR
  have hrem' := hrem R hR
  change s.siftedSum ≤ (Cmass + Crem) * logSquaredScale R
  calc
    s.siftedSum ≤
        (R : ℝ) * (SelbergFundamental.truncatedMass s)⁻¹ +
          s.errSum (BoundingSieve.lambdaSquared
            (SelbergFundamental.minimizingWeight s)) := by
      rw [hsMass] at hfinite
      exact hfinite
    _ ≤ Cmass * logSquaredScale R + Crem * logSquaredScale R :=
      add_le_add hmass' hrem'
    _ = (Cmass + Crem) * logSquaredScale R := by ring

end AffinePrimePair

end

end RankAmplification
