import Tengoku
import Tengoku.Piirrationalitymeasure.Formalization.BinomialExpansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxRecDepth 100000

/-!
Gaussian-integer factor identities for the Laurent summands in Section 2.2.
-/

namespace PiIrrationality

abbrev GI := GaussianInt

def giOneSubI : GI := ⟨1, -1⟩
def giOneAddI : GI := ⟨1, 1⟩
def giTwoSubI : GI := ⟨2, -1⟩
def giTwoAddI : GI := ⟨2, 1⟩

/--
@isnad1 id=eq.0h0v.s5.409cd32b2f07 from=translated src=- shape=62d93820 vocab=1f5bfb9b
-/
theorem giOneSubI_toComplex : (giOneSubI : ℂ) = 1 - Complex.I := by
  simp [giOneSubI, GaussianInt.toComplex_def']
  ring

/--
@isnad1 id=eq.0h0v.s5.1dfea24bdaf0 from=translated src=- shape=62d93820 vocab=23c2ea81
-/
theorem giOneAddI_toComplex : (giOneAddI : ℂ) = 1 + Complex.I := by
  simp [giOneAddI, GaussianInt.toComplex_def']

/--
@isnad1 id=eq.0h0v.s5.c0dc24a28f53 from=translated src=- shape=62d93820 vocab=742268ba
-/
theorem giTwoSubI_toComplex : (giTwoSubI : ℂ) = 2 - Complex.I := by
  simp [giTwoSubI, GaussianInt.toComplex_def']
  ring

/--
@isnad1 id=eq.0h0v.s5.d87d656b4096 from=translated src=- shape=62d93820 vocab=ad58cf36
-/
theorem giTwoAddI_toComplex : (giTwoAddI : ℂ) = 2 + Complex.I := by
  simp [giTwoAddI, GaussianInt.toComplex_def']

/--
@isnad1 id=eq.0h0v.s5.054921f63ce2 from=translated src=- shape=ba858747 vocab=c1754aa2
-/
theorem giTwo_factorization :
    (2 : GI) = giOneSubI * giOneAddI := by
  decide

/--
@isnad1 id=eq.0h0v.s6.f87dfcabaf34 from=translated src=- shape=6de3bec1 vocab=620efac0
-/
theorem giOneSubI_mul_inv :
    (giOneSubI : ℂ) * (giOneSubI : ℂ)⁻¹ = 1 := by
  rw [giOneSubI_toComplex]
  apply Complex.ext <;> norm_num [Complex.normSq]

/--
@isnad1 id=eq.0h0v.s6.06cca7d387be from=translated src=- shape=25426bba vocab=fc98caea
-/
theorem giOneSubI_inv :
    (giOneSubI : ℂ)⁻¹ = (giOneAddI : ℂ) / 2 := by
  rw [giOneSubI_toComplex, giOneAddI_toComplex]
  apply Complex.ext <;> norm_num [Complex.normSq]

/--
@isnad1 id=eq.0h0v.s6.3161c69277f7 from=translated src=- shape=25426bba vocab=fc98caea
-/
theorem giOneAddI_inv :
    (giOneAddI : ℂ)⁻¹ = (giOneSubI : ℂ) / 2 := by
  rw [giOneSubI_toComplex, giOneAddI_toComplex]
  apply Complex.ext <;> norm_num [Complex.normSq]

/--
@isnad1 id=eq.0h3v.s8.579ca88f98f0 from=translated src=- shape=cd5512a9 vocab=cafae611
-/
theorem gaussianSummand_inverse_expansion
    (n : ℕ) (j : ℤ) (m : LeibnizIndex n) :
    gaussianSummand n j m =
      (binomialWeight n m : ℂ) *
        2 ^ ((5 * 3714 - 2 * 5570) * n - 1 + j.toNat + m.m1) *
        5 ^ (2 * (1857 + 3714 - 5570) * n + j.toNat) *
        (1 - Complex.I)⁻¹ ^ m.m4 *
        (1 + Complex.I)⁻¹ ^ m.m5 *
        (2 + Complex.I) ^ (m.m2 + m.m5) *
        (2 - Complex.I) ^ (m.m3 + m.m4) := by
  simp only [gaussianSummand, zpow_neg, zpow_natCast]
  rw [← inv_pow, ← inv_pow]

/--
@isnad1 id=eq.0h3v.s8.ea910af8ade7 from=translated src=- shape=a2d5fd5d vocab=efd34d98
-/
theorem gaussianSummand_factor_expansion
    (n : ℕ) (j : ℤ) (m : LeibnizIndex n) :
    gaussianSummand n j m =
      (binomialWeight n m : ℂ) *
        2 ^ ((5 * 3714 - 2 * 5570) * n - 1 + j.toNat + m.m1) *
        5 ^ (2 * (1857 + 3714 - 5570) * n + j.toNat) *
        ((1 + Complex.I) / 2) ^ m.m4 *
        ((1 - Complex.I) / 2) ^ m.m5 *
        (2 + Complex.I) ^ (m.m2 + m.m5) *
        (2 - Complex.I) ^ (m.m3 + m.m4) := by
  rw [gaussianSummand_inverse_expansion]
  have h1 : (1 - Complex.I)⁻¹ = (1 + Complex.I) / 2 := by
    apply Complex.ext <;> norm_num [Complex.normSq]
  have h2 : (1 + Complex.I)⁻¹ = (1 - Complex.I) / 2 := by
    apply Complex.ext <;> norm_num [Complex.normSq]
  rw [h1, h2]

/--
@isnad1 id=ex.1h6v.s8.6095b811afc1 from=translated src=- shape=6c9fb15e vocab=2d63cdc4
-/
theorem gaussian_factor_is_gaussian_integer
    (B F m₄ m₅ u v : ℕ) (h : m₄ + m₅ ≤ B) :
    ∃ z : GI, (z : ℂ) =
      (2 : ℂ) ^ B * (5 : ℂ) ^ F *
        ((1 + Complex.I) / 2) ^ m₄ *
        ((1 - Complex.I) / 2) ^ m₅ *
        (2 + Complex.I) ^ u * (2 - Complex.I) ^ v := by
  let z : GI :=
    (2 : GI) ^ (B - m₄ - m₅) * (5 : GI) ^ F * giOneAddI ^ m₄ * giOneSubI ^ m₅ *
      giTwoAddI ^ u * giTwoSubI ^ v
  refine ⟨z, ?_⟩
  dsimp [z]
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow,
    map_pow, map_pow, map_pow]
  rw [giOneAddI_toComplex, giOneSubI_toComplex, giTwoAddI_toComplex,
    giTwoSubI_toComplex]
  have hpow : B - m₄ - m₅ + m₄ + m₅ = B := by omega
  have htwo : (GaussianInt.toComplex (2 : GI)) = (2 : ℂ) := by
    simpa using (map_natCast GaussianInt.toComplex 2)
  have hfive : (GaussianInt.toComplex (5 : GI)) = (5 : ℂ) := by
    simpa using (map_natCast GaussianInt.toComplex 5)
  rw [htwo, hfive]
  rw [div_pow, div_pow]
  have hplus : (2 + Complex.I : ℂ) ≠ 0 := by
    intro hzero
    have := congrArg Complex.re hzero
    norm_num at this
  have hminus : (2 - Complex.I : ℂ) ≠ 0 := by
    intro hzero
    have := congrArg Complex.re hzero
    norm_num at this
  have hfactor (a b : ℂ) :
      (2 : ℂ) ^ B * (a / 2) ^ m₄ * (b / 2) ^ m₅ =
        (2 : ℂ) ^ (B - m₄ - m₅) * a ^ m₄ * b ^ m₅ := by
    rw [div_pow, div_pow]
    field_simp [show (2 : ℂ) ≠ 0 by norm_num]
    have hrel : (2 : ℂ) ^ B =
        2 ^ (B - m₄ - m₅) * 2 ^ (m₄ + m₅) := by
      have hpow' : B - m₄ - m₅ + (m₄ + m₅) = B := by omega
      rw [← pow_add, hpow']
    calc
      _ = 2 ^ B * a ^ m₄ * b ^ m₅ := by ring
      _ = (2 ^ (B - m₄ - m₅) * 2 ^ (m₄ + m₅)) * a ^ m₄ * b ^ m₅ := by
        rw [hrel]
      _ = _ := by rw [pow_add]; ring
  calc
    _ = (5 : ℂ) ^ F *
        (2 : ℂ) ^ (B - m₄ - m₅) * (1 + Complex.I) ^ m₄ *
        (1 - Complex.I) ^ m₅ * (2 + Complex.I) ^ u *
        (2 - Complex.I) ^ v := by ring
    _ = (5 : ℂ) ^ F *
        ((2 : ℂ) ^ B * ((1 + Complex.I) / 2) ^ m₄ *
          ((1 - Complex.I) / 2) ^ m₅) *
        (2 + Complex.I) ^ u * (2 - Complex.I) ^ v := by
      rw [hfactor]
      ring
    _ = _ := by
      rw [div_pow, div_pow]
      ring

def gaussianBaseNat (n : ℕ) (j : ℤ) (m : LeibnizIndex n) : ℕ :=
  7430 * n - 1 + j.toNat + m.m1

def gaussianFiveNat (n : ℕ) (j : ℤ) : ℕ :=
  2 * n + j.toNat

/--
@isnad1 id=eq.1h3v.s6.bf9d5ec98cd5 from=translated src=- shape=9a852b91 vocab=3442e200
-/
theorem gaussianBaseNat_cast (n : ℕ) (j : ℤ) (m : LeibnizIndex n)
    (hn : 1 ≤ n) :
    (gaussianBaseNat n j m : ℤ) =
      (5 * 3714 - 2 * 5570 : ℤ) * n - 1 + j.toNat + m.m1 := by
  unfold gaussianBaseNat
  have hn' : 1 ≤ 7430 * n := by omega
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hn']
  norm_num

/--
@isnad1 id=eq.0h2v.s6.72c9ec380ede from=translated src=- shape=c14cb9d3 vocab=15f76bda
-/
theorem gaussianFiveNat_cast (n : ℕ) (j : ℤ) :
    (gaussianFiveNat n j : ℤ) =
      (2 * (1857 + 3714 - 5570 : ℤ)) * n + j.toNat := by
  unfold gaussianFiveNat
  norm_num

/--
@isnad1 id=le.2h3v.s5.46836e906cbe from=translated src=- shape=88f56018 vocab=5c905892
-/
theorem gaussianBaseNat_clears_inverse_indices
    (n : ℕ) (j : ℤ) (m : LeibnizIndex n)
    (hm : LeibnizIndex.Valid n j m) (hn : 1 ≤ n) :
    m.m4 + m.m5 ≤ gaussianBaseNat n j m := by
  rcases hm with ⟨hsum, hm1, hm2, hm3, hm4, hm5⟩
  unfold gaussianBaseNat
  norm_num at *
  omega

/--
@isnad1 id=ex.2h3v.s6.840606e0cf02 from=translated src=- shape=52bc7787 vocab=6be11710
-/
theorem gaussianSummand_is_gaussian_integer
    (n : ℕ) (j : ℤ) (m : LeibnizIndex n)
    (hm : LeibnizIndex.Valid n j m) (hn : 1 ≤ n) :
    ∃ z : GI, gaussianSummand n j m = (z : ℂ) := by
  have hbase := gaussianBaseNat_clears_inverse_indices n j m hm hn
  obtain ⟨z, hz⟩ := gaussian_factor_is_gaussian_integer
    (gaussianBaseNat n j m) (gaussianFiveNat n j) m.m4 m.m5
    (m.m2 + m.m5) (m.m3 + m.m4) hbase
  refine ⟨(binomialWeight n m : GI) * z, ?_⟩
  have hbpow :
      (2 : ℂ) ^ ((5 * 3714 - 2 * 5570) * n - 1 + j.toNat + m.m1) =
        (2 : ℂ) ^ gaussianBaseNat n j m := by
    congr 1
  have hfpow :
      (5 : ℂ) ^ (2 * (1857 + 3714 - 5570) * n + j.toNat) =
        (5 : ℂ) ^ gaussianFiveNat n j := by
    congr 1
  rw [gaussianSummand_factor_expansion]
  rw [hbpow, hfpow]
  simp only [map_mul]
  have hbin : GaussianInt.toComplex (binomialWeight n m : GI) =
      (binomialWeight n m : ℂ) := by
    simpa using (map_natCast GaussianInt.toComplex (binomialWeight n m))
  rw [hbin]
  rw [hz]
  ring

/--
@isnad1 id=ex.2h3v.s6.5c116b87bd1a from=translated src=- shape=5548d449 vocab=00b70990
-/
theorem gaussianSummand_sum_is_gaussian_integer
    (n : ℕ) (j : ℤ) (S : Finset (LeibnizIndex n))
    (hvalid : ∀ m ∈ S, LeibnizIndex.Valid n j m) (hn : 1 ≤ n) :
    ∃ z : GI, (∑ m ∈ S, gaussianSummand n j m) = (z : ℂ) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      simp
  | @insert m S hm ih =>
      have hmvalid : LeibnizIndex.Valid n j m := hvalid m (by simp)
      have hSvalid : ∀ x ∈ S, LeibnizIndex.Valid n j x := by
        intro x hx
        exact hvalid x (by simp [hx])
      obtain ⟨zm, hzm⟩ := gaussianSummand_is_gaussian_integer n j m hmvalid hn
      obtain ⟨zS, hzS⟩ := ih hSvalid
      refine ⟨zm + zS, ?_⟩
      simp only [Finset.sum_insert hm, map_add, hzm, hzS]

/--
@isnad1 id=valid.1h3v.s4.a74c5f70524d from=translated src=- shape=8b4bccca vocab=e10f33a1
-/
theorem conjugateIndex_valid
    (n : ℕ) (j : ℤ) (m : LeibnizIndex n)
    (hm : LeibnizIndex.Valid n j m) :
    LeibnizIndex.Valid n j (conjugateIndex m) := by
  rcases hm with ⟨hsum, hm1, hm2, hm3, hm4, hm5⟩
  dsimp [conjugateIndex, LeibnizIndex.Valid]
  omega

/--
@isnad1 id=ex.2h3v.s5.b6325e40bc20 from=translated src=- shape=3630cc65 vocab=6147c82b
-/
theorem gaussianPaired_is_integer
    (n : ℕ) (j : ℤ) (m : LeibnizIndex n)
    (hm : LeibnizIndex.Valid n j m) (hn : 1 ≤ n) :
    ∃ z : ℤ, gaussianPaired n j m = (z : ℂ) := by
  obtain ⟨z₁, hz₁⟩ := gaussianSummand_is_gaussian_integer n j m hm hn
  obtain ⟨z₂, hz₂⟩ := gaussianSummand_is_gaussian_integer n j
    (conjugateIndex m) (conjugateIndex_valid n j m hm) hn
  let z : GI := z₁ + z₂
  have hz : (z : ℂ) = gaussianPaired n j m := by
    dsimp [z, gaussianPaired]
    rw [map_add, hz₁, hz₂]
  obtain ⟨r, hr⟩ := gaussianPaired_is_real n j m
  have hre : (z : ℂ) = (r : ℂ) := hz.trans hr.symm
  have him : z.im = 0 := by
    have him' := congrArg Complex.im hre
    have himc : (z : ℂ).im = 0 := by
      norm_num at him' ⊢
      exact him'
    have himr : ((z.im : ℤ) : ℝ) = 0 := by
      rw [GaussianInt.intCast_im]
      exact himc
    exact_mod_cast himr
  refine ⟨z.re, ?_⟩
  rw [← hz]
  rw [GaussianInt.toComplex_def, him]
  norm_num

/--
@isnad1 id=ex.2h3v.s6.036d3280a5ed from=translated src=- shape=9dbb2dfc vocab=17d5a0b5
-/
theorem gaussianPaired_sum_is_integer
    (n : ℕ) (j : ℤ) (S : Finset (LeibnizIndex n))
    (hvalid : ∀ m ∈ S, LeibnizIndex.Valid n j m) (hn : 1 ≤ n) :
    ∃ z : ℤ, (∑ m ∈ S, gaussianPaired n j m) = (z : ℂ) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      simp
  | @insert m S hm ih =>
      have hmvalid : LeibnizIndex.Valid n j m := hvalid m (by simp)
      have hSvalid : ∀ x ∈ S, LeibnizIndex.Valid n j x := by
        intro x hx
        exact hvalid x (by simp [hx])
      obtain ⟨zm, hzm⟩ := gaussianPaired_is_integer n j m hmvalid hn
      obtain ⟨zS, hzS⟩ := ih hSvalid
      refine ⟨zm + zS, ?_⟩
      rw [Finset.sum_insert hm, hzm, hzS]
      norm_num

end PiIrrationality
