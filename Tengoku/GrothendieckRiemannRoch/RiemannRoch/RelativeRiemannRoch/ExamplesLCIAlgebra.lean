/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.RegularLocalRing.Defs
import Tengoku.Seed.RingTheory.Polynomial.Eisenstein.Basic
import Tengoku.Seed.RingTheory.KrullDimension.Polynomial
import Tengoku.Seed.RingTheory.KrullDimension.NonZeroDivisors
import Tengoku.Seed.Algebra.TrivSqZeroExt.Basic
import Tengoku.Seed.RingTheory.Localization.AtPrime.Basic
import Tengoku.Seed.RingTheory.Ideal.Height

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# G2E4 algebra: the affine nodal cubic over `K[x][y]` is a non-regular domain

`k = K[x][y]` (`Polynomial (Polynomial K)`), `F = y² − x³ − x²` (`nodal`).

The names say "nodal": the singular point is an ordinary node when `char k ≠ 2`; in
characteristic `2` the affine equation is `(y + x)² = x³`, a cusp. No statement here asserts an
ordinary node; non-regularity and all computations hold in every characteristic.

* `ExamplesLCI.nodal_prime` : `F` is prime (Eisenstein at `(x + 1)` in `K[x]`, monic in `y`);
* `ExamplesLCI.ringKrullDim_k` : `dim k = 2`;
* `ExamplesLCI.origin` : the prime `(x, y)/(F)` of `R = k/(F)`, as the kernel of the evaluation at the
  origin;
* `ExamplesLCI.not_isRegularLocalRing` : the local ring `R_(x,y)` is NOT regular: its dimension is
  `≤ 1` but its maximal ideal is not principal (the map to `K ⊕ (K × K)ε` sending `x ↦ ε₁`,
  `y ↦ ε₂` kills `F ∈ (x, y)²`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace ExamplesLCI

open Polynomial IsLocalRing

variable (K : Type u) [Field K]

/-- The coefficient ring `k = K[x][y]` (outer variable `y`, inner variable `x`).-/
abbrev Kxy : Type u := Polynomial (Polynomial K)

/-- The nodal cubic `F = y² − x³ − x² = y² − x²(x + 1)`.-/
def nodal : Kxy K := X ^ 2 - C (X ^ 2 * (X + 1))

/--
@isnad1 id=monic.0h1v.s4.76e737ebc349 from=translated src=- shape=aa7e0af4 vocab=04a0c635
-/
theorem nodal_monic : (nodal K).Monic := by
  unfold nodal
  exact monic_X_pow_sub_C _ (by norm_num)

/--
@isnad1 id=eq.0h1v.s5.00074fd013dd from=translated src=- shape=46a7a1bc vocab=60b1458b
-/
theorem nodal_natDegree : (nodal K).natDegree = 2 := by
  unfold nodal
  exact natDegree_X_pow_sub_C

/--
@isnad1 id=ne.0h1v.s5.72800dddce70 from=translated src=- shape=bbb5e9b9 vocab=343db248
-/
theorem nodal_ne_zero : nodal K ≠ 0 := (nodal_monic K).ne_zero

/-- `(x + 1)` is prime in `K[x]`.
@isnad1 id=prime.0h1v.s6.d2ddffb380b3 from=translated src=- shape=a302770b vocab=40b082ff
-/
theorem prime_X_add_one : Prime (X + 1 : Polynomial K) := by
  have h : (X + 1 : Polynomial K) = X - C (-1) := by simp [sub_eq_add_neg]
  rw [h]
  exact prime_X_sub_C (-1)

/--
@isnad1 id=isprime.0h1v.s7.519cdda68e28 from=translated src=- shape=356f5264 vocab=852c8a5b
-/
theorem span_X_add_one_isPrime : (Ideal.span {(X + 1 : Polynomial K)}).IsPrime :=
  (Ideal.span_singleton_prime (prime_X_add_one K).ne_zero).2 (prime_X_add_one K)

/--
@isnad1 id=iseisens.0h1v.s7.96c05ed1c5d8 from=translated src=- shape=7ba0c86f vocab=84c4e07b
-/
theorem nodal_isEisensteinAt :
    (nodal K).IsEisensteinAt (Ideal.span {(X + 1 : Polynomial K)}) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [(nodal_monic K).leadingCoeff]
    intro h
    exact (span_X_add_one_isPrime K).ne_top ((Ideal.eq_top_iff_one _).2 h)
  · intro n hn
    rw [nodal_natDegree] at hn
    rw [Ideal.mem_span_singleton]
    unfold nodal
    interval_cases n
    · simp only [coeff_sub, coeff_X_pow, coeff_C_zero]
      norm_num
    · simp only [coeff_sub, coeff_X_pow, coeff_C]
      norm_num
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold nodal
    simp only [coeff_sub, coeff_X_pow, coeff_C_zero, OfNat.zero_ne_ofNat, ite_false, zero_sub,
      dvd_neg]
    rintro ⟨q, hq⟩
    have h1 : (X + 1 : Polynomial K) ≠ 0 := by simpa using X_add_C_ne_zero (1 : K)
    have h2 : (X ^ 2 : Polynomial K) = (X + 1) * q := by
      apply mul_right_cancel₀ h1
      rw [hq]; ring
    have h3 := congrArg (eval (-1 : K)) h2
    simp at h3

/--
@isnad1 id=irreduci.0h1v.s5.80e9e9de8019 from=translated src=- shape=aa7e0af4 vocab=7e747129
-/
theorem nodal_irreducible : Irreducible (nodal K) :=
  (nodal_isEisensteinAt K).irreducible (span_X_add_one_isPrime K) (nodal_monic K).isPrimitive
    (by rw [nodal_natDegree]; norm_num)

/--
@isnad1 id=prime.0h1v.s5.b0d41e234284 from=translated src=- shape=aa7e0af4 vocab=2f792334
-/
theorem nodal_prime : Prime (nodal K) := (nodal_irreducible K).prime

/-- The affine nodal cubic ring `R = k/(F)`.-/
def NodalRing : Type u := Kxy K ⧸ Ideal.span {nodal K}

instance nodalRing_commRing : CommRing (NodalRing K) := Ideal.Quotient.commRing _

/-- The quotient map `k → R`.-/
def toNodal : Kxy K →+* NodalRing K := Ideal.Quotient.mk _

/--
@isnad1 id=surjecti.0h1v.s6.6301bb58deab from=translated src=- shape=c5bed54c vocab=114bd6e3
-/
theorem toNodal_surjective : Function.Surjective (toNodal K) := Ideal.Quotient.mk_surjective

/--
@isnad1 id=eq.0h1v.s7.c0e14e6c8c9b from=translated src=- shape=bd9f96e7 vocab=35eafbb8
-/
theorem toNodal_nodal : toNodal K (nodal K) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

/--
@isnad1 id=isnoethe.0h1v.s4.56b41cb4b884 from=translated src=- shape=1666ae32 vocab=4959ab2d
-/
instance nodalRing_isNoetherianRing : IsNoetherianRing (NodalRing K) :=
  Ideal.Quotient.isNoetherianRing (Ideal.span {nodal K})

/--
@isnad1 id=eq.0h1v.s5.75e237dc7354 from=translated src=- shape=fe60498e vocab=9fcc9c53
-/
theorem ringKrullDim_k : ringKrullDim (Kxy K) = 2 := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, Polynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field]
  rfl

/--
@isnad1 id=le.0h1v.s7.e0ad9a07e556 from=translated src=- shape=346c43db vocab=7115e070
-/
theorem ringKrullDim_quotient_le :
    ringKrullDim (Kxy K ⧸ Ideal.span {nodal K}) ≤ 1 := by
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_of_ne_zero (nodal_ne_zero K))
  rw [ringKrullDim_k] at h
  -- `d + 1 ≤ 2 → d ≤ 1` in `WithBot ℕ∞`
  generalize ringKrullDim (Kxy K ⧸ Ideal.span {nodal K}) = d at h ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe d =>
      have h' : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
        exact h
      have h'' : d + 1 ≤ 2 := ENat.natCast_le_natCast.1 (WithBot.coe_le_coe.1 h')
      have h3 : d ≤ 1 := by omega
      exact WithBot.coe_le_coe.2 (ENat.natCast_le_natCast.2 h3)

/--
@isnad1 id=le.0h1v.s5.1401461dbb2b from=translated src=- shape=fe60498e vocab=0b47f329
-/
theorem ringKrullDim_nodalRing_le : ringKrullDim (NodalRing K) ≤ 1 :=
  ringKrullDim_quotient_le K

/-! ## The first-order jet at the origin -/

/-- `D = K ⊕ (K × K)ε`, square-zero.-/
abbrev Jet : Type u := TrivSqZeroExt K (K × K)

/-- `K[x] → D`, `x ↦ ε₁`.-/
def jetX : Polynomial K →+* Jet K :=
  eval₂RingHom (TrivSqZeroExt.inlHom K (K × K)) (TrivSqZeroExt.inr ((1 : K), (0 : K)))

/-- `K[x][y] → D`, `x ↦ ε₁`, `y ↦ ε₂`.-/
def jetXY : Kxy K →+* Jet K :=
  eval₂RingHom (jetX K) (TrivSqZeroExt.inr ((0 : K), (1 : K)))

/--
@isnad1 id=eq.0h1v.s9.6fb753fafdc6 from=translated src=- shape=de961291 vocab=6df1be15
-/
theorem jetXY_x : jetXY K (C X) = TrivSqZeroExt.inr ((1 : K), (0 : K)) := by
  simp [jetXY, jetX]

/--
@isnad1 id=eq.0h1v.s8.59b833ad56d1 from=translated src=- shape=3ef1a510 vocab=fafc6044
-/
theorem jetXY_y : jetXY K X = TrivSqZeroExt.inr ((0 : K), (1 : K)) := by
  simp [jetXY]

/--
@isnad1 id=eq.0h1v.s8.c8590957e834 from=translated src=- shape=bd9f96e7 vocab=0641cc3c
-/
theorem jetXY_nodal : jetXY K (nodal K) = 0 := by
  simp only [nodal, map_sub, map_pow, map_mul, map_add, map_one, jetXY_y, jetXY_x]
  simp [pow_two, TrivSqZeroExt.inr_mul_inr]

/-- The jet map on `R = k/(F)`.-/
def jetR : NodalRing K →+* Jet K :=
  Ideal.Quotient.lift (Ideal.span {nodal K}) (jetXY K) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, jetXY_nodal, mul_zero])

/--
@isnad1 id=eq.0h2v.s9.4d1a04914862 from=translated src=- shape=189530c9 vocab=8518d697
-/
theorem jetR_toNodal (w : Kxy K) : jetR K (toNodal K w) = jetXY K w := rfl

/-- Evaluation at the origin.-/
def evalOrigin : NodalRing K →+* K := (TrivSqZeroExt.fstHom K K (K × K)).toRingHom.comp (jetR K)

/-- The origin `(x, y)/(F)`, the singular point.-/
def origin : Ideal (NodalRing K) := RingHom.ker (evalOrigin K)

/--
@isnad1 id=isprime.0h1v.s4.2e9b588f3d05 from=translated src=- shape=aa7e0af4 vocab=480c6830
-/
instance origin_isPrime : (origin K).IsPrime := RingHom.ker_isPrime _

/-- The local ring of the nodal cubic at the node.-/
abbrev NodeLocal : Type u := Localization.AtPrime (origin K)

/-- The jet map extends to the local ring.-/
def jetL : NodeLocal K →+* Jet K :=
  IsLocalization.lift (M := (origin K).primeCompl) (S := NodeLocal K) (g := jetR K)
    (fun s => by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]
      exact s.2)

/--
@isnad1 id=eq.1h2v.s9.741934991740 from=translated src=- shape=0f203aeb vocab=bcb83009
-/
theorem jetL_fst_of_mem (z : NodeLocal K) (hz : z ∈ maximalIdeal (NodeLocal K)) :
    (jetL K z).fst = 0 := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.mk'_surjective (origin K).primeCompl z
  have h' : IsLocalization.mk' (NodeLocal K) a s = z := h
  subst h'
  rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (NodeLocal K) (origin K)] at hz
  rw [jetL, IsLocalization.lift_mk', TrivSqZeroExt.fst_mul]
  have : (jetR K a).fst = 0 := hz
  rw [this, zero_mul]

/--
@isnad1 id=not.0h1v.s7.9cb5100e89ab from=translated src=- shape=1b2dc084 vocab=f0b9083d
-/
theorem maximalIdeal_not_principal :
    ¬ ∃ t : NodeLocal K, maximalIdeal (NodeLocal K) = Ideal.span {t} := by
  rintro ⟨t, ht⟩
  let xL : NodeLocal K := algebraMap (NodalRing K) (NodeLocal K) (toNodal K (C X))
  let yL : NodeLocal K := algebraMap (NodalRing K) (NodeLocal K) (toNodal K X)
  have hjx : jetL K xL = TrivSqZeroExt.inr ((1 : K), (0 : K)) := by
    simp only [xL, jetL, IsLocalization.lift_eq, jetR_toNodal, jetXY_x]
  have hjy : jetL K yL = TrivSqZeroExt.inr ((0 : K), (1 : K)) := by
    simp only [yL, jetL, IsLocalization.lift_eq, jetR_toNodal, jetXY_y]
  have hmem : ∀ w : Kxy K, (jetXY K w).fst = 0 →
      algebraMap (NodalRing K) (NodeLocal K) (toNodal K w) ∈ maximalIdeal _ := by
    intro w hw
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (NodeLocal K) (origin K)]
    exact hw
  have hxm : xL ∈ maximalIdeal (NodeLocal K) := hmem _ (by rw [jetXY_x]; rfl)
  have hym : yL ∈ maximalIdeal (NodeLocal K) := hmem _ (by rw [jetXY_y]; rfl)
  have htm : t ∈ maximalIdeal (NodeLocal K) := by rw [ht]; exact Ideal.subset_span rfl
  rw [ht, Ideal.mem_span_singleton'] at hxm hym
  obtain ⟨a, ha⟩ := hxm
  obtain ⟨b, hb⟩ := hym
  have ht0 := jetL_fst_of_mem K t htm
  have ex := congrArg (fun z => (jetL K z).snd) ha
  have ey := congrArg (fun z => (jetL K z).snd) hb
  simp only [map_mul, TrivSqZeroExt.snd_mul, ht0, hjx, hjy, TrivSqZeroExt.snd_inr,
    MulOpposite.op_zero, zero_smul, add_zero] at ex ey
  have e1 := congrArg Prod.fst ex
  have e2 := congrArg Prod.snd ex
  have e3 := congrArg Prod.fst ey
  have e4 := congrArg Prod.snd ey
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2 e3 e4
  -- e1 : α u = 1, e2 : α v = 0, e4 : β v = 1
  have hα : (jetL K a).fst ≠ 0 := by
    intro h; rw [h, zero_mul] at e1; exact zero_ne_one e1
  have hv : (jetL K t).snd.2 = 0 := by
    rcases mul_eq_zero.1 e2 with h | h
    · exact absurd h hα
    · exact h
  rw [hv, mul_zero] at e4
  exact zero_ne_one e4

/-- **The node is a singular point**: `R_(x,y)` is not a regular local ring.
@isnad1 id=not.0h1v.s6.364292e07411 from=translated src=- shape=fba248a8 vocab=0a3444e1
-/
theorem not_isRegularLocalRing : ¬ IsRegularLocalRing (NodeLocal K) := by
  intro hreg
  have hdim : ringKrullDim (NodeLocal K) ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (origin K) (NodeLocal K)]
    exact (Ideal.height_le_ringKrullDim_of_isPrime).trans (ringKrullDim_nodalRing_le K)
  have hspan := hreg.spanFinrank_maximalIdeal
  rw [← hspan] at hdim
  have hle : (maximalIdeal (NodeLocal K)).spanFinrank ≤ 1 := by exact_mod_cast hdim
  have hfg : (maximalIdeal (NodeLocal K)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan'⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank hfg
  have hs1 : s.encard ≤ 1 := by rw [hs]; exact_mod_cast hle
  rcases Set.encard_le_one_iff_eq.1 hs1 with h | ⟨t, rfl⟩
  · subst h
    apply maximalIdeal_not_principal K
    refine ⟨0, ?_⟩
    rw [← hspan']
    simp
  · exact maximalIdeal_not_principal K ⟨t, hspan'.symm⟩

end ExamplesLCI
