/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.QuantumGroup.CrystalBasis.TensorSl2
import Tengoku.LieLean.LieLean.Algebra.QuantumGroup.CrystalBasis.Valuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strings in a tensor product of two strings

Let `η ∈ M₁ᵃ`, `ζ ∈ M₂ᵇ` be primitive vectors of integrable `U_q(𝔰𝔩₂)`-modules and put
`uᵢ = F^{(i)} η`, `vⱼ = F^{(j)} ζ`. In `M₁ ⊗ M₂` (`QuantumGroup.IntegrableSl2.tensor`, Kashiwara's
coproduct) the vector
`w_s = Σ_{i ≤ s} cᵢ uᵢ ⊗ v_{s-i}`, `c₀ = 1`, `c_{i+1} = -cᵢ [b-s+i+1] q^{b-2s+2i+2} / [a-i]`
is primitive of weight `a + b - 2s` for `s ≤ a` (`QuantumGroup.IntegrableSl2.tensor_E_tensorHigh`),
and the vector
`z_s = Σ_{i ≤ s} dᵢ u_{a-s+i} ⊗ v_{b-i}`, `d₀ = 1`, `d_{i+1} = -dᵢ [a-s+i+1] q^{a-2s+2i+2} / [b-i]`
is killed by `F` for `s ≤ b` (`QuantumGroup.IntegrableSl2.tensor_F_tensorLow`).

Let `A` be a local ring with `ϖ ∈ A` a non-unit mapping to `q`, and `L` the `A`-span of the
`uᵢ ⊗ vⱼ`. Then modulo `ϖ L` (our own computation, via the orders of the coefficients):
* `F^{(r)} w_s ≡ u_r ⊗ v_s` for `r ≤ a - s` (`QuantumGroup.IntegrableSl2.tensor_dF_tensorHigh_sub`);
* `E^{(t)} z_s ≡ u_{a-s} ⊗ v_{b-t}` for `t ≤ b - s`
  (`QuantumGroup.IntegrableSl2.tensor_dE_tensorLow_sub`).
Every term other than the leading one has a coefficient in `ϖ A`: the term
`uᵢ ⊗ v_{s-i} ↦ u_{i+m} ⊗ v_{s-i+n}` of `F^{(r)} w_s` (`m + n = r`) has order
`i(a - s + 1 - r) + n(a - s - m)`. These are the two halves of the strings of the crystal
`B(a) ⊗ B(b)` through `u₀ ⊗ v_s`, which meet at `u_{a-s} ⊗ v_s`.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.4
  (Thm. 4.4.3 is proved there by induction on `b` from the case `b = 1`).
* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §1.
-/

open TensorProduct Finset

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁]
  [AddCommGroup M₂] [Module k M₂] (V₁ : IntegrableSl2 q M₁) (V₂ : IntegrableSl2 q M₂)
  (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
  {a b : ℕ} {η : M₁} {ζ : M₂}

/-! ### The primitive vectors `w_s` -/

variable (q a b) in
/-- The coefficients `cᵢ` of `w_s`.-/
noncomputable def highCoeff (s : ℕ) : ℕ → k
  | 0 => 1
  | i + 1 => -highCoeff s i * qIntZ q ((b : ℤ) - s + i + 1) * q ^ ((b : ℤ) - 2 * s + 2 * i + 2) /
      qIntZ q ((a : ℤ) - i)

variable (η ζ a b) in
/-- `w_s = Σ_{i ≤ s} cᵢ uᵢ ⊗ v_{s-i}`.-/
noncomputable def tensorHigh (s : ℕ) : M₁ ⊗[k] M₂ :=
  ∑ i ∈ range (s + 1), highCoeff q a b s i • (V₁.dF i η ⊗ₜ V₂.dF (s - i) ζ)

include hq0 hq

/-! ### The lowest vectors `z_s` -/

variable (q a b) in
/-- The coefficients `dᵢ` of `z_s`.-/
noncomputable def lowCoeff (s : ℕ) : ℕ → k
  | 0 => 1
  | i + 1 => -lowCoeff s i * qIntZ q ((a : ℤ) - s + i + 1) * q ^ ((a : ℤ) - 2 * s + 2 * i + 2) /
      qIntZ q ((b : ℤ) - i)

variable (η ζ a b) in
/-- `z_s = Σ_{i ≤ s} dᵢ u_{a-s+i} ⊗ v_{b-i}`.-/
noncomputable def tensorLow (s : ℕ) : M₁ ⊗[k] M₂ :=
  ∑ i ∈ range (s + 1), lowCoeff q a b s i • (V₁.dF (a - s + i) η ⊗ₜ V₂.dF (b - i) ζ)

/-! ### Divided powers of `w_s` and `z_s` -/

/-! ### Orders of the coefficients -/

section Orders

variable {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

omit hq0 hq in
/--
@isnad1 id=isunitpo.4h4v.s8.aa2b3cef72ee from=translated src=- shape=cccd7e49 vocab=50529455
-/
lemma isUnitPow_qIntZ [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hq : ∀ n : ℕ, 0 < n → algebraMap A k ϖ ^ n ≠ 1) (hq0 : algebraMap A k ϖ ≠ 0) {n : ℤ}
    (hn : 0 < n) : IsUnitPow ϖ (1 - n) (qIntZ (algebraMap A k ϖ) n) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
  rw [qIntZ_natCast (sub_inv_ne_zero_of_pow_ne_one hq0 hq)]
  exact (isOnePow_qInt hq0 (by omega)).isUnitPow hϖ

omit hq0 hq in
/--
@isnad1 id=isunitpo.3h5v.s8.9adbee9846f9 from=translated src=- shape=de57cac4 vocab=137849a6
-/
lemma isUnitPow_qBinomial [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hq0 : algebraMap A k ϖ ≠ 0) {n m : ℕ} (hmn : m ≤ n) :
    IsUnitPow ϖ (-(m * (n - m) : ℕ)) (qBinomial (algebraMap A k ϖ) n m) :=
  (isOnePow_qBinomial hq0 hmn).isUnitPow hϖ

variable (k ϖ) in
/-- Sums of vectors `κ • g p` with `κ ∈ ϖ A`.-/
def smallSpan {M : Type*} [AddCommGroup M] [Module k M] (g : ℕ × ℕ → M) : AddSubmonoid M :=
  AddSubmonoid.closure {x | ∃ (κ : k) (p : ℕ × ℕ), InPow ϖ 1 κ ∧ x = κ • g p}

omit hq0 hq in
/--
@isnad1 id=mem.1h7v.s7.d724eb1a8ad2 from=translated src=- shape=64915a38 vocab=9ad11060
-/
lemma smul_mem_smallSpan {M : Type*} [AddCommGroup M] [Module k M] (g : ℕ × ℕ → M) {κ : k}
    (hκ : InPow ϖ 1 κ) (p : ℕ × ℕ) : κ • g p ∈ smallSpan k ϖ g :=
  AddSubmonoid.subset_closure ⟨κ, p, hκ, rfl⟩

variable [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖq : algebraMap A k ϖ = q)
include hϖ hϖq

/-- `cᵢ ∈ q^{i(a-s+1)} A×`.
@isnad1 id=isunitpo.7h8v.s8.71e4f86d67db from=translated src=- shape=80f1b3ff vocab=181807e4
-/
lemma isUnitPow_highCoeff {s : ℕ} (hsa : s ≤ a) (hsb : s ≤ b) :
    ∀ i ≤ s, IsUnitPow ϖ ((i : ℤ) * ((a : ℤ) - s + 1)) (highCoeff q a b s i) := by
  subst hϖq
  intro i
  induction i with
  | zero => intro _; simpa [highCoeff] using isUnitPow_one
  | succ i ih =>
    intro hi
    rw [highCoeff]
    have h := (((ih (by omega)).neg.mul hq0 (isUnitPow_qIntZ hϖ hq hq0
      (n := (b : ℤ) - s + i + 1) (by omega))).mul hq0
      (isUnitPow_zpow ((b : ℤ) - 2 * s + 2 * i + 2))).div hq0
      (isUnitPow_qIntZ hϖ hq hq0 (n := (a : ℤ) - i) (by omega))
    convert h using 1
    push_cast; ring

/-- `dᵢ ∈ q^{i(b-s+1)} A×`.
@isnad1 id=isunitpo.7h8v.s8.2fe54358afc8 from=translated src=- shape=6bb9a399 vocab=846b61e4
-/
lemma isUnitPow_lowCoeff {s : ℕ} (hsa : s ≤ a) (hsb : s ≤ b) :
    ∀ i ≤ s, IsUnitPow ϖ ((i : ℤ) * ((b : ℤ) - s + 1)) (lowCoeff q a b s i) := by
  subst hϖq
  intro i
  induction i with
  | zero => intro _; simpa [lowCoeff] using isUnitPow_one
  | succ i ih =>
    intro hi
    rw [lowCoeff]
    have h := (((ih (by omega)).neg.mul hq0 (isUnitPow_qIntZ hϖ hq hq0
      (n := (a : ℤ) - s + i + 1) (by omega))).mul hq0
      (isUnitPow_zpow ((a : ℤ) - 2 * s + 2 * i + 2))).div hq0
      (isUnitPow_qIntZ hϖ hq hq0 (n := (b : ℤ) - i) (by omega))
    convert h using 1
    push_cast; ring

end Orders

end IntegrableSl2

end LieLean.QuantumGroup
