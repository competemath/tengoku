/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.QuantumGroup.QBinomialSeries
import Tengoku.Seed.LinearAlgebra.Span.Basic
import Tengoku.Seed.Order.SupIndep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integrable `U_q(𝔰𝔩₂)`-modules and their strings

Throughout, `k` is a field and `q ∈ k` is nonzero and not a root of unity. Following
[Lus] 5.1.1 we consider `ℤ`-graded `k`-vector spaces `M = ⊕_n M^n` with two locally
nilpotent operators `E`, `F` of degrees `2` and `-2` such that `EF - FE = [n]` on `M^n`,
where `[n] = (qⁿ - q⁻ⁿ)/(q - q⁻¹)` (`QuantumGroup.IntegrableSl2`). For an integrable module
`M` of `U_q(𝔤)` and a node `i` this is `M` with `Eᵢ`, `Fᵢ` and the grading by `⟨i, wt⟩`, with
`q = vᵢ`; in this file only the abstract structure appears.

A vector `η ∈ M^p` with `E η = 0` is *primitive*. We show:
* `E F^{(b+1)} η = [p - b] F^{(b)} η` and more generally
  `E^{(a)} F^{(b)} η = [p - b + a, a] F^{(b-a)} η` (`IntegrableSl2.dE_dF_of_primitive`);
* primitive vectors of negative weight vanish, and `F^{(b)} η = 0` for `b > p`
  (`IntegrableSl2.eq_zero_of_primitive_of_neg`, `IntegrableSl2.dF_eq_zero_of_primitive`);
* every `m ∈ M^n` is a sum of vectors `F^{(j)} η` with `η ∈ M^{n+2j}` primitive
  (`IntegrableSl2.mem_strings`).

The last statement replaces the eigenspace decomposition of the Casimir element in [Lus] 5.1.3:
for `n ≥ 0` we induct on the nilpotency order of `E` on `m` (subtracting a multiple of
`F^{(N)} E^{(N)} m`), and for `n < 0` we apply this to the module with `E` and `F` interchanged
(`IntegrableSl2.flip`) and convert lowest-weight strings into highest-weight strings. The
arguments are our own.

## Main definitions

* `QuantumGroup.qIntZ q n`: the quantum integer `[n]` for `n ∈ ℤ`.
* `QuantumGroup.IntegrableSl2 q M`: the structure above; `IntegrableSl2.dE`, `IntegrableSl2.dF`
  are the divided powers `E^{(a)} = E^a/[a]!`, `F^{(a)}`.
* `IntegrableSl2.flip`: the same module with `E`, `F` interchanged and the grading negated.
* `IntegrableSl2.strings V n`: the span of the `F^{(j)} η`, `η ∈ M^{n+2j}` primitive.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §5.1.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Ch. 2.
-/

open Finset

namespace LieLean.QuantumGroup

variable {k : Type*} [Field k]

/-! ### Quantum numbers -/

section QIntZ

variable (q : k)

/-- The quantum integer `[n]_q = (qⁿ - q⁻ⁿ)/(q - q⁻¹)` for `n ∈ ℤ`.-/
noncomputable def qIntZ (n : ℤ) : k := (q ^ n - q ^ (-n)) / (q - q⁻¹)

variable {q}

/--
@isnad1 id=eq.0h2v.s5.9bca5b131f1a from=translated src=- shape=4e114734 vocab=c1ec8025
-/
@[simp] lemma qIntZ_zero : qIntZ q 0 = 0 := by simp [qIntZ]

/--
@isnad1 id=eq.0h3v.s5.6977935e73fb from=translated src=- shape=cba72d6d vocab=94ea13f7
-/
lemma qIntZ_neg (n : ℤ) : qIntZ q (-n) = -qIntZ q n := by
  rw [qIntZ, qIntZ, neg_neg, ← neg_div, neg_sub]

/--
@isnad1 id=eq.1h3v.s6.a8847f05bb58 from=translated src=- shape=243d8e27 vocab=9c5705d6
-/
lemma qIntZ_natCast (hq : q - q⁻¹ ≠ 0) (n : ℕ) : qIntZ q n = qInt q n := by
  rw [qIntZ, div_eq_iff hq, mul_comm, qInt_mul_sub, zpow_neg, zpow_natCast, inv_pow]

/--
@isnad1 id=eq.1h2v.s6.b73ba2614d58 from=translated src=- shape=02eb5964 vocab=d88a14ee
-/
lemma qIntZ_one (hq : q - q⁻¹ ≠ 0) : qIntZ q 1 = 1 := by
  rw [qIntZ, zpow_one, zpow_neg_one, div_self hq]

/--
@isnad1 id=ne.2h3v.s6.2688ccb0bfb5 from=translated src=- shape=51fd82e7 vocab=03381104
-/
lemma zpow_ne_one_of_pow_ne_one (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) {n : ℤ} (hn : n ≠ 0) :
    q ^ n ≠ 1 := by
  rcases Int.natAbs_eq n with h | h
  · rw [h, zpow_natCast]; exact hq _ (Int.natAbs_pos.2 hn)
  · rw [h, zpow_neg, zpow_natCast, inv_ne_one]; exact hq _ (Int.natAbs_pos.2 hn)

section NotRoot

variable (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq0 hq

/--
@isnad1 id=ne.2h2v.s7.7a6b82515595 from=translated src=- shape=34b0635b vocab=cdc85ba8
-/
lemma sub_inv_ne_zero_of_pow_ne_one : q - q⁻¹ ≠ 0 := by
  intro h
  refine hq 2 two_pos ?_
  rw [sub_eq_zero] at h
  rw [sq]
  nth_rw 2 [h]
  exact mul_inv_cancel₀ hq0

/--
@isnad1 id=ne.3h3v.s6.9454865554bd from=translated src=- shape=da02a335 vocab=7b5d101a
-/
lemma qIntZ_ne_zero {n : ℤ} (hn : n ≠ 0) : qIntZ q n ≠ 0 := by
  refine div_ne_zero ?_ (sub_inv_ne_zero_of_pow_ne_one hq0 hq)
  rw [sub_ne_zero]
  intro h
  refine zpow_ne_one_of_pow_ne_one hq (show n + n ≠ 0 by omega) ?_
  rw [zpow_add₀ hq0]
  nth_rw 2 [h]
  rw [← zpow_add₀ hq0, add_neg_cancel, zpow_zero]

/--
@isnad1 id=ne.3h3v.s6.e2ba9de9296c from=translated src=- shape=bc1fa528 vocab=cb59f4d6
-/
lemma qInt_ne_zero_of_pow_ne_one {n : ℕ} (hn : 0 < n) : qInt q n ≠ 0 := by
  rw [← qIntZ_natCast (sub_inv_ne_zero_of_pow_ne_one hq0 hq)]
  exact qIntZ_ne_zero hq0 hq (by omega)

/--
@isnad1 id=ne.2h3v.s6.1a4e5ea7602d from=translated src=- shape=fc804d4f vocab=0c45c211
-/
lemma qFactorial_ne_zero_of_pow_ne_one (n : ℕ) : qFactorial q n ≠ 0 :=
  qFactorial_ne_zero hq0 fun m hm _ ↦ hq _ (by omega)

/--
@isnad1 id=ne.3h4v.s6.c58c14508bf7 from=translated src=- shape=e3ee786a vocab=b8d0f665
-/
lemma qBinomial_ne_zero_of_pow_ne_one {n j : ℕ} (h : j ≤ n) : qBinomial q n j ≠ 0 := by
  intro h0
  have e := qBinomial_mul_qFactorial_mul_qFactorial (v := q) h
  rw [h0, zero_mul, zero_mul] at e
  exact qFactorial_ne_zero_of_pow_ne_one hq0 hq n e.symm

end NotRoot

/-- `[b+1][n-b] + [n-2b-2] = [b+2][n-b-1]`.
@isnad1 id=eq.1h4v.s7.ca91bc2abcf7 from=translated src=- shape=fd768f5d vocab=a48dba40
-/
lemma qIntZ_succ_mul_add (hq0 : q ≠ 0) (n : ℤ) (b : ℕ) :
    qIntZ q (b + 1) * qIntZ q (n - b) + qIntZ q (n - 2 * b - 2) =
      qIntZ q (b + 2) * qIntZ q (n - b - 1) := by
  by_cases hq : q - q⁻¹ = 0
  · simp [qIntZ, hq]
  simp only [qIntZ, sub_eq_add_neg, neg_add, neg_neg, two_mul, zpow_add₀ hq0, zpow_neg,
    zpow_natCast, zpow_ofNat]
  field_simp
  ring

end QIntZ

/-! ### The structure -/

/-- A `ℤ`-graded `k`-vector space `M = ⊕ₙ Mⁿ` with locally nilpotent operators `E`, `F` of degrees
`±2` such that `EF - FE = [n]` on `Mⁿ` ([Lus] 5.1.1, the category `C'_i`). These are the
integrable `U_q(𝔰𝔩₂)`-modules of type 1.-/
structure IntegrableSl2 (q : k) (M : Type*) [AddCommGroup M] [Module k M] where
  /-- The raising operator.-/
  E : Module.End k M
  /-- The lowering operator.-/
  F : Module.End k M
  /-- The graded pieces `Mⁿ`.-/
  wt : ℤ → Submodule k M
  iSupIndep_wt : iSupIndep wt
  iSup_wt : ⨆ n, wt n = ⊤
  E_mem {n : ℤ} {m : M} : m ∈ wt n → E m ∈ wt (n + 2)
  F_mem {n : ℤ} {m : M} : m ∈ wt n → F m ∈ wt (n - 2)
  E_F_sub {n : ℤ} {m : M} : m ∈ wt n → E (F m) - F (E m) = qIntZ q n • m
  exists_E_pow_eq_zero (m : M) : ∃ N : ℕ, (E ^ N) m = 0
  exists_F_pow_eq_zero (m : M) : ∃ N : ℕ, (F ^ N) m = 0

namespace IntegrableSl2

variable {q : k} {M : Type*} [AddCommGroup M] [Module k M] (V : IntegrableSl2 q M)

/-- The divided power `E^{(a)} = E^a/[a]!`.-/
noncomputable abbrev dE (a : ℕ) : Module.End k M := qDivPow q a V.E

/-- The divided power `F^{(a)} = F^a/[a]!`.-/
noncomputable abbrev dF (a : ℕ) : Module.End k M := qDivPow q a V.F

/-- The same module with `E` and `F` interchanged and the grading negated.-/
def flip : IntegrableSl2 q M where
  E := V.F
  F := V.E
  wt n := V.wt (-n)
  iSupIndep_wt := V.iSupIndep_wt.comp neg_injective
  iSup_wt := by rw [← V.iSup_wt]; exact (Equiv.neg ℤ).iSup_comp (g := V.wt)
  E_mem {n m} h := by
    have := V.F_mem h
    rwa [show -n - 2 = -(n + 2) by ring] at this
  F_mem {n m} h := by
    have := V.E_mem h
    rwa [show -n + 2 = -(n - 2) by ring] at this
  E_F_sub {n m} h := by
    rw [← neg_sub, V.E_F_sub h, qIntZ_neg, neg_smul, neg_neg]
  exists_E_pow_eq_zero := V.exists_F_pow_eq_zero
  exists_F_pow_eq_zero := V.exists_E_pow_eq_zero

/--
@isnad1 id=eq.0h4v.s6.02293857d3fd from=translated src=- shape=864106f1 vocab=7a685b75
-/
@[simp] lemma flip_E : V.flip.E = V.F := rfl
/--
@isnad1 id=eq.0h4v.s6.5ef25f385364 from=translated src=- shape=864106f1 vocab=7a685b75
-/
@[simp] lemma flip_F : V.flip.F = V.E := rfl
/--
@isnad1 id=eq.0h5v.s6.974281fe5b56 from=translated src=- shape=33585580 vocab=71e2259e
-/
@[simp] lemma flip_wt (n : ℤ) : V.flip.wt n = V.wt (-n) := rfl
/--
@isnad1 id=eq.0h5v.s6.beac051fd159 from=translated src=- shape=c7019614 vocab=1f80b4d1
-/
@[simp] lemma flip_dE (a : ℕ) : V.flip.dE a = V.dF a := rfl
/--
@isnad1 id=eq.0h5v.s6.aa5d8277ec3a from=translated src=- shape=c7019614 vocab=1f80b4d1
-/
@[simp] lemma flip_dF (a : ℕ) : V.flip.dF a = V.dE a := rfl

variable {V}

/--
@isnad1 id=eq.0h6v.s8.2d22ccb82a14 from=translated src=- shape=408b076a vocab=ac5837f0
-/
lemma dE_apply (a : ℕ) (m : M) : V.dE a m = (qFactorial q a)⁻¹ • (V.E ^ a) m := rfl

/--
@isnad1 id=eq.0h6v.s8.e33d02fc2fb5 from=translated src=- shape=408b076a vocab=e12157a4
-/
lemma dF_apply (a : ℕ) (m : M) : V.dF a m = (qFactorial q a)⁻¹ • (V.F ^ a) m := rfl

/--
@isnad1 id=eq.0h5v.s6.d8acad862d6c from=translated src=- shape=9f0380a3 vocab=7cd8e4bf
-/
@[simp] lemma dE_zero (m : M) : V.dE 0 m = m := by simp [dE_apply]

/--
@isnad1 id=eq.0h5v.s6.8c7e298e5234 from=translated src=- shape=9f0380a3 vocab=1686578d
-/
@[simp] lemma dF_zero (m : M) : V.dF 0 m = m := by simp [dF_apply]

/--
@isnad1 id=mem.1h7v.s8.b18cc1c7b340 from=translated src=- shape=7c17963d vocab=02825ae5
-/
lemma E_pow_mem {n : ℤ} {m : M} (hm : m ∈ V.wt n) (a : ℕ) : (V.E ^ a) m ∈ V.wt (n + 2 * a) := by
  induction a with
  | zero => simpa using hm
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply]
    have := V.E_mem ih
    rwa [show n + 2 * (a : ℤ) + 2 = n + 2 * ((a + 1 : ℕ) : ℤ) by push_cast; ring] at this

/--
@isnad1 id=mem.1h7v.s8.d7ffeb39c463 from=translated src=- shape=7c17963d vocab=a2765288
-/
lemma F_pow_mem {n : ℤ} {m : M} (hm : m ∈ V.wt n) (a : ℕ) : (V.F ^ a) m ∈ V.wt (n - 2 * a) := by
  have := V.flip.E_pow_mem (n := -n) (by simpa using hm) a
  simpa [show -(-(n : ℤ) + 2 * a) = n - 2 * a by ring] using this

/--
@isnad1 id=mem.1h7v.s7.d3b00911a90a from=translated src=- shape=3c9fc936 vocab=baa3e6af
-/
lemma dE_mem {n : ℤ} {m : M} (hm : m ∈ V.wt n) (a : ℕ) : V.dE a m ∈ V.wt (n + 2 * a) := by
  rw [dE_apply]
  exact Submodule.smul_mem _ _ (E_pow_mem hm a)

/--
@isnad1 id=mem.1h7v.s7.8cb8fa85b13a from=translated src=- shape=3c9fc936 vocab=5a5355c2
-/
lemma dF_mem {n : ℤ} {m : M} (hm : m ∈ V.wt n) (a : ℕ) : V.dF a m ∈ V.wt (n - 2 * a) := by
  rw [dF_apply]
  exact Submodule.smul_mem _ _ (F_pow_mem hm a)

/-- `E F^{b+1} m = F^{b+1} E m + [b+1][n-b] F^b m` for `m ∈ Mⁿ`.
@isnad1 id=eq.3h7v.s9.3db27643c2c6 from=translated src=- shape=2ae6a067 vocab=69e412d5
-/
lemma E_F_pow_succ (hq0 : q ≠ 0) (hq : q - q⁻¹ ≠ 0) {n : ℤ} {m : M} (hm : m ∈ V.wt n) (b : ℕ) :
    V.E ((V.F ^ (b + 1)) m) = (V.F ^ (b + 1)) (V.E m) +
      (qIntZ q (b + 1) * qIntZ q (n - b)) • (V.F ^ b) m := by
  induction b with
  | zero =>
    have := V.E_F_sub hm
    simp only [pow_one, Nat.cast_zero, zero_add, sub_zero, qIntZ_one hq, one_mul, pow_zero,
      Module.End.one_apply]
    rw [← this]
    abel
  | succ b ih =>
    set w := (V.F ^ (b + 1)) m
    have hw : w ∈ V.wt (n - 2 * (b + 1 : ℕ)) := F_pow_mem hm (b + 1)
    have h2 := V.E_F_sub hw
    have e1 : (V.F ^ (b + 1 + 1)) m = V.F w := by rw [pow_succ', Module.End.mul_apply]
    have e2 : (V.F ^ (b + 1 + 1)) (V.E m) = V.F ((V.F ^ (b + 1)) (V.E m)) := by
      rw [pow_succ', Module.End.mul_apply]
    have e3 : V.F ((V.F ^ b) m) = w := by rw [← Module.End.mul_apply, ← pow_succ']
    have key := qIntZ_succ_mul_add hq0 n b
    rw [e1, e2, sub_eq_iff_eq_add.1 h2, ih, map_add, map_smul, e3]
    have hc : qIntZ q (n - 2 * ((b + 1 : ℕ) : ℤ)) + qIntZ q (b + 1) * qIntZ q (n - b) =
        qIntZ q ((b + 1 : ℕ) + 1) * qIntZ q (n - (b + 1 : ℕ)) := by
      push_cast
      rw [show n - 2 * ((b : ℤ) + 1) = n - 2 * b - 2 by ring, add_comm, key,
        show (b : ℤ) + 1 + 1 = b + 2 by ring, show n - ((b : ℤ) + 1) = n - b - 1 by ring]
    rw [← hc, add_smul]
    abel

variable (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq0 hq

/-- `F F^{(b)} = [b+1] F^{(b+1)}`.
@isnad1 id=eq.2h6v.s8.7a74795e4d05 from=translated src=- shape=e70394fd vocab=16b9101b
-/
lemma F_dF (b : ℕ) (m : M) : V.F (V.dF b m) = qInt q (b + 1) • V.dF (b + 1) m := by
  have hb := qInt_ne_zero_of_pow_ne_one hq0 hq (Nat.succ_pos b)
  rw [dF_apply, dF_apply, map_smul, ← Module.End.mul_apply, ← pow_succ', smul_smul,
    qFactorial_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]

/-- `E E^{(b)} = [b+1] E^{(b+1)}`.
@isnad1 id=eq.2h6v.s8.d6fd729cf87f from=translated src=- shape=e70394fd vocab=8b703df3
-/
lemma E_dE (b : ℕ) (m : M) : V.E (V.dE b m) = qInt q (b + 1) • V.dE (b + 1) m :=
  F_dF (V := V.flip) hq0 hq b m

/-- `E F^{(b+1)} m = F^{(b+1)} E m + [n - b] F^{(b)} m` for `m ∈ Mⁿ`.
@isnad1 id=eq.3h7v.s9.9a1aae4ae6f3 from=translated src=- shape=27878335 vocab=48d698a9
-/
lemma E_dF_succ {n : ℤ} {m : M} (hm : m ∈ V.wt n) (b : ℕ) :
    V.E (V.dF (b + 1) m) = V.dF (b + 1) (V.E m) + qIntZ q (n - b) • V.dF b m := by
  have hq2 := sub_inv_ne_zero_of_pow_ne_one hq0 hq
  have hb := qInt_ne_zero_of_pow_ne_one hq0 hq (Nat.succ_pos b)
  have hf := qFactorial_ne_zero_of_pow_ne_one hq0 hq b
  have hc : qIntZ q ((b : ℤ) + 1) = qInt q (b + 1) := by
    exact_mod_cast qIntZ_natCast hq2 (b + 1)
  rw [dF_apply, dF_apply, dF_apply, map_smul, E_F_pow_succ hq0 hq2 hm b, smul_add, smul_smul,
    smul_smul, hc, qFactorial_succ]
  congr 2
  field_simp

/-- For a primitive vector `η ∈ Mᵖ`: `E F^{(b+1)} η = [p - b] F^{(b)} η`.
@isnad1 id=eq.4h7v.s9.c65e955b0694 from=translated src=- shape=0a09ac40 vocab=48d698a9
-/
lemma E_dF_succ_of_primitive {p : ℤ} {η : M} (hη : η ∈ V.wt p) (hE : V.E η = 0) (b : ℕ) :
    V.E (V.dF (b + 1) η) = qIntZ q (p - b) • V.dF b η := by
  rw [E_dF_succ hq0 hq hη, hE, map_zero, zero_add]

/-- Primitive vectors of negative weight vanish.-/
lemma eq_zero_of_primitive_of_neg {p : ℤ} {η : M} (hη : η ∈ V.wt p) (hE : V.E η = 0)
    (hp : p < 0) : η = 0 := by
  obtain ⟨N, hN⟩ := V.exists_F_pow_eq_zero η
  have h : ∀ b, V.dF b η = 0 → V.dF 0 η = 0 := by
    intro b
    induction b with
    | zero => exact id
    | succ b ih =>
      intro hb
      apply ih
      have e := E_dF_succ_of_primitive hq0 hq hη hE b
      rw [hb, map_zero] at e
      exact (smul_eq_zero.1 e.symm).resolve_left (qIntZ_ne_zero hq0 hq (by omega))
  have := h N (by rw [dF_apply, hN, smul_zero])
  simpa using this

/-- For a primitive vector `η ∈ Mᵖ`, `F^{(b)} η = 0` for `b > p`.
@isnad1 id=eq.5h7v.s8.0192af626882 from=translated src=- shape=017c9a08 vocab=54d9d666
-/
lemma dF_eq_zero_of_primitive {p : ℤ} {η : M} (hη : η ∈ V.wt p) (hE : V.E η = 0) {b : ℕ}
    (hb : p < b) : V.dF b η = 0 := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [eq_zero_of_primitive_of_neg hq0 hq hη hE hp, map_zero]
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  have hb' : p + 1 ≤ b := by omega
  induction b, hb' using Nat.le_induction with
  | base =>
    refine eq_zero_of_primitive_of_neg hq0 hq (dF_mem hη (p + 1)) ?_ (by push_cast; omega)
    rw [E_dF_succ_of_primitive hq0 hq hη hE p, sub_self, qIntZ_zero, zero_smul]
  | succ b hb ih =>
    have hb1 := qInt_ne_zero_of_pow_ne_one hq0 hq (Nat.succ_pos b)
    have e := F_dF hq0 hq (V := V) b η
    rw [ih (by omega), map_zero] at e
    exact (smul_eq_zero.1 e.symm).resolve_left hb1

/-- For a primitive vector `η ∈ Mᵖ` and `a ≤ b ≤ p`:
`E^{(a)} F^{(b)} η = [p - b + a, a] F^{(b-a)} η` (cf. [Jan] 2.6(3)).
@isnad1 id=eq.6h8v.s9.4ec8ef5a6c19 from=translated src=- shape=693eab87 vocab=9b7608c2
-/
lemma dE_dF_of_primitive {p : ℕ} {η : M} (hη : η ∈ V.wt p) (hE : V.E η = 0) {a b : ℕ}
    (hab : a ≤ b) (hbp : b ≤ p) :
    V.dE a (V.dF b η) = qBinomial q (p - b + a) a • V.dF (b - a) η := by
  have hq2 := sub_inv_ne_zero_of_pow_ne_one hq0 hq
  induction a with
  | zero => simp
  | succ a ih =>
    have hi := qInt_ne_zero_of_pow_ne_one hq0 hq (Nat.succ_pos a)
    have e : V.dE (a + 1) (V.dF b η) = (qInt q (a + 1))⁻¹ • V.E (V.dE a (V.dF b η)) := by
      rw [E_dE hq0 hq, smul_smul, inv_mul_cancel₀ hi, one_smul]
    obtain ⟨c, hc⟩ : ∃ c, b - a = c + 1 := ⟨b - a - 1, by omega⟩
    rw [e, ih (by omega), map_smul, hc, E_dF_succ_of_primitive hq0 hq hη hE c, smul_smul,
      smul_smul, show b - (a + 1) = c by omega]
    congr 1
    -- `[a+1]⁻¹ [N, a] [N + 1] = [N + 1, a + 1]` with `N = p - b + a`
    have hN : (p : ℤ) - c = ((p - b + a + 1 : ℕ) : ℤ) := by omega
    rw [hN, qIntZ_natCast hq2, show p - b + (a + 1) = (p - b + a) + 1 by omega]
    have h1 := qBinomial_mul_qFactorial_mul_qFactorial (v := q) (show a ≤ p - b + a by omega)
    have h2 := qBinomial_mul_qFactorial_mul_qFactorial (v := q)
      (show a + 1 ≤ p - b + a + 1 by omega)
    rw [show p - b + a + 1 - (a + 1) = p - b + a - a by omega, qFactorial_succ q (p - b + a),
      qFactorial_succ q a] at h2
    have hf1 := qFactorial_ne_zero_of_pow_ne_one hq0 hq a
    have hf2 := qFactorial_ne_zero_of_pow_ne_one hq0 hq (p - b + a - a)
    rw [← h1] at h2
    have h3 : qBinomial q (p - b + a + 1) (a + 1) * qInt q (a + 1) =
        qInt q (p - b + a + 1) * qBinomial q (p - b + a) a := by
      apply mul_right_cancel₀ (mul_ne_zero hf1 hf2)
      linear_combination h2
    rw [mul_assoc, inv_mul_eq_iff_eq_mul₀ hi]
    linear_combination -h3

/-! ### Strings -/

variable (V) in
/-- The span of the vectors `F^{(j)} η` with `η ∈ M^{n+2j}` primitive.-/
def strings (n : ℤ) : Submodule k M :=
  Submodule.span k {x | ∃ (j : ℕ) (η : M), η ∈ V.wt (n + 2 * j) ∧ V.E η = 0 ∧ x = V.dF j η}

omit hq0 hq in
/--
@isnad1 id=mem.2h7v.s8.73256e41748d from=translated src=- shape=7195b829 vocab=1d9c6f28
-/
lemma dF_mem_strings {n : ℤ} {j : ℕ} {η : M} (hη : η ∈ V.wt (n + 2 * j)) (hE : V.E η = 0) :
    V.dF j η ∈ V.strings n :=
  Submodule.subset_span ⟨j, η, hη, hE, rfl⟩

/--
@isnad1 id=mem.4h6v.s7.73c4f5dfe3bb from=translated src=- shape=4ec82d7e vocab=273aca01
-/
lemma mem_strings_of_nonneg {n : ℤ} (hn : 0 ≤ n) {m : M} (hm : m ∈ V.wt n) :
    m ∈ V.strings n := by
  obtain ⟨N, hN⟩ := V.exists_E_pow_eq_zero m
  have hpow : ∀ (N : ℕ) (m : M), (V.E ^ N) m = qFactorial q N • V.dE N m := fun N m ↦ by
    rw [dE_apply, smul_smul, mul_inv_cancel₀ (qFactorial_ne_zero_of_pow_ne_one hq0 hq N),
      one_smul]
  induction N generalizing m with
  | zero => simp only [pow_zero, Module.End.one_apply] at hN; rw [hN]; exact zero_mem _
  | succ N ih =>
    set y := V.dE N m
    have hy : y ∈ V.wt (n + 2 * N) := dE_mem hm N
    have hyE : V.E y = 0 := by
      have h1 : V.dE (N + 1) m = 0 := by
        rw [hpow] at hN
        exact (smul_eq_zero.1 hN).resolve_left (qFactorial_ne_zero_of_pow_ne_one hq0 hq _)
      rw [E_dE hq0 hq, h1, smul_zero]
    obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = n + 2 * N := ⟨(n + 2 * N).toNat, by omega⟩
    have hNp : N ≤ p := by omega
    set c := qBinomial q p N
    have hc : c ≠ 0 := qBinomial_ne_zero_of_pow_ne_one hq0 hq hNp
    set m' := m - c⁻¹ • V.dF N y
    have hy' : y ∈ V.wt (p : ℤ) := hp ▸ hy
    have hm' : m' ∈ V.wt n := by
      refine sub_mem hm (Submodule.smul_mem _ _ ?_)
      have := dF_mem hy N
      rwa [show n + 2 * (N : ℤ) - 2 * N = n by ring] at this
    have hEm' : (V.E ^ N) m' = 0 := by
      rw [hpow, map_sub, map_smul, dE_dF_of_primitive hq0 hq hy' hyE le_rfl hNp, Nat.sub_self,
        show p - N + N = p by omega, smul_smul, inv_mul_cancel₀ hc, one_smul, dF_zero, sub_self,
        smul_zero]
    have h1 := ih hm' hEm'
    have h2 : V.dF N y ∈ V.strings n := dF_mem_strings hy hyE
    have : m = m' + c⁻¹ • V.dF N y := by simp [m']
    rw [this]
    exact add_mem h1 (Submodule.smul_mem _ _ h2)

/-- Every `m ∈ Mⁿ` is a sum of vectors `F^{(j)} η` with `η ∈ M^{n+2j}` primitive.
@isnad1 id=mem.3h6v.s7.0fc84430fb6e from=translated src=- shape=cac87807 vocab=b2365cac
-/
theorem mem_strings {n : ℤ} {m : M} (hm : m ∈ V.wt n) : m ∈ V.strings n := by
  rcases le_or_gt 0 n with hn | hn
  · exact mem_strings_of_nonneg hq0 hq hn hm
  -- apply the nonnegative case to the flipped module
  have h := mem_strings_of_nonneg (V := V.flip) hq0 hq (n := -n) (by omega)
    (by simpa using hm)
  refine Submodule.span_le.2 ?_ h
  rintro _ ⟨j, ξ, hξ, hFξ, rfl⟩
  -- `ξ ∈ M^{n - 2j}` with `F ξ = 0`; put `p = 2j - n` and `η = E^{(p)} ξ`
  simp only [flip_wt, flip_E] at hξ hFξ
  rw [show -(-n + 2 * (j : ℤ)) = n - 2 * j by ring] at hξ
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = 2 * j - n := ⟨(2 * j - n).toNat, by omega⟩
  have hjp : j ≤ p := by omega
  have hξ' : ξ ∈ V.flip.wt (p : ℤ) := by
    rw [flip_wt, hp, show -(2 * (j : ℤ) - n) = n - 2 * j by ring]
    exact hξ
  set η := V.dE p ξ
  have hη : η ∈ V.wt (p : ℤ) := by
    have := dE_mem hξ p
    rwa [show n - 2 * (j : ℤ) + 2 * p = p by omega] at this
  have hηE : V.E η = 0 := by
    have h0 := dF_eq_zero_of_primitive (V := V.flip) hq0 hq hξ' hFξ
      (show (p : ℤ) < (p + 1 : ℕ) by push_cast; omega)
    rw [flip_dF] at h0
    rw [E_dE hq0 hq, h0, smul_zero]
  -- `F^{(p)} η = ξ`
  have hξη : V.dF p η = ξ := by
    have := dE_dF_of_primitive (V := V.flip) hq0 hq hξ' hFξ (le_refl p) (le_refl p)
    simpa using this
  -- hence `E^{(j)} ξ = F^{(p - j)} η`
  have e : V.flip.dF j ξ = V.dF (p - j) η := by
    rw [flip_dF, ← hξη, dE_dF_of_primitive hq0 hq hη hηE hjp le_rfl,
      show p - p + j = j by omega, qBinomial_self, one_smul]
  rw [e]
  refine dF_mem_strings ?_ hηE
  rwa [show n + 2 * ((p - j : ℕ) : ℤ) = p by push_cast [hjp]; omega]

end IntegrableSl2

end LieLean.QuantumGroup
