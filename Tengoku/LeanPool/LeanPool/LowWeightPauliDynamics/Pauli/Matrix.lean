/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.LowWeightPauliDynamics.Pauli.Basic

/-!
# The matrix model of the Pauli group

`Pauli/Basic.lean` builds `PauliString n` as a group of symbols. This file supplies the operators
those symbols denote, `toMatrix s : Matrix (Bits n) (Bits n) ℂ`, proves that `toMatrix` is a
faithful `*`-monoid homomorphism, and so turns every statement there into a statement about
matrices — which is the form `Rotation.lean` consumes.

## The index type, and why there are no Kronecker products here

The Hilbert space is indexed by **bit strings**, `Bits n := Fin n → ZMod 2`, of cardinality `2^n`
(`card_bits`). So `Matrix (Bits n) (Bits n) ℂ` is a `2^n × 2^n` matrix algebra — the operator
algebra of `n` qubits, up to the reindexing provided by `PauliString.bitsMatrixEquiv` in
`Pauli/Tensor.lean` — and

  `toMatrix s a b = i^{phase} · (-1)^{z ⬝ᵥ b}` when `a = b + x`, and `0` otherwise

is `i^{phase} X^x Z^z` written out: `Z^z` is diagonal with entries `(-1)^{z·b}`, and `X^x` shifts
the basis label by `x`. Every Pauli string is a **monomial matrix** — one non-zero entry per row
and per column — and that is what this form buys: the matrix-product sum `∑_k A_{ik} B_{kj}` has
exactly one surviving term, so `toMatrix_mul` is `Finset.sum_eq_single` plus bookkeeping in
`ZMod 4`, and no induction on `n` appears anywhere in the file.

The definition does factorize over sites — `toMatrix ⟨x,z,0⟩ a b = ∏ᵢ ([aᵢ = bᵢ + xᵢ]·(−1)^{zᵢbᵢ})`,
an `n`-fold tensor product of `X^{xᵢ} Z^{zᵢ}` — but those factors range over `{I, X, Z, XZ}`, and
`XZ = −i Y` is not in the set `{I,X,Y,Z}` of `def:pauli_basis`. Reaching that set needs the
further phase normalization `phase = #{Y-sites} mod 4`. `Pauli/Tensor.lean` proves the
phase-correct tensor identity and provides that positive representative; neither fact is assumed
by the matrix model.

## Main definitions

* `Bits n`: the computational basis labels `Fin n → ZMod 2`.
* `iPow`, `negOnePow`: the characters `k ↦ i^k` on `ZMod 4` and `a ↦ (-1)^a` on `ZMod 2`.
* `PauliString.toMatrix`: the matrix of a Pauli string.

## Main results

* `toMatrix_one`, `toMatrix_mul`, `toMatrix_star`: `toMatrix` is a `*`-monoid homomorphism **on
  the nose**, not projectively. This is what carrying `phase : ZMod 4` in `PauliString` was for.
* `toMatrix_injective`: the representation is **faithful** — distinct group elements, phase
  variants included, are distinct operators — so nothing below is a statement about a collapsed
  model. It does *not* say the image is linearly independent, and cannot: `toMatrix (phaseMul 1 s)`
  is `i · toMatrix s`. Linear independence is a statement about a *basis*; the one instance of it
  needed in this file is `toMatrix_mul_ne_smul`, and the orthogonality of the signless classes is
  in `Pauli/Trace.lean`.
* `toMatrix_commute_or_anticommute`: the commute-or-anticommute dichotomy as a statement about
  operators. This is the exhaustiveness of the two cases of `apd:eq:pauli_rotation_branch`, which
  `Lean4LPD.rot_conj_of_commute` and `Lean4LPD.rot_conj_of_anticommute` cannot see over an
  abstract algebra. `toMatrix_commute_iff` and `toMatrix_anticommute_iff` identify the two cases
  with `sympForm s t = 0` and `sympForm s t = 1`.
* `star_toMatrix_of_isSelfAdjoint` and `toMatrix_mul_self_of_isSelfAdjoint` discharge, from the
  single hypothesis `IsSelfAdjoint s`, both hypotheses `rot_conj_of_commute`,
  `rot_conj_of_anticommute` and `rot_mem_unitary` carry between them.
* `toMatrix_mul_ne_smul` and `linearIndependent_toMatrix_mul_pair`: for anticommuting `G, s` the
  partner `G s` is **not** a scalar multiple of `s`, and the two are genuinely linearly
  independent — which needs `toMatrix_ne_zero` on top of non-collinearity. `Rotation.lean` records
  that reading `i sin(dt)` as the amplitude of a new transition needs exactly this and that
  distinctness does not give it, exhibiting `G = Z`, `P = E₁₀` in `Matrix (Fin 2) (Fin 2) ℂ` where
  both rotation hypotheses hold and `G * P = -P`. Inside the Pauli group that cannot happen, and
  this is the theorem that says so.

`Pauli/Branch.lean` assembles these into the paper's branching rule.
-/

@[expose] public section

namespace Lean4LPD

/-! ### Fourth and second roots of unity

`iPow` and `negOnePow` are the two characters the representation needs. Everything about them
reduces to `I ^ 4 = 1` and a finite case check. -/

private lemma zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

private lemma zmod_two_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

private lemma zmod_four_cases (k : ZMod 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  revert k; decide

private lemma pow_mod_of_pow_eq_one {x : ℂ} {N : ℕ} (hx : x ^ N = 1) (m : ℕ) :
    x ^ (m % N) = x ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m N]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

/-- `i^k` for an exponent in `ZMod 4`. Well defined because `I ^ 4 = 1`. -/
noncomputable def iPow (k : ZMod 4) : ℂ := Complex.I ^ k.val

/-- `(-1)^a` for an exponent in `ZMod 2`. -/
noncomputable def negOnePow (a : ZMod 2) : ℂ := (-1 : ℂ) ^ a.val

/--
@isnad1 id=eq.0h0v.s5.7dc29d46fad2 from=translated src=- shape=012516b9 vocab=5387f48a
-/
@[simp] lemma iPow_zero : iPow 0 = 1 := by simp [iPow]

/--
@isnad1 id=eq.0h0v.s5.57e2d40db95a from=translated src=- shape=fdee698a vocab=64cebf19
-/
lemma iPow_one : iPow 1 = Complex.I := by simp [iPow, show (1 : ZMod 4).val = 1 from rfl]

/--
@isnad1 id=eq.0h0v.s5.0147a18ed66d from=translated src=- shape=f05c4898 vocab=6f022afe
-/
@[simp] lemma iPow_two : iPow 2 = -1 := by
  simp [iPow, show (2 : ZMod 4).val = 2 from rfl, pow_two, Complex.I_mul_I]

/--
@isnad1 id=eq.0h0v.s5.14d93b769488 from=translated src=- shape=a5e329d7 vocab=eeeb9e47
-/
lemma iPow_three : iPow 3 = -Complex.I := by
  have : (3 : ZMod 4).val = 3 := rfl
  rw [iPow, this, pow_succ, pow_two, Complex.I_mul_I]
  ring

private lemma I_pow_four : (Complex.I) ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]
  norm_num

/--
@isnad1 id=eq.0h2v.s6.5d6072bbced6 from=translated src=- shape=b67944bb vocab=93e59051
-/
lemma iPow_add (k l : ZMod 4) : iPow (k + l) = iPow k * iPow l := by
  rw [iPow, iPow, iPow, ZMod.val_add, pow_mod_of_pow_eq_one I_pow_four, pow_add]

/--
@isnad1 id=eq.0h0v.s6.c4f2ce35d330 from=translated src=- shape=012516b9 vocab=b53d4e22
-/
@[simp] lemma negOnePow_zero : negOnePow 0 = 1 := by simp [negOnePow]

/--
@isnad1 id=eq.0h0v.s6.b65dde33e1c2 from=translated src=- shape=f05c4898 vocab=5c6ecee6
-/
@[simp] lemma negOnePow_one : negOnePow 1 = -1 := by
  simp [negOnePow, show (1 : ZMod 2).val = 1 from rfl]

/--
@isnad1 id=eq.0h2v.s6.cd87ef78802d from=translated src=- shape=b67944bb vocab=f8720e5a
-/
lemma negOnePow_add (a b : ZMod 2) : negOnePow (a + b) = negOnePow a * negOnePow b := by
  rw [negOnePow, negOnePow, negOnePow, ZMod.val_add,
    pow_mod_of_pow_eq_one (by norm_num : (-1 : ℂ) ^ 2 = 1), pow_add]

/-- The two characters agree where they must: `(-1)^a = i^{2a}`.
@isnad1 id=eq.0h1v.s3.a8858f6ba445 from=translated src=- shape=79c5de43 vocab=6fec1fd9
-/
@[simp] lemma iPow_signPhase (a : ZMod 2) : iPow (signPhase a) = negOnePow a := by
  rcases zmod_two_cases a with rfl | rfl <;> simp

/--
@isnad1 id=eq.0h1v.s4.8d04fb6414c1 from=translated src=- shape=4975ee10 vocab=f13bb4fd
-/
@[simp] lemma negOnePow_mul_self (a : ZMod 2) : negOnePow a * negOnePow a = 1 := by
  rw [← negOnePow_add, zmod_two_add_self, negOnePow_zero]

/--
@isnad1 id=ne.0h1v.s4.f32e323da58b from=translated src=- shape=9a4b31c0 vocab=5387f48a
-/
lemma iPow_ne_zero (k : ZMod 4) : iPow k ≠ 0 := by
  rcases zmod_four_cases k with rfl | rfl | rfl | rfl <;>
    simp [iPow_one, iPow_three, Complex.I_ne_zero]

/--
@isnad1 id=ne.0h1v.s4.c041e4872077 from=translated src=- shape=9a4b31c0 vocab=b53d4e22
-/
lemma negOnePow_ne_zero (a : ZMod 2) : negOnePow a ≠ 0 := by
  rcases zmod_two_cases a with rfl | rfl <;> simp

/--
@isnad1 id=injectiv.0h0v.s3.926cd32c16cd from=translated src=- shape=bfe16b09 vocab=84ef4255
-/
lemma negOnePow_injective : Function.Injective negOnePow := by
  intro a b hab
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · simp only [negOnePow_zero, negOnePow_one] at hab; norm_num at hab
  · simp only [negOnePow_zero, negOnePow_one] at hab; norm_num at hab
  · rfl

/--
@isnad1 id=iff.0h1v.s6.6df7d4e0aec8 from=translated src=- shape=bb2e466f vocab=b53d4e22
-/
lemma negOnePow_eq_one_iff {a : ZMod 2} : negOnePow a = 1 ↔ a = 0 := by
  constructor
  · intro h; exact negOnePow_injective (by rw [h, negOnePow_zero])
  · rintro rfl; simp

/--
@isnad1 id=iff.0h1v.s6.53af28d276d9 from=translated src=- shape=bb2e466f vocab=5387f48a
-/
lemma iPow_eq_one_iff {k : ZMod 4} : iPow k = 1 ↔ k = 0 := by
  constructor
  · intro h
    rcases zmod_four_cases k with rfl | rfl | rfl | rfl
    · rfl
    · rw [iPow_one] at h
      exact absurd (congrArg Complex.im h) (by norm_num)
    · rw [iPow_two] at h
      exact absurd h (by norm_num)
    · rw [iPow_three] at h
      exact absurd (congrArg Complex.im h) (by norm_num)
  · rintro rfl; simp

/--
@isnad1 id=injectiv.0h0v.s3.f23778773238 from=translated src=- shape=bfe16b09 vocab=adf35418
-/
lemma iPow_injective : Function.Injective iPow := by
  intro k l h
  have hkl : iPow (k - l) = 1 := by
    rw [sub_eq_add_neg, iPow_add, h, ← iPow_add, add_neg_cancel, iPow_zero]
  exact sub_eq_zero.1 (iPow_eq_one_iff.1 hkl)

/--
@isnad1 id=eq.0h1v.s5.a3cedf6cc44f from=translated src=- shape=d4cbb841 vocab=fb6ac8a1
-/
@[simp] lemma conj_negOnePow (a : ZMod 2) : starRingEnd ℂ (negOnePow a) = negOnePow a := by
  rcases zmod_two_cases a with rfl | rfl <;> simp

/--
@isnad1 id=eq.0h1v.s6.fab5f1c27c01 from=translated src=- shape=a1d4e60b vocab=74475f51
-/
lemma conj_iPow (k : ZMod 4) : starRingEnd ℂ (iPow k) = iPow (-k) := by
  have e1 : -(1 : ZMod 4) = 3 := by decide
  have e2 : -(2 : ZMod 4) = 2 := by decide
  have e3 : -(3 : ZMod 4) = 1 := by decide
  rcases zmod_four_cases k with rfl | rfl | rfl | rfl
  · simp
  · rw [e1, iPow_one, iPow_three]; simp
  · rw [e2, iPow_two]; simp
  · rw [e3, iPow_three, iPow_one]; simp

/--
@isnad1 id=eq.0h1v.s5.13efd84cf071 from=translated src=- shape=40f9c612 vocab=2d0e26cc
-/
@[simp] lemma star_negOnePow (a : ZMod 2) : star (negOnePow a) = negOnePow a := by
  rw [Complex.star_def]; exact conj_negOnePow a

/--
@isnad1 id=eq.0h1v.s6.b5d80991ae71 from=translated src=- shape=e0aa08e8 vocab=7a341012
-/
lemma star_iPow (k : ZMod 4) : star (iPow k) = iPow (-k) := by
  rw [Complex.star_def]; exact conj_iPow k

/-! ### The Hilbert space -/

/-- The computational basis of `n` qubits, indexed by bit strings. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- There are `2^n` basis states, so `Matrix (Bits n) (Bits n) ℂ` is *a* `2^n × 2^n` matrix
algebra. `Rotation.lean`'s closing `example` names the same algebra as
`Matrix (Fin (2^n)) (Fin (2^n)) ℂ`, which is a different Lean type; the reindexing along
`Bits n ≃ Fin (2^n)` is supplied by `PauliString.bitsEquivFin` in `Pauli/Tensor.lean`, together
with the induced equivalence of matrix algebras `PauliString.bitsMatrixEquiv`.
@isnad1 id=eq.0h1v.s5.6d2e7b04ac3f from=translated src=- shape=5b09d1d5 vocab=3ffacbb0
-/
lemma card_bits (n : ℕ) : Fintype.card (Bits n) = 2 ^ n := by simp

private lemma bits_eq_add_comm {n : ℕ} {u v w : Bits n} : u = v + w ↔ v = u + w := by
  constructor <;> · rintro rfl; rw [add_assoc, bits_add_self, add_zero]

namespace PauliString

variable {n : ℕ} {G s t : PauliString n}

/-! ### The representation -/

/-- The **matrix representation** `i^{phase} X^{x} Z^{z}` of a Pauli string, as a monomial matrix
on bit strings: the entry in row `a`, column `b` is non-zero only when `a = b + x`, where it is
`i^{phase} (-1)^{z ⬝ᵥ b}`.

This is a *definition*. That it deserves the name is `toMatrix_one`, `toMatrix_mul`,
`toMatrix_star` (it is a `*`-monoid homomorphism) and `toMatrix_injective` (it is faithful). -/
noncomputable def toMatrix (s : PauliString n) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.of fun a b => if a = b + s.x then iPow s.phase * negOnePow (s.z ⬝ᵥ b) else 0

/--
@isnad1 id=eq.0h4v.s8.9360bf35923d from=translated src=- shape=a521e7fe vocab=0d256799
-/
lemma toMatrix_apply (s : PauliString n) (a b : Bits n) :
    toMatrix s a b = if a = b + s.x then iPow s.phase * negOnePow (s.z ⬝ᵥ b) else 0 := rfl

/-- The one non-zero entry of each column.
@isnad1 id=eq.0h3v.s7.4c7077e238c5 from=translated src=- shape=001305bc vocab=08a9f618
-/
lemma toMatrix_apply_add (s : PauliString n) (b : Bits n) :
    toMatrix s (b + s.x) b = iPow s.phase * negOnePow (s.z ⬝ᵥ b) := by
  rw [toMatrix_apply, ite_eq_left rfl]

/--
@isnad1 id=eq.1h4v.s6.4ed110ab18ac from=translated src=- shape=19dd99ad vocab=180ecd70
-/
lemma toMatrix_apply_ne (s : PauliString n) {a b : Bits n} (h : a ≠ b + s.x) :
    toMatrix s a b = 0 := by rw [toMatrix_apply, ite_eq_right h]

/--
@isnad1 id=eq.0h1v.s6.f6386b69e971 from=translated src=- shape=2aa6dcd6 vocab=f9fbb210
-/
@[simp] lemma toMatrix_one : toMatrix (1 : PauliString n) = 1 := by
  ext a b
  rw [toMatrix_apply, Matrix.one_apply]
  simp

/--
@isnad1 id=eq.0h3v.s5.84ebcd2a7c0e from=translated src=- shape=f1ec47d4 vocab=899e5286
-/
@[simp] lemma toMatrix_phaseMul (k : ZMod 4) (s : PauliString n) :
    toMatrix (phaseMul k s) = iPow k • toMatrix s := by
  ext a b
  rw [toMatrix_apply, Matrix.smul_apply, toMatrix_apply, phaseMul_x, phaseMul_z, phaseMul_phase]
  by_cases h : a = b + s.x
  · rw [ite_eq_left h, ite_eq_left h, iPow_add, smul_eq_mul]
    ring
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]

/-- **The representation is multiplicative.** Exactly, with no phase ambiguity: this is what
`phase : ZMod 4` was carried for.
@isnad1 id=eq.0h3v.s6.e515802b59fc from=translated src=- shape=631cefe4 vocab=13ecaedf
-/
theorem toMatrix_mul (s t : PauliString n) :
    toMatrix s * toMatrix t = toMatrix (s * t) := by
  ext a c
  rw [Matrix.mul_apply, Finset.sum_eq_single (c + t.x)]
  · rw [toMatrix_apply_add t c, toMatrix_apply, toMatrix_apply, mul_x, mul_z, mul_phase]
    by_cases h : a = c + (s.x + t.x)
    · have h' : a = c + t.x + s.x := by rw [h]; abel
      rw [ite_eq_left h', ite_eq_left h, dotProduct_add, negOnePow_add, add_dotProduct,
        negOnePow_add, iPow_add, iPow_add, iPow_signPhase]
      ring
    · have h' : ¬ a = c + t.x + s.x := fun hc => h (by rw [hc]; abel)
      rw [ite_eq_right h', ite_eq_right h, zero_mul]
  · intro b _ hb
    rw [toMatrix_apply_ne t hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The representation respects the adjoint.** This is the theorem that justifies calling
`PauliString`'s `star` an adjoint at all — in `Pauli/Basic.lean` it is only *defined*, as the
group inverse.
@isnad1 id=eq.0h2v.s5.1a6285299fe1 from=translated src=- shape=be29517f vocab=a806c37b
-/
theorem toMatrix_star (s : PauliString n) : star (toMatrix s) = toMatrix (star s) := by
  ext a b
  rw [Matrix.star_apply, toMatrix_apply, star_eq_inv, toMatrix_apply, inv_x, inv_z, inv_phase]
  by_cases h : a = b + s.x
  · have hb : b = a + s.x := bits_eq_add_comm.1 h
    rw [ite_eq_left hb, ite_eq_left h, hb, dotProduct_add, negOnePow_add, iPow_add, iPow_signPhase]
    rw [show iPow (-s.phase) * negOnePow (s.z ⬝ᵥ s.x)
        * (negOnePow (s.z ⬝ᵥ a) * negOnePow (s.z ⬝ᵥ s.x))
      = iPow (-s.phase) * negOnePow (s.z ⬝ᵥ a)
        * (negOnePow (s.z ⬝ᵥ s.x) * negOnePow (s.z ⬝ᵥ s.x)) by ring]
    rw [negOnePow_mul_self, mul_one, star_mul', star_iPow, star_negOnePow]
  · have hb : ¬ b = a + s.x := fun hc => h (bits_eq_add_comm.1 hc)
    rw [ite_eq_right hb, ite_eq_right h, star_zero]

/-! ### Faithfulness -/

private lemma dotProduct_eq_zero_of_forall {u : Bits n} (h : ∀ b : Bits n, u ⬝ᵥ b = 0) : u = 0 := by
  funext i
  have := h (Pi.single i 1)
  rwa [dotProduct_single, mul_one] at this

/-- **The representation is faithful.** Distinct Pauli strings — including strings differing only
in their phase — are distinct operators, so nothing proved through `toMatrix` is a statement about
a collapsed model.
@isnad1 id=injectiv.0h1v.s3.9f2521182338 from=translated src=- shape=8501b48c vocab=154e6893
-/
theorem toMatrix_injective : Function.Injective (toMatrix (n := n)) := by
  intro s t hst
  have key : ∀ a b : Bits n, toMatrix s a b = toMatrix t a b := fun a b => by rw [hst]
  have hx : s.x = t.x := by
    have h0 := key (0 + s.x) 0
    rw [toMatrix_apply_add, toMatrix_apply] at h0
    by_cases hxx : 0 + s.x = 0 + t.x
    · simpa using hxx
    · rw [ite_eq_right hxx] at h0
      exact absurd h0 (mul_ne_zero (iPow_ne_zero _) (negOnePow_ne_zero _))
  have hp : s.phase = t.phase := by
    have h0 := key (0 + s.x) 0
    rw [toMatrix_apply_add, toMatrix_apply, ite_eq_left (by rw [hx])] at h0
    simp only [dotProduct_zero, negOnePow_zero, mul_one] at h0
    exact iPow_injective h0
  have hz : s.z = t.z := by
    have hzz : ∀ b : Bits n, (s.z + t.z) ⬝ᵥ b = 0 := by
      intro b
      have h0 := key (b + s.x) b
      rw [toMatrix_apply_add, toMatrix_apply, ite_eq_left (by rw [hx]), hp] at h0
      have := mul_left_cancel₀ (iPow_ne_zero t.phase) h0
      have hb : s.z ⬝ᵥ b = t.z ⬝ᵥ b := negOnePow_injective this
      rw [add_dotProduct, hb]
      exact zmod_two_add_self _
    have := dotProduct_eq_zero_of_forall hzz
    exact bits_add_eq_zero_iff.1 this
  exact ext' hx hz hp

/-! ### The dichotomy, at the level of operators -/

/-- **Any two Pauli operators either commute or anticommute.** The operator form of
`PauliString.commute_or_anticommute`, and the exhaustiveness that
`Lean4LPD.rot_conj_of_commute` / `Lean4LPD.rot_conj_of_anticommute` presuppose: those two cover a
commuting and an anticommuting generator, and over an abstract algebra nothing rules out a third
case. For Pauli operators it shows that the two cases of `apd:eq:pauli_rotation_branch` are the
only ones.
@isnad1 id=or.0h3v.s7.73180eaf00b0 from=translated src=- shape=58681336 vocab=93cbcc14
-/
theorem toMatrix_commute_or_anticommute (s t : PauliString n) :
    Commute (toMatrix s) (toMatrix t) ∨
      toMatrix s * toMatrix t = -(toMatrix t * toMatrix s) := by
  rcases commute_or_anticommute s t with h | h
  · left
    rw [Commute, SemiconjBy, toMatrix_mul, toMatrix_mul, h.eq]
  · right
    rw [toMatrix_mul, toMatrix_mul, h, toMatrix_phaseMul, iPow_two, neg_smul, one_smul]

/-- Commuting Pauli strings give commuting operators.
@isnad1 id=commute.1h3v.s6.0492a2bcdc6e from=translated src=- shape=19191e21 vocab=a01c64d5
-/
theorem toMatrix_commute (h : sympForm s t = 0) :
    Commute (toMatrix s) (toMatrix t) := by
  rw [Commute, SemiconjBy, toMatrix_mul, toMatrix_mul,
    ((commute_iff_sympForm_eq_zero s t).2 h).eq]

/-- Anticommuting Pauli strings give anticommuting operators — the hypothesis
`Lean4LPD.rot_conj_of_anticommute` takes, spelled the way that file spells it.
@isnad1 id=eq.1h3v.s7.8928cb18619a from=translated src=- shape=80aa1577 vocab=0a24a654
-/
theorem toMatrix_anticommute (h : sympForm s t = 1) :
    toMatrix s * toMatrix t = -(toMatrix t * toMatrix s) := by
  rw [toMatrix_mul, toMatrix_mul, (anticommute_iff_sympForm_eq_one s t).2 h,
    toMatrix_phaseMul, iPow_two, neg_smul, one_smul]

/-- The commuting branch condition is an **iff** at the level of operators, not just an
implication: `toMatrix` is injective, so operators commuting forces the symbols to. Without this
the `if` in `pauli_rotation_branch` would be a sufficient condition for the paper's `[G,P] = 0`
rather than a rendering of it.
@isnad1 id=iff.0h3v.s6.3cc0b10eaf40 from=translated src=- shape=998ad8e3 vocab=a01c64d5
-/
theorem toMatrix_commute_iff (s t : PauliString n) :
    Commute (toMatrix s) (toMatrix t) ↔ sympForm s t = 0 := by
  refine ⟨fun h => ?_, toMatrix_commute⟩
  rw [← commute_iff_sympForm_eq_zero]
  exact toMatrix_injective (by rw [← toMatrix_mul, ← toMatrix_mul]; exact h.eq)

/-- The anticommuting branch condition, likewise an **iff**.
@isnad1 id=iff.0h3v.s7.2282dc58aad9 from=translated src=- shape=d84a7434 vocab=0a24a654
-/
theorem toMatrix_anticommute_iff (s t : PauliString n) :
    toMatrix s * toMatrix t = -(toMatrix t * toMatrix s) ↔ sympForm s t = 1 := by
  refine ⟨fun h => ?_, toMatrix_anticommute⟩
  rw [← anticommute_iff_sympForm_eq_one]
  refine toMatrix_injective ?_
  rw [toMatrix_phaseMul, iPow_two, neg_smul, one_smul, ← toMatrix_mul, ← toMatrix_mul]
  exact h

/-! ### Discharging `Rotation.lean`'s hypotheses -/

/-- A Hermitian Pauli string is a **self-adjoint operator**: discharges `star G = G` in
`Lean4LPD.rot_mem_unitary`.
@isnad1 id=eq.1h2v.s5.560a3adba178 from=translated src=- shape=5b4aed25 vocab=4e913388
-/
theorem star_toMatrix_of_isSelfAdjoint (h : IsSelfAdjoint s) :
    star (toMatrix s) = toMatrix s := by rw [toMatrix_star, h]

/-- A Hermitian Pauli string is an **involution**: discharges `hG : G * G = 1`, the hypothesis the
two branch lemmas and `rot_mem_unitary` carry (`rot_zero`, `commute_rot`,
`rot_mul_eq_mul_rot_neg` and `star_rot` do not). Note this comes from the *same* hypothesis as
self-adjointness — `Pauli/Basic.lean`'s `isSelfAdjoint_iff_mul_self_eq_one`.
@isnad1 id=eq.1h2v.s7.69296032cae3 from=translated src=- shape=67ea31b5 vocab=a6bf442f
-/
theorem toMatrix_mul_self_of_isSelfAdjoint (h : IsSelfAdjoint s) :
    toMatrix s * toMatrix s = 1 := by
  rw [toMatrix_mul, isSelfAdjoint_iff_mul_self_eq_one.1 h, toMatrix_one]

/-- Every Pauli operator is invertible, with `toMatrix s⁻¹` as inverse.
@isnad1 id=eq.0h2v.s7.dad6b397093f from=translated src=- shape=f81aed84 vocab=8e2aceee
-/
theorem toMatrix_mul_toMatrix_inv (s : PauliString n) :
    toMatrix s * toMatrix s⁻¹ = 1 := by
  rw [toMatrix_mul, mul_inv_cancel, toMatrix_one]

/-- No Pauli operator is zero: the entry at `(b + x, b)` is `i^{phase}`, a fourth root of unity.
@isnad1 id=ne.0h2v.s5.8dbfc7cc799b from=translated src=- shape=d918362f vocab=fa3b45e7
-/
lemma toMatrix_ne_zero (s : PauliString n) : toMatrix s ≠ 0 := by
  intro h
  have := congrFun (congrFun h (0 + s.x)) 0
  rw [toMatrix_apply_add] at this
  exact (mul_ne_zero (iPow_ne_zero _) (negOnePow_ne_zero _)) this

/-- **Hermiticity transfers in both directions.** `toMatrix_star` alone gives only
symbol-to-operator; faithfulness supplies the converse, so a Pauli handed over as a self-adjoint
*operator* — which is how the generators `G_g` enter `apd:thm:local_flow_k_local` — is a
self-adjoint Pauli string, and `isSelfAdjoint_iff_mul_self_eq_one` applies to it.
@isnad1 id=iff.0h2v.s5.b9467683291d from=translated src=- shape=eeb69bc2 vocab=30e3e1e7
-/
theorem isSelfAdjoint_toMatrix_iff {s : PauliString n} :
    IsSelfAdjoint (toMatrix s) ↔ IsSelfAdjoint s := by
  constructor
  · intro h
    exact toMatrix_injective (by rw [← toMatrix_star]; exact h)
  · intro h
    exact star_toMatrix_of_isSelfAdjoint h

/-! ### Independence of the two branch terms -/

private lemma x_and_z_eq_zero_of_toMatrix_eq_smul_one {c : ℂ}
    (h : toMatrix G = c • (1 : Matrix (Bits n) (Bits n) ℂ)) :
    G.x = 0 ∧ G.z = 0 := by
  have key : ∀ a b : Bits n, toMatrix G a b = c * (if a = b then 1 else 0) := by
    intro a b
    rw [h, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hx : G.x = 0 := by
    by_contra hne
    have h0 := key (0 + G.x) 0
    rw [toMatrix_apply_add] at h0
    rw [ite_eq_right (by simpa using hne), mul_zero] at h0
    exact (mul_ne_zero (iPow_ne_zero _) (negOnePow_ne_zero _)) h0
  have hc : c = iPow G.phase := by
    have h0 := key (0 + G.x) 0
    rw [toMatrix_apply_add, ite_eq_left (by simp [hx]), mul_one] at h0
    simpa using h0.symm
  refine ⟨hx, ?_⟩
  refine dotProduct_eq_zero_of_forall (fun b => ?_)
  have h0 := key (b + G.x) b
  rw [toMatrix_apply_add, ite_eq_left (by simp [hx]), mul_one, hc] at h0
  exact negOnePow_eq_one_iff.1 (mul_left_cancel₀ (iPow_ne_zero G.phase) (by rw [h0, mul_one]))

/-- **The two branch terms are independent.** When `G` anticommutes with `s`, the partner `G s` is
not a scalar multiple of `s`, so the `i sin(dt)` coefficient in `apd:eq:pauli_rotation_branch`
really is the amplitude of a *new* transition rather than a rescaling of the old one.

`Rotation.lean` states that the damping consequence of the branching rule needs exactly this and
that mere distinctness is not enough, exhibiting `G = Z`, `P = E₁₀` in
`Matrix (Fin 2) (Fin 2) ℂ` — both rotation hypotheses hold there and `G * P = -P`. That example
is not a Pauli string, and this theorem is why no Pauli string can play its role.
@isnad1 id=ne.1h4v.s7.f105230d4b72 from=translated src=- shape=1d9ce7b6 vocab=e15ee47c
-/
theorem toMatrix_mul_ne_smul_aux (h : sympForm G s = 1) (c : ℂ) :
    toMatrix (G * s) ≠ c • toMatrix s := by
  intro heq
  rw [← toMatrix_mul] at heq
  have hG : toMatrix G = c • (1 : Matrix (Bits n) (Bits n) ℂ) := by
    have := congrArg (· * toMatrix s⁻¹) heq
    simp only [smul_mul_assoc, mul_assoc, toMatrix_mul_toMatrix_inv, mul_one] at this
    exact this
  obtain ⟨hx, hz⟩ := x_and_z_eq_zero_of_toMatrix_eq_smul_one hG
  rw [sympForm_eq_zero_of_x_eq_zero_of_z_eq_zero hx hz] at h
  exact absurd h (by decide)

/-- The same statement, named for what it is used for.
@isnad1 id=ne.1h4v.s7.f105230d4b72 from=translated src=- shape=1d9ce7b6 vocab=e15ee47c
-/
theorem toMatrix_mul_ne_smul (h : sympForm G s = 1) (c : ℂ) :
    toMatrix (G * s) ≠ c • toMatrix s := toMatrix_mul_ne_smul_aux h c

/-- **The two branch terms are linearly independent.** Non-collinearity (`toMatrix_mul_ne_smul`) is
not by itself linear independence — it leaves open `a • A = 0` with `a ≠ 0` — and what closes the
gap is `toMatrix_ne_zero`. This is the property `Rotation.lean` names as what the damping
consequence of `apd:eq:pauli_rotation_branch` needs.
@isnad1 id=linearin.1h3v.s7.ce499f65c1bd from=translated src=- shape=d655a8b0 vocab=abb1bad4
-/
theorem linearIndependent_toMatrix_mul_pair (h : sympForm G s = 1) :
    LinearIndependent ℂ ![toMatrix s, toMatrix (G * s)] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  by_cases hb : b = 0
  · subst hb
    rw [zero_smul, add_zero, smul_eq_zero] at hab
    exact ⟨hab.resolve_right (toMatrix_ne_zero s), rfl⟩
  · refine absurd ?_ (toMatrix_mul_ne_smul h (-(b⁻¹ * a)))
    have hB : b • toMatrix (G * s) = (-a) • toMatrix s := by
      rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
      exact hab
    calc toMatrix (G * s) = b⁻¹ • (b • toMatrix (G * s)) := by
          rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = (-(b⁻¹ * a)) • toMatrix s := by rw [hB, smul_smul]; congr 1; ring

/-! ### One qubit, entry by entry

The check that the definition really is the operator it is named for. Everything above is a
statement *about* `toMatrix`, so a sign or transpose slip here would be invisible to the kernel and
fatal to the correspondence with the paper's operators. `Bits 1` has the two labels `0` and `1`;
entries
are listed in that order, so the three displays below read

  `X = ((0,1),(1,0))`,   `Z = ((1,0),(0,−1))`,   `Y = ((0,−i),(i,0))`,

which are the standard Pauli matrices with the standard signs.

`X1` and `Z1` are the one-qubit case of the phase-zero factorization
`toMatrix ⟨x,z,0⟩ = ⨂ᵢ X^{xᵢ} Z^{zᵢ}`. `Y1` is deliberately **not**: at `(x,z) = (1,1)` the
phase-zero string is `X Z = −i Y`, and the `+Y` displayed below is the phase-one representative —
exactly the `#{Y-sites}` normalization that reaching the set `{I,X,Y,Z}^{⊗n}` of
`def:pauli_basis` requires. `phase = 3` would give `−Y`, and `isSelfAdjoint_iff_phase` admits
both. The general tensor and phase identities are proved in `Pauli/Tensor.lean`; these are finite
sanity checks. -/

end PauliString

end Lean4LPD
