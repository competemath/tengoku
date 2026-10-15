/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Core.State
public import Tengoku

/-!
# Hilbert operators and unitary gates

`HilbertOperator n` is the raw `2^n × 2^n` complex matrix type. It is used for
observables, projectors, matrix sums, and block-encoding operators that are not
necessarily unitary.

`Gate n` is a unitary Hilbert operator. Gate application maps pure states to
pure states; arbitrary linear combinations stay at the raw `StateVector` layer
until separately normalized.

Pinned Mathlib API: `Matrix.mulVec` (and `mulVec_add/smul/single_one`,
`one_mulVec`, `mulVec_mulVec`), `Matrix.mem_unitaryGroup_iff`,
`Equiv.Perm.permMatrix` (and `Matrix.permMatrix_mulVec`,
`Matrix.conjTranspose_permMatrix`, `Matrix.permMatrix_mul`,
`Matrix.permMatrix_one`), `Finset.sum_ite_eq'`.
-/

@[expose] public section

namespace QuantumAlg

/-- Raw linear operator on an `n`-qubit Hilbert space. -/
abbrev HilbertOperator (n : ℕ) : Type := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

namespace HilbertOperator

section

variable {n : ℕ}

/-- A Hilbert operator acts on a raw state vector by matrix-vector multiplication. -/
noncomputable def applyVec (A : HilbertOperator n) (ψ : StateVector n) : StateVector n :=
  WithLp.toLp 2 (A.mulVec ψ.ofLp)

/--
@isnad1 id=eq.0h4v.s8.77ae6c5fe634 from=translated src=- shape=9b01956b vocab=e823b623
-/
@[simp]
theorem applyVec_apply (A : HilbertOperator n) (ψ : StateVector n) (i : Fin (2 ^ n)) :
    applyVec A ψ i = ∑ j, A i j * ψ j :=
  rfl

/--
@isnad1 id=eq.0h4v.s8.2fb62fc2d6ea from=translated src=- shape=9f57457d vocab=290e0c56
-/
@[simp]
theorem applyVec_add (A : HilbertOperator n) (ψ φ : StateVector n) :
    applyVec A (ψ + φ) = applyVec A ψ + applyVec A φ := by
  unfold applyVec
  rw [show (ψ + φ).ofLp = ψ.ofLp + φ.ofLp from rfl, Matrix.mulVec_add]
  rfl

/--
@isnad1 id=eq.0h4v.s8.6025e5308c06 from=translated src=- shape=9f57457d vocab=38b94fe8
-/
@[simp]
theorem applyVec_sub (A : HilbertOperator n) (ψ φ : StateVector n) :
    applyVec A (ψ - φ) = applyVec A ψ - applyVec A φ := by
  unfold applyVec
  rw [show (ψ - φ).ofLp = ψ.ofLp - φ.ofLp from rfl, Matrix.mulVec_sub]
  rfl

/--
@isnad1 id=eq.0h4v.s7.7a6af559e5d0 from=translated src=- shape=23fab539 vocab=f1531693
-/
@[simp]
theorem applyVec_smul (A : HilbertOperator n) (c : ℂ) (ψ : StateVector n) :
    applyVec A (c • ψ) = c • applyVec A ψ := by
  unfold applyVec
  rw [show (c • ψ).ofLp = c • ψ.ofLp from rfl, Matrix.mulVec_smul]
  rfl

/--
@isnad1 id=eq.0h3v.s8.80ab91c2c2e2 from=translated src=- shape=0b9785c1 vocab=c7f4f4a7
-/
@[simp]
theorem applyVec_neg (A : HilbertOperator n) (ψ : StateVector n) :
    applyVec A (-ψ) = -applyVec A ψ := by
  unfold applyVec
  rw [show (-ψ).ofLp = -ψ.ofLp from rfl, Matrix.mulVec_neg]
  rfl

/--
@isnad1 id=eq.0h4v.s7.0c92de4a6bcd from=translated src=- shape=48515009 vocab=290e0c56
-/
@[simp]
theorem add_applyVec (A B : HilbertOperator n) (ψ : StateVector n) :
    applyVec (A + B) ψ = applyVec A ψ + applyVec B ψ := by
  unfold applyVec
  rw [Matrix.add_mulVec]
  rfl

/--
@isnad1 id=eq.0h4v.s7.25aebe28f7a9 from=translated src=- shape=05592dce vocab=f1531693
-/
@[simp]
theorem smul_applyVec (c : ℂ) (A : HilbertOperator n) (ψ : StateVector n) :
    applyVec (c • A) ψ = c • applyVec A ψ := by
  unfold applyVec
  rw [Matrix.smul_mulVec]
  rfl

/--
@isnad1 id=eq.0h2v.s5.b000b4a90a71 from=translated src=- shape=4e126b5d vocab=6dae396a
-/
@[simp]
theorem one_applyVec (ψ : StateVector n) : applyVec (1 : HilbertOperator n) ψ = ψ := by
  unfold applyVec
  rw [Matrix.one_mulVec]

/--
@isnad1 id=eq.0h4v.s7.e0c0188b44fc from=translated src=- shape=65456d1e vocab=4abf571c
-/
theorem mul_applyVec (A B : HilbertOperator n) (ψ : StateVector n) :
    applyVec (A * B) ψ = applyVec A (applyVec B ψ) := by
  unfold applyVec
  simp_all

/-- A Hilbert operator sends a basis ket to its corresponding column.
@isnad1 id=eq.0h4v.s7.d4d26940fb1d from=translated src=- shape=ea690282 vocab=9935da2d
-/
theorem applyVec_ket (A : HilbertOperator n) (x : Fin (2 ^ n)) (i : Fin (2 ^ n)) :
    applyVec A (PureState.ket x : StateVector n) i = A i x := by
  simp_all

/-- A unitary Hilbert operator preserves inner products on raw state vectors.
@isnad1 id=eq.1h4v.s11.af76d4bbe8b0 from=translated src=- shape=ef3e07a3 vocab=26a57c6d
-/
theorem inner_applyVec_applyVec_of_mem_unitaryGroup {U : HilbertOperator n}
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (ψ φ : StateVector n) :
    inner ℂ (applyVec U ψ) (applyVec U φ) = inner ℂ ψ φ := by
  have hUU : U.conjTranspose * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  simp only [PiLp.inner_apply, RCLike.inner_apply, applyVec_apply]
  calc ∑ i, (∑ k, U i k * φ k) * starRingEnd ℂ (∑ j, U i j * ψ j)
      = ∑ i, ∑ k, ∑ j, (U i k * starRingEnd ℂ (U i j))
          * (φ k * starRingEnd ℂ (ψ j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        ring
    _ = ∑ k, ∑ j, (∑ i, U i k * starRingEnd ℂ (U i j))
          * (φ k * starRingEnd ℂ (ψ j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ k, ∑ j, (1 : HilbertOperator n) j k * (φ k * starRingEnd ℂ (ψ j)) := by
        refine Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        congr 1
        rw [← hUU, Matrix.mul_apply]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Matrix.conjTranspose_apply,
            show star (U i j) = starRingEnd ℂ (U i j) from rfl, mul_comm]
    _ = ∑ k, φ k * starRingEnd ℂ (ψ k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
        exact Fintype.sum_ite_eq' k fun j => φ k * starRingEnd ℂ (ψ j)

/-- A unitary Hilbert operator preserves raw vector norms.
@isnad1 id=eq.1h3v.s9.4fca2c989055 from=translated src=- shape=ab419800 vocab=5b82a380
-/
theorem norm_applyVec_of_mem_unitaryGroup {U : HilbertOperator n}
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (ψ : StateVector n) :
    ‖applyVec U ψ‖ = ‖ψ‖ := by
  have h := inner_applyVec_applyVec_of_mem_unitaryGroup hU ψ ψ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖applyVec U ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by exact_mod_cast h
  simp_all

end

end HilbertOperator

/-- A unitary gate on an `n`-qubit Hilbert space. -/
structure Gate (n : ℕ) where
  /-- Underlying Hilbert-space operator. -/
  op : HilbertOperator n
  /-- Gates are unitary by definition. -/
  unitary : op ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ

namespace Gate

noncomputable section

variable {n : ℕ}

instance : Coe (Gate n) (HilbertOperator n) := ⟨Gate.op⟩

instance : CoeFun (Gate n) (fun _ => Fin (2 ^ n) → Fin (2 ^ n) → ℂ) :=
  ⟨fun G => G.op⟩

instance : HMul (Gate n) (HilbertOperator n) (HilbertOperator n) where
  hMul G A := (G : HilbertOperator n) * A

instance : HMul (HilbertOperator n) (Gate n) (HilbertOperator n) where
  hMul A G := A * (G : HilbertOperator n)

/--
@isnad1 id=eq.1h3v.s6.b412f2e4240f from=translated src=- shape=81a36159 vocab=0dae5a02
-/
@[ext]
theorem ext {G K : Gate n} (h : ∀ i j, G i j = K i j) : G = K := by
  cases G with
  | mk G hG =>
    cases K with
    | mk K hK =>
      have hGK : G = K := by
        ext i j
        exact h i j
      simp_all

/-- Build a gate from a unitary Hilbert operator. -/
def ofUnitary (U : HilbertOperator n)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) : Gate n := ⟨U, hU⟩

/--
@isnad1 id=eq.1h2v.s9.9d5e227a387c from=translated src=- shape=3f8411e1 vocab=b41d035a
-/
@[simp]
theorem coe_ofUnitary (U : HilbertOperator n)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    ((ofUnitary U hU : Gate n) : HilbertOperator n) = U := rfl

instance : Monoid (Gate n) where
  one := ofUnitary 1 (one_mem _)
  mul G K := ofUnitary ((G : HilbertOperator n) * (K : HilbertOperator n))
    (mul_mem G.unitary K.unitary)
  one_mul G := by
    ext i j
    change ((1 : HilbertOperator n) * (G : HilbertOperator n)) i j = G i j
    simp
  mul_one G := by
    ext i j
    change ((G : HilbertOperator n) * (1 : HilbertOperator n)) i j = G i j
    simp
  mul_assoc G K L := by
    ext i j
    change (((G : HilbertOperator n) * (K : HilbertOperator n)) * (L : HilbertOperator n)) i j
      = ((G : HilbertOperator n) * ((K : HilbertOperator n) * (L : HilbertOperator n))) i j
    rw [Matrix.mul_assoc]

/--
@isnad1 id=eq.0h1v.s6.c2711b8e450f from=translated src=- shape=771c46e9 vocab=1f7fa39a
-/
@[simp]
theorem coe_one : (((1 : Gate n) : HilbertOperator n)) = 1 := rfl

/--
@isnad1 id=eq.0h3v.s7.da609a1f745b from=translated src=- shape=ce15e3e4 vocab=53f52548
-/
@[simp]
theorem coe_mul (G K : Gate n) :
    (((G * K : Gate n) : HilbertOperator n))
      = (G : HilbertOperator n) * (K : HilbertOperator n) := rfl

/-- Conjugate transpose of a unitary gate, again as a gate. -/
def conjTranspose (G : Gate n) : Gate n :=
  ofUnitary ((G : HilbertOperator n).conjTranspose) (by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp G.unitary)

instance : Inv (Gate n) := ⟨conjTranspose⟩

/--
@isnad1 id=eq.0h2v.s6.54c073845f9c from=translated src=- shape=cb1a814e vocab=e08ce6af
-/
@[simp]
theorem coe_conjTranspose (G : Gate n) :
    ((G.conjTranspose : Gate n) : HilbertOperator n)
      = (G : HilbertOperator n).conjTranspose := rfl

/-- A gate acts on a raw vector by its underlying Hilbert operator. -/
def applyVec (G : Gate n) (ψ : StateVector n) : StateVector n :=
  HilbertOperator.applyVec (G : HilbertOperator n) ψ

/-- A gate evolves a pure state to a pure state. -/
def apply (G : Gate n) (ψ : PureState n) : PureState n :=
  PureState.ofVec (G.applyVec (ψ : StateVector n)) (by
    change ‖HilbertOperator.applyVec (G : HilbertOperator n) (ψ : StateVector n)‖ = 1
    rw [HilbertOperator.norm_applyVec_of_mem_unitaryGroup G.unitary, ψ.norm_eq_one])

/-- Alias for `apply`, emphasizing unitary time evolution. -/
def evolve (G : Gate n) (ψ : PureState n) : PureState n := G.apply ψ

/--
@isnad1 id=eq.0h4v.s8.32579c5e89e3 from=translated src=- shape=a714ce9d vocab=68e41184
-/
@[simp]
theorem applyVec_apply (G : Gate n) (ψ : StateVector n) (i : Fin (2 ^ n)) :
    G.applyVec ψ i = ∑ j, G i j * ψ j := rfl

/--
@isnad1 id=eq.0h4v.s8.5b00dd275469 from=translated src=- shape=b1714c4a vocab=dc48d5bd
-/
@[simp]
theorem apply_apply (G : Gate n) (ψ : PureState n) (i : Fin (2 ^ n)) :
    G.apply ψ i = ∑ j, G i j * ψ j := by
  change G.applyVec (ψ : StateVector n) i = ∑ j, G i j * ψ j
  rfl

/--
@isnad1 id=eq.0h4v.s8.004869bb5127 from=translated src=- shape=9f57457d vocab=202d0447
-/
@[simp]
theorem applyVec_add (G : Gate n) (ψ φ : StateVector n) :
    G.applyVec (ψ + φ) = G.applyVec ψ + G.applyVec φ :=
  HilbertOperator.applyVec_add (G : HilbertOperator n) ψ φ

/--
@isnad1 id=eq.0h4v.s8.51c569f9b534 from=translated src=- shape=9f57457d vocab=6a7840d3
-/
@[simp]
theorem applyVec_sub (G : Gate n) (ψ φ : StateVector n) :
    G.applyVec (ψ - φ) = G.applyVec ψ - G.applyVec φ :=
  HilbertOperator.applyVec_sub (G : HilbertOperator n) ψ φ

/--
@isnad1 id=eq.0h4v.s7.386c006c3b9e from=translated src=- shape=23fab539 vocab=89993793
-/
@[simp]
theorem applyVec_smul (G : Gate n) (c : ℂ) (ψ : StateVector n) :
    G.applyVec (c • ψ) = c • G.applyVec ψ :=
  HilbertOperator.applyVec_smul (G : HilbertOperator n) c ψ

/--
@isnad1 id=eq.0h3v.s8.20f8162b0452 from=translated src=- shape=0b9785c1 vocab=2e52f1e9
-/
@[simp]
theorem applyVec_neg (G : Gate n) (ψ : StateVector n) :
    G.applyVec (-ψ) = -G.applyVec ψ :=
  HilbertOperator.applyVec_neg (G : HilbertOperator n) ψ

-- Compatibility names for linear proofs at the raw vector layer.
/--
@isnad1 id=eq.0h4v.s8.004869bb5127 from=translated src=- shape=9f57457d vocab=202d0447
-/
theorem apply_add (G : Gate n) (ψ φ : StateVector n) :
    G.applyVec (ψ + φ) = G.applyVec ψ + G.applyVec φ :=
  applyVec_add G ψ φ

/--
@isnad1 id=eq.0h4v.s7.386c006c3b9e from=translated src=- shape=23fab539 vocab=89993793
-/
theorem apply_smul (G : Gate n) (c : ℂ) (ψ : StateVector n) :
    G.applyVec (c • ψ) = c • G.applyVec ψ :=
  applyVec_smul G c ψ

/--
@isnad1 id=eq.0h2v.s4.d67ec593a785 from=translated src=- shape=4e126b5d vocab=23de8666
-/
@[simp]
theorem one_apply (ψ : PureState n) : (1 : Gate n).apply ψ = ψ := by
  ext i
  change HilbertOperator.applyVec (1 : HilbertOperator n) (ψ : StateVector n) i = ψ i
  rw [HilbertOperator.one_applyVec]

/--
@isnad1 id=eq.0h2v.s4.258784b17281 from=translated src=- shape=4e126b5d vocab=9090de5a
-/
@[simp]
theorem one_applyVec (ψ : StateVector n) : (1 : Gate n).applyVec ψ = ψ :=
  HilbertOperator.one_applyVec ψ

/--
@isnad1 id=eq.0h4v.s5.a22cf9a697a6 from=translated src=- shape=76375c2b vocab=9da31385
-/
theorem mul_applyVec (G K : Gate n) (ψ : StateVector n) :
    (G * K).applyVec ψ = G.applyVec (K.applyVec ψ) :=
  HilbertOperator.mul_applyVec (G : HilbertOperator n) (K : HilbertOperator n) ψ

/--
@isnad1 id=eq.0h4v.s5.5c1cbb26d1c9 from=translated src=- shape=76375c2b vocab=abd193eb
-/
theorem mul_apply (G K : Gate n) (ψ : PureState n) :
    (G * K).apply ψ = G.apply (K.apply ψ) := by
  ext i
  change (G * K).applyVec (ψ : StateVector n) i
      = G.applyVec (K.applyVec (ψ : StateVector n)) i
  rw [mul_applyVec]

/-- A gate sends the basis ket `|x⟩` to its `x`-th column.
@isnad1 id=eq.0h4v.s7.4638045f29a4 from=translated src=- shape=6f33c92e vocab=d712f41e
-/
theorem apply_ket (G : Gate n) (x : Fin (2 ^ n)) (i : Fin (2 ^ n)) :
    G.apply (PureState.ket x) i = G i x := by
  simp_all

/-! ## Permutation gates -/

/-- The gate permuting the computational basis by `σ`:
`(ofPerm σ).apply (ket x) = ket (σ⁻¹ x)`. Unitary by construction. -/
def ofPerm (σ : Equiv.Perm (Fin (2 ^ n))) : Gate n :=
  ofUnitary (σ.permMatrix ℂ) (by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
      inv_mul_cancel, Matrix.permMatrix_one])

/--
@isnad1 id=eq.0h4v.s8.dda806cf7c5e from=translated src=- shape=16ea88fb vocab=c5ff7479
-/
theorem ofPerm_apply (σ : Equiv.Perm (Fin (2 ^ n))) (ψ : PureState n)
    (i : Fin (2 ^ n)) : (ofPerm σ).apply ψ i = ψ (σ i) := by
  change HilbertOperator.applyVec (σ.permMatrix ℂ) (ψ : StateVector n) i = ψ (σ i)
  simp_all

/--
@isnad1 id=eq.0h3v.s8.f397c507c42d from=translated src=- shape=b7306318 vocab=c80a1a10
-/
theorem ofPerm_apply_ket (σ : Equiv.Perm (Fin (2 ^ n))) (x : Fin (2 ^ n)) :
    (ofPerm σ).apply (PureState.ket x) = PureState.ket (σ⁻¹ x) := by
  ext i
  rw [ofPerm_apply, PureState.ket_apply, PureState.ket_apply]
  by_cases h : σ i = x
  · rw [ite_eq_left h, ite_eq_left (by rw [← h]; exact (Equiv.symm_apply_apply σ i).symm)]
  · rw [ite_eq_right h,
      ite_eq_right (fun hi => h (by rw [hi]; exact Equiv.apply_symm_apply σ x))]

/--
@isnad1 id=mem.0h2v.s9.af78a46ddbc5 from=translated src=- shape=18410892 vocab=32470428
-/
theorem ofPerm_mem_unitaryGroup (σ : Equiv.Perm (Fin (2 ^ n))) :
    (ofPerm σ : HilbertOperator n) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  (ofPerm σ).unitary

/-! ## Unitary gates preserve inner products and norms -/

/--
@isnad1 id=eq.0h3v.s6.26156f232e5b from=translated src=- shape=33cd66c3 vocab=f77c5a45
-/
theorem norm_apply (U : Gate n) (ψ : PureState n) :
    ‖(U.apply ψ : StateVector n)‖ = 1 :=
  (U.apply ψ).norm_eq_one

end

end Gate

end QuantumAlg
