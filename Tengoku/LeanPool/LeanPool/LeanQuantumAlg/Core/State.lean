/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Tengoku

/-!
# Qubit states

An `n`-qubit pure state is a unit vector in `ℂ^(2^n)` with the L2 inner
product. The raw Hilbert-space vector type is `StateVector n`; `PureState n`
bundles such a vector with its unit-norm proof.

## Naming: `PureState`, not `State`

In quantum mechanics the general notion of a state is a *density operator*
(density matrix); pure states are the special case of a closed system with
maximal knowledge. The algorithms in this library live entirely in that
special case (pure state + unitary evolution + projective measurement), but
the library does not redefine the standard term: this type is `PureState`,
and the bare name `State` is deliberately left undefined, reserved for the
density-operator concept should the library later introduce mixed states
(a pure state then embeds as the rank-one projector `|ψ⟩⟨ψ|`).

## Conventions

- **Endianness**: computational basis states of an `n`-qubit register are
  labelled by `n`-bit strings read as integers `0, …, 2^n - 1`
  [dW19, qcnotes.tex:587], leftmost bit most significant. We index qubits
  left to right, so the basis label `x : Fin (2 ^ n)` encodes
  `|q₀ q₁ … q_{n-1}⟩` with `x = Σ qᵢ · 2^(n-1-i)`: qubit 0 carries the most
  significant bit.
- **Normalization** is part of `PureState`: every value carries a proof that its
  underlying vector has norm `1`. Linear combinations live at the raw
  `StateVector` layer until separately proved normalized.
- Components are accessed by plain application `ψ i`; the underlying
  vector of `ψ : PureState n` is `(ψ : StateVector n)`.

## Main definitions

- `LeanPool.LeanQuantumAlg.StateVector n` — the Hilbert-space vector type
  `EuclideanSpace ℂ (Fin (2 ^ n))`.
- `LeanPool.LeanQuantumAlg.PureState n` — unit vectors in `StateVector n`.
- `LeanPool.LeanQuantumAlg.PureState.ket x` — computational basis ket `|x⟩`
  (`PiLp.single 2 x 1`).

The named one-qubit kets (`ket0`, `ket1`, `ketPlus`, `ketMinus`) and the
scalar `invSqrt2` now live in `LeanPool.LeanQuantumAlg.Core.Components.Kets`.

Pinned Mathlib API: `PiLp.single`, `PiLp.single_apply`, `PiLp.norm_single`,
`EuclideanSpace.norm_eq`.
-/

@[expose] public section

namespace QuantumAlg

/-- Raw Hilbert-space vector for an `n`-qubit pure-state register. -/
abbrev StateVector (n : ℕ) : Type := EuclideanSpace ℂ (Fin (2 ^ n))

/-- An `n`-qubit pure state: a unit vector in the computational Hilbert space.

The general (density-operator) notion of state is intentionally not defined
here — see the module docstring. -/
structure PureState (n : ℕ) where
  /-- Underlying Hilbert-space vector. -/
  vec : StateVector n
  /-- Pure states are normalized by definition. -/
  norm_eq_one : ‖vec‖ = 1

namespace PureState

noncomputable section

variable {n : ℕ}

instance : Coe (PureState n) (StateVector n) := ⟨PureState.vec⟩

instance : CoeFun (PureState n) (fun _ => Fin (2 ^ n) → ℂ) :=
  ⟨fun ψ => ψ.vec⟩

instance : Norm (PureState n) := ⟨fun ψ => ‖(ψ : StateVector n)‖⟩

instance : Inner ℂ (PureState n) :=
  ⟨fun ψ φ => inner ℂ (ψ : StateVector n) (φ : StateVector n)⟩

instance : HAdd (PureState n) (PureState n) (StateVector n) :=
  ⟨fun ψ φ => (ψ : StateVector n) + (φ : StateVector n)⟩

instance : HSub (PureState n) (PureState n) (StateVector n) :=
  ⟨fun ψ φ => (ψ : StateVector n) - (φ : StateVector n)⟩

instance : HSMul ℂ (PureState n) (StateVector n) :=
  ⟨fun c ψ => c • (ψ : StateVector n)⟩

/--
@isnad1 id=eq.0h4v.s8.c30a8629de67 from=translated src=- shape=107c23fb vocab=5e307335
-/
@[simp]
theorem hAdd_apply (ψ φ : PureState n) (i : Fin (2 ^ n)) :
    (ψ + φ : StateVector n) i = ψ i + φ i := rfl

/--
@isnad1 id=eq.0h4v.s8.f3f4990a52d1 from=translated src=- shape=107c23fb vocab=530c04a0
-/
@[simp]
theorem hSub_apply (ψ φ : PureState n) (i : Fin (2 ^ n)) :
    (ψ - φ : StateVector n) i = ψ i - φ i := rfl

/--
@isnad1 id=eq.0h4v.s8.1adbe98b6593 from=translated src=- shape=0498d063 vocab=7eb28758
-/
@[simp]
theorem hSMul_apply (c : ℂ) (ψ : PureState n) (i : Fin (2 ^ n)) :
    (c • ψ : StateVector n) i = c * ψ i := rfl

/-- Build a pure state from a normalized Hilbert-space vector. -/
def ofVec (v : StateVector n) (h : ‖v‖ = 1) : PureState n := ⟨v, h⟩

/--
@isnad1 id=eq.1h2v.s6.8510b60585aa from=translated src=- shape=6370a5ad vocab=22778322
-/
@[simp]
theorem coe_ofVec (v : StateVector n) (h : ‖v‖ = 1) :
    ((ofVec v h : PureState n) : StateVector n) = v := rfl

/--
@isnad1 id=eq.1h3v.s8.a06cd3f4a97e from=translated src=- shape=9766eb95 vocab=7a94afde
-/
@[simp]
theorem ofVec_apply (v : StateVector n) (h : ‖v‖ = 1) (i : Fin (2 ^ n)) :
    ofVec v h i = v i := rfl

/--
@isnad1 id=eq.0h2v.s6.7a67e94bacbc from=translated src=- shape=a01a8b7d vocab=eb52a5c9
-/
@[simp]
theorem norm_eq_one' (ψ : PureState n) : ‖(ψ : StateVector n)‖ = 1 :=
  ψ.norm_eq_one

/--
@isnad1 id=eq.1h3v.s7.cbeb4a01ab25 from=translated src=- shape=bcd3bc53 vocab=b575e033
-/
@[ext]
theorem ext {ψ φ : PureState n} (h : ∀ i, ψ i = φ i) : ψ = φ := by
  cases ψ with
  | mk ψ hψ =>
    cases φ with
    | mk φ hφ =>
      have hv : ψ = φ := by
        apply WithLp.ofLp_injective
        funext i
        exact h i
      simp_all

/-- The computational basis ket `|x⟩ : PureState n`, big-endian (qubit 0 is
the most significant bit of `x`). -/
def ket (x : Fin (2 ^ n)) : PureState n :=
  ofVec (PiLp.single 2 x 1) (by simp)

/--
@isnad1 id=eq.0h3v.s8.3699bd9d6b81 from=translated src=- shape=18a9eaaa vocab=ee6a49bc
-/
@[simp]
theorem ket_apply (x i : Fin (2 ^ n)) : ket x i = if i = x then 1 else 0 := by
  simp [ket]

/--
@isnad1 id=injectiv.0h1v.s4.c7a1925f1d17 from=translated src=- shape=894818b8 vocab=cbe40891
-/
theorem ket_injective : Function.Injective (ket (n := n)) := by
  intro x y hxy
  by_contra hne
  have h : ket x x = ket y x := by rw [hxy]
  rw [ket_apply, ket_apply, ite_eq_left rfl, ite_eq_right hne] at h
  exact one_ne_zero h

/--
@isnad1 id=eq.0h2v.s7.d6f776f0106c from=translated src=- shape=a03841fa vocab=ecbeef2d
-/
theorem norm_ket (x : Fin (2 ^ n)) : ‖(ket x : StateVector n)‖ = 1 := by
  exact (ket x).norm_eq_one

end

end PureState

end QuantumAlg
