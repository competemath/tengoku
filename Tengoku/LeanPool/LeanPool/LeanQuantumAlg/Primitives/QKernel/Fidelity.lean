/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Core.Tensor
public import Tengoku

/-!
# Quantum kernel methods: the fidelity kernel and its Gram-matrix positive semidefiniteness

A data-encoding *quantum feature map* sends a classical input `x` to a quantum
state `|φ(x)⟩`. The induced *fidelity quantum kernel* is
`k(x, y) = |⟨φ(x) | φ(y)⟩|²` (for pure states this equals `tr[ρ(x) ρ(y)]`,
the Hilbert–Schmidt inner product of the density operators). The core fact that
makes such a `k` a legitimate kernel for classical kernel methods (SVMs, etc.)
is that every Gram matrix `K_{ij} = k(xᵢ, xⱼ)` is positive semidefinite.

The proof realizes the fidelity kernel as a genuine inner-product Gram matrix:
with the feature vector `w(x) := φ(x) ⊗ conj φ(x)` one has
`⟨w(x), w(y)⟩ = ⟨φ(x), φ(y)⟩ · conj⟨φ(x), φ(y)⟩ = |⟨φ(x), φ(y)⟩|²`
(via `PureState.inner_tensor_tensor`), so the kernel Gram matrix factors as
`K = Bᴴ B` and is positive semidefinite by
`Matrix.posSemidef_conjTranspose_mul_self`.

Sources: Schuld & Killoran (2019), *Quantum machine learning in feature Hilbert
spaces*; Schuld (2021), *Supervised quantum machine learning models are kernel
methods*.

## Main definitions / results

- `LeanPool.LeanQuantumAlg.PureState.conjState` — elementwise complex conjugate of a state.
- `LeanPool.LeanQuantumAlg.quantumKernel` — the fidelity quantum kernel `|⟨φ(x), φ(y)⟩|²`.
- `LeanPool.LeanQuantumAlg.quantumKernel_eq_inner_featureTensor` — the kernel as an inner
  product of feature vectors `φ(x) ⊗ conj φ(x)`.
- `LeanPool.LeanQuantumAlg.quantumKernel_gram_posSemidef` — the kernel Gram matrix is
  positive semidefinite (the validity-of-the-kernel theorem). Being
  positive semidefinite it is in particular Hermitian, i.e. symmetric.
- `LeanPool.LeanQuantumAlg.quantumKernel_self` — the diagonal value on a pure state.
-/

@[expose] public section

namespace QuantumAlg

namespace PureState

section

variable {n : ℕ}

/-- Elementwise complex conjugate of a pure state. -/
noncomputable def conjState (ψ : PureState n) : PureState n :=
  ofVec (WithLp.toLp 2 fun i => starRingEnd ℂ (ψ i)) (by
    calc
      ‖WithLp.toLp 2 (fun i => starRingEnd ℂ (ψ i))‖
          = ‖(ψ : StateVector n)‖ := by
            rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
            simp_all
      _ = 1 := ψ.norm_eq_one)

@[simp]
theorem conjState_apply (ψ : PureState n) (i : Fin (2 ^ n)) :
    conjState ψ i = starRingEnd ℂ (ψ i) := rfl

/-- Conjugating both arguments conjugates the inner product. -/
theorem inner_conjState (a b : PureState n) :
    inner ℂ (conjState a) (conjState b) = starRingEnd ℂ (inner ℂ a b) := by
  change inner ℂ ((conjState a : PureState n) : StateVector n)
      ((conjState b : PureState n) : StateVector n)
    = starRingEnd ℂ (inner ℂ (a : StateVector n) (b : StateVector n))
  simp only [PiLp.inner_apply, RCLike.inner_apply, conjState_apply, map_sum, map_mul]

end

end PureState

noncomputable section

variable {n : ℕ} {X : Type*}

/-- The feature vector `φ(x) ⊗ conj φ(x)` whose inner products realize the
fidelity kernel as a Gram matrix. -/
def featureTensor (φ : X → PureState n) (x : X) : PureState (n + n) :=
  (φ x).tensor (PureState.conjState (φ x))

/-- The fidelity quantum kernel `k(x, y) = |⟨φ(x), φ(y)⟩|²`, written as the
complex product `⟨φ(x), φ(y)⟩ · conj⟨φ(x), φ(y)⟩` (a nonnegative real). -/
def quantumKernel (φ : X → PureState n) (x y : X) : ℂ :=
  inner ℂ (φ x) (φ y) * starRingEnd ℂ (inner ℂ (φ x) (φ y))

open scoped ComplexOrder

namespace QuantumKernel

end QuantumKernel

end

end QuantumAlg
