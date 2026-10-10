import Tengoku

/-!
# Tensor index encoding

Indexing helpers for `d`-dimensional `n`-fold tensor product spaces, used to
address basis vectors of `(ℂᵈ)^⊗n ≅ ℂ^(dⁿ)` by tuples `Fin n → Fin d`.

## Main definitions
- `TensorIndex` — the tuple index type `Fin n → Fin d`.
- `tensorIndexEquiv` — the mixed-radix equivalence `TensorIndex d n ≃ Fin (dⁿ)`.
-/

noncomputable section

namespace Math.RepresentationTheory

/-- Index type for `dⁿ`-dimensional tensor product space.
    We represent indices as functions `Fin n → Fin d`, encoding which basis
    vector is selected in each tensor factor. -/
abbrev TensorIndex (d n : ℕ) := Fin n → Fin d

/-- Convert between `TensorIndex` and `Fin (dⁿ)`.
    This equivalence lets us work with tensor indices as tuples while storing
    matrices with `Fin (dⁿ)` indices (mixed-radix encoding). -/
def tensorIndexEquiv (d n : ℕ) [NeZero d] : TensorIndex d n ≃ Fin (d ^ n) :=
  finFunctionFinEquiv

end Math.RepresentationTheory

end
