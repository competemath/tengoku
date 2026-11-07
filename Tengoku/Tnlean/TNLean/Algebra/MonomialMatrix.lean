/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Seed.Data.Matrix.Mul
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin
import Tengoku.Seed.LinearAlgebra.UnitaryGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Monomial matrices

A monomial matrix is a permutation matrix whose single nonzero entry in each
column is an arbitrary scalar. The matrix `Matrix.monomial σ φ` sends the basis
vector at `s` to `φ s` times the basis vector at `σ s`:

`(monomial σ φ) t s = if t = σ s then φ s else 0`.

Such matrices describe operators of the form
$T\ket{s}=\varphi(s)\ket{\sigma(s)}$; a vector `v` is fixed by `T` exactly
when `v (σ s) = φ s * v s` for every `s`. Products, adjoints, reindexings, and
scalar multiples of monomial matrices are again monomial, and a monomial
matrix with unimodular phases is unitary.
-/

namespace Matrix

variable {ι κ R : Type*} [DecidableEq ι]

/-- The monomial matrix with permutation `σ` and column phases `φ`: the entry in
row `σ s` and column `s` is `φ s`, and every other entry vanishes.-/
def monomial [Zero R] (σ : Equiv.Perm ι) (φ : ι → R) : Matrix ι ι R :=
  Matrix.of fun t s ↦ if t = σ s then φ s else 0

/--
@isnad1 id=eq.0h6v.s6.3ef88c72ed5b from=translated src=- shape=8c9e599d vocab=20b12c51
-/
theorem monomial_apply [Zero R] (σ : Equiv.Perm ι) (φ : ι → R) (t s : ι) :
    monomial σ φ t s = if t = σ s then φ s else 0 :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.7a222000ef9b from=translated src=- shape=14321905 vocab=83afb7a1
-/
@[simp]
theorem monomial_apply_perm [Zero R] (σ : Equiv.Perm ι) (φ : ι → R) (s : ι) :
    monomial σ φ (σ s) s = φ s := by
  simp [monomial_apply]

/--
@isnad1 id=eq.1h6v.s5.e21901ef6f36 from=translated src=- shape=dbdf71ce vocab=83afb7a1
-/
theorem monomial_apply_of_ne [Zero R] (σ : Equiv.Perm ι) (φ : ι → R) {t s : ι}
    (h : t ≠ σ s) :
    monomial σ φ t s = 0 := by
  simp [monomial_apply, h]

/-- Scalar multiples of monomial matrices are monomial.
@isnad1 id=eq.0h5v.s6.6486bf7926c2 from=translated src=- shape=01c008b4 vocab=0b5b1adc
-/
theorem smul_monomial [MulZeroClass R] (σ : Equiv.Perm ι) (φ : ι → R) (c : R) :
    c • monomial σ φ = monomial σ (c • φ) := by
  ext t s
  by_cases h : t = σ s <;> simp [monomial_apply, h]

/-- The identity is the monomial matrix of the identity permutation with all
phases equal to one.
@isnad1 id=eq.0h2v.s6.bb7e5f4eca0a from=translated src=- shape=e7de6747 vocab=38091c3a
-/
theorem monomial_one [MulZeroOneClass R] :
    monomial (1 : Equiv.Perm ι) (fun _ ↦ (1 : R)) = 1 := by
  ext t s
  by_cases h : t = s <;> simp [monomial_apply, one_apply, h]

/-- The adjoint of a monomial matrix is monomial for the inverse permutation, with
conjugated phases.
@isnad1 id=eq.0h4v.s6.70c17fc55f67 from=translated src=- shape=2a192746 vocab=06ef1f58
-/
theorem conjTranspose_monomial [AddMonoid R] [StarAddMonoid R] (σ : Equiv.Perm ι)
    (φ : ι → R) :
    (monomial σ φ)ᴴ = monomial σ.symm fun t ↦ star (φ (σ.symm t)) := by
  ext s t
  simp only [conjTranspose_apply, monomial_apply]
  by_cases h : t = σ s
  · subst h
    simp
  · rw [ite_eq_right h, ite_eq_right, star_zero]
    intro h'
    exact h (by rw [h', Equiv.apply_symm_apply])

/-- Simultaneous reindexing of a monomial matrix is monomial for the conjugated
permutation.
@isnad1 id=eq.0h6v.s7.6d4cdf50acc3 from=translated src=- shape=0f2c491d vocab=fa66e62f
-/
theorem reindex_monomial [Zero R] [DecidableEq κ] (e : ι ≃ κ) (σ : Equiv.Perm ι)
    (φ : ι → R) :
    reindex e e (monomial σ φ) =
      monomial (e.symm.trans (σ.trans e)) (φ ∘ e.symm) := by
  ext t s
  by_cases h : t = e (σ (e.symm s)) <;>
    simp [reindex_apply, monomial_apply, Equiv.symm_apply_eq, h]

variable [Fintype ι]

/-- A monomial matrix acts on a vector by permuting coordinates and multiplying by
the phases.
@isnad1 id=eq.0h5v.s6.5bc1734e0bf2 from=translated src=- shape=3100254b vocab=905d12f3
-/
theorem monomial_mulVec [NonAssocSemiring R] (σ : Equiv.Perm ι) (φ : ι → R)
    (v : ι → R) :
    monomial σ φ *ᵥ v = fun t ↦ φ (σ.symm t) * v (σ.symm t) := by
  funext t
  simp only [mulVec, dotProduct, monomial_apply]
  rw [Finset.sum_eq_single (σ.symm t)]
  · simp
  · intro s _ hs
    rw [ite_eq_right, zero_mul]
    intro h
    exact hs (by rw [h, Equiv.symm_apply_apply])
  · simp

/-- A monomial matrix carries a standard basis vector to its phase times the
permuted standard basis vector.
@isnad1 id=eq.0h5v.s7.839eed29363c from=translated src=- shape=238d3e61 vocab=ac3dba30
-/
theorem monomial_mulVec_single [NonAssocSemiring R] (σ : Equiv.Perm ι) (φ : ι → R) (s : ι) :
    monomial σ φ *ᵥ Pi.single s 1 = φ s • Pi.single (σ s) 1 := by
  rw [monomial_mulVec]
  funext t
  by_cases h : t = σ s
  · subst h
    simp
  · have hne : σ.symm t ≠ s := fun hc ↦ h (by rw [← hc, Equiv.apply_symm_apply])
    simp [h, hne]

/-- A vector is fixed by a monomial matrix exactly when its coordinates transport
along the permutation with the given phases.
@isnad1 id=iff.0h5v.s6.b1f4455dc4d6 from=translated src=- shape=29cd9dba vocab=16085ba1
-/
theorem monomial_mulVec_eq_self_iff [NonAssocSemiring R] (σ : Equiv.Perm ι) (φ : ι → R)
    (v : ι → R) :
    monomial σ φ *ᵥ v = v ↔ ∀ s, v (σ s) = φ s * v s := by
  rw [monomial_mulVec, funext_iff]
  constructor
  · intro h s
    simpa using (h (σ s)).symm
  · intro h t
    simpa using (h (σ.symm t)).symm

/-- The product of two monomial matrices is monomial for the composite permutation,
with the phases multiplied along the way.
@isnad1 id=eq.0h6v.s7.ab39d1bb7cd6 from=translated src=- shape=fc9151ca vocab=a36b83e4
-/
theorem monomial_mul_monomial [NonAssocSemiring R] (σ τ : Equiv.Perm ι) (φ ψ : ι → R) :
    monomial σ φ * monomial τ ψ = monomial (σ * τ) fun s ↦ φ (τ s) * ψ s := by
  ext t s
  simp only [mul_apply, monomial_apply]
  rw [Finset.sum_eq_single (τ s)]
  · by_cases h : t = σ (τ s) <;> simp [h, Equiv.Perm.mul_apply]
  · intro r _ hr
    simp [hr]
  · simp

/-- A monomial matrix with unimodular phases is unitary.
@isnad1 id=mem.1h4v.s7.75136712b17f from=translated src=- shape=119fba40 vocab=6fbed7f4
-/
theorem monomial_mem_unitaryGroup [CommRing R] [StarRing R] (σ : Equiv.Perm ι) (φ : ι → R)
    (h : ∀ s, star (φ s) * φ s = 1) :
    monomial σ φ ∈ unitaryGroup ι R := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_monomial,
    monomial_mul_monomial]
  have hσ : σ.symm * σ = 1 := by
    ext x
    simp
  rw [hσ]
  simp only [Equiv.symm_apply_apply, h]
  exact monomial_one

end Matrix
