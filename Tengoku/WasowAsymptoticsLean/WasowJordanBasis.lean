import Tengoku.WasowAsymptoticsLean.WasowLeadingBlocks
import Tengoku.Seed.Algebra.Module.PID
import Tengoku.Seed.Algebra.Polynomial.Module.AEval
import Tengoku.Seed.RingTheory.AdjoinRoot
import Tengoku.Seed.LinearAlgebra.DirectSum.Basis
import Tengoku.Seed.Data.Fin.Rev

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms primary_torsion` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_cyclic_decomposition` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reversedBasis_apply` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms X_smul_reversedBasis_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms X_smul_reversedBasis_succ` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sumBasis_apply` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms chainBasis_apply` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms chainBasis_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms chainBasis_succ` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms positiveBasis_apply` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms positiveBasis_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms positiveBasis_succ` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms toMatrix_positiveBasis` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_jordan_basis` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_jordan_matrix_coordinates` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_generalized_jordan_basis` (it only prints; the queue checks the axioms of every declaration). -/

/-! Genuine Jordan chain coordinates for a nilpotent complex operator, derived
from the structure theorem for primary torsion modules over the PID ℂ[X]. -/
set_option autoImplicit false
noncomputable section
open Module Polynomial
open scoped DirectSum
namespace WasowJordanBasis
abbrev Truncated (k : ℕ) := ℂ[X] ⧸ Ideal.span {((X : ℂ[X]) ^ k)}

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Nilpotence supplies the primary torsion hypothesis; no chain basis is assumed.
@isnad1 id=istorsio.1h2v.s9.049b31dff80a from=translated src=- shape=3cced8d9 vocab=5394a1da
-/
theorem primary_torsion (f : End ℂ V) (hf : IsNilpotent f) :
    Module.IsTorsion' (Module.AEval' f) (Submonoid.powers (X : ℂ[X])) := by
  obtain ⟨n, hn⟩ := hf
  apply (Submodule.isTorsion'_powers_iff (X : ℂ[X])).mpr
  intro x
  refine ⟨n, ?_⟩
  obtain ⟨v, rfl⟩ := (Module.AEval'.of f).surjective x
  rw [Module.AEval'.X_pow_smul_of, hn, zero_smul, map_zero]

/-- The actual polynomial-linear decomposition into truncated polynomial rings.
@isnad1 id=ex.1h2v.s9.5afd1f8c8027 from=translated src=- shape=1cadc46e vocab=3df8b4f8
-/
theorem exists_cyclic_decomposition [FiniteDimensional ℂ V] (f : End ℂ V) (hf : IsNilpotent f) :
    ∃ (d : ℕ) (k : Fin d → ℕ),
      Nonempty (Module.AEval' f ≃ₗ[ℂ[X]] ⨁ i : Fin d, Truncated (k i)) := by
  exact Module.torsion_by_prime_power_decomposition Polynomial.irreducible_X
    (primary_torsion f hf)

/-- The quotient presentation with its inherited scalar structure.-/
def quotientEquiv (k : ℕ) : AdjoinRoot ((X : ℂ[X]) ^ k) ≃ₗ[ℂ] Truncated k where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reversing the monomial basis gives the usual superdiagonal shift convention.-/
def reversedBasis (k : ℕ) : Basis (Fin k) ℂ (Truncated k) :=
  (((AdjoinRoot.powerBasis' ((monic_X : (X : ℂ[X]).Monic).pow k)).basis.reindex
    (finCongr (by simp))).reindex (Fin.revPerm (n := k))).map (quotientEquiv k)

/--
@isnad1 id=eq.0h2v.s9.445579b90129 from=translated src=- shape=fba72ea3 vocab=714374cc
-/
theorem reversedBasis_apply (k : ℕ) (i : Fin k) :
    reversedBasis k i = AdjoinRoot.root ((X : ℂ[X]) ^ k) ^ (k - 1 - i.val) := by
  unfold reversedBasis
  rw [Basis.map_apply, Basis.reindex_apply, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  simp [quotientEquiv, Fin.revPerm, Fin.rev, Nat.sub_sub, Nat.add_comm]
  rfl

/-- Multiplication by X kills the first vector in each reversed chain.
@isnad1 id=eq.1h1v.s9.223e1f1aaa34 from=translated src=- shape=95977251 vocab=55139ff9
-/
theorem X_smul_reversedBasis_zero (k : ℕ) (hk : 0 < k) :
    (X : ℂ[X]) • reversedBasis k ⟨0, hk⟩ = 0 := by
  rw [reversedBasis_apply]
  change AdjoinRoot.root ((X : ℂ[X]) ^ k) *
    AdjoinRoot.root ((X : ℂ[X]) ^ k) ^ (k - 1 - 0) = 0
  rw [Nat.sub_zero, ← pow_succ', Nat.sub_add_cancel hk]
  simpa only [map_pow, AdjoinRoot.mk_X] using (AdjoinRoot.mk_self (f := (X : ℂ[X]) ^ k))

/-- The remaining vectors move one step down the chain.
@isnad1 id=eq.1h2v.s9.2edcf7c480d1 from=translated src=- shape=bdf6bbfe vocab=f6ad1542
-/
theorem X_smul_reversedBasis_succ (k : ℕ) (i : Fin k) (hi : 0 < i.val) :
    (X : ℂ[X]) • reversedBasis k i = reversedBasis k ⟨i.val - 1, by omega⟩ := by
  rw [reversedBasis_apply, reversedBasis_apply]
  change AdjoinRoot.root ((X : ℂ[X]) ^ k) *
    AdjoinRoot.root ((X : ℂ[X]) ^ k) ^ (k - 1 - i.val) = _
  rw [← pow_succ']
  congr 1
  change k - 1 - i.val + 1 = k - 1 - (i.val - 1)
  omega

/-- Evaluation of the actual direct-sum basis.
@isnad1 id=eq.0h4v.s10.6edca2aaace4 from=translated src=- shape=5d45ecbd vocab=f2115c43
-/
theorem sumBasis_apply {d : ℕ} (k : Fin d → ℕ) (a : Fin d) (i : Fin (k a)) :
    DFinsupp.basis (fun a => reversedBasis (k a)) ⟨a, i⟩ =
      DFinsupp.single a (reversedBasis (k a) i) := by
  apply Basis.apply_eq_iff.mpr
  ext ⟨b, j⟩
  change (reversedBasis (k b)).repr ((DFinsupp.single a (reversedBasis (k a) i) :
    Π₀ c : Fin d, Truncated (k c)) b) j =
    Finsupp.single (⟨a, i⟩ : Σ c : Fin d, Fin (k c)) 1 ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    simp [Finsupp.single_apply_left sigma_mk_injective]
  · simp [hab]

/-- Transport the direct sum's chain basis back to the original vector space.-/
def chainBasis (f : End ℂ V) {d : ℕ} {k : Fin d → ℕ}
    (e : Module.AEval' f ≃ₗ[ℂ[X]] ⨁ a : Fin d, Truncated (k a)) :
    Basis (Σ a : Fin d, Fin (k a)) ℂ V :=
  (DFinsupp.basis (fun a => reversedBasis (k a))).map
    ((e.symm.restrictScalars ℂ).trans (Module.AEval'.of f).symm)

/--
@isnad1 id=eq.0h7v.s12.3eb071cf4104 from=translated src=- shape=00196f82 vocab=f5bc3408
-/
theorem chainBasis_apply (f : End ℂ V) {d : ℕ} {k : Fin d → ℕ}
    (e : Module.AEval' f ≃ₗ[ℂ[X]] ⨁ a : Fin d, Truncated (k a))
    (a : Fin d) (i : Fin (k a)) :
    chainBasis f e ⟨a, i⟩ =
      (Module.AEval'.of f).symm (e.symm (DFinsupp.single a (reversedBasis (k a) i))) := by
  simp [chainBasis, sumBasis_apply]

/--
@isnad1 id=eq.1h6v.s9.9999c31b720c from=translated src=- shape=c001086c vocab=1b15a8a2
-/
theorem chainBasis_zero (f : End ℂ V) {d : ℕ} {k : Fin d → ℕ}
    (e : Module.AEval' f ≃ₗ[ℂ[X]] ⨁ a : Fin d, Truncated (k a))
    (a : Fin d) (ha : 0 < k a) :
    f (chainBasis f e ⟨a, ⟨0, ha⟩⟩) = 0 := by
  rw [chainBasis_apply, ← Module.AEval'.of_symm_X_smul, ← e.symm.map_smul,
    ← DFinsupp.single_smul, X_smul_reversedBasis_zero _ ha]
  simp

/--
@isnad1 id=eq.1h7v.s9.5932e032ae85 from=translated src=- shape=967ad31a vocab=003e2783
-/
theorem chainBasis_succ (f : End ℂ V) {d : ℕ} {k : Fin d → ℕ}
    (e : Module.AEval' f ≃ₗ[ℂ[X]] ⨁ a : Fin d, Truncated (k a))
    (a : Fin d) (i : Fin (k a)) (hi : 0 < i.val) :
    f (chainBasis f e ⟨a, i⟩) = chainBasis f e ⟨a, ⟨i.val - 1, by omega⟩⟩ := by
  rw [chainBasis_apply, chainBasis_apply, ← Module.AEval'.of_symm_X_smul,
    ← e.symm.map_smul, ← DFinsupp.single_smul, X_smul_reversedBasis_succ _ i hi]

/-- Empty cyclic factors disappear, and every surviving length is a successor.-/
def positiveIndexEquiv {d : ℕ} (k : Fin d → ℕ) :
    WasowMultiShiftReduction.Index (fun a : {a : Fin d // 0 < k a} => k a.val - 1) ≃
      (Σ a : Fin d, Fin (k a)) where
  toFun x := ⟨x.1.val, ⟨x.2.val, by have := x.2.isLt; have := x.1.property; dsimp at *; omega⟩⟩
  invFun x := ⟨⟨x.1, by have := x.2.isLt; omega⟩,
    ⟨x.2.val, by have := x.2.isLt; dsimp at *; omega⟩⟩
  left_inv x := by rcases x with ⟨⟨a, ha⟩, ⟨i, hi⟩⟩; rfl
  right_inv x := by rcases x with ⟨a, ⟨i, hi⟩⟩; rfl

def positiveBasis (f : End ℂ V) {d : ℕ} {k : Fin d → ℕ}
    (e : Module.AEval' f ≃ₗ[ℂ[X]] ⨁ a : Fin d, Truncated (k a)) :
    Basis (WasowMultiShiftReduction.Index (fun a : {a : Fin d // 0 < k a} => k a.val - 1)) ℂ V :=
  (chainBasis f e).reindex (positiveIndexEquiv k).symm

/--
@isnad1 id=eq.0h7v.s10.8e4bfec34351 from=translated src=- shape=bb216b58 vocab=8fa73edf
-/
theorem positiveBasis_apply (f : End ℂ V) {d : ℕ} {k : Fin d → ℕ}
    (e : Module.AEval' f ≃ₗ[ℂ[X]] ⨁ a : Fin d, Truncated (k a))
    (a : {a : Fin d // 0 < k a}) (i : Fin (k a.val - 1 + 1)) :
    positiveBasis f e ⟨a, i⟩ =
      chainBasis f e ⟨a.val, ⟨i.val, by have := i.isLt; have := a.property; omega⟩⟩ := by
  rw [positiveBasis, Basis.reindex_apply]
  rfl

/--
@isnad1 id=eq.0h6v.s10.487488ce3263 from=translated src=- shape=8a1be097 vocab=9482ba45
-/
theorem positiveBasis_zero (f : End ℂ V) {d : ℕ} {k : Fin d → ℕ}
    (e : Module.AEval' f ≃ₗ[ℂ[X]] ⨁ a : Fin d, Truncated (k a))
    (a : {a : Fin d // 0 < k a}) : f (positiveBasis f e ⟨a, 0⟩) = 0 := by
  rw [positiveBasis_apply]
  exact chainBasis_zero f e a.val a.property

/--
@isnad1 id=eq.1h7v.s10.aba9d5f5b7a0 from=translated src=- shape=a5fc1fa2 vocab=f03ea2a4
-/
theorem positiveBasis_succ (f : End ℂ V) {d : ℕ} {k : Fin d → ℕ}
    (e : Module.AEval' f ≃ₗ[ℂ[X]] ⨁ a : Fin d, Truncated (k a))
    (a : {a : Fin d // 0 < k a}) (i : Fin (k a.val - 1 + 1)) (hi : 0 < i.val) :
    f (positiveBasis f e ⟨a, i⟩) =
      positiveBasis f e ⟨a, ⟨i.val - 1, by dsimp at *; omega⟩⟩ := by
  rw [positiveBasis_apply, positiveBasis_apply]
  exact chainBasis_succ f e a.val _ hi

/-- The actual Jordan matrix in the constructed chain basis.
@isnad1 id=eq.0h5v.s11.c02a5a0ea0c9 from=translated src=- shape=48ac436c vocab=4c32121a
-/
theorem toMatrix_positiveBasis (f : End ℂ V) {d : ℕ} {k : Fin d → ℕ}
    (e : Module.AEval' f ≃ₗ[ℂ[X]] ⨁ a : Fin d, Truncated (k a)) :
    LinearMap.toMatrix (positiveBasis f e) (positiveBasis f e) f =
      WasowMultiShiftReduction.jordanShift (fun a : {a : Fin d // 0 < k a} => k a.val - 1) := by
  classical
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [LinearMap.toMatrix_apply]
  by_cases hj : j.val = 0
  · have hj0 : j = 0 := Fin.ext hj
    subst j
    rw [positiveBasis_zero, map_zero, Finsupp.zero_apply]
    by_cases hab : a = b
    · subst b
      simp [WasowMultiShiftReduction.jordanShift, WasowShiftReduction.shift]
    · rw [WasowMultiShiftReduction.jordanShift, Matrix.blockDiagonal'_apply_ne _ _ _ hab]
  · have hjp : 0 < j.val := Nat.pos_of_ne_zero hj
    rw [positiveBasis_succ f e b j hjp, Basis.repr_self_apply]
    by_cases hab : a = b
    · subst b
      rw [WasowMultiShiftReduction.jordanShift, Matrix.blockDiagonal'_apply_eq]
      unfold WasowShiftReduction.shift
      have heq : ((⟨a, ⟨j.val - 1, by dsimp at *; omega⟩⟩ :
          WasowMultiShiftReduction.Index (fun a : {a : Fin d // 0 < k a} => k a.val - 1)) = ⟨a, i⟩) ↔
          j.val = i.val + 1 := by
        rw [Sigma.mk.inj_iff]
        simp only [heq_eq_eq, true_and, Fin.ext_iff]
        omega
      simp only [heq]
    · rw [WasowMultiShiftReduction.jordanShift, Matrix.blockDiagonal'_apply_ne _ _ _ hab]
      have hne : (⟨b, ⟨j.val - 1, by dsimp at *; omega⟩⟩ :
          WasowMultiShiftReduction.Index (fun a : {a : Fin d // 0 < k a} => k a.val - 1)) ≠ ⟨a, i⟩ := by
        intro hh
        exact hab (congrArg Sigma.fst hh).symm
      simp only [hne, ite_false]

/-- Every nilpotent complex operator has a genuine finite Jordan shift basis.
@isnad1 id=ex.1h2v.s9.bb6204bbc963 from=translated src=- shape=3bb3fae4 vocab=bba937e4
-/
theorem exists_jordan_basis [FiniteDimensional ℂ V] (f : End ℂ V) (hf : IsNilpotent f) :
    ∃ (σ : Type) (_ : Fintype σ) (_ : DecidableEq σ) (h : σ → ℕ)
      (b : Basis (WasowMultiShiftReduction.Index h) ℂ V),
      LinearMap.toMatrix b b f = WasowMultiShiftReduction.jordanShift h := by
  classical
  obtain ⟨d, k, ⟨e⟩⟩ := exists_cyclic_decomposition f hf
  exact ⟨{a : Fin d // 0 < k a}, inferInstance, inferInstance, (fun a => k a.val - 1),
    positiveBasis f e, toMatrix_positiveBasis f e⟩

/-- Actual mutually inverse matrix coordinates for an arbitrary nilpotent matrix.
@isnad1 id=ex.1h2v.s8.9fbf8c8d9d12 from=translated src=- shape=f9aa5360 vocab=8398573c
-/
theorem exists_jordan_matrix_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : IsNilpotent A) :
    ∃ (σ : Type) (_ : Fintype σ) (_ : DecidableEq σ) (h : σ → ℕ)
      (P : Matrix ι (WasowMultiShiftReduction.Index h) ℂ)
      (Q : Matrix (WasowMultiShiftReduction.Index h) ι ℂ),
      P * Q = 1 ∧ Q * P = 1 ∧ Q * A * P = WasowMultiShiftReduction.jordanShift h := by
  have hnil : IsNilpotent (Matrix.toLin' A) := by
    exact hA.map (Matrix.toLinAlgEquiv (Pi.basisFun ℂ ι))
  obtain ⟨σ, fσ, dσ, h, b, hb⟩ := exists_jordan_basis (Matrix.toLin' A) hnil
  let := fσ
  let := dσ
  refine ⟨σ, fσ, dσ, h, (Pi.basisFun ℂ ι).toMatrix b, b.toMatrix (Pi.basisFun ℂ ι),
    Basis.toMatrix_mul_toMatrix_flip _ _, Basis.toMatrix_mul_toMatrix_flip _ _, ?_⟩
  have hh := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    b (Pi.basisFun ℂ ι) b (Pi.basisFun ℂ ι) (Matrix.toLin' A)
  simpa only [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', hb] using hh

/-- Every generalized-eigenvalue block is further split into genuine Jordan
chains. Repeated eigenvalues and multiple chains within one eigenspace are allowed.
@isnad1 id=ex.0h2v.s10.8e47d369ce22 from=translated src=- shape=a07c4f91 vocab=282cc703
-/
theorem exists_generalized_jordan_basis [FiniteDimensional ℂ V] (f : End ℂ V) :
    ∃ (τ : WasowLeadingBlocks.Eigenvalues f → Type)
      (_ : ∀ a, Fintype (τ a)) (_ : ∀ a, DecidableEq (τ a)) (h : ∀ a, τ a → ℕ)
      (b : Basis (Σ a, WasowMultiShiftReduction.Index (h a)) ℂ V),
      LinearMap.toMatrix b b f = Matrix.blockDiagonal'
        (fun a => a.val • 1 + WasowMultiShiftReduction.jordanShift (h a)) := by
  classical
  let g (a : WasowLeadingBlocks.Eigenvalues f) :
      End ℂ (WasowLeadingBlocks.blockSpace f a) :=
    WasowLeadingBlocks.restriction f a -
      algebraMap ℂ (End ℂ (WasowLeadingBlocks.blockSpace f a)) a.val
  have hn (a : WasowLeadingBlocks.Eigenvalues f) : IsNilpotent (g a) :=
    WasowLeadingBlocks.restriction_sub_nilpotent f a
  choose τ fτ dτ h b hb using fun a => exists_jordan_basis (g a) (hn a)
  let _ (a) := fτ a
  let _ (a) := dτ a
  refine ⟨τ, fτ, dτ, h, (WasowLeadingBlocks.internal_blocks f).collectedBasis b, ?_⟩
  rw [LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal'
    (WasowLeadingBlocks.internal_blocks f) (WasowLeadingBlocks.internal_blocks f) b b
    (WasowLeadingBlocks.block_invariant f)]
  congr 1
  funext a
  have hrel : WasowLeadingBlocks.restriction f a = g a +
      algebraMap ℂ (End ℂ (WasowLeadingBlocks.blockSpace f a)) a.val := by
    dsimp [g]
    abel
  change LinearMap.toMatrix (b a) (b a) (WasowLeadingBlocks.restriction f a) = _
  rw [hrel, map_add, hb a]
  simp [Algebra.algebraMap_eq_smul_one, add_comm]

end WasowJordanBasis
