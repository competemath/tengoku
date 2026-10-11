/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.SecondOrder.Certificate.Defs
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.SecondOrder.Certificate.Internal

/-!
# Verified binary certificates for existential second-order logic

An existential-SO formula is true exactly when its certificate checker accepts
some bit string. Every accepted certificate has exactly the sum of the truth
table sizes of the prefix relations. For sentences, the encoded checker gives
the same characterization of the existing query language, rejects malformed
structure encodings, and bounds certificate length by a fixed polynomial in
input length. `SecondOrder.PolynomialTime` proves that a polynomial-time machine
computes the checker's verdict, giving the upper direction of Fagin's theorem.
-/

public section

namespace Complexity.DescriptiveComplexity

namespace SOFormula

variable {V : Vocabulary} {rctx : List Nat} {n : Nat}

/-- An FO matrix has no relation-witness prefix. -/
theorem witnessArities_of_isFOMatrix (φ : SOFormula V rctx n) (h : φ.IsFOMatrix) :
    φ.witnessArities = [] := by
  cases φ <;> first | rfl | exact h.elim

/-- The witness polynomial evaluates to the exact sum of relation-table sizes. -/
@[simp] theorem witnessPolynomial_eval (φ : SOFormula V rctx n) (card : Nat) :
    φ.witnessPolynomial.eval card = DecREnv.encodingLength card φ.witnessArities :=
  DecREnv.encodingPolynomial_eval card φ.witnessArities

/-- A matrix consumes no witness bits and uses the existing matrix evaluator. -/
theorem checkCertificate_matrix (A : DecFinStruct V) (φ : SOFormula V rctx n)
    (h : φ.IsExistSO) (hm : φ.IsFOMatrix) (σ : Env A.card n)
    (ρ : DecREnv A.card rctx) (bits : List Bool) :
    φ.checkCertificate A h σ ρ bits = (bits.isEmpty && φ.evalMatrixB A hm σ ρ) := by
  cases φ <;> first | rfl | exact hm.elim

/-- An embedded FO formula needs the empty certificate and runs the FO evaluator. -/
theorem checkCertificate_ofFormula (A : DecFinStruct V) (φ : Formula V n)
    (σ : Env A.card n) (ρ : DecREnv A.card rctx) (bits : List Bool) :
    (ofFormula φ rctx).checkCertificate A (ofFormula_isExistSO φ rctx) σ ρ bits =
      (bits.isEmpty && Formula.evalB A σ φ) := by
  rw [checkCertificate_matrix A _ _ (ofFormula_isFOMatrix φ rctx), evalMatrixB_ofFormula]

/-- An encoded prefix table is consumed exactly, leaving the next relation environment. -/
theorem checkCertificate_soExist_append (A : DecFinStruct V) {k : Nat}
    (φ : SOFormula V (k :: rctx) n) (h : φ.IsExistSO) (σ : Env A.card n)
    (ρ : DecREnv A.card rctx) (τ : DecREnv A.card [k]) (bits : List Bool) :
    (soExist k φ).checkCertificate A h σ ρ (τ.encode ++ bits) =
      φ.checkCertificate A h σ (ρ.cons (τ 0)) bits := by
  have hlen : τ.encode.length = A.card ^ k := by simp
  simp only [checkCertificate, List.take_left' hlen, List.drop_left' hlen,
    DecREnv.decode_encode]

/-- An accepted certificate proves satisfaction of the existential-SO formula. -/
theorem checkCertificate_sound (A : DecFinStruct V) (φ : SOFormula V rctx n)
    (h : φ.IsExistSO) (σ : Env A.card n) (ρ : DecREnv A.card rctx) (bits : List Bool)
    (haccept : φ.checkCertificate A h σ ρ bits = true) :
    φ.Sat A.toFinStruct σ ρ.toREnv :=
  (checkCertificate_sound_internal A φ h σ ρ bits haccept).2

/-- Every accepted certificate has exactly the prescribed truth-table length. -/
theorem checkCertificate_length (A : DecFinStruct V) (φ : SOFormula V rctx n)
    (h : φ.IsExistSO) (σ : Env A.card n) (ρ : DecREnv A.card rctx) (bits : List Bool)
    (haccept : φ.checkCertificate A h σ ρ bits = true) :
    bits.length = DecREnv.encodingLength A.card φ.witnessArities :=
  (checkCertificate_sound_internal A φ h σ ρ bits haccept).1

/-- Binary certificates are sound and complete for existential-SO satisfaction. -/
theorem exists_checkCertificate_iff (A : DecFinStruct V) (φ : SOFormula V rctx n)
    (h : φ.IsExistSO) (σ : Env A.card n) (ρ : DecREnv A.card rctx) :
    (∃ bits, φ.checkCertificate A h σ ρ bits = true) ↔
      φ.Sat A.toFinStruct σ ρ.toREnv :=
  ⟨fun ⟨bits, hb⟩ => checkCertificate_sound A φ h σ ρ bits hb,
    checkCertificate_complete_internal A φ h σ ρ⟩

end SOFormula

namespace SOSentence

variable {V : Vocabulary}

end SOSentence

end Complexity.DescriptiveComplexity
