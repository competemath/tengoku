module
public import Tengoku
public import Tengoku.Stafford38Formal.Stafford38.ChallengeDefinitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Transport of Stafford certificates

The right-ideal certificate is `1 = e * R + F * e * S`.
This module supplies the generic conditional reduction from monicization and
an exponent hypothesis, together with transport through algebra automorphisms
and nonzero scalars. These conditional interfaces are retained for current
imports; the unconditional theorem is proved in `Stafford38.FoundationClosure`.
-/

namespace Stafford
namespace Reduction

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- The monic right-coefficient presentation `X ^ N + ∑_{i<N} X ^ i * β i`.-/
def monicElt (X : A) (N : ℕ) (β : Fin N → A) : A :=
  X ^ N + ∑ i : Fin N, X ^ (i : ℕ) * β i

/-! ## Transport lemmas -/

/-- Stafford 3.8 transports along any ring automorphism.-/
theorem stafford38_of_ringEquiv (φ : A ≃+* A) {e : A} (h : Stafford38 (φ e)) :
    Stafford38 e := by
  obtain ⟨F, R, S, hFRS⟩ := h
  refine ⟨φ.symm F, φ.symm R, φ.symm S, ?_⟩
  have := congrArg φ.symm hFRS
  simpa using this

/-- Stafford 3.8 transports along scalar multiples (no nonvanishing needed: the
scalar is absorbed into the cofactors `R` and `S`).-/
theorem stafford38_smul (c : k) {e : A} (h : Stafford38 (c • e)) :
    Stafford38 e := by
  obtain ⟨F, R, S, hFRS⟩ := h
  refine ⟨F, c • R, c • S, ?_⟩
  have key : ∀ a b : A, (c • a) * b = a * (c • b) := by
    intro a b
    rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← Algebra.commutes c a]
  rw [hFRS, key e R]
  congr 1
  calc F * (c • e) * S = F * ((c • e) * S) := by rw [mul_assoc]
    _ = F * (e * (c • S)) := by rw [key e S]
    _ = F * e * (c • S) := by rw [mul_assoc]

/-- A cofactor of the special form `Y ^ s` already witnesses Stafford 3.8.-/
theorem stafford38_of_power {e Y : A} {s : ℕ} {R S : A}
    (h : (1 : A) = e * R + Y ^ s * e * S) : Stafford38 e :=
  ⟨Y ^ s, R, S, h⟩

/-! ## The two hypotheses -/

/-! ## The reduction -/

end Reduction
end Stafford
