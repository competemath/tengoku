import Tengoku
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.Universal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Specialization of Theorem `thm:universal` to weighted-permutation sequences
`A_w`, and its easy corollaries: `cor:iterated`, the eigenvector corollary,
`cor:dynamics`.
-/

namespace CongruenceTheory

open Finset MvPolynomial

/-- `A_w(n)`, the weighted-permutation enumerator for an integral weight sequence `w`.-/
noncomputable def Aw (w : ℕ → ℤ) (n : ℕ) : ℤ := MvPolynomial.eval w (C n)

lemma cast_Aw_eq_eval_Cmod (k : ℕ) (w : ℕ → ℤ) (m : ℕ) :
    ((Aw w m : ℤ) : ZMod k) = MvPolynomial.eval (fun j => ((w j : ℤ) : ZMod k)) (Cmod k m) := by
  show (Int.castRingHom (ZMod k)) (Aw w m) = _
  rw [Aw, Cmod, MvPolynomial.eval₂_comp (Int.castRingHom (ZMod k)) w (C m),
    ← MvPolynomial.eval_map]
  rfl

/-- **Theorem `thm:universal`, specialized to `A_w`.** `A_w(n+k) ≡ A_w(n) A_w(k) (mod k)`.-/
theorem Aw_shift_mod (k : ℕ) (hk : 1 ≤ k) (w : ℕ → ℤ) (n : ℕ) :
    (k : ℤ) ∣ (Aw w (n + k) - Aw w n * Aw w k) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [cast_Aw_eq_eval_Cmod, cast_Aw_eq_eval_Cmod, cast_Aw_eq_eval_Cmod,
    universal_shift_mod k hk n, map_mul]
  ring

/-- The `A_w`-eigenvector corollary: `A_w(n+k) ≡ A_w(k) A_w(n) (mod k)`, i.e. `A_w` modulo `k` is
an eigenvector of the translation operator `T_k`, with eigenvalue `A_w(k)`.-/
theorem Aw_translation_eigenvector (k : ℕ) (hk : 1 ≤ k) (w : ℕ → ℤ) (n : ℕ) :
    (k : ℤ) ∣ (Aw w (n + k) - Aw w k * Aw w n) := by
  have := Aw_shift_mod k hk w n
  have heq : Aw w (n + k) - Aw w k * Aw w n = Aw w (n + k) - Aw w n * Aw w k := by ring
  rwa [heq]

end CongruenceTheory
