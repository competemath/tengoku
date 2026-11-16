import Tengoku.OspTriviality.InhomogeneousDeformations.Native

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Independent oracle (T1), degree/skew (T2), Jacobi (T3)

`oracleFull` is an independent literal transcription of the fifteen-row table
in I105_R1A_N1_ORACLE_AND_TESTS.md §1, reversed to all 25 ordered pairs by the
document's own stated skew rule `[Y,X]=-(-1)^{p(X)p(Y)}[X,Y]`, applied here by
hand (not derived from `Native.bracket`/`bracketBasis`). `bracket_eq_oracle`
(T1) is the independent comparison; native formulas are not defined by this
table.
-/

namespace InhomogeneousDeformations

open Basis5

/--
@isnad1 id=eq.0h3v.s6.a88633916bde from=translated src=- shape=20aef74d vocab=d12b0440
-/
@[simp] lemma crat_smul_e (q : ℚ) (b : Basis5) (k : Basis5) :
    (crat q • e b) k = if k = b then crat q else 0 := by
  simp [crat, e, smul_eq_mul]

/-- `crat` is (the restriction of) a ring homomorphism `ℚ →+* Coeff`: these let
`simp` collapse any combination of `crat`-constants and raw `Coeff` numerals
down to a single `crat (single rational)`, closeable by `norm_num`/injectivity.
@isnad1 id=eq.0h0v.s5.c84c5f882d84 from=translated src=- shape=1ac31801 vocab=5551a90b
-/
@[simp] lemma crat_zero : crat (0 : ℚ) = 0 := by simp [crat]
/--
@isnad1 id=eq.0h0v.s5.7a09ebee0f5e from=translated src=- shape=1ac31801 vocab=5551a90b
-/
@[simp] lemma crat_one : crat (1 : ℚ) = 1 := by simp [crat]
/--
@isnad1 id=eq.0h2v.s5.f07c4ab7d4b1 from=translated src=- shape=967b4483 vocab=177bcffa
-/
@[simp] lemma crat_add (a b : ℚ) : crat a + crat b = crat (a + b) := by
  simp [crat]
/--
@isnad1 id=eq.0h2v.s5.65a15ef379b7 from=translated src=- shape=967b4483 vocab=d60844a7
-/
@[simp] lemma crat_mul (a b : ℚ) : crat a * crat b = crat (a * b) := by
  simp [crat]
/--
@isnad1 id=eq.0h1v.s5.e3bbe54926cb from=translated src=- shape=114bec3c vocab=a0a3d1e8
-/
@[simp] lemma crat_neg (a : ℚ) : -crat a = crat (-a) := by
  simp [crat]
/--
@isnad1 id=eq.0h1v.s5.defd55d4c5ae from=translated src=- shape=b4830d71 vocab=24a70e3a
-/
@[simp] lemma crat_natCast (n : ℕ) : (n : Coeff) = crat (n : ℚ) := by
  simp [crat]
/--
@isnad1 id=injectiv.0h0v.s2.cd5acab7caa0 from=translated src=- shape=54c8eceb vocab=8b107e1f
-/
lemma crat_injective : Function.Injective crat := by
  intro a b hab
  have h0 : MvPolynomial.coeff (0 : Fin 2 →₀ ℕ) (crat a) = MvPolynomial.coeff 0 (crat b) :=
    congrArg (MvPolynomial.coeff 0) hab
  simpa [crat, MvPolynomial.coeff_C] using h0
/--
@isnad1 id=iff.0h2v.s3.e8b5af551940 from=translated src=- shape=e5555f7a vocab=8bc55639
-/
@[simp] lemma crat_eq_iff (a b : ℚ) : crat a = crat b ↔ a = b := crat_injective.eq_iff
/--
@isnad1 id=eq.0h0v.s6.bae25522f269 from=translated src=- shape=5b7a101b vocab=a0a3d1e8
-/
@[simp] lemma crat_neg_one : crat (-1 : ℚ) = -1 := by
  rw [show (-1 : ℚ) = -(1 : ℚ) from rfl, ← crat_neg, crat_one]
/--
@isnad1 id=eq.0h0v.s5.9c3566a89144 from=translated src=- shape=4dcb44f2 vocab=5551a90b
-/
lemma crat_two : (2 : Coeff) = crat (2 : ℚ) := by
  rw [show (2 : ℚ) = 1 + 1 from by norm_num, ← crat_add, crat_one]
  norm_num
/--
@isnad1 id=eq.0h1v.s6.a9962a1dc3de from=translated src=- shape=00730b5b vocab=d60844a7
-/
@[simp] lemma crat_two_mul (a : ℚ) : (2 : Coeff) * crat a = crat (2 * a) := by
  rw [crat_two, crat_mul]
/--
@isnad1 id=eq.0h1v.s6.d74edc629201 from=translated src=- shape=eee1721b vocab=d60844a7
-/
@[simp] lemma crat_mul_two (a : ℚ) : crat a * (2 : Coeff) = crat (a * 2) := by
  rw [crat_two, crat_mul]

/-- Independent literal fifteen-row oracle, reversed to all 25 ordered pairs.-/
noncomputable def oracleFull : Basis5 → Basis5 → Mod
  | .L11, .L11 => crat 0 • e .L11
  | .L11, .L12 => crat 1 • e .L11
  | .L11, .L22 => crat 2 • e .L12
  | .L11, .F1  => crat 0 • e .F1
  | .L11, .F2  => crat 1 • e .F1
  | .L12, .L11 => crat (-1) • e .L11
  | .L12, .L12 => crat 0 • e .L12
  | .L12, .L22 => crat 1 • e .L22
  | .L12, .F1  => crat (-1 / 2) • e .F1
  | .L12, .F2  => crat (1 / 2) • e .F2
  | .L22, .L11 => crat (-2) • e .L12
  | .L22, .L12 => crat (-1) • e .L22
  | .L22, .L22 => crat 0 • e .L22
  | .L22, .F1  => crat (-1) • e .F2
  | .L22, .F2  => crat 0 • e .F2
  | .F1,  .L11 => crat 0 • e .F1
  | .F1,  .L12 => crat (1 / 2) • e .F1
  | .F1,  .L22 => crat 1 • e .F2
  | .F1,  .F1  => crat (1 / 2) • e .L11
  | .F1,  .F2  => crat (1 / 2) • e .L12
  | .F2,  .L11 => crat (-1) • e .F1
  | .F2,  .L12 => crat (-1 / 2) • e .F2
  | .F2,  .L22 => crat 0 • e .F2
  | .F2,  .F1  => crat (1 / 2) • e .L12
  | .F2,  .F2  => crat (1 / 2) • e .L22

/-- Parity sign helper for the graded formulas, `(-1)^(p·q)`, valued in `Coeff`.-/
noncomputable def gsign (p q : ZMod 2) : Coeff := if p = 1 ∧ q = 1 then crat (-1) else crat 1

/-- `bracket 0 y = 0` and `bracket x 0 = 0`: the finite double sum vanishes term
by term since `(0 : Mod) i = 0`.
@isnad1 id=eq.0h1v.s6.54e4e885f2fa from=translated src=- shape=fe2c2146 vocab=15a2c82a
-/
@[simp] lemma bracket_zero_left (y : Mod) : bracket 0 y = 0 := by
  unfold bracket; simp
/--
@isnad1 id=eq.0h1v.s6.8e00742a76d2 from=translated src=- shape=1d838610 vocab=15a2c82a
-/
@[simp] lemma bracket_zero_right (x : Mod) : bracket x 0 = 0 := by
  unfold bracket; simp

end InhomogeneousDeformations
