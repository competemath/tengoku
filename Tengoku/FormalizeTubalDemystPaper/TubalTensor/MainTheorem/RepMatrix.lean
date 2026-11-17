import Tengoku.FormalizeTubalDemystPaper.TubalTensor.Defs.TubalRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/MainTheorem/RepMatrix.lean
  Definition 39: Representation matrix R_a.
  Lemmas 42, 43, 44, Corollary 44, Definition 45, Lemma 46.

  For an abstract tubal ring (Definition 10), the representation matrix R_a of
  an element a ∈ ℝⁿ is the unique n × n real matrix such that R_a x = a · x for all x.
-/

namespace TubalTensor

open Matrix

variable {n : ℕ} (tr : TubalRing n)

/-! ## Helper: standard basis decomposition -/

/-! ## Definition 39: Representation matrix -/

/-- **Definition 39**: The representation matrix `R_a` of a tubal ring element `a`.
    Column `j` of `R_a` is `a · eⱼ` where `eⱼ` is the `j`-th standard basis vector.-/
noncomputable def repMatrix (a : TubalCarrier n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => tr.mul a (Pi.single j 1) i)

/-- `repMatrix` unfolds entry-by-entry. This is definitional (`rfl`).
@isnad1 id=eq.0h5v.s5.6e3ef672aa21 from=translated src=- shape=9c8409b3 vocab=7f79be97
-/
@[simp]
theorem repMatrix_apply (a : TubalCarrier n) (i j : Fin n) :
    repMatrix tr a i j = tr.mul a (Pi.single j 1) i := rfl

/-! ## Lemma 43: Properties of the representation map -/

/-- **Lemma 43.3**: `R_{αx} = α R_x`.
@isnad1 id=eq.0h4v.s6.d09e33f4f443 from=translated src=- shape=d660d32c vocab=771b4ac6
-/
theorem repMatrix_smul (r : ℝ) (a : TubalCarrier n) :
    repMatrix tr (r • a) = r • repMatrix tr a := by
  ext i j
  exact congr_fun (tr.smul_mul r a (Pi.single j 1)) i

/-! ## Lemma 41 (part 2) and Lemma 42: Injectivity -/

/-! ## Corollary 44: Rep(ℝⁿ) is a sub-algebra of ℝ^{n×n}

  Summary of Lemma 43:
  - `repMatrix_add`:  R_{a+b} = R_a + R_b
  - `repMatrix_smul`: R_{αa} = α R_a
  - `repMatrix_mul`:  R_{a·b} = R_a R_b
  - `repMatrix_one`:  R_e = I
  - `repMatrix_injective`: a ↦ R_a is injective

  Together these say Rep(ℝⁿ) is a commutative sub-algebra of ℝ^{n×n}. -/

/-! ## Definition 45 & Lemma 46: Idempotent elements -/

/-- **Definition 45**: An element `a` in the tubal ring is *idempotent* if `a · a = a`.-/
def IsIdempotent (a : TubalCarrier n) : Prop := tr.mul a a = a

end TubalTensor
