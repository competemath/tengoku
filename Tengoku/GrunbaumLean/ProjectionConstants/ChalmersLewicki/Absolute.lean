/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Authors: Giuliano Basso, Claude
-/
import Tengoku.GrunbaumLean.ProjectionConstants.ChalmersLewicki.Formula
import Tengoku.GrunbaumLean.ProjectionConstants.Foundations.Reduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The maximal absolute projection constant via the Chalmers–Lewicki formula

Combining Theorem 1.1 with the reduction to `ℓ∞^N`:

* `maxProjConst_eq_iSup_maxRelProjConst` : `λ_𝕜(m) = sup_N λ_𝕜(m, N)`;
* `maxProjConst_eq_iSup_clConst` : `λ_𝕜(m) = sup_N sup { ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| }`;
* `relProjConst_le_sqrt`, `absProjConst_le_sqrt`, `maxProjConst_le_sqrt` : the
  **Kadec–Snobar theorem** `λ(Y) ≤ √m` for every `m`-dimensional normed space;
* `weightedAbsSum_le_maxProjConst` : every configuration gives a lower bound for `λ_𝕜(m)`.
-/

namespace ProjectionConstants

universe u

variable {𝕜 : Type*} [RCLike 𝕜]

/--
@isnad1 id=le.0h3v.s4.9bad6f656708 from=translated src=- shape=d1ee11de vocab=fcee8920
-/
lemma maxRelProjConst_le_sqrt' (m : ℕ) : ∀ N, maxRelProjConst 𝕜 m N ≤ √m :=
  fun N => maxRelProjConst_le_sqrt m N

/-- **Kadec–Snobar.** `λ(Y, X) ≤ √m` for every `m`-dimensional subspace of a normed space.
@isnad1 id=le.1h4v.s8.8e52f273fd1a from=translated src=- shape=d06b1e83 vocab=24a03342
-/
theorem relProjConst_le_sqrt {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (Y : Submodule 𝕜 X) [FiniteDimensional 𝕜 Y] {m : ℕ} (hY : Module.finrank 𝕜 Y = m) :
    relProjConst Y ≤ √m :=
  relProjConst_le_of_maxRelProjConst_le (maxRelProjConst_le_sqrt' m) Y hY

/-- **Kadec–Snobar.** `λ(Y) ≤ √m` for every `m`-dimensional normed space `Y`.
@isnad1 id=le.1h3v.s6.ef8b3afdbf88 from=translated src=- shape=ae4f700f vocab=216f275c
-/
theorem absProjConst_le_sqrt (Y : Type u) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y] {m : ℕ} (hY : Module.finrank 𝕜 Y = m) : absProjConst 𝕜 Y ≤ √m :=
  absProjConst_le_of_maxRelProjConst_le (maxRelProjConst_le_sqrt' m) Y hY

/-- **Kadec–Snobar.** `λ_𝕜(m) ≤ √m`.
@isnad1 id=le.0h2v.s4.7d6d5f386988 from=translated src=- shape=20503de9 vocab=a83d775d
-/
theorem maxProjConst_le_sqrt (m : ℕ) : maxProjConst 𝕜 m ≤ √m :=
  maxProjConst_le_of_maxRelProjConst_le (maxRelProjConst_le_sqrt' m)

section Type0

variable {𝕜 : Type} [RCLike 𝕜]

/-- `λ_𝕜(m) = sup_N λ_𝕜(m, N)`.
@isnad1 id=eq.0h2v.s4.a3d0e3a5ac60 from=translated src=- shape=1325c6cb vocab=f4966e0c
-/
theorem maxProjConst_eq_iSup_maxRelProjConst (m : ℕ) :
    maxProjConst 𝕜 m = ⨆ N, maxRelProjConst 𝕜 m N :=
  maxProjConst_eq_iSup (maxRelProjConst_le_sqrt' m)

/-- `λ_𝕜(m) = sup_N sup { ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| : t ≥ 0, ‖t‖ = 1, P ∈ 𝒫ₘ(N) }`.
@isnad1 id=eq.0h2v.s4.d6ebc90ee5db from=translated src=- shape=3373bf89 vocab=c059bc96
-/
theorem maxProjConst_eq_iSup_clConst (m : ℕ) :
    maxProjConst 𝕜 m = ⨆ N, clConst 𝕜 (Fin N) m := by
  rw [maxProjConst_eq_iSup_maxRelProjConst]
  simp_rw [maxRelProjConst_eq_clConst]

/--
@isnad1 id=le.0h3v.s4.4999118ed7a6 from=translated src=- shape=21938dec vocab=d3454503
-/
lemma maxRelProjConst_le_maxProjConst (m N : ℕ) : maxRelProjConst 𝕜 m N ≤ maxProjConst 𝕜 m := by
  rw [maxProjConst_eq_iSup_maxRelProjConst]
  exact le_ciSup ⟨√m, by rintro _ ⟨N, rfl⟩; exact maxRelProjConst_le_sqrt m N⟩ N

/--
@isnad1 id=le.0h3v.s4.03baa303da8b from=translated src=- shape=98416d19 vocab=f3dfcf8c
-/
lemma clConst_le_maxProjConst (m N : ℕ) : clConst 𝕜 (Fin N) m ≤ maxProjConst 𝕜 m := by
  rw [← maxRelProjConst_eq_clConst]; exact maxRelProjConst_le_maxProjConst m N

/-- Every `m`-dimensional `Y ⊆ ℓ∞^N` gives a lower bound `λ(Y, ℓ∞^N) ≤ λ_𝕜(m)`.
@isnad1 id=le.1h4v.s9.573f4f941747 from=translated src=- shape=d34cc74f vocab=1533255d
-/
lemma relProjConst_le_maxProjConst' {m N : ℕ} (Y : Submodule 𝕜 (Fin N → 𝕜))
    (hY : Module.finrank 𝕜 Y = m) : relProjConst Y ≤ maxProjConst 𝕜 m :=
  relProjConst_le_maxProjConst (maxRelProjConst_le_sqrt' m) Y hY

/-- Every configuration `(t, P)` gives a lower bound for `λ_𝕜(m)`.
@isnad1 id=le.2h5v.s6.cd757e3f9fad from=translated src=- shape=3e03d63a vocab=3569dbf4
-/
lemma weightedAbsSum_le_maxProjConst {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ι → ℝ} (ht : IsUnitWeight t) {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    weightedAbsSum t P ≤ maxProjConst 𝕜 m := by
  -- relabel `ι` as `Fin N`
  let e := (Fintype.equivFin ι).symm
  have hP' := submatrix_mem_orthProjs e hP
  have ht' : IsUnitWeight (t ∘ e) :=
    ⟨fun i => ht.nonneg _, by rw [← ht.sum_sq]; exact e.sum_comp (fun i => t i ^ 2)⟩
  have h1 : weightedAbsSum (t ∘ e) (P.submatrix e e) = weightedAbsSum t P := by
    simp only [weightedAbsSum, Function.comp_apply, Matrix.submatrix_apply]
    rw [e.sum_comp (fun i => ∑ j, t i * t (e j) * ‖P i (e j)‖)]
    exact Finset.sum_congr rfl fun i _ => e.sum_comp (fun j => t i * t j * ‖P i j‖)
  rw [← h1]
  exact (le_clConst ht' hP').trans (clConst_le_maxProjConst m _)

/-- `μ(m, ι) ≤ λ(m)`.
@isnad1 id=le.0h3v.s4.aa76f9b868e9 from=translated src=- shape=98416d19 vocab=76007816
-/
lemma quasiRelConst_le_maxProjConst {m : ℕ} (N : ℕ) :
    quasiRelConst 𝕜 (Fin N) m ≤ maxProjConst 𝕜 m :=
  (quasiRelConst_le_maxRelProjConst m N).trans (maxRelProjConst_le_maxProjConst m N)

/-- `μ(m) ≤ λ(m)`.
@isnad1 id=le.0h2v.s4.03b133352fdd from=translated src=- shape=f3496c54 vocab=e80bddef
-/
lemma quasiMaxConst_le_maxProjConst (m : ℕ) : quasiMaxConst 𝕜 m ≤ maxProjConst 𝕜 m :=
  quasiMaxConst_le (maxProjConst_nonneg m) fun N => quasiRelConst_le_maxProjConst N

end Type0

end ProjectionConstants
