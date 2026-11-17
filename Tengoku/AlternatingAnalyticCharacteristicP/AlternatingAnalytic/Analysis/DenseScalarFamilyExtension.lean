import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.DenseMultilinearFamilyExtension
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.DenseScalarRestriction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dense inputs and dense scalar extension for multilinear families

Let `K` be dense in `L`. A bounded `K`-multilinear map on dense `K`-subspaces of
`L`-spaces `H i`, with values in a complete space `Z`, extends uniquely to a bounded
`L`-multilinear map on `∏ i, H i` with the same norm. This is the completion
principle stated in Appendix H before Lemma H.5. Only `Z` needs to be complete.
-/

noncomputable section

namespace AlternatingAnalytic

variable {K L : Type*} [NontriviallyNormedField K] [NontriviallyNormedField L]
  [NormedAlgebra K L]
  {I : Type*} {H : I → Type*} {Z : Type*}
  [∀ i, NormedAddCommGroup (H i)]
  [∀ i, NormedSpace K (H i)] [∀ i, NormedSpace L (H i)]
  [∀ i, IsScalarTower K L (H i)]
  [NormedAddCommGroup Z] [NormedSpace K Z] [NormedSpace L Z]
  [IsScalarTower K L Z]

/-- A continuous `K`-multilinear map between `L`-spaces is `L`-multilinear when `K` is
dense in `L`.-/
def denseScalarMultilinearFamilyExtension (hKL : DenseRange (algebraMap K L))
    (f : ContinuousMultilinearMap K H Z) : ContinuousMultilinearMap L H Z where
  toFun := f
  map_update_add' := f.map_update_add
  map_update_smul' m i c x :=
    map_smul_of_dense_algebraMap hKL (f.toContinuousLinearMap m i) c x
  cont := f.cont

/--
@isnad1 id=eq.1h7v.s10.113cd4cb953d from=translated src=- shape=2dfe1a40 vocab=2cde73cf
-/
@[simp]
theorem denseScalarMultilinearFamilyExtension_apply
    (hKL : DenseRange (algebraMap K L)) (f : ContinuousMultilinearMap K H Z)
    (x : ∀ i, H i) : denseScalarMultilinearFamilyExtension hKL f x = f x := rfl

/--
@isnad1 id=eq.1h6v.s10.d1a2ecc5e24f from=translated src=- shape=86e21146 vocab=60c323ab
-/
@[simp]
theorem restrict_denseScalarMultilinearFamilyExtension
    (hKL : DenseRange (algebraMap K L)) (f : ContinuousMultilinearMap K H Z) :
    (denseScalarMultilinearFamilyExtension hKL f).restrictScalars K = f := by
  ext x
  rfl

variable [Fintype I]

/--
@isnad1 id=eq.1h6v.s10.fb14de20c6f2 from=translated src=- shape=0592333f vocab=b6776c7d
-/
@[simp]
theorem norm_denseScalarMultilinearFamilyExtension
    (hKL : DenseRange (algebraMap K L)) (f : ContinuousMultilinearMap K H Z) :
    ‖denseScalarMultilinearFamilyExtension hKL f‖ = ‖f‖ := by
  rw [← ContinuousMultilinearMap.norm_restrictScalars (𝕜' := K),
    restrict_denseScalarMultilinearFamilyExtension]

section DenseInputs

variable {E : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]
  [CompleteSpace Z]

/-- The extension along the dense isometries `j i`, as an `L`-multilinear map.-/
def denseScalarFamilyExtension (hKL : DenseRange (algebraMap K L))
    (j : ∀ i, E i →ₗᵢ[K] H i) (hj : ∀ i, DenseRange (j i))
    (P : ContinuousMultilinearMap K E Z) : ContinuousMultilinearMap L H Z :=
  denseScalarMultilinearFamilyExtension hKL (denseMultilinearFamilyExtension j hj P)

/--
@isnad1 id=eq.2h9v.s10.a0d972ec6095 from=translated src=- shape=ebd5ae43 vocab=02b2e449
-/
@[simp]
theorem denseScalarFamilyExtension_apply (hKL : DenseRange (algebraMap K L))
    (j : ∀ i, E i →ₗᵢ[K] H i) (hj : ∀ i, DenseRange (j i))
    (P : ContinuousMultilinearMap K E Z) (x : ∀ i, E i) :
    denseScalarFamilyExtension hKL j hj P (fun i => j i (x i)) = P x :=
  denseMultilinearFamilyExtension_apply j hj P x

/--
@isnad1 id=eq.2h8v.s11.940dff561ac4 from=translated src=- shape=56b736f0 vocab=0a69b1e7
-/
@[simp]
theorem restrict_denseScalarFamilyExtension (hKL : DenseRange (algebraMap K L))
    (j : ∀ i, E i →ₗᵢ[K] H i) (hj : ∀ i, DenseRange (j i))
    (P : ContinuousMultilinearMap K E Z) :
    (denseScalarFamilyExtension hKL j hj P).restrictScalars K =
      denseMultilinearFamilyExtension j hj P :=
  restrict_denseScalarMultilinearFamilyExtension hKL _

/--
@isnad1 id=eq.2h8v.s10.8d4e953ca738 from=translated src=- shape=27848fc4 vocab=4d2ce072
-/
@[simp]
theorem norm_denseScalarFamilyExtension (hKL : DenseRange (algebraMap K L))
    (j : ∀ i, E i →ₗᵢ[K] H i) (hj : ∀ i, DenseRange (j i))
    (P : ContinuousMultilinearMap K E Z) :
    ‖denseScalarFamilyExtension hKL j hj P‖ = ‖P‖ := by
  rw [denseScalarFamilyExtension, norm_denseScalarMultilinearFamilyExtension,
    norm_denseMultilinearFamilyExtension]

/-- Agreement on the original inputs determines the extension among `L`-multilinear maps.
@isnad1 id=eq.3h9v.s11.e3cdbf51af63 from=translated src=- shape=dfc5b343 vocab=02b2e449
-/
theorem denseScalarFamilyExtension_unique (hKL : DenseRange (algebraMap K L))
    (j : ∀ i, E i →ₗᵢ[K] H i) (hj : ∀ i, DenseRange (j i))
    (P : ContinuousMultilinearMap K E Z) (R : ContinuousMultilinearMap L H Z)
    (hR : ∀ x, R (fun i => j i (x i)) = P x) :
    R = denseScalarFamilyExtension hKL j hj P := by
  have h := denseMultilinearFamilyExtension_unique j hj P (R.restrictScalars K) hR
  ext x
  exact congrArg (fun f : ContinuousMultilinearMap K H Z => f x) h

/-- The completion principle: existence and uniqueness of the extension, with the same norm.
@isnad1 id=existsun.2h8v.s12.b4f0dd027392 from=translated src=- shape=974533d5 vocab=b33ee181
-/
theorem existsUnique_denseScalarFamilyExtension (hKL : DenseRange (algebraMap K L))
    (j : ∀ i, E i →ₗᵢ[K] H i) (hj : ∀ i, DenseRange (j i))
    (P : ContinuousMultilinearMap K E Z) :
    ∃! Q : ContinuousMultilinearMap L H Z,
      (∀ x, Q (fun i => j i (x i)) = P x) ∧
      Q.restrictScalars K = denseMultilinearFamilyExtension j hj P ∧ ‖Q‖ = ‖P‖ := by
  refine ⟨denseScalarFamilyExtension hKL j hj P, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact denseScalarFamilyExtension_apply hKL j hj P
  · exact restrict_denseScalarFamilyExtension hKL j hj P
  · exact norm_denseScalarFamilyExtension hKL j hj P
  · intro R hR
    exact denseScalarFamilyExtension_unique hKL j hj P R hR.1

/-- The completion principle for a multilinear map with a bound `C`; the extension
keeps the bound.
@isnad1 id=existsun.4h9v.s12.7ea8f6328adc from=translated src=- shape=fdfa2b8d vocab=ec3757eb
-/
theorem existsUnique_denseScalarFamilyExtension_of_bound
    (hKL : DenseRange (algebraMap K L))
    (j : ∀ i, E i →ₗᵢ[K] H i) (hj : ∀ i, DenseRange (j i))
    (P : MultilinearMap K E Z) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖P x‖ ≤ C * ∏ i, ‖x i‖) :
    ∃! Q : ContinuousMultilinearMap L H Z,
      (∀ x, Q (fun i => j i (x i)) = P x) ∧
      Q.restrictScalars K = denseMultilinearFamilyExtension j hj (P.mkContinuous C hbound) ∧
      ‖Q‖ = ‖P.mkContinuous C hbound‖ ∧ ‖Q‖ ≤ C ∧
      ∀ y, ‖Q y‖ ≤ C * ∏ i, ‖y i‖ := by
  let P₀ := P.mkContinuous C hbound
  let Q := denseScalarFamilyExtension hKL j hj P₀
  have hnorm : ‖Q‖ = ‖P₀‖ := norm_denseScalarFamilyExtension hKL j hj P₀
  have hle : ‖Q‖ ≤ C := hnorm.le.trans (P.mkContinuous_norm_le hC hbound)
  refine ⟨Q, ⟨?_, ?_, hnorm, hle, ?_⟩, ?_⟩
  · exact denseScalarFamilyExtension_apply hKL j hj P₀
  · exact restrict_denseScalarFamilyExtension hKL j hj P₀
  · intro y
    exact (Q.le_opNorm y).trans (mul_le_mul_of_nonneg_right hle (by positivity))
  · intro R hR
    exact denseScalarFamilyExtension_unique hKL j hj P₀ R hR.1

/-- Agreement on the original inputs determines the extension.
@isnad1 id=eq.4h10v.s11.f2c1c13d61b4 from=translated src=- shape=549e713f vocab=3308be44
-/
theorem denseScalarFamilyExtension_mkContinuous_unique
    (hKL : DenseRange (algebraMap K L))
    (j : ∀ i, E i →ₗᵢ[K] H i) (hj : ∀ i, DenseRange (j i))
    (P : MultilinearMap K E Z) {C : ℝ}
    (hbound : ∀ x, ‖P x‖ ≤ C * ∏ i, ‖x i‖)
    (R : ContinuousMultilinearMap L H Z)
    (hR : ∀ x, R (fun i => j i (x i)) = P x) :
    R = denseScalarFamilyExtension hKL j hj (P.mkContinuous C hbound) :=
  denseScalarFamilyExtension_unique hKL j hj (P.mkContinuous C hbound) R hR

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace K W]

/-- For a map into a smaller space `W` included in `Z`, the extension takes values in
`W` on the original inputs.
@isnad1 id=mem.2h11v.s11.87178b3d023a from=translated src=- shape=a9a5eccf vocab=982abb1f
-/
theorem denseScalarFamilyExtension_comp_apply_mem_range
    (hKL : DenseRange (algebraMap K L))
    (j : ∀ i, E i →ₗᵢ[K] H i) (hj : ∀ i, DenseRange (j i))
    (e : W →L[K] Z) (P : ContinuousMultilinearMap K E W) (x : ∀ i, E i) :
    denseScalarFamilyExtension hKL j hj (e.compContinuousMultilinearMap P)
      (fun i => j i (x i)) ∈ Set.range e := by
  rw [denseScalarFamilyExtension_apply]
  exact ⟨P x, rfl⟩

/-- Composing with an isometric inclusion of the codomain does not change the norm.
@isnad1 id=eq.2h10v.s10.32f021edf571 from=translated src=- shape=88412bad vocab=72e5f167
-/
@[simp]
theorem norm_denseScalarFamilyExtension_comp
    (hKL : DenseRange (algebraMap K L))
    (j : ∀ i, E i →ₗᵢ[K] H i) (hj : ∀ i, DenseRange (j i))
    (e : W →ₗᵢ[K] Z) (P : ContinuousMultilinearMap K E W) :
    ‖denseScalarFamilyExtension hKL j hj
      (e.toContinuousLinearMap.compContinuousMultilinearMap P)‖ = ‖P‖ := by
  rw [norm_denseScalarFamilyExtension, e.norm_compContinuousMultilinearMap]

end DenseInputs

section Submodules

variable [CompleteSpace Z]

/-- The completion principle for dense `K`-submodules of the `L`-spaces `H i`.
@isnad1 id=existsun.2h7v.s12.c734484070f8 from=translated src=- shape=f1f871f9 vocab=ecab5587
-/
theorem existsUnique_denseScalarSubmoduleFamilyExtension
    (hKL : DenseRange (algebraMap K L))
    (S : ∀ i, Submodule K (H i)) (hS : ∀ i, Dense (S i : Set (H i)))
    (P : ContinuousMultilinearMap K (fun i => S i) Z) :
    ∃! Q : ContinuousMultilinearMap L H Z,
      (∀ x : ∀ i, S i, Q (fun i => (x i : H i)) = P x) ∧
      ‖Q‖ = ‖P‖ := by
  let j := fun i => (S i).subtypeₗᵢ
  have hj : ∀ i, DenseRange (j i) := fun i => (hS i).denseRange_val
  refine ⟨denseScalarFamilyExtension hKL j hj P, ⟨?_, ?_⟩, ?_⟩
  · exact denseScalarFamilyExtension_apply hKL j hj P
  · exact norm_denseScalarFamilyExtension hKL j hj P
  · intro R hR
    exact denseScalarFamilyExtension_unique hKL j hj P R hR.1

/-- The completion principle of Appendix H, for bounded maps on dense subspaces of
Banach spaces. The completeness of `L` and `H i` matches the paper and is not used.
@isnad1 id=existsun.4h8v.s14.e7fbfb8c6951 from=translated src=- shape=91e4e3ee vocab=0119e6db
-/
theorem existsUnique_denseScalarSubmoduleFamilyExtension_of_bound
    [CompleteSpace L] [∀ i, CompleteSpace (H i)]
    (hKL : DenseRange (algebraMap K L))
    (S : ∀ i, Submodule K (H i)) (hS : ∀ i, Dense (S i : Set (H i)))
    (P : MultilinearMap K (fun i => S i) Z) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖P x‖ ≤ C * ∏ i, ‖x i‖) :
    ∃! Q : ContinuousMultilinearMap L H Z,
      (∀ x : ∀ i, S i, Q (fun i => (x i : H i)) = P x) ∧
      Q.restrictScalars K = denseMultilinearFamilyExtension
        (fun i => (S i).subtypeₗᵢ) (fun i => (hS i).denseRange_val)
        (P.mkContinuous C hbound) ∧
      ‖Q‖ = ‖P.mkContinuous C hbound‖ ∧ ‖Q‖ ≤ C ∧
      ∀ y, ‖Q y‖ ≤ C * ∏ i, ‖y i‖ :=
  existsUnique_denseScalarFamilyExtension_of_bound hKL
    (fun i => (S i).subtypeₗᵢ) (fun i => (hS i).denseRange_val) P hC hbound

end Submodules

end AlternatingAnalytic
