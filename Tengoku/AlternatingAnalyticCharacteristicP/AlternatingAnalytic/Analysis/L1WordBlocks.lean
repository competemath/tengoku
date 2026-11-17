import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.L1Coordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Word blocks in ℓ¹

For words `Words I = Σ n, Fin n → I`, the degree `n` word block is the `n`-linear map
ℓ¹(I, K)ⁿ → ℓ¹(Words I, K) with coordinates `(s⁻¹)^n * ∏ i, x i (a i)` on words of length
`n` and zero elsewhere. These are the multilinear coefficients of the map `g` in the proof
of Theorem 4.5(2). The scalar field need not be complete.
-/

open scoped lp BigOperators

namespace L1Coordinates

abbrev L1 (K I : Type*) [NormedAddCommGroup K] : Type _ := lp (fun _ : I => K) 1
abbrev Words (I : Type*) := Σ n : ℕ, Fin n → I

variable {K I : Type*} [NontriviallyNormedField K]

noncomputable local instance : DecidableEq I := Classical.decEq I
noncomputable local instance : DecidableEq (Words I) := Classical.decEq (Words I)

private theorem word_mk_injective (n : ℕ) :
    Function.Injective (fun a : Fin n → I => (⟨n, a⟩ : Words I)) := by
  intro a b h
  simpa using h

/-- A coordinate of the degree `n` block, as a scalar multilinear map.-/
noncomputable def wordCoordinateMap (n : ℕ) (w : Words I) :
    MultilinearMap K (fun _ : Fin n => L1 K I) K :=
  Function.extend (Sigma.mk n)
    (fun a => coordinateTerm (K := K) (fun _ : Fin n → I => (1 : K)) a) 0 w

/--
@isnad1 id=eq.0h5v.s9.bea4ac4d483c from=translated src=- shape=179c0a67 vocab=995c580e
-/
@[simp]
theorem wordCoordinateMap_same (n : ℕ) (a : Fin n → I)
    (x : Fin n → L1 K I) :
    wordCoordinateMap (K := K) n ⟨n, a⟩ x = ∏ i, x i (a i) := by
  rw [wordCoordinateMap, (word_mk_injective n).extend_apply]
  simp

/--
@isnad1 id=eq.1h4v.s9.84e48b871875 from=translated src=- shape=b839638b vocab=90aa5429
-/
theorem wordCoordinateMap_of_not_mem (n : ℕ) (w : Words I)
    (h : w ∉ Set.range (Sigma.mk n)) :
    wordCoordinateMap (K := K) n w = 0 := by
  exact Function.extend_apply' _ _ _ h

/--
@isnad1 id=eq.1h6v.s8.493bc178974c from=translated src=- shape=447b57c9 vocab=bf315ee8
-/
@[simp]
theorem wordCoordinateMap_ne (n : ℕ) {m : ℕ} (a : Fin m → I)
    (h : m ≠ n) (x : Fin n → L1 K I) :
    wordCoordinateMap (K := K) n ⟨m, a⟩ x = 0 := by
  rw [wordCoordinateMap_of_not_mem]
  · rfl
  · rintro ⟨b, hb⟩
    exact h (congrArg Sigma.fst hb).symm

/-- The coordinate norms of a degree `n` block sum to the product of the input norms.
@isnad1 id=hassum.0h4v.s9.a6b4e34607f3 from=translated src=- shape=0068f8a9 vocab=b6a3228f
-/
theorem hasSum_norm_wordCoordinateMap (n : ℕ) (x : Fin n → L1 K I) :
    HasSum (fun w : Words I => ‖wordCoordinateMap (K := K) n w x‖) (∏ i, ‖x i‖) := by
  apply ((word_mk_injective n).hasSum_iff ?_).mp
  · simpa [Function.comp_def, norm_prod] using hasSum_prod_norm n x
  · intro w hw
    rw [wordCoordinateMap_of_not_mem n w hw]
    simp

/-- The unscaled degree `n` word block.-/
noncomputable def wordBlockMultilinear (n : ℕ) :
    MultilinearMap K (fun _ : Fin n => L1 K I) (L1 K (Words I)) where
  toFun x := ⟨fun w => wordCoordinateMap (K := K) n w x, by
    apply memℓp_gen
    simpa using (hasSum_norm_wordCoordinateMap (K := K) n x).summable⟩
  map_update_add' x i y z := by
    apply Subtype.ext
    funext w
    exact (wordCoordinateMap (K := K) n w).map_update_add x i y z
  map_update_smul' x i t y := by
    apply Subtype.ext
    funext w
    exact (wordCoordinateMap (K := K) n w).map_update_smul x i t y

/--
@isnad1 id=eq.0h4v.s9.c5daf31bfb34 from=translated src=- shape=80c04c9e vocab=9c2e224f
-/
theorem norm_wordBlockMultilinear (n : ℕ) (x : Fin n → L1 K I) :
    ‖wordBlockMultilinear (K := K) n x‖ = ∏ i, ‖x i‖ := by
  exact (hasSum_norm (wordBlockMultilinear (K := K) n x)).unique
    (hasSum_norm_wordCoordinateMap (K := K) n x)

/-- The degree `n` word block with scaling factor `(s⁻¹)^n`.-/
noncomputable def wordBlock (s : K) (n : ℕ) :
    ContinuousMultilinearMap K (fun _ : Fin n => L1 K I) (L1 K (Words I)) :=
  (s⁻¹)^n • (wordBlockMultilinear (K := K) (I := I) n).mkContinuous 1
    (fun x => by simp [norm_wordBlockMultilinear])

/--
@isnad1 id=eq.0h6v.s10.e9fd769bd1f5 from=translated src=- shape=be9d0e34 vocab=a1dd4b75
-/
@[simp]
theorem wordBlock_apply_same (s : K) (n : ℕ) (x : Fin n → L1 K I)
    (a : Fin n → I) :
    wordBlock s n x ⟨n, a⟩ = (s⁻¹)^n * ∏ i, x i (a i) := by
  change (s⁻¹)^n * wordCoordinateMap (K := K) n ⟨n, a⟩ x = _
  rw [wordCoordinateMap_same]

/--
@isnad1 id=eq.1h7v.s10.3543c92efa15 from=translated src=- shape=51f7de86 vocab=447654e7
-/
@[simp]
theorem wordBlock_apply_ne (s : K) (n : ℕ) (x : Fin n → L1 K I)
    {m : ℕ} (a : Fin m → I) (h : m ≠ n) :
    wordBlock s n x ⟨m, a⟩ = 0 := by
  change (s⁻¹)^n * wordCoordinateMap (K := K) n ⟨m, a⟩ x = _
  rw [wordCoordinateMap_ne n a h, mul_zero]

/-- On basis vectors, a word block gives the scaled basis vector of the word.
@isnad1 id=eq.0h5v.s12.d13fda29f47c from=translated src=- shape=03d2340d vocab=9c909896
-/
@[simp]
theorem wordBlock_single (s : K) (n : ℕ) (a : Fin n → I) :
    wordBlock s n (fun i => lp.single 1 (a i) (1 : K)) =
      (s⁻¹)^n • lp.single 1 ⟨n, a⟩ (1 : K) := by
  classical
  apply lp.ext
  funext w
  obtain ⟨m, b⟩ := w
  by_cases hm : m = n
  · subst m
    rw [wordBlock_apply_same]
    by_cases hb : b = a
    · subst b
      simp
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
      have hs : (⟨n, b⟩ : Words I) ≠ ⟨n, a⟩ := by simpa using hb
      change (s⁻¹)^n * (∏ r, (lp.single 1 (a r) (1 : K) : L1 K I) (b r)) =
        (s⁻¹)^n * ((lp.single 1 ⟨n, a⟩ (1 : K) : L1 K (Words I)) ⟨n, b⟩)
      rw [lp.single_apply_ne _ _ _ hs, mul_zero]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (lp.single_apply_ne 1 (a i) 1 hi)]
      simp
  · rw [wordBlock_apply_ne s n _ b hm]
    have hs : (⟨m, b⟩ : Words I) ≠ ⟨n, a⟩ := fun h => hm (congrArg Sigma.fst h)
    change 0 = (s⁻¹)^n * ((lp.single 1 ⟨n, a⟩ (1 : K) : L1 K (Words I)) ⟨m, b⟩)
    rw [lp.single_apply_ne _ _ _ hs, mul_zero]

end L1Coordinates
