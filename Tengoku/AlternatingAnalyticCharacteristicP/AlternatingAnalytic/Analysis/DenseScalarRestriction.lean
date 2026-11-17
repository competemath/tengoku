import Tengoku.Seed.Analysis.Normed.Module.Alternating.Basic
import Tengoku.Seed.Analysis.Normed.Module.Completion
import Tengoku.Seed.Analysis.Normed.Field.Instances

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Restriction along a dense scalar inclusion

Let `K` be dense in `L`. Continuous `K`-linear, multilinear and alternating maps
between `L`-spaces are `L`-linear, with the same functions and norms, so the map
spaces over `K` and over `L` are isometric. This is the map-space part of
Lemma D.11.
-/

namespace AlternatingAnalytic

section DenseScalars

variable {K L E F : Type*} [NontriviallyNormedField K] [NontriviallyNormedField L]
  [NormedAlgebra K L]
  [NormedAddCommGroup E] [NormedSpace K E] [NormedSpace L E] [IsScalarTower K L E]
  [NormedAddCommGroup F] [NormedSpace K F] [NormedSpace L F] [IsScalarTower K L F]

/-- A continuous `K`-linear map is `L`-linear when `K` is dense in `L`.
@isnad1 id=eq.1h7v.s10.29a33cac9afd from=translated src=- shape=c53c09a0 vocab=ddacb87c
-/
theorem map_smul_of_dense_algebraMap (hd : DenseRange (algebraMap K L))
    (f : E →L[K] F) (c : L) (x : E) : f (c • x) = c • f x := by
  have h : (fun a : L => f (a • x)) = fun a : L => a • f x := by
    apply hd.equalizer (f.continuous.comp (continuous_id.smul continuous_const))
      (continuous_id.smul continuous_const)
    funext a
    change f ((algebraMap K L a) • x) = (algebraMap K L a) • f x
    simpa only [algebraMap_smul] using f.map_smul a x
  exact congrFun h c

/-- A continuous `K`-linear map viewed as an `L`-linear map.-/
def denseScalarLinearExtension (hd : DenseRange (algebraMap K L))
    (f : E →L[K] F) : E →L[L] F where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_smul_of_dense_algebraMap hd f
  cont := f.continuous

/--
@isnad1 id=eq.1h6v.s10.3f93cab6647c from=translated src=- shape=9ced2620 vocab=8e1961fa
-/
@[simp]
theorem denseScalarLinearExtension_apply (hd : DenseRange (algebraMap K L))
    (f : E →L[K] F) (x : E) : denseScalarLinearExtension hd f x = f x := rfl

/--
@isnad1 id=eq.1h5v.s9.179a4f3c1a9a from=translated src=- shape=7bcfc133 vocab=ebb00263
-/
@[simp]
theorem restrict_denseScalarLinearExtension (hd : DenseRange (algebraMap K L))
    (f : E →L[K] F) : (denseScalarLinearExtension hd f).restrictScalars K = f := by
  ext x
  rfl

/--
@isnad1 id=eq.1h5v.s9.a73f936ec7cd from=translated src=- shape=886f2f76 vocab=0d112691
-/
@[simp]
theorem norm_denseScalarLinearExtension (hd : DenseRange (algebraMap K L))
    (f : E →L[K] F) : ‖denseScalarLinearExtension hd f‖ = ‖f‖ := by
  rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := K),
    restrict_denseScalarLinearExtension]

/-- The spaces of continuous linear maps over `K` and over `L` are isometric; the
inverse is restriction of scalars.-/
def denseScalarLinearEquiv (hd : DenseRange (algebraMap K L)) :
    (E →L[K] F) ≃ₗᵢ[L] (E →L[L] F) where
  toFun := denseScalarLinearExtension hd
  invFun := ContinuousLinearMap.restrictScalars K
  left_inv := restrict_denseScalarLinearExtension hd
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl
  norm_map' := norm_denseScalarLinearExtension hd

/--
@isnad1 id=eq.1h6v.s11.196f6b352e3c from=translated src=- shape=01196cef vocab=47b67a9c
-/
@[simp]
theorem denseScalarLinearEquiv_apply (hd : DenseRange (algebraMap K L))
    (f : E →L[K] F) (x : E) : denseScalarLinearEquiv hd f x = f x := rfl

/--
@isnad1 id=eq.1h5v.s11.bbb7bea67abf from=translated src=- shape=21ba5d26 vocab=3831b300
-/
@[simp]
theorem denseScalarLinearEquiv_symm_apply (hd : DenseRange (algebraMap K L))
    (f : E →L[L] F) : (denseScalarLinearEquiv hd).symm f = f.restrictScalars K := rfl

variable {n : ℕ}

/-- A continuous `K`-multilinear map viewed as an `L`-multilinear map.-/
def denseScalarMultilinearExtension (hd : DenseRange (algebraMap K L))
    (f : E [×n]→L[K] F) : E [×n]→L[L] F where
  toFun := f
  map_update_add' := f.map_update_add
  map_update_smul' x i c y := map_smul_of_dense_algebraMap hd (f.toContinuousLinearMap x i) c y
  cont := f.cont

/--
@isnad1 id=eq.1h7v.s10.24a9f2a1f3dd from=translated src=- shape=9a86870c vocab=8a29ed2d
-/
@[simp]
theorem denseScalarMultilinearExtension_apply (hd : DenseRange (algebraMap K L))
    (f : E [×n]→L[K] F) (x : Fin n → E) : denseScalarMultilinearExtension hd f x = f x := rfl

/--
@isnad1 id=eq.1h6v.s9.52ea06ef7e30 from=translated src=- shape=8bf57252 vocab=356e3365
-/
@[simp]
theorem restrict_denseScalarMultilinearExtension (hd : DenseRange (algebraMap K L))
    (f : E [×n]→L[K] F) : (denseScalarMultilinearExtension hd f).restrictScalars K = f := by
  ext x
  rfl

/--
@isnad1 id=eq.1h6v.s9.15b837ec88c3 from=translated src=- shape=5378bbb9 vocab=c6b7804a
-/
@[simp]
theorem norm_denseScalarMultilinearExtension (hd : DenseRange (algebraMap K L))
    (f : E [×n]→L[K] F) : ‖denseScalarMultilinearExtension hd f‖ = ‖f‖ := rfl

/-- The spaces of continuous multilinear maps over `K` and over `L` are isometric.-/
def denseScalarMultilinearEquiv (hd : DenseRange (algebraMap K L)) :
    (E [×n]→L[K] F) ≃ₗᵢ[L] (E [×n]→L[L] F) where
  toFun := denseScalarMultilinearExtension hd
  invFun := ContinuousMultilinearMap.restrictScalars K
  left_inv := restrict_denseScalarMultilinearExtension hd
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl
  norm_map' := norm_denseScalarMultilinearExtension hd

/--
@isnad1 id=eq.1h7v.s11.9a20f3111938 from=translated src=- shape=f4ee019a vocab=29492131
-/
@[simp]
theorem denseScalarMultilinearEquiv_apply (hd : DenseRange (algebraMap K L))
    (f : E [×n]→L[K] F) (x : Fin n → E) :
    denseScalarMultilinearEquiv (E := E) (F := F) (n := n) hd f x = f x := rfl

/--
@isnad1 id=eq.1h6v.s11.0521840c1f3a from=translated src=- shape=c4834d9e vocab=89ecf6de
-/
@[simp]
theorem denseScalarMultilinearEquiv_symm_apply (hd : DenseRange (algebraMap K L))
    (f : E [×n]→L[L] F) :
    (denseScalarMultilinearEquiv (E := E) (F := F) (n := n) hd).symm f =
      f.restrictScalars K := rfl

/-- A continuous `K`-alternating map viewed as an `L`-alternating map.-/
def denseScalarAlternatingExtension (hd : DenseRange (algebraMap K L))
    (f : E [⋀^Fin n]→L[K] F) : E [⋀^Fin n]→L[L] F :=
  ⟨denseScalarMultilinearExtension hd f.toContinuousMultilinearMap,
    fun x _ _ h hij => f.map_eq_zero_of_eq x h hij⟩

/--
@isnad1 id=eq.1h7v.s9.e679f26e4252 from=translated src=- shape=62c2dc4d vocab=a7a24437
-/
@[simp]
theorem denseScalarAlternatingExtension_apply (hd : DenseRange (algebraMap K L))
    (f : E [⋀^Fin n]→L[K] F) (x : Fin n → E) : denseScalarAlternatingExtension hd f x = f x := rfl

/--
@isnad1 id=eq.1h6v.s9.b2b8c30fc239 from=translated src=- shape=81659c6c vocab=25dc76ce
-/
@[simp]
theorem restrict_denseScalarAlternatingExtension (hd : DenseRange (algebraMap K L))
    (f : E [⋀^Fin n]→L[K] F) : (denseScalarAlternatingExtension hd f).restrictScalars K = f := by
  ext x
  rfl

/--
@isnad1 id=eq.1h6v.s9.708d967ce40f from=translated src=- shape=80a1e2aa vocab=020024ab
-/
@[simp]
theorem norm_denseScalarAlternatingExtension (hd : DenseRange (algebraMap K L))
    (f : E [⋀^Fin n]→L[K] F) : ‖denseScalarAlternatingExtension hd f‖ = ‖f‖ := rfl

/-- The spaces of continuous alternating maps over `K` and over `L` are isometric.-/
def denseScalarAlternatingEquiv (hd : DenseRange (algebraMap K L)) :
    (E [⋀^Fin n]→L[K] F) ≃ₗᵢ[L] (E [⋀^Fin n]→L[L] F) where
  toFun := denseScalarAlternatingExtension hd
  invFun := ContinuousAlternatingMap.restrictScalars K
  left_inv := restrict_denseScalarAlternatingExtension hd
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl
  norm_map' := norm_denseScalarAlternatingExtension hd

/--
@isnad1 id=eq.1h7v.s11.08f54049e53a from=translated src=- shape=cf6a4d29 vocab=ba78fa75
-/
@[simp]
theorem denseScalarAlternatingEquiv_apply (hd : DenseRange (algebraMap K L))
    (f : E [⋀^Fin n]→L[K] F) (x : Fin n → E) : denseScalarAlternatingEquiv hd f x = f x := rfl

/--
@isnad1 id=eq.1h6v.s11.d5098d0c8560 from=translated src=- shape=7938fd43 vocab=dd1d74ea
-/
@[simp]
theorem denseScalarAlternatingEquiv_symm_apply (hd : DenseRange (algebraMap K L))
    (f : E [⋀^Fin n]→L[L] F) : (denseScalarAlternatingEquiv hd).symm f = f.restrictScalars K := rfl

end DenseScalars

section Completion

variable (K : Type*) [NontriviallyNormedField K]

/-- The completion of `K` is a nontrivially normed field.-/
noncomputable instance completionNontriviallyNormedField :
    NontriviallyNormedField (UniformSpace.Completion K) where
  __ : NormedField (UniformSpace.Completion K) := inferInstance
  non_trivial := by
    obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
    exact ⟨(x : UniformSpace.Completion K), by simpa using hx⟩

/-- The algebra map to the completion of `K` has dense range.
@isnad1 id=denseran.0h1v.s8.e9625b575172 from=translated src=- shape=f8f0cf54 vocab=236ae834
-/
theorem denseRange_algebraMap_completion :
    DenseRange (algebraMap K (UniformSpace.Completion K)) := by
  change DenseRange (fun x : K => (x : UniformSpace.Completion K))
  exact UniformSpace.Completion.denseRange_coe

/-- The same algebra map is isometric.
@isnad1 id=isometry.0h1v.s8.eefbe92fc07b from=translated src=- shape=1c78c667 vocab=93704351
-/
theorem isometry_algebraMap_completion :
    Isometry (algebraMap K (UniformSpace.Completion K)) :=
  algebraMap_isometry K (UniformSpace.Completion K)

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace K E] [NormedSpace (UniformSpace.Completion K) E]
  [IsScalarTower K (UniformSpace.Completion K) E]
  [NormedAddCommGroup F] [NormedSpace K F] [NormedSpace (UniformSpace.Completion K) F]
  [IsScalarTower K (UniformSpace.Completion K) F]

/-- The identification of linear map spaces, for the completion of `K`.-/
noncomputable def completionScalarLinearEquiv :
    (E →L[K] F) ≃ₗᵢ[UniformSpace.Completion K] (E →L[UniformSpace.Completion K] F) :=
  denseScalarLinearEquiv (denseRange_algebraMap_completion K)

/-- The identification of multilinear map spaces, for the completion of `K`.-/
noncomputable def completionScalarMultilinearEquiv (n : ℕ) :
    (E [×n]→L[K] F) ≃ₗᵢ[UniformSpace.Completion K] (E [×n]→L[UniformSpace.Completion K] F) :=
  denseScalarMultilinearEquiv (denseRange_algebraMap_completion K)

/-- The identification of alternating map spaces, for the completion of `K`.-/
noncomputable def completionScalarAlternatingEquiv (n : ℕ) :
    (E [⋀^Fin n]→L[K] F) ≃ₗᵢ[UniformSpace.Completion K]
      (E [⋀^Fin n]→L[UniformSpace.Completion K] F) :=
  denseScalarAlternatingEquiv (denseRange_algebraMap_completion K)

end Completion

end AlternatingAnalytic
