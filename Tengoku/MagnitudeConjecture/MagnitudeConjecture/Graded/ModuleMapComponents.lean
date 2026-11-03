import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Graded.LinearMapComponents
import Tengoku.Seed.LinearAlgebra.BilinearMap
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Homogeneous components of module maps

Projection of an algebra-linear map to a homogeneous degree is again
algebra-linear. We work with left modules; applying the construction to the
opposite algebra gives the project's right-module convention.
-/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace MagnitudeConjecture.Graded

variable {k A M : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- An internal vector-space grading compatible with the homogeneous algebra
action. Multiplicativity of the algebra grading is not needed for this lemma.-/
structure ModuleGrading (R : VectorGrading k A) extends VectorGrading k M where
  smul_mem : ∀ {i j : ℤ} {a : A} {x : M},
    a ∈ R.component i → x ∈ component j → a • x ∈ component (i + j)

namespace ModuleGrading

variable {R : VectorGrading k A} (G : ModuleGrading (M := M) R)

/-- Multiplication by a homogeneous algebra element shifts the projections.
@isnad1 id=eq.1h9v.s9.78e03db44b11 from=translated src=- shape=796d26b7 vocab=e69fdadd
-/
theorem projection_smul {i : ℤ} {a : A} (ha : a ∈ R.component i)
    (j : ℤ) (x : M) :
    G.projection (i + j) (a • x) = a • G.projection j x := by
  letI := G.internal.chooseDecomposition
  apply DirectSum.Decomposition.inductionOn (ℳ := G.component)
    (motive := fun x ↦ G.projection (i + j) (a • x) = a • G.projection j x)
  · simp
  · intro l x
    by_cases hl : l = j
    · subst l
      rw [G.toVectorGrading.projection_of_mem (G.smul_mem ha x.property),
        G.toVectorGrading.projection_of_mem x.property]
    · rw [G.toVectorGrading.projection_of_mem_ne x.property hl,
        G.toVectorGrading.projection_of_mem_ne (G.smul_mem ha x.property) (by omega)]
      simp
  · intro x y hx hy
    simp only [smul_add, map_add, hx, hy]

variable {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable (H : ModuleGrading (M := N) R) [FiniteDimensional k M]

/--
@isnad1 id=eq.2h13v.s9.63c29c5c99cb from=translated src=- shape=0cbfcc23 vocab=25fe0501
-/
theorem mapPart_smul_homogeneous (d : ℤ) (f : M →ₗ[A] N)
    {i j : ℤ} {a : A} {x : M} (ha : a ∈ R.component i) (hx : x ∈ G.component j) :
    G.toVectorGrading.mapPart H.toVectorGrading d (f.restrictScalars k) (a • x) =
      a • G.toVectorGrading.mapPart H.toVectorGrading d (f.restrictScalars k) x := by
  rw [G.toVectorGrading.mapPart_apply_of_mem H.toVectorGrading d _ (G.smul_mem ha hx),
    G.toVectorGrading.mapPart_apply_of_mem H.toVectorGrading d _ hx]
  change H.projection (i + j + d) (f (a • x)) = a • H.projection (j + d) (f x)
  rw [f.map_smul, show i + j + d = i + (j + d) by omega]
  exact H.projection_smul ha (j + d) (f x)

/-- Every homogeneous component of an algebra-linear map commutes with all
algebra elements, not just homogeneous ones.
@isnad1 id=eq.0h11v.s9.3ea54d8b2c96 from=translated src=- shape=d5c2992f vocab=45a3e1ab
-/
theorem mapPart_smul (d : ℤ) (f : M →ₗ[A] N) (a : A) (x : M) :
    G.toVectorGrading.mapPart H.toVectorGrading d (f.restrictScalars k) (a • x) =
      a • G.toVectorGrading.mapPart H.toVectorGrading d (f.restrictScalars k) x := by
  letI := R.internal.chooseDecomposition
  letI := G.internal.chooseDecomposition
  apply DirectSum.Decomposition.inductionOn (ℳ := R.component)
    (motive := fun a ↦ G.toVectorGrading.mapPart H.toVectorGrading d (f.restrictScalars k) (a • x) =
      a • G.toVectorGrading.mapPart H.toVectorGrading d (f.restrictScalars k) x)
  · simp
  · intro i a
    apply DirectSum.Decomposition.inductionOn (ℳ := G.component)
      (motive := fun x ↦ G.toVectorGrading.mapPart H.toVectorGrading d (f.restrictScalars k) (a.val • x) =
        a.val • G.toVectorGrading.mapPart H.toVectorGrading d (f.restrictScalars k) x)
    · simp
    · intro j x
      exact G.mapPart_smul_homogeneous H d f a.property x.property
    · intro x y hx hy
      simp only [smul_add, map_add, hx, hy]
  · intro a b ha hb
    simp only [add_smul, map_add, ha, hb]

/-- The degree component as an actual algebra-linear map.-/
def homPart (d : ℤ) (f : M →ₗ[A] N) : M →ₗ[A] N where
  toFun := G.toVectorGrading.mapPart H.toVectorGrading d (f.restrictScalars k)
  map_add' := map_add _
  map_smul' := G.mapPart_smul H d f

/--
@isnad1 id=mem.1h11v.s9.d0eda7a40dd7 from=translated src=- shape=91a4d559 vocab=9e1b6e45
-/
theorem homPart_mem (d : ℤ) (f : M →ₗ[A] N)
    {i : ℤ} {x : M} (hx : x ∈ G.component i) :
    G.homPart H d f x ∈ H.component (i + d) :=
  G.toVectorGrading.mapPart_mem H.toVectorGrading d (f.restrictScalars k) hx

/-- A degree-preserving condition stated directly for algebra-linear maps.-/
def Homogeneous (d : ℤ) (f : M →ₗ[A] N) : Prop :=
  ∀ i : ℤ, ∀ x ∈ G.component i, f x ∈ H.component (i + d)

/--
@isnad1 id=homogene.0h9v.s8.d6c81ce0b371 from=translated src=- shape=2ef9a498 vocab=499a3ad8
-/
theorem homPart_homogeneous (d : ℤ) (f : M →ₗ[A] N) :
    G.Homogeneous H d (G.homPart H d f) :=
  fun _ _ hx ↦ G.homPart_mem H d f hx

/--
@isnad1 id=eq.1h9v.s8.5d51f0b89b09 from=translated src=- shape=a194ddaf vocab=499a3ad8
-/
theorem homPart_of_homogeneous {d : ℤ} {f : M →ₗ[A] N}
    (hf : G.Homogeneous H d f) : G.homPart H d f = f := by
  apply LinearMap.ext
  intro x
  letI := G.internal.chooseDecomposition
  apply DirectSum.Decomposition.inductionOn (ℳ := G.component)
    (motive := fun x ↦ G.homPart H d f x = f x)
  · simp
  · intro i x
    change G.toVectorGrading.mapPart H.toVectorGrading d (f.restrictScalars k) x.val = f x.val
    rw [G.toVectorGrading.mapPart_apply_of_mem H.toVectorGrading d _ x.property]
    exact H.toVectorGrading.projection_of_mem (hf i x.val x.property)
  · intro x y hx hy
    simp only [map_add, hx, hy]

/--
@isnad1 id=eq.2h10v.s9.856953e2dda4 from=translated src=- shape=2df44109 vocab=499a3ad8
-/
theorem homPart_of_homogeneous_ne {d e : ℤ} {f : M →ₗ[A] N}
    (hf : G.Homogeneous H d f) (hde : d ≠ e) : G.homPart H e f = 0 := by
  apply LinearMap.ext
  intro x
  letI := G.internal.chooseDecomposition
  apply DirectSum.Decomposition.inductionOn (ℳ := G.component)
    (motive := fun x ↦ G.homPart H e f x = 0)
  · simp
  · intro i x
    change G.toVectorGrading.mapPart H.toVectorGrading e (f.restrictScalars k) x.val = 0
    rw [G.toVectorGrading.mapPart_apply_of_mem H.toVectorGrading e _ x.property]
    exact H.toVectorGrading.projection_of_mem_ne (hf i x.val x.property) (by omega)
  · intro x y hx hy
    simp only [map_add, hx, hy, add_zero]

/--
@isnad1 id=eq.0h8v.s9.80bab576b1ec from=translated src=- shape=5f6a3026 vocab=c4af53f8
-/
theorem sum_homPart [FiniteDimensional k N] (f : M →ₗ[A] N) :
    ∑ d ∈ G.toVectorGrading.mapDegreeSupport H.toVectorGrading, G.homPart H d f = f := by
  apply LinearMap.ext
  intro x
  have hs := LinearMap.congr_fun
    (G.toVectorGrading.sum_mapPart H.toVectorGrading (f.restrictScalars k)) x
  simpa only [LinearMap.sum_apply, homPart, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.restrictScalars_apply] using hs

/--
@isnad1 id=eq.1h9v.s9.4a87b61ef623 from=translated src=- shape=4ec9db1e vocab=911a0064
-/
theorem homPart_eq_zero_outside [FiniteDimensional k N] (d : ℤ) (f : M →ₗ[A] N)
    (hd : d ∉ G.toVectorGrading.mapDegreeSupport H.toVectorGrading) :
    G.homPart H d f = 0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun
    (G.toVectorGrading.mapPart_eq_zero_outside H.toVectorGrading d (f.restrictScalars k) hd) x

/--
@isnad1 id=homogene.0h5v.s7.7429411d81e4 from=translated src=- shape=34ccb4ce vocab=81d22cf5
-/
theorem id_homogeneous : G.Homogeneous G 0 (LinearMap.id : M →ₗ[A] M) := by
  intro i x hx
  simpa using hx

variable {P : Type*} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]

/--
@isnad1 id=homogene.2h13v.s9.d550fd8ca182 from=translated src=- shape=30aff093 vocab=841fc1a6
-/
theorem homogeneous_comp (J : ModuleGrading (M := P) R)
    {d e : ℤ} {f : M →ₗ[A] N} {g : N →ₗ[A] P}
    (hf : G.Homogeneous H d f) (hg : H.Homogeneous J e g) :
    G.Homogeneous J (d + e) (g.comp f) := by
  intro i x hx
  have hh := hg (i + d) (f x) (hf i x hx)
  simpa [add_assoc] using hh

end ModuleGrading

end MagnitudeConjecture.Graded
