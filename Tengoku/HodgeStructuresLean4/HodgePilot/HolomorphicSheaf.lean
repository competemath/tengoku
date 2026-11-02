import Tengoku.Seed.Geometry.Manifold.Sheaf.Smooth
import Tengoku.Seed.Geometry.Manifold.ContMDiff.NormedSpace
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Analysis.Complex.HasPrimitives
import Tengoku.Seed.Analysis.Calculus.DifferentialForm.Basic
import Tengoku.Seed.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Tengoku.Seed.Analysis.Calculus.FDeriv.Analytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The sheaf of holomorphic functions, holomorphic forms, and the one-variable
# holomorphic Poincaré lemma

Stage 1 of the Wall-1 Poincaré campaign (design memo:
`wall1_poincare_design_memo.md`).  Three layers, each grown from a compiled
probe:

**Layer 1 — `O_an`.**  `holomorphicSheaf n` is the sheaf of holomorphic
(ℂ-analytic) functions on `ℂⁿ`, obtained by instantiating Mathlib's
smoothness-generic `LocalInvariantProp` structure-sheaf machinery at
analyticity `ω` — no upstream refactor is needed, because
`contDiffWithinAt_localInvariantProp`, `ContMDiffMap.commRing` and
`instFieldContMDiffRing` are all generic in the smoothness exponent.
`holomorphicSheafOfChartedSpace` is the same one-liner on an arbitrary
charted space (the future `X(ℂ)_an`).  Sections over `U` are
*definitionally* the bundled `C^ω` maps `U → ℂ` and carry a commutative
ring structure; the dictionary with `AnalyticAt`/`AnalyticOnNhd` is proved
in both directions (`analyticAt_sectionExtend`, `sectionOfAnalyticOnNhd`),
the ℂ-constants embed as a ring homomorphism compatible with restriction
(`constRingHom` — the augmentation of the future de Rham complex), and
`holomorphicSheafCommRing` packages everything as a sheaf of commutative
rings.  Stalk evaluation is provided by `holomorphicSheafEval`.

**Layer 2 — the differential of `Ω^p_an`.**  Holomorphic `p`-forms on opens
of `ℂⁿ` are carried by the pin's normed-space differential-forms layer
(`extDeriv` on `E → E [⋀^Fin p]→L[ℂ] ℂ`, which over `ℂ` *is* the
holomorphic exterior derivative): `AnalyticOnNhd.extDeriv_analytic` shows
`d` preserves analyticity in any dimension and degree, and
`extDeriv_extDeriv_of_analytic` is `d ∘ d = 0` on analytic forms.

**Layer 3 — the holomorphic Poincaré lemma in one variable, degree one.**
`exists_primitive_form`: every analytic 1-form on a disc in `ℂ` is the
exterior derivative of a holomorphic 0-form, via the pin's Morera-based
full-disc primitives (`DifferentiableOn.isExactOn_ball`).

Everything here is one complex variable or dimension-generic *calculus*;
no several-complex-variables claim is made anywhere.  Exactness in degrees
≥ 1 for `n ≥ 2` variables (the SCV wall, memo §4.4) is out of scope.
-/

noncomputable section

open TopologicalSpace Opposite

namespace HodgePilot

/-! ## Layer 1: the sheaf of holomorphic functions on `ℂⁿ` -/

section SheafOfHolomorphic

open Manifold
open scoped ContDiff

/-- The sheaf of holomorphic (ℂ-analytic) functions on `ℂⁿ`, as a sheaf of types:
Mathlib's `LocalInvariantProp` sheaf machinery instantiated at smoothness `ω`.
No upstream change needed: `contDiffWithinAt_localInvariantProp` is generic in
the smoothness exponent.-/
def holomorphicSheaf (n : ℕ) : TopCat.Sheaf (Type) (TopCat.of (Fin n → ℂ)) :=
  (contDiffWithinAt_localInvariantProp (I := 𝓘(ℂ, Fin n → ℂ)) (I' := 𝓘(ℂ)) ω).sheaf
    (Fin n → ℂ) ℂ

/-- The sheaf of `C^ω` functions on an arbitrary charted space over a complex
model (e.g. a future `X(ℂ)_an`): the same machinery, with no manifold or
groupoid hypothesis.-/
def holomorphicSheafOfChartedSpace (H M : Type) [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (I : ModelWithCorners ℂ E H) :
    TopCat.Sheaf (Type) (TopCat.of M) :=
  (contDiffWithinAt_localInvariantProp (I := I) (I' := 𝓘(ℂ)) ω).sheaf M ℂ

/-- Sections of `holomorphicSheaf n` over `U` are *definitionally* the bundled
`C^ω` maps `U → ℂ`.-/
lemma holomorphicSheaf_obj_eq (n : ℕ) (U : (Opens (TopCat.of (Fin n → ℂ)))ᵒᵖ) :
    (holomorphicSheaf n).presheaf.obj U =
      ContMDiffMap 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ) (unop U : Opens (Fin n → ℂ)) ℂ ω := rfl

/-- The commutative ring structure on sections of the holomorphic sheaf: fires
at `ω` with no new instances, since `ContMDiffMap.commRing` is generic in the
smoothness exponent and `instFieldContMDiffRing` provides `ContMDiffRing 𝓘(ℂ) ω ℂ`.-/
instance holomorphicSheaf.instCommRingSections (n : ℕ)
    (U : (Opens (TopCat.of (Fin n → ℂ)))ᵒᵖ) :
    CommRing ((holomorphicSheaf n).presheaf.obj U) :=
  inferInstanceAs <| CommRing
    (ContMDiffMap 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ) (unop U : Opens (Fin n → ℂ)) ℂ ω)

/-- Sections of the holomorphic sheaf coerce to functions.-/
instance holomorphicSheaf.coeFun (n : ℕ) (U : (Opens (TopCat.of (Fin n → ℂ)))ᵒᵖ) :
    CoeFun ((holomorphicSheaf n).presheaf.obj U) (fun _ => ↑(unop U) → ℂ) where
  coe a := a.1

/-- The dictionary on the model space: a global `C^ω` function `ℂⁿ → ℂ` is
exactly an everywhere-analytic function.-/
theorem contMDiff_omega_iff_analyticOnNhd (n : ℕ) (f : (Fin n → ℂ) → ℂ) :
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ) ω f ↔ AnalyticOnNhd ℂ f Set.univ := by
  rw [contMDiff_iff_contDiff, contDiff_omega_iff_analyticOnNhd]

variable {n : ℕ}

/-- The underlying function of a section of the holomorphic sheaf is `C^ω`.-/
lemma holomorphicSheaf.contMDiff_section {U : (Opens (TopCat.of (Fin n → ℂ)))ᵒᵖ}
    (f : (holomorphicSheaf n).presheaf.obj U) :
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ) ω f.1 :=
  f.2

/-! ### The `AnalyticOnNhd` dictionary on opens

A section of `holomorphicSheaf n` over `U` is a bundled `C^ω` function on the
*subtype* `↥U`.  The two lemmas below translate this into the unbundled
`AnalyticAt`/`AnalyticOnNhd` language of the forms layer: a section, extended
by junk, is analytic at every point of `U`; conversely an analytic function
restricts to a section. -/

open Classical in
/-- A section of the holomorphic sheaf over `U`, extended by junk (`0`) to a
globally defined function on `ℂⁿ`.-/
def sectionExtend {U : Opens (Fin n → ℂ)}
    (f : (holomorphicSheaf n).presheaf.obj (op U)) : (Fin n → ℂ) → ℂ :=
  fun y => if h : y ∈ U then f.1 ⟨y, h⟩ else 0

@[simp] lemma sectionExtend_apply_of_mem {U : Opens (Fin n → ℂ)}
    (f : (holomorphicSheaf n).presheaf.obj (op U)) {y : Fin n → ℂ} (hy : y ∈ U) :
    sectionExtend f y = f.1 ⟨y, hy⟩ :=
  dite_eq_left hy

/-- **Sections are analytic**: a section of the holomorphic sheaf over `U`,
extended by junk, is analytic at every point of `U`.  (The junk extension is
invisible to `AnalyticAt` since `U` is open.)-/
theorem analyticOnNhd_sectionExtend {U : Opens (Fin n → ℂ)}
    (f : (holomorphicSheaf n).presheaf.obj (op U)) :
    AnalyticOnNhd ℂ (sectionExtend f) (U : Set (Fin n → ℂ)) := by
  intro y hy
  have hf : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ) ω f.1 := f.2
  have h1 : (fun z : ↥U => sectionExtend f ↑z) = f.1 :=
    funext fun z => dite_eq_left z.2
  have h2 : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ) ω
      (fun z : ↥U => sectionExtend f ↑z) ⟨y, hy⟩ := by
    rw [h1]; exact hf ⟨y, hy⟩
  have h3 : ContDiffAt ℂ ω (sectionExtend f) y :=
    contMDiffAt_iff_contDiffAt.mp (contMDiffAt_subtype_iff.mp h2)
  exact analyticWithinAt_univ.mp (contDiffWithinAt_omega_iff_analyticWithinAt.mp h3)

/-- **Analytic functions restrict to sections**: the restriction to `U` of a
function analytic at every point of `U` is a section of the holomorphic
sheaf.-/
def sectionOfAnalyticOnNhd {U : Opens (Fin n → ℂ)} {g : (Fin n → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g (U : Set (Fin n → ℂ))) :
    (holomorphicSheaf n).presheaf.obj (op U) :=
  ⟨fun y => g ↑y, fun y =>
    contMDiffAt_subtype_iff.mpr ((hg ↑y y.2).contDiffAt.contMDiffAt)⟩

@[simp] lemma sectionOfAnalyticOnNhd_apply {U : Opens (Fin n → ℂ)}
    {g : (Fin n → ℂ) → ℂ} (hg : AnalyticOnNhd ℂ g (U : Set (Fin n → ℂ)))
    (y : ↥U) :
    (sectionOfAnalyticOnNhd hg).1 y = g ↑y := rfl

/-- Round trip: extending the section obtained from an analytic function
recovers the function on `U`.-/
lemma sectionExtend_sectionOfAnalyticOnNhd {U : Opens (Fin n → ℂ)}
    {g : (Fin n → ℂ) → ℂ} (hg : AnalyticOnNhd ℂ g (U : Set (Fin n → ℂ)))
    {y : Fin n → ℂ} (hy : y ∈ U) :
    sectionExtend (sectionOfAnalyticOnNhd hg) y = g y :=
  dite_eq_left hy

/-! ### The constants: the augmentation `ℂ → O_an` -/

/-- The constant function `c` as a section of the holomorphic sheaf.-/
def constSection (n : ℕ) (U : (Opens (TopCat.of (Fin n → ℂ)))ᵒᵖ) (c : ℂ) :
    (holomorphicSheaf n).presheaf.obj U :=
  ⟨fun _ => c, contMDiff_const⟩

/-- The ℂ-constants map into the holomorphic sheaf as a ring homomorphism —
the augmentation of the (future) holomorphic de Rham complex.-/
def constRingHom (n : ℕ) (U : (Opens (TopCat.of (Fin n → ℂ)))ᵒᵖ) :
    ℂ →+* (holomorphicSheaf n).presheaf.obj U where
  toFun := constSection n U
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Constant sections are compatible with restriction: the augmentation is a
morphism of presheaves.-/
@[simp] lemma map_constSection {U V : (Opens (TopCat.of (Fin n → ℂ)))ᵒᵖ}
    (i : U ⟶ V) (c : ℂ) :
    (holomorphicSheaf n).presheaf.map i (constSection n U c) = constSection n V c :=
  rfl

/-! ### `O_an` as a sheaf of commutative rings -/

/-- The presheaf of holomorphic functions on `ℂⁿ` as a presheaf of commutative
rings.  (The `ω`-instantiation of `smoothPresheafCommRing`.)-/
def holomorphicPresheafCommRing (n : ℕ) :
    TopCat.Presheaf CommRingCat (TopCat.of (Fin n → ℂ)) where
  obj U := CommRingCat.of ((holomorphicSheaf n).presheaf.obj U)
  map h := CommRingCat.ofHom <|
    ContMDiffMap.restrictRingHom 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ) ℂ <| CategoryTheory.leOfHom h.unop
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `O_an` on `ℂⁿ`: the sheaf of holomorphic functions as a sheaf of commutative
rings.  (The `ω`-instantiation of `smoothSheafCommRing`.)-/
def holomorphicSheafCommRing (n : ℕ) :
    TopCat.Sheaf CommRingCat (TopCat.of (Fin n → ℂ)) where
  obj := holomorphicPresheafCommRing n
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (holomorphicSheaf n).property

/-! ### Stalk evaluation -/

/-- Stalk evaluation: the canonical map from the stalk of the holomorphic sheaf
at `x` onto `ℂ`, given by evaluating germs at `x`.-/
def holomorphicSheafEval (n : ℕ) (x : TopCat.of (Fin n → ℂ)) :
    (holomorphicSheaf n).presheaf.stalk x → ℂ :=
  TopCat.stalkToFiber
    (StructureGroupoid.LocalInvariantProp.localPredicate (Fin n → ℂ) ℂ _) x

@[simp] lemma holomorphicSheafEval_germ (U : Opens (TopCat.of (Fin n → ℂ)))
    (x : TopCat.of (Fin n → ℂ)) (hx : x ∈ U)
    (f : (holomorphicSheaf n).presheaf.obj (op U)) :
    holomorphicSheafEval n x ((holomorphicSheaf n).presheaf.germ U x hx f) =
      f.1 ⟨x, hx⟩ :=
  TopCat.stalkToFiber_germ _ U x hx f

/-- Stalk evaluation is surjective.-/
lemma holomorphicSheafEval_surjective (n : ℕ) (x : TopCat.of (Fin n → ℂ)) :
    Function.Surjective (holomorphicSheafEval n x) := by
  apply TopCat.stalkToFiber_surjective
  intro z
  exact ⟨⊤, fun _ => z, contMDiff_const, rfl⟩

end SheafOfHolomorphic

/-! ## Layer 2: the differential of the holomorphic de Rham complex -/

section Forms

open ContinuousAlternatingMap

variable {n p : ℕ}

/-- `d` preserves analyticity: the exterior derivative of an analytic `p`-form on
an open set in `ℂⁿ` is an analytic `(p+1)`-form.  (Any dimension, any degree.)-/
theorem AnalyticOnNhd.extDeriv_analytic {s : Set (Fin n → ℂ)} (hs : IsOpen s)
    {ω : (Fin n → ℂ) → ((Fin n → ℂ) [⋀^Fin p]→L[ℂ] ℂ)}
    (hω : AnalyticOnNhd ℂ ω s) :
    AnalyticOnNhd ℂ (extDeriv ω) s := by
  intro x hx
  have h1 : AnalyticAt ℂ (fderiv ℂ ω) x := hω.fderiv_of_isOpen hs x hx
  exact ((alternatizeUncurryFinCLM ℂ (Fin n → ℂ) ℂ).analyticAt _).comp h1

/-- `d ∘ d = 0` on analytic forms (pointwise).-/
theorem extDeriv_extDeriv_of_analytic
    {ω : (Fin n → ℂ) → ((Fin n → ℂ) [⋀^Fin p]→L[ℂ] ℂ)} {x : Fin n → ℂ}
    (hω : AnalyticAt ℂ ω x) :
    extDeriv (extDeriv ω) x = 0 :=
  extDeriv_extDeriv_apply hω.contDiffAt le_top

end Forms

/-! ## Layer 3: the holomorphic Poincaré lemma in one variable, degree one -/

section PoincareOneVar

open Complex Metric ContinuousAlternatingMap

variable {c : ℂ} {r : ℝ}

/-- The coefficient of a 1-form on ℂ: `coeff1 ω z = ω z (1)`.-/
def coeff1 (ω : ℂ → (ℂ [⋀^Fin 1]→L[ℂ] ℂ)) (z : ℂ) : ℂ :=
  ω z (fun _ => 1)

/-- Reconstruction: a `Fin 1`-alternating map on ℂ is determined by its value
at the single basis vector.-/
lemma alt_fin1_eq (φ : ℂ [⋀^Fin 1]→L[ℂ] ℂ) (v : Fin 1 → ℂ) :
    φ v = v 0 * φ (fun _ => 1) := by
  have h : v = fun i => v i • (fun _ : Fin 1 => (1 : ℂ)) i := by
    funext i; simp
  rw [h, φ.map_smul_univ]
  simp [smul_eq_mul]

/-- **Holomorphic Poincaré lemma on a disc, one variable, degree one.**
Every analytic 1-form on a disc in ℂ is the exterior derivative of a
holomorphic 0-form.-/
theorem exists_primitive_form (ω : ℂ → (ℂ [⋀^Fin 1]→L[ℂ] ℂ))
    (hω : AnalyticOnNhd ℂ ω (ball c r)) :
    ∃ G : ℂ → ℂ, ∀ z ∈ ball c r,
      extDeriv (fun x => constOfIsEmpty ℂ ℂ (Fin 0) (G x)) z = ω z := by
  -- the coefficient function is holomorphic on the disc
  have hωd : DifferentiableOn ℂ ω (ball c r) := fun z hz =>
    (hω z hz).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℂ (coeff1 ω) (ball c r) :=
    hωd.continuousAlternatingMap_apply (fun _ => differentiableOn_const 1)
  -- the pin's Morera-based primitive on the disc
  obtain ⟨G, hG⟩ := hg.isExactOn_ball
  refine ⟨G, fun z hz => ?_⟩
  have hfd : fderiv ℂ G z =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (coeff1 ω z) :=
    (hG z hz).hasFDerivAt.fderiv
  rw [extDeriv_constOfIsEmpty, hfd]
  ext
  simp [coeff1]

end PoincareOneVar

end HodgePilot
