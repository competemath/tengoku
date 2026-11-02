/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.AlgebraicGeometry.FunctionField
import Tengoku.Seed.AlgebraicGeometry.IdealSheaf.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brick G2XRAT (part 1): regular loci and denominator ideals of rational functions

On an integral scheme `X`, for a rational function `g ∈ K(X)`:

* `RegOn g W`: `g` is the germ at the generic point of a section over `W`;
  `ratLocus g := sSup {W | RegOn g W}` is the **regular locus** of `g`, and
  `ratSec g ∈ Γ(X, ratLocus g)` is `g` as a section there (glued by the sheaf condition, unique
  because sections of an integral scheme are determined by their generic germs, `sec_ext`).
* `mem_ratLocus_of_algebraMap`: `y ∈ ratLocus g` as soon as `g` comes from the stalk at `y`;
  `mem_ratLocus_inv_of_isUnit`: if the germ of `ratSec g` at `y` is a unit, `g⁻¹` is regular at `y`;
  `ratSec_mul_ratSec_inv`: `ratSec g · ratSec g⁻¹ = 1` on the overlap.
* `denIdeal g U = {a ∈ Γ(X, U) | a g regular on U}` (the **denominator ideal**) and the ideal
  sheaf `denIdealSheaf g` (`denIdeal_map_basicOpen`: compatible with basic-open localisation).

These are the rational-function analogues of G2XFR1's `regLocus`/`ratio` (which need global
numerator and denominator) and feed the graph model of `RatGraphModelT2.lean`.
-/

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Chow.M7.RatGraph

variable {X : Scheme.{u}}

/-! ### The regular locus -/

/-- `g` is regular on `W`: it is the generic germ of a section over `W`.-/
def RegOn [IrreducibleSpace X] (g : X.functionField) (W : X.Opens) : Prop :=
  ∃ c : Γ(X, W), ∀ hη : genericPoint X ∈ W, X.presheaf.germ W (genericPoint X) hη c = g

/-- The regular locus of a rational function.-/
def ratLocus [IrreducibleSpace X] (g : X.functionField) : X.Opens :=
  sSup {W : X.Opens | RegOn g W}

theorem le_ratLocus [IrreducibleSpace X] {g : X.functionField} {W : X.Opens} (h : RegOn g W) :
    W ≤ ratLocus g :=
  le_sSup h

variable [IsIntegral X]

theorem genericPoint_mem_of_mem {W : X.Opens} {x : X} (hx : x ∈ W) : genericPoint X ∈ W :=
  (genericPoint_specializes x).mem_open W.isOpen hx

theorem eq_bot_of_genericPoint_notMem {W : X.Opens} (hη : genericPoint X ∉ W) : W = ⊥ := by
  rw [← Opens.not_nonempty_iff_eq_bot]
  rintro ⟨x, hx⟩
  exact hη (genericPoint_mem_of_mem hx)

theorem subsingleton_sec {W : X.Opens} (hη : genericPoint X ∉ W) : Subsingleton Γ(X, W) := by
  obtain rfl := eq_bot_of_genericPoint_notMem hη
  infer_instance

/-- Sections of an integral scheme are determined by their generic germs.-/
theorem sec_ext {W : X.Opens} {c c' : Γ(X, W)}
    (h : ∀ hη : genericPoint X ∈ W,
      X.presheaf.germ W (genericPoint X) hη c = X.presheaf.germ W (genericPoint X) hη c') :
    c = c' := by
  by_cases hη : genericPoint X ∈ W
  · exact germ_injective_of_isIntegral X _ hη (h hη)
  · haveI := subsingleton_sec hη
    exact Subsingleton.elim _ _

theorem regOn_ratLocus (g : X.functionField) : RegOn g (ratLocus g) := by
  let ι := {W : X.Opens // RegOn g W}
  let U : ι → X.Opens := fun i ↦ i.1
  let sf : ∀ i : ι, Γ(X, U i) := fun i ↦ i.2.choose
  have hsf : ∀ (i : ι) (hη : genericPoint X ∈ U i),
      X.presheaf.germ (U i) (genericPoint X) hη (sf i) = g := fun i ↦ i.2.choose_spec
  have hcover : ratLocus g ≤ iSup U := sSup_le fun W hW ↦ le_iSup U ⟨W, hW⟩
  let iUV : ∀ i : ι, U i ⟶ ratLocus g := fun i ↦ homOfLE (le_ratLocus i.2)
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U sf := by
    intro i j
    apply sec_ext
    intro hη
    change X.presheaf.germ _ _ hη (X.presheaf.map (Opens.infLELeft (U i) (U j)).op (sf i)) =
      X.presheaf.germ _ _ hη (X.presheaf.map (Opens.infLERight (U i) (U j)).op (sf j))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hsf, hsf]
  obtain ⟨ρ, hρ, -⟩ := X.sheaf.existsUnique_gluing' U (ratLocus g) iUV hcover sf hcompat
  refine ⟨ρ, fun hη ↦ ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover hη)
  have hρi : X.presheaf.map (iUV i).op (show Γ(X, ratLocus g) from ρ) = sf i := hρ i
  calc X.presheaf.germ (ratLocus g) (genericPoint X) hη ρ
      = X.presheaf.germ (U i) (genericPoint X) hi
          (X.presheaf.map (iUV i).op (show Γ(X, ratLocus g) from ρ)) :=
        (TopCat.Presheaf.germ_res_apply X.presheaf (iUV i) (genericPoint X) hi ρ).symm
    _ = g := by rw [hρi]; exact hsf i hi

/-- **`g` as a section over its regular locus.**-/
def ratSec (g : X.functionField) : Γ(X, ratLocus g) :=
  (regOn_ratLocus g).choose

theorem germ_ratSec (g : X.functionField) (hη : genericPoint X ∈ ratLocus g) :
    X.presheaf.germ (ratLocus g) (genericPoint X) hη (ratSec g) = g :=
  (regOn_ratLocus g).choose_spec hη

/-- **Stalk criterion**: if `g` comes from the stalk at `y`, then `y ∈ ratLocus g`.-/
theorem mem_ratLocus_of_algebraMap {g : X.functionField} {y : X} (a : X.presheaf.stalk y)
    (ha : algebraMap (X.presheaf.stalk y) X.functionField a = g) : y ∈ ratLocus g := by
  obtain ⟨W, hyW, c, rfl⟩ := X.presheaf.exists_germ_eq a
  refine le_ratLocus (W := W) ⟨c, fun hη ↦ ?_⟩ hyW
  haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
  rw [← ha, Scheme.algebraMap_germ_eq_germToFunctionField]

theorem algebraMap_germ_ratSec (g : X.functionField) {y : X} (hy : y ∈ ratLocus g) :
    algebraMap (X.presheaf.stalk y) X.functionField
      (X.presheaf.germ (ratLocus g) y hy (ratSec g)) = g := by
  haveI : Nonempty (ratLocus g) := ⟨⟨y, hy⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  exact germ_ratSec g _

theorem mem_ratLocus_iff {g : X.functionField} {y : X} :
    y ∈ ratLocus g ↔ ∃ a : X.presheaf.stalk y,
      algebraMap (X.presheaf.stalk y) X.functionField a = g :=
  ⟨fun hy ↦ ⟨_, algebraMap_germ_ratSec g hy⟩, fun ⟨a, ha⟩ ↦ mem_ratLocus_of_algebraMap a ha⟩

/-- The generic point lies in every regular locus.-/
theorem genericPoint_mem_ratLocus (g : X.functionField) : genericPoint X ∈ ratLocus g := by
  obtain ⟨W, hηW, c, hc⟩ := X.presheaf.exists_germ_eq (x := genericPoint X) g
  exact le_ratLocus ⟨c, fun _ ↦ hc⟩ hηW

/-- If the germ of `ratSec g` at `y` is a unit, then `g⁻¹` is regular at `y`.-/
theorem mem_ratLocus_inv_of_isUnit {g : X.functionField} {y : X} (hy : y ∈ ratLocus g)
    (hu : IsUnit (X.presheaf.germ (ratLocus g) y hy (ratSec g))) : y ∈ ratLocus g⁻¹ := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine mem_ratLocus_of_algebraMap v ?_
  have h1 := congrArg (algebraMap (X.presheaf.stalk y) X.functionField) hv
  rw [map_mul, map_one, algebraMap_germ_ratSec] at h1
  exact eq_inv_of_mul_eq_one_right h1

/-- `ratSec g · ratSec g⁻¹ = 1` on the overlap of the regular loci.-/
theorem ratSec_mul_ratSec_inv {g : X.functionField} (hg : g ≠ 0) :
    ratSec g |_ (ratLocus g ⊓ ratLocus g⁻¹) * ratSec g⁻¹ |_ (ratLocus g ⊓ ratLocus g⁻¹) = 1 := by
  apply sec_ext
  intro hη
  have h1 : X.presheaf.germ (ratLocus g ⊓ ratLocus g⁻¹) (genericPoint X) hη
      (ratSec g |_ (ratLocus g ⊓ ratLocus g⁻¹)) =
        X.presheaf.germ (ratLocus g) (genericPoint X) hη.1 (ratSec g) :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have h2 : X.presheaf.germ (ratLocus g ⊓ ratLocus g⁻¹) (genericPoint X) hη
      (ratSec g⁻¹ |_ (ratLocus g ⊓ ratLocus g⁻¹)) =
        X.presheaf.germ (ratLocus g⁻¹) (genericPoint X) hη.2 (ratSec g⁻¹) :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [map_mul, h1, h2, germ_ratSec, germ_ratSec, map_one, mul_inv_cancel₀ hg]

/-! ### The denominator ideal -/

/-- The **denominator ideal** of `g` on `U`: sections `a` with `a g` regular on `U`.-/
def denIdeal (g : X.functionField) (U : X.Opens) : Ideal Γ(X, U) where
  carrier := {a | ∀ hη : genericPoint X ∈ U, ∃ b : Γ(X, U),
    X.presheaf.germ U (genericPoint X) hη b = X.presheaf.germ U (genericPoint X) hη a * g}
  add_mem' := by
    intro a a' ha ha' hη
    obtain ⟨b, hb⟩ := ha hη
    obtain ⟨b', hb'⟩ := ha' hη
    exact ⟨b + b', by rw [map_add, map_add, hb, hb', add_mul]⟩
  zero_mem' := fun _ ↦ ⟨0, by rw [map_zero, zero_mul]⟩
  smul_mem' := by
    intro c a ha hη
    obtain ⟨b, hb⟩ := ha hη
    exact ⟨c * b, by rw [smul_eq_mul, map_mul, map_mul, hb, mul_assoc]⟩

theorem mem_denIdeal {g : X.functionField} {U : X.Opens} {a : Γ(X, U)} :
    a ∈ denIdeal g U ↔ ∀ hη : genericPoint X ∈ U, ∃ b : Γ(X, U),
      X.presheaf.germ U (genericPoint X) hη b = X.presheaf.germ U (genericPoint X) hη a * g :=
  Iff.rfl

/-- Localisation compatibility of the denominator ideal.-/
theorem denIdeal_map_basicOpen (g : X.functionField) (U : X.affineOpens) (s : Γ(X, U.1)) :
    (denIdeal g U.1).map (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom =
      denIdeal g (X.basicOpen s) := by
  haveI := U.2.isLocalization_basicOpen s
  change Ideal.map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen s)) _ = _
  by_cases hη : genericPoint X ∈ X.basicOpen s
  swap
  · haveI := subsingleton_sec hη
    ext x
    rw [Subsingleton.elim x 0]
    simp only [Submodule.zero_mem]
  have hηU : genericPoint X ∈ U.1 := X.basicOpen_le s hη
  have hres : ∀ a : Γ(X, U.1), X.presheaf.germ (X.basicOpen s) (genericPoint X) hη
      (algebraMap Γ(X, U.1) Γ(X, X.basicOpen s) a) = X.presheaf.germ U.1 (genericPoint X) hηU a :=
    fun a ↦ TopCat.Presheaf.germ_res_apply _ _ _ _ _
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha _
    obtain ⟨b, hb⟩ := ha hηU
    exact ⟨algebraMap _ _ b, by rw [hres, hres, hb]⟩
  · intro x hx
    rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers s)]
    obtain ⟨⟨a, m⟩, ham⟩ := IsLocalization.surj (Submonoid.powers s) x
    obtain ⟨b', hb'⟩ := hx hη
    obtain ⟨⟨c, m'⟩, hcm⟩ := IsLocalization.surj (Submonoid.powers s) b'
    dsimp only at ham hcm
    have e1 := congrArg (X.presheaf.germ (X.basicOpen s) (genericPoint X) hη) ham
    have e2 := congrArg (X.presheaf.germ (X.basicOpen s) (genericPoint X) hη) hcm
    rw [map_mul, hres, hres] at e1 e2
    refine ⟨⟨⟨a * m', fun _ ↦ ⟨c * m, ?_⟩⟩, m * m'⟩, ?_⟩
    · rw [map_mul, map_mul, ← e1, ← e2, hb']
      ring
    · simp only [Submonoid.coe_mul, map_mul]
      rw [← ham]
      ring

/-- **The denominator ideal sheaf** of a rational function.-/
def denIdealSheaf (g : X.functionField) : X.IdealSheafData where
  ideal U := denIdeal g U.1
  map_ideal_basicOpen U s := denIdeal_map_basicOpen g U s

theorem denIdealSheaf_ideal (g : X.functionField) (U : X.affineOpens) :
    (denIdealSheaf g).ideal U = denIdeal g U.1 := rfl

/-- On a nonempty affine open the denominator ideal is nonzero (`g = a / b`, `b ≠ 0`).-/
theorem exists_mem_denIdeal_ne_zero (g : X.functionField) (U : X.affineOpens)
    [Nonempty U.1] : ∃ b ∈ denIdeal g U.1, b ≠ 0 := by
  haveI := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, U.1)) g
  have hbK : algebraMap Γ(X, U.1) X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  refine ⟨b, fun hη ↦ ⟨a, ?_⟩, nonZeroDivisors.ne_zero hb⟩
  change X.germToFunctionField U.1 a = X.germToFunctionField U.1 b * g
  change algebraMap Γ(X, U.1) X.functionField a = algebraMap Γ(X, U.1) X.functionField b * g
  rw [← hab]
  field_simp

/-- `a ∈ den(g)` with `a g = b` gives `b ∈ den(g⁻¹)` (for `g ≠ 0`).-/
theorem mem_denIdeal_inv {g : X.functionField} (hg : g ≠ 0) {U : X.Opens} {a b : Γ(X, U)}
    (hab : ∀ hη : genericPoint X ∈ U,
      X.presheaf.germ U (genericPoint X) hη b = X.presheaf.germ U (genericPoint X) hη a * g) :
    b ∈ denIdeal g⁻¹ U := fun hη ↦ ⟨a, by rw [hab hη, mul_assoc, mul_inv_cancel₀ hg, mul_one]⟩

end AlgebraicGeometry.Chow.M7.RatGraph
