import Tengoku.Seed.CategoryTheory.Linear.LinearFunctor
import Tengoku.Seed.CategoryTheory.Quotient.Linear
import Tengoku.DgLean.DG.Category.Homotopy.HomotopyShift
import Tengoku.DgLean.DG.Category.Linear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Linearity over the ground ring for dg modules over a dg category

Let `R` be a commutative ring and `C` a dg category over `R` (`DG.DGLinear R C`). The scalar
endomorphisms `r • 𝟙 X` are central degree-`0` cocycles of `C`, so they act on every dg module
`M` over `C` by endomorphisms of degree `0` commuting with the differential and with the action
of `C`. This makes the constructions of the homotopy theory of dg modules over `C` `R`-linear.
It is the analogue for dg categories of `DG.Module.HomLinear`, `DG.Homotopy.ModuleCat` (the
`R`-linear structure) and `DG.Homotopy.ShiftLinear` (the case of a dg `R`-algebra).

## Main definitions and results

* `DG.CatModule.Cochain.instModuleGround`: the cochains `Cochain M N n` form an `R`-module, with
  `(r • z).app X x = (r • 𝟙 X) • z.app X x` (`DG.CatModule.Cochain.smul_ground_app`); cochains
  commute with the action of `R` (`DG.CatModule.Cochain.map_smul_id`), composition is
  `R`-bilinear (`DG.CatModule.Cochain.smul_comp`, `DG.CatModule.Cochain.comp_smul`) and the
  differential of the Hom complex is `R`-linear (`DG.CatModule.δ_smul_ground`,
  `DG.CatModule.HOM.d_smul_ground`). So `HOM_C(M, N)` is a complex of `R`-modules.
* `DG.CatModule.instLinear`: the category `DG.CatModule C` is `R`-linear, and so are its shift
  functors (`DG.CatModule.shiftFunctor_linear`).
* `DG.CatModule.HomotopyCategory.instLinear`: the homotopy category is `R`-linear, the quotient
  functor is `R`-linear (`DG.CatModule.HomotopyCategory.quotient_linear`), and so are the shift
  functors of the homotopy category (`DG.CatModule.HomotopyCategory.shiftFunctor_linear`).

## Implementation notes

The `R`-module structures are declared with low priority: for `R = ℤ` (with
`DG.DGLinear.int`) they agree with the integer actions of the abelian groups only
propositionally, and those should be found first.
-/

open scoped DG

open CategoryTheory

universe w v u

namespace DG

namespace CatModule

variable {R : Type*} [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] [DGLinear R C]

/-! ### The action of the scalar endomorphisms on a dg module -/

section Action

variable {M : CatModule.{w} C}

/--
@isnad1 id=mem.1h7v.s9.7940588bfa94 from=translated src=- shape=3682357b vocab=9989b630
-/
theorem smul_id_smul_mem {X : C} (r : R) {i : ℤ} {m : M.obj X} (hm : m ∈ grading i) :
    (r • 𝟙 X) • m ∈ grading i := by
  simpa using smul_mem_grading (DGLinear.smul_id_mem r X) hm

/--
@isnad1 id=eq.0h6v.s10.805ce5ca6c3e from=translated src=- shape=d4e0c8a0 vocab=434ec622
-/
theorem d_smul_id_smul {X : C} (r : R) (m : M.obj X) : d ((r • 𝟙 X) • m) = (r • 𝟙 X) • d m := by
  rw [d_smul_of_d_eq_zero (DGLinear.smul_id_mem r X) (DGLinear.d_smul_id r X), koszulSign_zero,
    one_smul]

omit [DGCategory C] [DGLinear R C] in
/-- The scalar endomorphisms act centrally: `(r • 𝟙 Y) • f • m = f • (r • 𝟙 X) • m`.
@isnad1 id=eq.0h8v.s9.88e548e2081e from=translated src=- shape=ffe87929 vocab=f2990ae6
-/
theorem smul_id_smul_comm {X Y : C} (r : R) (f : X ⟶ Y) (m : M.obj X) :
    (r • 𝟙 Y) • f • m = f • (r • 𝟙 X) • m := by
  rw [← comp_smul, ← comp_smul, DGLinear.smul_id_comp_eq_comp_smul_id]

omit [DGCategory C] [DGLinear R C] in
/--
@isnad1 id=eq.0h8v.s9.51f6e3d0582f from=translated src=- shape=fafa591e vocab=f2990ae6
-/
theorem smul_smul_id {X Y : C} (r : R) (f : X ⟶ Y) (m : M.obj X) :
    (r • f) • m = (r • 𝟙 Y) • f • m := by
  rw [← comp_smul, DGLinear.comp_smul_id]

omit [DGCategory C] [DGLinear R C] in
/--
@isnad1 id=eq.0h7v.s9.f4e273f9ff85 from=translated src=- shape=44cb916d vocab=6594bb6a
-/
theorem mul_smul_id_smul {X : C} (r s : R) (m : M.obj X) :
    ((r * s) • 𝟙 X) • m = (r • 𝟙 X) • (s • 𝟙 X) • m := by
  rw [← comp_smul, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, mul_comm]

omit [DGCategory C] [DGLinear R C] in
/--
@isnad1 id=eq.0h7v.s10.c2d22f6cf527 from=translated src=- shape=e809fc73 vocab=c7047eb2
-/
theorem add_smul_id_smul {X : C} (r s : R) (m : M.obj X) :
    ((r + s) • 𝟙 X) • m = (r • 𝟙 X) • m + (s • 𝟙 X) • m := by
  rw [_root_.add_smul, add_smul]

omit [DGCategory C] [DGLinear R C] in
/--
@isnad1 id=eq.0h5v.s8.ef38df4d0410 from=translated src=- shape=91e76c48 vocab=f2990ae6
-/
@[simp]
theorem one_smul_id_smul {X : C} (m : M.obj X) : ((1 : R) • 𝟙 X) • m = m := by
  rw [_root_.one_smul, id_smul]

omit [DGCategory C] [DGLinear R C] in
/--
@isnad1 id=eq.0h5v.s8.1e3532fd800d from=translated src=- shape=3d789657 vocab=f2990ae6
-/
@[simp]
theorem zero_smul_id_smul {X : C} (m : M.obj X) : ((0 : R) • 𝟙 X) • m = 0 := by
  rw [_root_.zero_smul, zero_smul]

end Action

/-! ### The Hom complex is a complex of `R`-modules -/

namespace Cochain

variable {M N P : CatModule.{w} C} {n : ℤ}

/-- A cochain commutes with the scalar endomorphisms.
@isnad1 id=eq.0h9v.s10.38b93be1896b from=translated src=- shape=d83b9bf0 vocab=6f7d373b
-/
theorem map_smul_id (z : Cochain M N n) {X : C} (r : R) (x : M.obj X) :
    z.app X ((r • 𝟙 X) • x) = (r • 𝟙 X) • z.app X x := by
  rw [z.map_smul (DGLinear.smul_id_mem r X), mul_zero, koszulSign_zero, one_smul]

/-- The action of `R` on cochains, `(r • z).app X x = (r • 𝟙 X) • z.app X x`.-/
instance (priority := 100) instSMulGround : SMul R (Cochain M N n) :=
  ⟨fun r z =>
    { app := fun X => (N.act (r • 𝟙 X)).comp (z.app X)
      map_mem' := fun hx => smul_id_smul_mem r (z.map_mem hx)
      map_smul' := fun {X Y i f} hf x => by
        change (r • 𝟙 Y) • z.app Y (f • x) = koszulSign (n * i) • (f • (r • 𝟙 X) • z.app X x)
        rw [z.map_smul hf, smul_units_smul, smul_id_smul_comm] }⟩

/--
@isnad1 id=eq.0h9v.s9.9fc8bf01679d from=translated src=- shape=1d26d8e8 vocab=6f7d373b
-/
theorem smul_ground_app (r : R) (z : Cochain M N n) {X : C} (x : M.obj X) :
    (r • z).app X x = (r • 𝟙 X) • z.app X x := rfl

/-- Cochains of degree `n` form an `R`-module.-/
instance (priority := 100) instModuleGround : Module R (Cochain M N n) where
  one_smul z := ext fun _ _ => by rw [smul_ground_app, one_smul_id_smul]
  mul_smul r s z := ext fun _ _ => by
    rw [smul_ground_app, smul_ground_app, smul_ground_app, mul_smul_id_smul]
  smul_zero r := ext fun _ _ => by rw [smul_ground_app, zero_apply, smul_zero]
  smul_add r z z' := ext fun _ _ => by
    rw [smul_ground_app, add_apply, add_apply, smul_add, smul_ground_app, smul_ground_app]
  add_smul r s z := ext fun _ _ => by
    rw [smul_ground_app, add_apply, smul_ground_app, smul_ground_app, add_smul_id_smul]
  zero_smul z := ext fun _ _ => by rw [smul_ground_app, zero_smul_id_smul, zero_apply]

/--
@isnad1 id=eq.1h11v.s9.15e6d02b7a1b from=translated src=- shape=97f8bec2 vocab=ae3d6093
-/
theorem smul_comp {n₁ n₂ n₁₂ : ℤ} (r : R) (z₁ : Cochain M N n₁) (z₂ : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) : (r • z₂).comp z₁ h = r • z₂.comp z₁ h := rfl

/--
@isnad1 id=eq.1h11v.s9.51de784b42c6 from=translated src=- shape=a9129e5f vocab=ae3d6093
-/
theorem comp_smul {n₁ n₂ n₁₂ : ℤ} (r : R) (z₁ : Cochain M N n₁) (z₂ : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) : z₂.comp (r • z₁) h = r • z₂.comp z₁ h :=
  ext fun _ _ => map_smul_id z₂ r _

end Cochain

variable {M N P : CatModule.{w} C}

/-- The differential of the Hom complex is `R`-linear.
@isnad1 id=eq.0h8v.s9.b95d8ec0c547 from=translated src=- shape=8a931438 vocab=77571aa6
-/
@[simp]
theorem δ_smul_ground (n m : ℤ) (r : R) (z : Cochain M N n) : δ n m (r • z) = r • δ n m z := by
  by_cases hnm : n + 1 = m
  · ext X x
    rw [Cochain.smul_ground_app, δ_apply _ _ hnm, δ_apply _ _ hnm, Cochain.smul_ground_app,
      Cochain.smul_ground_app, d_smul_id_smul, smul_sub, smul_units_smul]
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm, _root_.smul_zero]

namespace HOM

/--
@isnad1 id=eq.0h7v.s10.013240330fa0 from=translated src=- shape=0673d02d vocab=64249176
-/
theorem smul_of (r : R) (n : ℤ) (z : Cochain M N n) :
    r • (DirectSum.of (fun n => Cochain M N n) n z : HOM M N) =
      DirectSum.of (fun n => Cochain M N n) n (r • z) := by
  rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R, map_smul]

/-- The differential of `HOM_C(M, N)` is `R`-linear.
@isnad1 id=eq.0h6v.s9.9adb190c7f04 from=translated src=- shape=526ca5ab vocab=716bcc24
-/
theorem d_smul_ground (r : R) (F : HOM M N) : d (r • F) = r • d F := by
  induction F using DirectSum.induction_on with
  | zero => simp
  | of n z => rw [smul_of, d_of, d_of, δ_smul_ground, smul_of]
  | add F G hF hG => rw [_root_.smul_add, d_add, hF, hG, d_add, _root_.smul_add]

/-- The homogeneous components of `HOM_C(M, N)` are `R`-submodules.
@isnad1 id=mem.1h7v.s8.83a6f342e4ea from=translated src=- shape=b6d5ce7e vocab=02cb882c
-/
theorem smul_mem_grading (r : R) {n : ℤ} {F : HOM M N} (hF : F ∈ grading n) :
    r • F ∈ grading n := by
  obtain ⟨z, rfl⟩ := hF
  rw [smul_of]
  exact of_mem_summand _ _

end HOM

/-! ### The `R`-linear category of dg modules -/

/-- The action of `R` on morphisms of dg modules, `(r • φ).app X m = (r • 𝟙 X) • φ.app X m`.-/
instance (priority := 100) instSMulHom : SMul R (M ⟶ N) :=
  ⟨fun r φ =>
    { app := fun X => (N.act (r • 𝟙 X)).comp (φ.app X)
      map_mem' := fun hm => smul_id_smul_mem r (φ.map_mem hm)
      map_d' := fun {X} m => by
        change (r • 𝟙 X) • φ.app X (d m) = d ((r • 𝟙 X) • φ.app X m)
        rw [d_smul_id_smul, Hom.map_d]
      map_smul' := fun {X Y} f m => by
        change (r • 𝟙 Y) • φ.app Y (f • m) = f • (r • 𝟙 X) • φ.app X m
        rw [Hom.map_smul, smul_id_smul_comm] }⟩

/--
@isnad1 id=eq.0h8v.s9.49d07da32ff5 from=translated src=- shape=6d54240c vocab=aab979b1
-/
theorem smul_app (r : R) (φ : M ⟶ N) {X : C} (m : M.obj X) :
    (r • φ).app X m = (r • 𝟙 X) • φ.app X m := rfl

/-- The morphisms of dg modules `M ⟶ N` form an `R`-module.-/
instance (priority := 100) instModuleHom : Module R (M ⟶ N) where
  one_smul φ := hom_ext fun X m => by rw [smul_app, one_smul_id_smul]
  mul_smul r s φ := hom_ext fun X m => by rw [smul_app, smul_app, smul_app, mul_smul_id_smul]
  smul_zero r := hom_ext fun X m => by rw [smul_app, zero_app, smul_zero]
  smul_add r φ ψ := hom_ext fun X m => by
    rw [smul_app, add_app, add_app, smul_add, smul_app, smul_app]
  add_smul r s φ := hom_ext fun X m => by
    rw [smul_app, add_app, smul_app, smul_app, add_smul_id_smul]
  zero_smul φ := hom_ext fun X m => by rw [smul_app, zero_smul_id_smul, zero_app]

/-- The category of dg modules over a dg category over `R` is `R`-linear.-/
instance (priority := 100) instLinear : Linear R (CatModule.{w} C) where
  homModule _ _ := instModuleHom
  smul_comp _ _ _ r φ ψ := hom_ext fun _ _ => by
    rw [comp_app, smul_app, smul_app, Hom.map_smul, comp_app]
  comp_smul _ _ _ φ r ψ := hom_ext fun _ _ => rfl

/--
@isnad1 id=eq.0h6v.s10.7326735fc7ff from=translated src=- shape=001e67a1 vocab=186b0250
-/
theorem Cochain.ofHom_smul (r : R) (φ : M ⟶ N) : Cochain.ofHom (r • φ) = r • Cochain.ofHom φ :=
  rfl

/-! ### Homotopies and the homotopy category -/

namespace DGHomotopy

variable {f g : M ⟶ N}

/-- A homotopy `h` from `f` to `g` gives the homotopy `r • h` from `r • f` to `r • g`.-/
@[simps]
def smul (r : R) (h : DGHomotopy f g) : DGHomotopy (r • f) (r • g) where
  hom := r • h.hom
  ofHom_eq := by rw [Cochain.ofHom_smul, Cochain.ofHom_smul, h.ofHom_eq, δ_smul_ground, _root_.smul_add]

end DGHomotopy

/--
@isnad1 id=homotopi.1h7v.s10.05c8ff2feffc from=translated src=- shape=550aba10 vocab=38d72fd2
-/
theorem Homotopic.smul {f g : M ⟶ N} (r : R) (h : Homotopic f g) : Homotopic (r • f) (r • g) :=
  ⟨h.some.smul r⟩

namespace HomotopyCategory

variable (R C)

/-- The homotopy category of dg modules over a dg category over `R` is `R`-linear.-/
instance (priority := 100) instLinear : Linear R (HomotopyCategory.{w} C) :=
  Quotient.linear R (homotopic.{w} C) fun r _ _ _ _ h => Homotopic.smul r h

end HomotopyCategory

end CatModule

end DG
