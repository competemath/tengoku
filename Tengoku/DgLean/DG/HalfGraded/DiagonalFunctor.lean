import Tengoku.DgLean.DG.HalfGraded.DiagonalModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The diagonal ordinary-module functor

Ordinary dg module morphisms act componentwise on the diagonal half-regrading.
The resulting functor uses the existing bigraded-module / weight-category comparison.
-/

open scoped DG

open CategoryTheory DirectSum

universe v u

namespace DG.Diagonal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Ring A] [DGAddCommGroup A]
  {M N P : DGModuleCat.{v} A}

/-- Ordinary degree-zero morphisms preserve the diagonal grading.
@isnad1 id=mem.1h6v.s8.b087a55c553b from=translated src=- shape=36ce2dc2 vocab=25aa8c7c
-/
theorem map_mem_grading (f : M ⟶ N) {p : ℤ × ZMod 2} {m : M}
    (hm : m ∈ grading M p) : f.hom m ∈ grading N p := by
  refine induction_on (P := fun m => f.hom m ∈ grading N p) hm
    (by simp) (fun n m hm hn => ?_)
    (fun m m' h h' => by simpa only [map_add] using add_mem h h')
  rw [← hn]
  exact mem_grading (f.hom.map_mem hm)

/-- The componentwise additive map on the full half-regraded direct sum.-/
def regradedMap (f : M ⟶ N) : RegradedModule M →+ RegradedModule N :=
  DirectSum.map fun _ =>
    { toFun := fun m => ⟨f.hom m, map_mem_grading f m.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }

/--
@isnad1 id=eq.1h6v.s10.326f693bbb82 from=translated src=- shape=815038d1 vocab=eb64a029
-/
@[simp] theorem regradedMap_mk (f : M ⟶ N) (p : ℤ × ℤ) (m : M)
    (hm : m ∈ grading M (halfDegree 2 p)) :
    regradedMap f (HalfRegrade.mk (grading M) 2 p m hm) =
      HalfRegrade.mk (grading N) 2 p (f.hom m) (map_mem_grading f hm) :=
  DirectSum.map_of _ _ _

/-- The componentwise map preserves cohomological degrees.
@isnad1 id=mem.1h6v.s10.3735d5a636b3 from=translated src=- shape=347244fc vocab=cc992d87
-/
theorem regradedMap_mem_grading (f : M ⟶ N) {n : ℤ} {x : RegradedModule M}
    (hx : x ∈ DG.grading n) : regradedMap f x ∈ DG.grading n := by
  refine HalfRegrade.cohGrading_induction
    (P := fun x => regradedMap f x ∈ DG.grading n) (by simp)
    (fun w m hm => ?_) (fun x y hx hy => by simpa only [map_add] using add_mem hx hy) hx
  rw [regradedMap_mk]
  exact HalfRegrade.mk_mem_cohGrading (n, w) _

/-- The componentwise map preserves every weight.
@isnad1 id=mem.1h6v.s10.412637c2d4b6 from=translated src=- shape=5deba3cc vocab=b999959f
-/
theorem regradedMap_mem_wgrading (f : M ⟶ N) {w : ℤ} {x : RegradedModule M}
    (hx : x ∈ wgrading w) : regradedMap f x ∈ wgrading w := by
  refine HalfRegrade.weightGrading_induction
    (P := fun x => regradedMap f x ∈ wgrading w) (by simp)
    (fun n m hm => ?_) (fun x y hx hy => by simpa only [map_add] using add_mem hx hy) hx
  rw [regradedMap_mk]
  exact HalfRegrade.mk_mem_weightGrading (n, w) _

/-- The componentwise map commutes with the original differential.
@isnad1 id=eq.0h5v.s11.94c705112847 from=translated src=- shape=fc3f3b29 vocab=8da89e43
-/
theorem regradedMap_d (f : M ⟶ N) (x : RegradedModule M) :
    regradedMap f (d x) = d (regradedMap f x) := by
  induction x using HalfRegrade.induction_on with
  | zero => simp
  | mk p m hm =>
    simp only [d_mk, regradedMap_mk]
    exact HalfRegrade.mk_congr rfl (f.hom.map_d m) _ _
  | add x y hx hy => simp only [map_add, hx, hy]

variable [DGRing A]

/-- The original linearity gives linearity for the regraded ring action.
@isnad1 id=eq.0h6v.s11.bb832aba0e3f from=translated src=- shape=711388f2 vocab=1145c0af
-/
theorem regradedMap_smul (f : M ⟶ N) (a : (HalfGradedDGRing.ofDGRing A).Regraded)
    (x : RegradedModule M) : regradedMap f (a • x) = a • regradedMap f x := by
  induction a using HalfGradedDGRing.induction_on with
  | zero => simp
  | mk p a ha =>
    induction x using HalfRegrade.induction_on with
    | zero => simp
    | mk q m hm =>
      rw [place_smul_mk, regradedMap_mk, regradedMap_mk, place_smul_mk]
      exact HalfRegrade.mk_congr rfl (f.hom.map_smul a m) _ _
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | add a b ha hb => simp only [add_smul, map_add, ha, hb]

/-- The diagonal lift as an actual morphism of bigraded dg modules.-/
def toBigradedMap (f : M ⟶ N) :
    BigradedDGModuleCat.of (HalfGradedDGRing.ofDGRing A).Regraded (RegradedModule M) ⟶
      BigradedDGModuleCat.of (HalfGradedDGRing.ofDGRing A).Regraded (RegradedModule N) where
  hom :=
    { toLinearMap := { regradedMap f with map_smul' := regradedMap_smul f }
      map_mem' := regradedMap_mem_grading f
      map_d' := regradedMap_d f }
  map_mem_wgrading := regradedMap_mem_wgrading f

variable (A) in
/-- Diagonal half-regrading as a functor on ordinary dg modules.-/
def toBigraded : DGModuleCat.{v} A ⥤
    BigradedDGModuleCat.{v} (HalfGradedDGRing.ofDGRing A).Regraded where
  obj M := BigradedDGModuleCat.of _ (RegradedModule M)
  map := toBigradedMap
  map_id M := by
    apply BigradedDGModuleCat.hom_ext
    apply DGModuleHom.ext
    intro x
    change regradedMap (𝟙 M) x = x
    induction x using HalfRegrade.induction_on with
    | zero => exact map_zero _
    | mk p m hm => rw [regradedMap_mk]; rfl
    | add x y hx hy => rw [map_add, hx, hy]
  map_comp f g := by
    apply BigradedDGModuleCat.hom_ext
    apply DGModuleHom.ext
    intro x
    change regradedMap (f ≫ g) x = regradedMap g (regradedMap f x)
    induction x using HalfRegrade.induction_on with
    | zero => simp
    | mk p m hm => simp only [regradedMap_mk]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]

variable (A) in
/-- The ordinary-module functor to modules over the diagonal weight dg category.-/
def toCatModule : DGModuleCat.{v} A ⥤
    CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) :=
  toBigraded A ⋙ BigradedDGModuleCat.toCatModule _

/--
@isnad1 id=eq.0h2v.s9.3778158db4ee from=translated src=- shape=f5f3f99b vocab=cdd9418f
-/
@[simp] theorem toCatModule_obj (M : DGModuleCat.{v} A) :
    (toCatModule A).obj M = toCatModuleObj A M := rfl

/-- The weight-category morphism is the restriction of the componentwise map.
@isnad1 id=eq.0h6v.s14.7be851020634 from=translated src=- shape=f034d274 vocab=e26e3ffb
-/
@[simp] theorem toCatModule_map_app_coe (f : M ⟶ N)
    (w : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)
    (m : (toCatModuleObj A M).obj w) :
    (((toCatModule A).map f).app w m).1 = regradedMap f m.1 := rfl

/-- The published homogeneous weight-zero injection is natural in ordinary module maps.
@isnad1 id=eq.0h6v.s14.2c523c730bce from=translated src=- shape=97073fc5 vocab=0b9631fc
-/
@[simp] theorem toCatModule_map_toWeightZero (f : M ⟶ N) (n : ℤ)
    (m : DG.grading (M := M) n) :
    ((toCatModule A).map f).app ⟨0⟩ (toWeightZero A M n m) =
      toWeightZero A N n ⟨f.hom m, f.hom.map_mem m.2⟩ := by
  apply Subtype.ext
  exact regradedMap_mk f (n, 0) m _

end

end DG.Diagonal
