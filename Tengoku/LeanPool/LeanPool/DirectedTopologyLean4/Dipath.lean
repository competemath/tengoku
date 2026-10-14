/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
module

public import Tengoku.LeanPool.LeanPool.DirectedTopologyLean4.DirectedUnitInterval
public import Tengoku.LeanPool.LeanPool.DirectedTopologyLean4.Fraction

/-!
# LeanPool.DirectedTopologyLean4.Dipath
-/

@[expose] public section

/-
  This file contains the definition of a dipath in a directed space:
  A path between two points paired with the proof that it is a dipath.
  The following dipath constructions are given:
  * refl : the constant dipath
  * trans : the concatenation of dipaths
  * map : the image of a dipath under a directed map
  * subparam : the monotonic subparametrization of a dipath
-/

noncomputable section

open DirectedMap Set
open scoped unitInterval

universe u
variable {X : Type u} [DirectedSpace X] {x y z : X}

/-- A dipath is a path together with a proof that that path "is a dipath" -/
structure Dipath (x y : X) extends Path x y where
  dipath_toPath : IsDipath toPath

instance : Coe (Dipath x y) (Path x y) := ⟨fun γ => γ.toPath⟩

namespace Dipath

/--
@isnad1 id=directed.0h4v.s5.36fe4690d007 from=translated src=- shape=a6c9aba6 vocab=e6bb14a0
-/
lemma directed (γ : Dipath x y) : DirectedMap.Directed γ.toContinuousMap :=
  fun _ _ _ φ_dipath => isDipath_reparam φ_dipath γ.dipath_toPath

/-- Convert a dipath to its underlying directed map `D(I, X)`. -/
def toDirectedMap (γ : Dipath x y) : D(I,X) where
  toFun := γ.toFun
  continuous_toFun := γ.continuous_toFun
  directed_toFun := Dipath.directed γ

instance instFunLike : FunLike (Dipath x y) I X where
  coe := fun γ => γ.toFun
  coe_injective := fun γ γ' h => by
    obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := γ
    obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := γ'
    congr

/--
@isnad1 id=directed.0h3v.s4.5ac07e9005e2 from=translated src=- shape=b5bea07c vocab=e3e1d40a
-/
instance directedMapClass : DirectedMapClass (Dipath x y) I X where
  map_continuous := fun γ => γ.continuous_toFun
  map_directed := fun γ => directed γ

end Dipath

/--
@isnad1 id=eq.1h5v.s6.6486e7b24ef0 from=translated src=- shape=321dc963 vocab=45fd4d4b
-/
@[ext]
protected lemma Dipath.ext : ∀ {γ₁ γ₂ : Dipath x y}, (γ₁ : I → X) = γ₂ → γ₁ = γ₂ := by
  simp_all

namespace Dipath

/-- Promote a path with a proof of directedness into a dipath. -/
def ofIsDipath {γ : Path x y} (hγ : IsDipath γ) : Dipath x y := {
  toPath := γ,
  dipath_toPath := hγ,
}

/-- An directed map from I to a directed space can be turned into a dipath -/
def ofDirectedMap (f : D(I,X)) : Dipath (f 0) (f 1) where
  toFun := f
  continuous_toFun := f.continuous_toFun
  source' := rfl
  target' := rfl
  dipath_toPath := DirectedUnitInterval.isDipath_of_isDipath_comp_id <|
    f.directed_toFun DirectedUnitInterval.IdentityPath DirectedUnitInterval.isDipath_identityPath

/--
@isnad1 id=eq.4h4v.s8.f9d5d030bb43 from=translated src=- shape=95434e9e vocab=b43ef897
-/
@[simp] lemma coe_mk (f : I → X) (h₀ h₁ h₂ h₃) : ⇑(mk ⟨⟨f, h₀⟩, h₁, h₂⟩ h₃ : Dipath x y) = f := rfl

variable (γ : Dipath x y)

/--
@isnad1 id=continuo.0h4v.s5.90942b0cee5f from=translated src=- shape=3b254289 vocab=aa223a6c
-/
@[continuity]
protected lemma continuous : Continuous γ :=
  γ.continuous_toFun

/--
@isnad1 id=eq.0h4v.s5.ffffd5bd8cec from=translated src=- shape=284d63f7 vocab=45fd4d4b
-/
@[simp] protected lemma source : γ 0 = x :=
  γ.source'

/--
@isnad1 id=eq.0h4v.s5.a9c5279c7f36 from=translated src=- shape=88c80a01 vocab=45fd4d4b
-/
@[simp] protected lemma target : γ 1 = y :=
  γ.target'

namespace simps

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def apply : I → X :=
  γ

end simps

initialize_simps_projections Dipath
  (toPath_toContinuousMap_toFun → simps.apply, -toPath_toContinuousMap)

/--
@isnad1 id=eq.0h4v.s6.4eb0e4711584 from=translated src=- shape=b309d63b vocab=5930e5ff
-/
lemma coe_toContinuousMap : ⇑γ.toContinuousMap = γ := rfl
/--
@isnad1 id=eq.0h4v.s6.5cc25169838b from=translated src=- shape=f134d090 vocab=46e54730
-/
@[simp]
lemma coe_toDirectedMap : ⇑γ.toDirectedMap = γ := rfl

/-- Any function `φ : Π (a : α), Dipath (x a) (y a)` can be seen as a function `α × I → X`. -/
instance hasUncurryDipath {X α : Type*} [DirectedSpace X] {x y : α → X} :
  Function.HasUncurry (∀ a : α, Dipath (x a) (y a)) (α × I) X :=
⟨fun φ p => φ p.1 p.2⟩

/-! ### Properites about the range of dipaths -/

/--
@isnad1 id=eq.0h4v.s6.6c27ca59807e from=translated src=- shape=ee4e46e5 vocab=79d9fa5d
-/
@[simp] lemma coe_range (γ : Dipath x y) : range γ = range γ.toPath := rfl
/--
@isnad1 id=eq.0h4v.s6.868dbd405f54 from=translated src=- shape=48013f72 vocab=36705c86
-/
lemma range_eq_image (γ : Dipath x y) : range γ = γ.extend '' I :=
  Set.ext (fun z =>
    ⟨fun ⟨t, ht⟩ => ⟨t, t.2, by
      simp only [Subtype.coe_prop, Path.extend_apply, Subtype.coe_eta]
      exact ht⟩,
    fun ⟨t, t_mem_I, ht⟩ => ⟨⟨t, t_mem_I⟩, by
      rw [ht.symm, Path.extend_apply γ.toPath t_mem_I]
      rfl⟩⟩)

/--
@isnad1 id=eq.0h4v.s6.446fa8593a8e from=translated src=- shape=a0e907f6 vocab=8efdaa8a
-/
lemma range_eq_image_I (γ : Dipath x y) : range γ = γ '' Icc 0 1 :=
  Set.ext (fun _ =>
    ⟨fun ⟨t, ht⟩ => ⟨t, t.2, ht⟩,
    fun ⟨t, t_mem_I, ht⟩ => ⟨⟨t, t_mem_I⟩, ht⟩⟩)

/--
@isnad1 id=eq.0h6v.s7.f42622ec01c6 from=translated src=- shape=2d37adf4 vocab=c39caa3a
-/
lemma image_extend_eq_image (γ : Dipath x y) (a b : I) :
    γ.extend '' Icc ↑a ↑b = γ '' Icc a b := by
  ext y
  constructor
  · rintro ⟨t, t_ab, ht⟩
    have ht_mem : t ∈ I := ⟨le_trans a.2.1 t_ab.1, le_trans t_ab.2 b.2.2⟩
    refine ⟨⟨t, ht_mem⟩, t_ab, ?_⟩
    rw [← ht, Path.extend_apply γ.toPath ht_mem]
    rfl
  · rintro ⟨t, t_ab, ht⟩
    refine ⟨t, t_ab, ?_⟩
    rw [← ht]
    convert Path.extend_apply γ.toPath ⟨le_trans a.2.1 t_ab.1, le_trans t_ab.2 b.2.2⟩
    first
      | (all_goals grind; done)
      | (all_goals simp_all; done)
      | (all_goals aesop; done)
      | (all_goals omega; done)
      | (all_goals norm_num; done)
      | (all_goals positivity; done)
      | (all_goals linarith; done)
      | (all_goals decide; done)
      | (all_goals tauto; done)

/-! ### Reflexive dipaths -/

/-- The constant dipath from a point to itself -/
@[refl, simps!]
def refl (x : X) : Dipath x x where
  toPath := Path.refl x
  dipath_toPath := isDipath_constant x

/--
@isnad1 id=eq.0h2v.s5.e60e8b97c7da from=translated src=- shape=46ebd5be vocab=eb3f69ba
-/
lemma refl_range {a : X} : range (Dipath.refl a) = {a} := Path.refl_range

/-! ### Concatenation of dipaths -/

/-- Directed paths can be concatenated -/
@[trans] def trans (γ : Dipath x y) (γ' : Dipath y z) : Dipath x z :=
{
  γ.toPath.trans γ'.toPath with
  dipath_toPath := isDipath_concat γ.dipath_toPath γ'.dipath_toPath
}

/--
@isnad1 id=eq.0h6v.s6.a093801a5947 from=translated src=- shape=582ae835 vocab=db8a754b
-/
@[simp] lemma trans_to_path (γ : Dipath x y) (γ' : Dipath y z) :
  γ.toPath.trans γ'.toPath = (γ.trans γ').toPath := by
  ext t
  rfl

/--
@isnad1 id=eq.0h7v.s8.68630058f3af from=translated src=- shape=01d63160 vocab=01490646
-/
lemma trans_apply (γ : Dipath x y) (γ' : Dipath y z) (t : I) : (γ.trans γ') t =
  if h : (t : ℝ) ≤ 1/2 then
    γ ⟨2 * t, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨t.2.1, h⟩⟩
  else
    γ' ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ :=
Path.trans_apply (γ.toPath) (γ'.toPath) t

/--
@isnad1 id=eq.0h6v.s6.12e739507d8b from=translated src=- shape=7ea954f5 vocab=8734e887
-/
lemma trans_range (γ : Dipath x y) (γ' : Dipath y z) : range (γ.trans γ') = range γ ∪ range γ' :=
  Path.trans_range γ.toPath γ'.toPath

/--
@isnad1 id=eq.0h6v.s6.0d8b12462d6c from=translated src=- shape=21c8b866 vocab=2dddfee3
-/
lemma trans_eval_at_half (γ : Dipath x y) (γ' : Dipath y z) :
    (γ.trans γ') (Fraction.ofPos two_pos) = y := by
  rw [Dipath.trans_apply]
  simp

/-! ### Mapping dipaths -/

/-- Image of a dipath from `x` to `y` by a directed map -/
def map (γ : Dipath x y) {Y : Type*} [DirectedSpace Y] (f : D(X,Y)) : Dipath (f x) (f y) :=
{
  γ.toPath.map f.continuous_toFun with
  dipath_toPath := f.directed_toFun γ.toPath γ.dipath_toPath,
}

/--
@isnad1 id=eq.0h6v.s7.b0420658721e from=translated src=- shape=a1277206 vocab=38329e6d
-/
@[simp] lemma map_coe (γ : Dipath x y) {Y : Type*} [DirectedSpace Y] (f : D(X,Y)) :
  (γ.map f : I → Y) = f ∘ γ :=
by { ext t; rfl }

/--
@isnad1 id=eq.0h8v.s7.3b91cbf19e0d from=translated src=- shape=8aaddc84 vocab=165fc984
-/
@[simp] lemma map_trans (γ : Dipath x y) (γ' : Dipath y z) {Y : Type*} [DirectedSpace Y]
    (f : D(X,Y)) :
  (γ.trans γ').map f = (γ.map f).trans (γ'.map f) := by
  ext t
  rw [trans_apply, map_coe, Function.comp_apply, trans_apply]
  simp
  split_ifs <;> rfl

/--
@isnad1 id=eq.0h4v.s6.d0901623fd7e from=translated src=- shape=9710cd9f vocab=3dc7866a
-/
@[simp] lemma map_id (γ : Dipath x y) : γ.map (DirectedMap.id X) = γ := by { ext; rfl }

/--
@isnad1 id=eq.0h8v.s7.5e076cfa7579 from=translated src=- shape=4ee26042 vocab=99757a3d
-/
@[simp] lemma map_map (γ : Dipath x y) {Y : Type*} [DirectedSpace Y] {Z : Type*} [DirectedSpace Z]
  (f : D(X,Y)) (g : D(Y,Z)) : (γ.map f).map g = γ.map (g.comp f) := by { ext; rfl }

/-! ### Casting dipaths -/

/-- Casting a dipath from `x` to `y` to a dipath from `x'` to `y'` when `x' = x` and `y' = y` -/
def cast (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) : Dipath x' y' :=
{ toFun := γ,
  continuous_toFun := γ.continuous,
  dipath_toPath := isDipath_cast γ.toPath hx hy γ.dipath_toPath,
  source' := by simp [hx],
  target' := by simp [hy]
}

/--
@isnad1 id=eq.2h7v.s6.33a501036b15 from=translated src=- shape=2f8232a9 vocab=58ebf087
-/
lemma cast_apply (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) (t : I) :
  (γ.cast hx hy) t = γ t := rfl

/--
@isnad1 id=eq.3h9v.s6.c07210921766 from=translated src=- shape=9922498b vocab=f95e8a53
-/
@[simp] lemma trans_cast {X : Type*} [DirectedSpace X] {a₁ a₂ b₁ b₂ c₁ c₂ : X}
  (γ : Dipath a₂ b₂) (γ' : Dipath b₂ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) :
  (γ.cast ha hb).trans (γ'.cast hb hc) = (γ.trans γ').cast ha hc := rfl

/--
@isnad1 id=eq.2h6v.s6.dc26237fc523 from=translated src=- shape=51839a52 vocab=58ebf087
-/
@[simp] lemma cast_coe (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) :
  (γ.cast hx hy : I → X) = γ := rfl

/--
@isnad1 id=eq.2h6v.s6.ed0a551a4710 from=translated src=- shape=9a735e59 vocab=62924e1e
-/
lemma cast_range (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) :
  range (γ.cast hx hy) = range γ := rfl

/--
@isnad1 id=eq.2h8v.s7.9a3d6592d772 from=translated src=- shape=051b2c86 vocab=d52599f2
-/
lemma cast_image (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) (a b : ℝ) :
  (γ.cast hx hy).extend '' Icc a b = γ.extend '' Icc a b := rfl

/--
@isnad1 id=eq.0h4v.s7.de48733bcc7b from=translated src=- shape=4fecd1c7 vocab=828ac4ec
-/
lemma dipath_of_directed_map_of_to_dimap (γ : Dipath x y) :
  Dipath.ofDirectedMap (γ.toDirectedMap) = γ.cast γ.source' γ.target' := by {ext t; rfl }

/-! ### Reparametrising a path -/

/-- Reparametrize a dipath by precomposing it with a directed self-map of the unit interval. -/
def subparam (γ : Dipath x y) (f : D(I,I)) : Dipath (γ (f 0)) (γ (f 1)) :=
{
  toFun := γ ∘ f
  continuous_toFun := by continuity
  source' := rfl
  target' := rfl
  dipath_toPath := by
      set p : Path (f 0) (f 1) :=
        { toFun := f,
          continuous_toFun := f.continuous_toFun,
          source' := rfl,
          target' := rfl
        }
      have p_mono : Monotone p := DirectedUnitInterval.monotone_of_directed f
      exact isDipath_reparam p_mono γ.dipath_toPath
}

/--
@isnad1 id=le.0h5v.s8.6b97e5fe8b1a from=translated src=- shape=359aa5cc vocab=b4873444
-/
lemma subparam_range (γ : Dipath x y) (f : D(I,I)) :
  range (γ.subparam f) ⊆ range γ := fun _ ⟨a, ha⟩ => ⟨f a, ha⟩

/-- Given a dipath `γ` and a dimap `f : I → I` where `f 0 = 0` and `f 1 = 1`, `γ.reparam f` is the
dipath defined by `γ ∘ f`.
-/
def reparam (γ : Dipath x y) (f : D(I,I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  Dipath x y :=
(subparam γ f).cast (hf₀.symm ▸ γ.source.symm) (hf₁.symm ▸ γ.target.symm)

/--
@isnad1 id=eq.2h5v.s7.0eef2edba6d9 from=translated src=- shape=2671650d vocab=3c24d8f6
-/
@[simp]
lemma coe_to_fun (γ : Dipath x y) (f : D(I,I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  ⇑(γ.reparam f hf₀ hf₁) = γ ∘ f := rfl

/--
@isnad1 id=eq.0h4v.s5.5014bbd2f405 from=translated src=- shape=dfe9d078 vocab=c164bcea
-/
@[simp]
lemma reparam_id (γ : Dipath x y) : γ.reparam (DirectedMap.id I) rfl rfl = γ :=
by { ext; rfl }

/--
@isnad1 id=eq.2h5v.s7.baecd798ed39 from=translated src=- shape=458e408f vocab=58619af9
-/
lemma range_reparam (γ : Dipath x y) (f : D(I,I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  range (γ.reparam f hf₀ hf₁) = range γ :=
Path.range_reparam γ.toPath f.continuous_toFun hf₀ hf₁

variable {Y : Type*} [DirectedSpace Y] {x₀ x₁ : X} {y₀ y₁ : Y}

/-- Two dipaths together form a dipath in the product space -/
def dipathProduct (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath y₀ y₁) : Dipath (x₀, y₀) (x₁, y₁) where
  toFun := fun t => (γ₁ t, γ₂ t)
  source' := by simp
  target' := by simp
  dipath_toPath := ⟨γ₁.dipath_toPath, γ₂.dipath_toPath⟩

/-- Given a directed path in a product space, we can project it to its first coordinate to
obtain a directed path -/
def ofProductFst (γ : Dipath (x₀, y₀) (x₁, y₁)) : Dipath x₀ x₁ where
  toPath := γ.toPath.map continuous_fst
  dipath_toPath := γ.dipath_toPath.1

/-- Given a directed path in a product space, we can project it to its second coordinate to
obtain a directed path -/
def ofProductSnd (γ : Dipath (x₀, y₀) (x₁, y₁)) : Dipath y₀ y₁ where
  toPath := γ.toPath.map continuous_snd
  dipath_toPath := γ.dipath_toPath.2

end Dipath
