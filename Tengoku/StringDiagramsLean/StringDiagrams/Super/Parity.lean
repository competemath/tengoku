import Tengoku.StringDiagramsLean.StringDiagrams.Super.Functor
import Tengoku.Seed.Algebra.DirectSum.Decomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Parity components of morphisms in a supercategory

For a supercategory in the sense of `StringDiagrams.Supercategory` (Brundan–Ellis,
*Monoidal supercategories*, arXiv:1603.05928v3, Definition 1.1(i)), every morphism decomposes
uniquely as `f = f₀ + f₁` with `fₚ` of parity `p`. This file packages that decomposition.

## Main definitions

* `Supercategory.sign R p`: the sign `(-1)^p ∈ R` of `p : ZMod 2`.
* `Supercategory.proj p`: the projection `f ↦ fₚ`, an `R`-linear map on each Hom-module.
* `Supercategory.twist p`: the map `f ↦ f₀ + (-1)^p f₁`; for homogeneous `f` it is
  multiplication by `(-1)^{p|f|}`. It is the sign that appears in the definition of a
  supernatural transformation of parity `p` (Definition 1.1(iii)).

## Main statements

* `Supercategory.proj_add_proj`: `f = f₀ + f₁`.
* `Supercategory.induction_on`: induction on morphisms via homogeneous ones.
* `Supercategory.twist_comp`: `twist p` is compatible with composition.
* `Supercategory.inv_mem`: the inverse of a homogeneous isomorphism is homogeneous of the same
  parity.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w w₁ w₂

namespace Supercategory

/-! ## Signs -/

section Sign

variable (R : Type w) [CommRing R]

/-- The sign `(-1)^p` of a parity `p : ZMod 2`.-/
def sign (p : ZMod 2) : R := if p = 0 then 1 else -1

/--
@isnad1 id=eq.0h1v.s6.272f04a8e907 from=translated src=- shape=0233a910 vocab=61e05722
-/
@[simp] theorem sign_zero : sign R 0 = 1 := rfl

/--
@isnad1 id=eq.0h1v.s6.b7491ccdf90f from=translated src=- shape=253466b5 vocab=26cc08c4
-/
@[simp] theorem sign_one : sign R 1 = -1 := ite_eq_right (by decide)

variable {R}

/--
@isnad1 id=eq.0h1v.s7.dd8a2a9e100c from=translated src=- shape=3d23854a vocab=014cf724
-/
theorem zmod2_add_self (p : ZMod 2) : p + p = 0 := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;> rfl

/--
@isnad1 id=ne.0h1v.s7.3b13b517c9db from=translated src=- shape=411374f6 vocab=014cf724
-/
theorem zmod2_add_one_ne (p : ZMod 2) : p + 1 ≠ p := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;> decide

/--
@isnad1 id=eq.0h3v.s6.7ced881f7bd3 from=translated src=- shape=a9f596b0 vocab=61e69f72
-/
theorem sign_add (p q : ZMod 2) : sign R (p + q) = sign R p * sign R q := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    simp [sign, show (1 : ZMod 2) + 1 = 0 from rfl, show ¬((1 : ZMod 2) = 0) by decide]

/-- The sign `(-1)^{pq}` is the Koszul sign.
@isnad1 id=eq.0h3v.s6.17eb9a2bfdb0 from=translated src=- shape=3ac38e54 vocab=b5d3dbda
-/
theorem sign_mul (p q : ZMod 2) : sign R (p * q) = (koszulSign p q : R) := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    simp [sign, show ¬((1 : ZMod 2) = 0) by decide]

/--
@isnad1 id=eq.0h5v.s7.f25415a10a60 from=translated src=- shape=c80bf9b5 vocab=7dfd2ee4
-/
theorem koszulSign_smul {M : Type*} [AddCommGroup M] [Module R M] (p q : ZMod 2) (x : M) :
    koszulSign p q • x = sign R (p * q) • x := by
  rw [sign_mul, Int.cast_smul_eq_zsmul]

/--
@isnad1 id=eq.0h2v.s5.19d5b0a2732b from=translated src=- shape=aa71e0d1 vocab=fc8a84af
-/
theorem sign_mul_self (p : ZMod 2) : sign R p * sign R p = 1 := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;> simp [sign, show ¬((1 : ZMod 2) = 0) by decide]

/--
@isnad1 id=eq.0h4v.s7.93bc0ed0b657 from=translated src=- shape=1a329432 vocab=12c7be7c
-/
@[simp] theorem sign_smul_sign_smul {M : Type*} [AddCommGroup M] [Module R M] (p : ZMod 2)
    (x : M) : sign R p • sign R p • x = x := by
  rw [smul_smul, sign_mul_self, one_smul]

end Sign

/-! ## Parity projections -/

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C]

variable (R) in
/-- The decomposition of a Hom-module into its even and odd parts.-/
@[instance_reducible]
def decomposition (X Y : C) : DirectSum.Decomposition (parity (R := R) X Y) :=
  (isInternal X Y).chooseDecomposition

variable (R) in
/-- The parity-`p` component `f ↦ fₚ` of morphisms `X ⟶ Y`.-/
def proj (p : ZMod 2) {X Y : C} : (X ⟶ Y) →ₗ[R] (X ⟶ Y) :=
  letI := decomposition R X Y
  (parity (R := R) X Y p).subtype ∘ₗ
    (DirectSum.component R (ZMod 2) (fun q => parity (R := R) X Y q) p) ∘ₗ
      (DirectSum.decomposeLinearEquiv (parity (R := R) X Y)).toLinearMap

/--
@isnad1 id=eq.0h6v.s12.27ce106723b8 from=translated src=- shape=a5db5e61 vocab=2a0ac509
-/
theorem proj_apply (p : ZMod 2) {X Y : C} (f : X ⟶ Y) :
    letI := decomposition R X Y
    proj R p f = (DirectSum.decompose (parity (R := R) X Y) f p : X ⟶ Y) := rfl

/--
@isnad1 id=mem.0h6v.s8.4dbe9f546483 from=translated src=- shape=08a764f7 vocab=6eb6913c
-/
theorem proj_mem (p : ZMod 2) {X Y : C} (f : X ⟶ Y) : proj R p f ∈ parity (R := R) X Y p :=
  letI := decomposition R X Y
  (DirectSum.decompose (parity (R := R) X Y) f p).2

/--
@isnad1 id=eq.1h6v.s8.67195570d476 from=translated src=- shape=baceb886 vocab=6eb6913c
-/
theorem proj_of_mem {p : ZMod 2} {X Y : C} {f : X ⟶ Y} (hf : f ∈ parity (R := R) X Y p) :
    proj R p f = f :=
  letI := decomposition R X Y
  DirectSum.decompose_of_mem_same _ hf

/--
@isnad1 id=eq.2h7v.s9.8c99c360d91f from=translated src=- shape=bb629bd6 vocab=6eb6913c
-/
theorem proj_of_mem_ne {p q : ZMod 2} {X Y : C} {f : X ⟶ Y} (hf : f ∈ parity (R := R) X Y q)
    (h : q ≠ p) : proj R p f = 0 :=
  letI := decomposition R X Y
  DirectSum.decompose_of_mem_ne _ hf h

/-- Induction on morphisms: a property closed under `0` and `+` holds for all morphisms if it
holds for homogeneous ones.
@isnad1 id=var.0h9v.s8.72e025f845a9 from=translated src=- shape=d58ae676 vocab=a6b07b58
-/
@[elab_as_elim]
theorem induction_on {X Y : C} {P : (X ⟶ Y) → Prop} (f : X ⟶ Y) (zero : P 0)
    (hom : ∀ (p : ZMod 2) (g : X ⟶ Y), g ∈ parity (R := R) X Y p → P g)
    (add : ∀ g h, P g → P h → P (g + h)) : P f :=
  letI := decomposition R X Y
  DirectSum.Decomposition.inductionOn (parity (R := R) X Y) zero (fun g => hom _ _ g.2) add f

/--
@isnad1 id=iff.0h6v.s8.f3a4d55fae13 from=translated src=- shape=03d95463 vocab=6eb6913c
-/
theorem mem_iff_proj {p : ZMod 2} {X Y : C} {f : X ⟶ Y} :
    f ∈ parity (R := R) X Y p ↔ proj R p f = f :=
  ⟨proj_of_mem, fun h => h ▸ proj_mem p f⟩

/--
@isnad1 id=eq.0h6v.s9.33f673b63922 from=translated src=- shape=1895b420 vocab=5f30c0fc
-/
theorem proj_proj (p : ZMod 2) {X Y : C} (f : X ⟶ Y) : proj R p (proj R p f) = proj R p f :=
  proj_of_mem (proj_mem p f)

/--
@isnad1 id=eq.1h7v.s9.e2f278c9ec08 from=translated src=- shape=7ad74b94 vocab=5f30c0fc
-/
theorem proj_proj_of_ne {p q : ZMod 2} (h : q ≠ p) {X Y : C} (f : X ⟶ Y) :
    proj R p (proj R q f) = 0 :=
  proj_of_mem_ne (proj_mem q f) h

/--
@isnad1 id=eq.0h5v.s9.d4a89725401c from=translated src=- shape=17a15257 vocab=75ce6192
-/
theorem proj_add_proj {X Y : C} (f : X ⟶ Y) : proj R 0 f + proj R 1 f = f := by
  refine induction_on (R := R) f (by simp) (fun p g hg => ?_) (fun g h hg hh => ?_)
  · rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [proj_of_mem hg, proj_of_mem_ne hg (by decide), add_zero]
    · rw [proj_of_mem hg, proj_of_mem_ne hg (by decide), zero_add]
  · rw [map_add, map_add, add_add_add_comm, hg, hh]

/--
@isnad1 id=eq.0h6v.s9.b0b0c4ca3855 from=translated src=- shape=4bd413c4 vocab=75ce6192
-/
theorem proj_add_proj_add_one (s : ZMod 2) {X Y : C} (f : X ⟶ Y) :
    proj R s f + proj R (s + 1) f = f := by
  rcases parity_eq_zero_or_one s with rfl | rfl
  · exact proj_add_proj f
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl, add_comm]; exact proj_add_proj f

/-- The components are characterized by homogeneity: if `f = g + h` with `g` of parity `p` and
`h` of parity `p + 1`, then `fₚ = g`.
@isnad1 id=eq.3h8v.s9.4b7adea93a7c from=translated src=- shape=76c9b0e3 vocab=652040f1
-/
theorem proj_eq_of_add {p : ZMod 2} {X Y : C} {f g h : X ⟶ Y} (e : f = g + h)
    (hg : g ∈ parity (R := R) X Y p) (hh : h ∈ parity (R := R) X Y (p + 1)) : proj R p f = g := by
  rw [e, map_add, proj_of_mem hg, proj_of_mem_ne hh (zmod2_add_one_ne p), add_zero]

/-- Two morphisms are equal if all their parity components are.
@isnad1 id=eq.1h6v.s9.26245c0bbe07 from=translated src=- shape=98705216 vocab=5f30c0fc
-/
theorem ext_proj {X Y : C} {f g : X ⟶ Y} (h : ∀ p, proj R p f = proj R p g) : f = g := by
  rw [← proj_add_proj (R := R) f, ← proj_add_proj (R := R) g, h, h]

/--
@isnad1 id=eq.1h9v.s9.6c941c861a70 from=translated src=- shape=6fccd9e3 vocab=638de41b
-/
theorem proj_comp_of_mem_left {p : ZMod 2} (q : ZMod 2) {X Y Z : C} {f : X ⟶ Y}
    (hf : f ∈ parity (R := R) X Y p) (g : Y ⟶ Z) :
    proj R (p + q) (f ≫ g) = f ≫ proj R q g := by
  refine induction_on (R := R) g (by simp) (fun r g hg => ?_) (fun g h hg hh => ?_)
  · by_cases h : r = q
    · subst h; rw [proj_of_mem (comp_mem hf hg), proj_of_mem hg]
    · rw [proj_of_mem_ne (comp_mem hf hg) (fun e => h (add_left_cancel e)),
        proj_of_mem_ne hg h, Limits.comp_zero]
  · rw [Preadditive.comp_add, map_add, hg, hh, map_add, Preadditive.comp_add]

/--
@isnad1 id=eq.1h9v.s9.2dbba0bbea84 from=translated src=- shape=42dced71 vocab=638de41b
-/
theorem proj_comp_of_mem_right (p : ZMod 2) {q : ZMod 2} {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z}
    (hg : g ∈ parity (R := R) Y Z q) :
    proj R (p + q) (f ≫ g) = proj R p f ≫ g := by
  refine induction_on (R := R) f (by simp) (fun r f hf => ?_) (fun f h hf hh => ?_)
  · by_cases h : r = p
    · subst h; rw [proj_of_mem (comp_mem hf hg), proj_of_mem hf]
    · rw [proj_of_mem_ne (comp_mem hf hg) (fun e => h (add_right_cancel e)),
        proj_of_mem_ne hf h, Limits.zero_comp]
  · rw [Preadditive.add_comp, map_add, hf, hh, map_add, Preadditive.add_comp]

/--
@isnad1 id=eq.0h4v.s8.517aa47f8de9 from=translated src=- shape=61d3e0de vocab=6eefd0f0
-/
theorem proj_id (X : C) (p : ZMod 2) : proj R p (𝟙 X) = if p = 0 then 𝟙 X else 0 := by
  split_ifs with h
  · subst h; exact proj_of_mem (id_mem X)
  · exact proj_of_mem_ne (id_mem X) (Ne.symm h)

/-- The inverse of a homogeneous isomorphism is homogeneous of the same parity.
@isnad1 id=mem.1h6v.s8.9409ea4cf937 from=translated src=- shape=cfd58698 vocab=d77d1256
-/
theorem inv_mem {p : ZMod 2} {X Y : C} (e : X ≅ Y) (he : e.hom ∈ parity (R := R) X Y p) :
    e.inv ∈ parity (R := R) Y X p := by
  have key : proj R (p + 1) e.inv = 0 := by
    have h1 : e.hom ≫ proj R (p + 1) e.inv = 0 := by
      rw [← proj_comp_of_mem_left _ he, e.hom_inv_id, proj_id,
        ite_eq_right (by rcases parity_eq_zero_or_one p with rfl | rfl <;> decide)]
    calc proj R (p + 1) e.inv = e.inv ≫ e.hom ≫ proj R (p + 1) e.inv := by
          rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
      _ = 0 := by rw [h1, Limits.comp_zero]
  have h := proj_add_proj (R := R) e.inv
  rcases parity_eq_zero_or_one p with rfl | rfl
  · have : proj R 1 e.inv = 0 := key
    rw [this, add_zero] at h
    exact h ▸ proj_mem _ _
  · have : proj R 0 e.inv = 0 := key
    rw [this, zero_add] at h
    exact h ▸ proj_mem _ _

/-! ## The twist `f₀ + (-1)^p f₁` -/

variable (R) in
/-- The map `f ↦ f₀ + (-1)^p f₁`.-/
def twist (p : ZMod 2) {X Y : C} : (X ⟶ Y) →ₗ[R] (X ⟶ Y) := proj R 0 + sign R p • proj R 1

/--
@isnad1 id=eq.0h6v.s10.42b79fa0ac1b from=translated src=- shape=5368eed1 vocab=55e5436b
-/
theorem twist_apply (p : ZMod 2) {X Y : C} (f : X ⟶ Y) :
    twist R p f = proj R 0 f + sign R p • proj R 1 f := rfl

/--
@isnad1 id=eq.1h7v.s9.a6070dd36529 from=translated src=- shape=deab2189 vocab=42f72b3b
-/
theorem twist_of_mem (p : ZMod 2) {q : ZMod 2} {X Y : C} {f : X ⟶ Y}
    (hf : f ∈ parity (R := R) X Y q) : twist R p f = sign R (p * q) • f := by
  rw [twist_apply]
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [proj_of_mem hf, proj_of_mem_ne hf (by decide)]; simp
  · rw [proj_of_mem hf, proj_of_mem_ne hf (by decide)]; simp

/--
@isnad1 id=eq.0h5v.s8.8160d8d6c5ad from=translated src=- shape=c169a433 vocab=cc15c37e
-/
@[simp] theorem twist_zero {X Y : C} (f : X ⟶ Y) : twist R 0 f = f := by
  rw [twist_apply, sign_zero, one_smul, proj_add_proj]

/--
@isnad1 id=mem.1h7v.s9.89408c4bb180 from=translated src=- shape=dd8574df vocab=dc4dcded
-/
theorem twist_mem (p : ZMod 2) {q : ZMod 2} {X Y : C} {f : X ⟶ Y}
    (hf : f ∈ parity (R := R) X Y q) : twist R p f ∈ parity (R := R) X Y q := by
  rw [twist_of_mem p hf]; exact Submodule.smul_mem _ _ hf

/--
@isnad1 id=eq.0h6v.s9.3d9a77d8ba15 from=translated src=- shape=de68c896 vocab=cc15c37e
-/
theorem twist_twist (p : ZMod 2) {X Y : C} (f : X ⟶ Y) : twist R p (twist R p f) = f := by
  refine induction_on (R := R) f (by simp) (fun q g hg => ?_) (fun g h hg hh => ?_)
  · rw [twist_of_mem p hg, map_smul, twist_of_mem p hg, sign_smul_sign_smul]
  · rw [map_add, map_add, hg, hh]

/--
@isnad1 id=eq.0h7v.s9.71ba7cb5bb0c from=translated src=- shape=9f8dea6d vocab=f7e871ab
-/
theorem twist_add (p q : ZMod 2) {X Y : C} (f : X ⟶ Y) :
    twist R (p + q) f = twist R p (twist R q f) := by
  refine induction_on (R := R) f (by simp) (fun r g hg => ?_) (fun g h hg hh => ?_)
  · rw [twist_of_mem _ hg, twist_of_mem q hg, map_smul, twist_of_mem p hg, smul_smul, add_mul,
      sign_add, mul_comm]
  · rw [map_add, map_add, map_add, hg, hh]

/--
@isnad1 id=eq.0h8v.s9.79f48fe3cc86 from=translated src=- shape=558fd761 vocab=ebd16137
-/
theorem twist_comp (p : ZMod 2) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    twist R p (f ≫ g) = twist R p f ≫ twist R p g := by
  refine induction_on (R := R) f (by simp) (fun q f hf => ?_) (fun f h hf hh => ?_)
  · refine induction_on (R := R) g (by simp) (fun r g hg => ?_) (fun g h hg hh => ?_)
    · rw [twist_of_mem p (comp_mem hf hg), twist_of_mem p hf, twist_of_mem p hg,
        Linear.smul_comp, Linear.comp_smul, smul_smul, mul_add, sign_add, mul_comm]
    · rw [Preadditive.comp_add, map_add, hg, hh, map_add, Preadditive.comp_add]
  · rw [Preadditive.add_comp, map_add, hf, hh, map_add, Preadditive.add_comp]

/--
@isnad1 id=eq.0h4v.s8.8b915fbf4f5f from=translated src=- shape=714acf79 vocab=5dc9af6a
-/
@[simp] theorem twist_id (p : ZMod 2) (X : C) : twist R p (𝟙 X) = 𝟙 X := by
  rw [twist_of_mem p (id_mem X), mul_zero, sign_zero, one_smul]

/--
@isnad1 id=eq.1h6v.s9.b2e30dd24639 from=translated src=- shape=702ffb3e vocab=6088541c
-/
theorem twist_one_of_mem {q : ZMod 2} {X Y : C} {f : X ⟶ Y} (hf : f ∈ parity (R := R) X Y q) :
    twist R 1 f = sign R q • f := by
  rw [twist_of_mem 1 hf, one_mul]

/--
@isnad1 id=eq.0h7v.s10.4a06303808e0 from=translated src=- shape=9252d746 vocab=63a228cd
-/
theorem proj_twist (p q : ZMod 2) {X Y : C} (f : X ⟶ Y) :
    proj R q (twist R p f) = sign R (p * q) • proj R q f := by
  refine induction_on (R := R) f (by simp) (fun r g hg => ?_) (fun g h hg hh => ?_)
  · rw [twist_of_mem p hg, map_smul]
    by_cases h : r = q
    · subst h; rfl
    · rw [proj_of_mem_ne hg h, smul_zero, smul_zero]
  · rw [map_add, map_add, hg, hh, map_add, smul_add]

end Supercategory

end StringDiagrams

end
