import Tengoku.StringDiagramsLean.StringDiagrams.Super.MonoidalPi
import Tengoku.Seed.LinearAlgebra.TensorProduct.Basic
import Tengoku.Seed.LinearAlgebra.Projection
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions
import Tengoku.Seed.LinearAlgebra.Dimension.Free
import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The supercategory of superspaces

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
§1.2, Examples 1.2(i), 1.5(i), 1.8 and 1.13(i), over a commutative ground ring `k` (as in §2 of
the paper; §1 works over a field of characteristic different from `2`).

A *superspace* is a `ℤ/2`-graded `k`-module `V = V₀ ⊕ V₁`. We record the grading by the
projection `V.odd : V → V` onto `V₁` along `V₀` (an idempotent linear map); the homogeneous
components are `V.part p` (`isInternal_part`), and conversely every decomposition of a module
into two complementary submodules defines a superspace (`SVec.ofIsCompl`, `SVec.ofProd`).

## The supercategory `SVec`

Morphisms `V ⟶ W` in `SVec k` are *all* `k`-linear maps. A linear map is even (resp. odd) if
it preserves (resp. reverses) parity; every linear map is uniquely the sum of an even and an odd
map (`homProj`), which makes `SVec k` a supercategory (Example 1.2(i),
`SVec.instSupercategory`). Its underlying category of even maps is
`Underlying k (SVec k)`.

## The monoidal supercategory `SVec`

The tensor product of superspaces is the tensor product of modules with
`(V ⊗ W)₀ = V₀ ⊗ W₀ ⊕ V₁ ⊗ W₁` and `(V ⊗ W)₁ = V₀ ⊗ W₁ ⊕ V₁ ⊗ W₀`. The tensor product of
linear maps carries the Koszul sign `(f ⊗ g)(v ⊗ w) = (-1)^{|g||v|} f(v) ⊗ g(w)`
(`superTensorHom_tmul`); in whiskering form `(1_V ⊗ g)(v ⊗ w) = (-1)^{|g||v|} v ⊗ g(w)`
(`whiskerLeft_tmul`) and `(f ⊗ 1_W)(v ⊗ w) = f(v) ⊗ w` (`whiskerRight_tmul`). With the unit
object `k` (even) and the associator and unitors of `TensorProduct`, `SVec k` is a monoidal
supercategory (Example 1.5(i), `SVec.instMonoidalSupercategory`); the composition rule (1.1) is
`MonoidalSupercategory.superTensorHom_comp_superTensorHom`.

## Parity shift

`Π V` is `V` with the opposite grading and `ζ_V : Π V → V` the identity function, an odd
isomorphism; this makes `SVec k` a Π-supercategory (Example 1.8 with `A = B = k`,
`SVec.instPiSupercategory`), with `Π f = (-1)^{|f|} f` (`pi_map_of_mem`) and `ξ_V = -1`
(`ξ_hom`). With `π := Π k` and `ζ : Π k → k` the identity function, `SVec k` is a monoidal
Π-supercategory (Example 1.13(i) for `A = k`, `SVec.instMonoidalPiSupercategory`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory TensorProduct

universe u

/-- A superspace over `k` (Brundan–Ellis, §1.2): a `k`-module with a `ℤ/2`-grading, recorded by
the projection `odd` onto the odd part along the even part.-/
structure SVec (k : Type u) [CommRing k] where
  /-- The underlying module.-/
  carrier : Type u
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module k carrier]
  /-- The projection onto the odd part.-/
  odd : carrier →ₗ[k] carrier
  odd_comp_odd : odd ∘ₗ odd = odd

namespace SVec

variable {k : Type u} [CommRing k]

instance : CoeSort (SVec k) (Type u) := ⟨SVec.carrier⟩

attribute [instance] isAddCommGroup isModule

/-! ## Homogeneous components -/

/--
@isnad1 id=eq.0h0v.s7.6ce499010dad from=translated src=- shape=21086a1f vocab=014cf724
-/
@[simp] theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := rfl

section Proj

variable (V : SVec k)

/-- The projection `V → V_p` onto the component of parity `p`.-/
def proj (p : ZMod 2) : V →ₗ[k] V := if p = 0 then LinearMap.id - V.odd else V.odd

/--
@isnad1 id=eq.0h2v.s8.520f63ef00f0 from=translated src=- shape=945dab71 vocab=1e9f736e
-/
theorem proj_zero : V.proj 0 = LinearMap.id - V.odd := ite_eq_left rfl

/--
@isnad1 id=eq.0h2v.s7.a9ec0fdea83b from=translated src=- shape=35a12ff3 vocab=5e59295b
-/
theorem proj_one : V.proj 1 = V.odd := ite_eq_right (by decide)

/--
@isnad1 id=eq.0h3v.s8.c2dc98a0152d from=translated src=- shape=5c166399 vocab=1a73054c
-/
theorem odd_apply_odd (v : V) : V.odd (V.odd v) = V.odd v :=
  LinearMap.congr_fun V.odd_comp_odd v

/--
@isnad1 id=eq.0h2v.s8.6c0c7dc81144 from=translated src=- shape=4a4ed09c vocab=2157aa4e
-/
theorem proj_add_proj : V.proj 0 + V.proj 1 = LinearMap.id := by simp [proj_zero, proj_one]

/--
@isnad1 id=eq.0h3v.s8.bd7df7e570cc from=translated src=- shape=e1977d19 vocab=53efb728
-/
theorem proj_apply_add (v : V) : V.proj 0 v + V.proj 1 v = v := by
  simp [proj_zero, proj_one]

/--
@isnad1 id=eq.0h3v.s7.8a299e61bbd6 from=translated src=- shape=8b5f449d vocab=95595c8d
-/
theorem proj_comp_proj_self (p : ZMod 2) : V.proj p ∘ₗ V.proj p = V.proj p := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · ext v; simp [proj_zero, odd_apply_odd]
  · simpa [proj_one] using V.odd_comp_odd

/--
@isnad1 id=eq.0h3v.s8.2c15c20ea300 from=translated src=- shape=63964579 vocab=483000c8
-/
theorem proj_comp_proj_add_one (p : ZMod 2) : V.proj p ∘ₗ V.proj (p + 1) = 0 := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · ext v; simp [proj_zero, proj_one, odd_apply_odd]
  · ext v; simp [proj_zero, proj_one, odd_apply_odd]

/--
@isnad1 id=eq.1h4v.s8.b1739d0c673e from=translated src=- shape=f32a2d06 vocab=95595c8d
-/
theorem proj_comp_proj_of_ne {p q : ZMod 2} (h : p ≠ q) : V.proj p ∘ₗ V.proj q = 0 := by
  have : q = p + 1 := by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      rcases parity_eq_zero_or_one q with rfl | rfl <;> simp_all
  subst this; exact proj_comp_proj_add_one V p

/--
@isnad1 id=eq.0h4v.s8.a3ac31277356 from=translated src=- shape=e145c93b vocab=c984b572
-/
theorem proj_proj_apply (p : ZMod 2) (v : V) : V.proj p (V.proj p v) = V.proj p v :=
  LinearMap.congr_fun (proj_comp_proj_self V p) v

/--
@isnad1 id=eq.1h5v.s8.8e2f20cc746a from=translated src=- shape=6451d348 vocab=c984b572
-/
theorem proj_proj_apply_of_ne {p q : ZMod 2} (h : p ≠ q) (v : V) :
    V.proj p (V.proj q v) = 0 :=
  LinearMap.congr_fun (proj_comp_proj_of_ne V h) v

/--
@isnad1 id=eq.0h3v.s8.d062a4aa9933 from=translated src=- shape=a8cad7ff vocab=c984b572
-/
@[simp] theorem proj_zero_proj_one (v : V) : V.proj 0 (V.proj 1 v) = 0 :=
  proj_proj_apply_of_ne V (by decide) v

/--
@isnad1 id=eq.0h3v.s8.b5f7d6eed58b from=translated src=- shape=a8cad7ff vocab=c984b572
-/
@[simp] theorem proj_one_proj_zero (v : V) : V.proj 1 (V.proj 0 v) = 0 :=
  proj_proj_apply_of_ne V (by decide) v

/--
@isnad1 id=eq.0h4v.s8.a9ccd66676f9 from=translated src=- shape=27315460 vocab=53efb728
-/
theorem proj_apply_add' (q : ZMod 2) (v : V) : V.proj q v + V.proj (q + 1) v = v := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · exact proj_apply_add V v
  · rw [add_comm]; exact proj_apply_add V v

/-- The homogeneous component `V_p`.-/
def part (p : ZMod 2) : Submodule k V := LinearMap.range (V.proj p)

/--
@isnad1 id=iff.0h4v.s7.ff5d3e3c947e from=translated src=- shape=035a3058 vocab=292084ab
-/
theorem mem_part_iff {p : ZMod 2} {v : V} : v ∈ V.part p ↔ V.proj p v = v := by
  constructor
  · rintro ⟨w, rfl⟩; exact proj_proj_apply V p w
  · intro h; exact ⟨v, h⟩

/--
@isnad1 id=mem.0h4v.s7.24716acb003d from=translated src=- shape=37af9204 vocab=292084ab
-/
theorem proj_mem_part (p : ZMod 2) (v : V) : V.proj p v ∈ V.part p := ⟨v, rfl⟩

/--
@isnad1 id=eq.1h5v.s8.641a4a12e6f2 from=translated src=- shape=4681faff vocab=fd7f0662
-/
theorem proj_apply_of_mem_part {p q : ZMod 2} {v : V} (hv : v ∈ V.part q) :
    V.proj p v = if p = q then v else 0 := by
  obtain ⟨w, rfl⟩ := hv
  split_ifs with h
  · subst h; exact proj_proj_apply V p w
  · exact proj_proj_apply_of_ne V h w

/--
@isnad1 id=iff.0h3v.s8.8cc5dd1d95b3 from=translated src=- shape=7e901bb0 vocab=189143fa
-/
theorem mem_part_zero_iff {v : V} : v ∈ V.part 0 ↔ V.odd v = 0 := by
  rw [mem_part_iff, proj_zero, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_self]

/--
@isnad1 id=iff.0h3v.s8.fd3a457605bd from=translated src=- shape=dcf266bf vocab=189143fa
-/
theorem mem_part_one_iff {v : V} : v ∈ V.part 1 ↔ V.odd v = v := by
  rw [mem_part_iff, proj_one]

/-- A superspace is the direct sum of its even and odd parts.
@isnad1 id=isintern.0h2v.s6.d3b83ab2ceaa from=translated src=- shape=7a44e824 vocab=30412f1e
-/
theorem isInternal_part : DirectSum.IsInternal V.part := by
  rw [DirectSum.isInternal_submodule_iff_isCompl V.part (i := 0) (j := 1) (by decide)
    (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
  constructor
  · rw [Submodule.disjoint_def]
    intro v h0 h1
    rw [mem_part_iff] at h0 h1
    rw [← h0, ← h1, proj_proj_apply_of_ne V (by decide)]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [← proj_apply_add V v]
    exact Submodule.add_mem_sup (proj_mem_part V 0 v) (proj_mem_part V 1 v)

end Proj

/-! ## Constructions of superspaces -/

/-- The superspace with even part `V₀` and odd part `V₁`: the module `V₀ × V₁`.-/
def ofProd (V₀ V₁ : Type u) [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁] [Module k V₁] :
    SVec k where
  carrier := V₀ × V₁
  odd := LinearMap.inr k V₀ V₁ ∘ₗ LinearMap.snd k V₀ V₁
  odd_comp_odd := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=mem.0h4v.s8.78789cd290a0 from=translated src=- shape=4c69a00c vocab=00e85ea5
-/
theorem ofProd_mem_part_zero {V₀ V₁ : Type u} [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁]
    [Module k V₁] (v : V₀) : ((v, 0) : ofProd (k := k) V₀ V₁) ∈ (ofProd (k := k) V₀ V₁).part 0 := by
  rw [mem_part_zero_iff]; simp [ofProd]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=mem.0h4v.s8.0d2973835aab from=translated src=- shape=7d9ff915 vocab=00e85ea5
-/
theorem ofProd_mem_part_one {V₀ V₁ : Type u} [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁]
    [Module k V₁] (v : V₁) : ((0, v) : ofProd (k := k) V₀ V₁) ∈ (ofProd (k := k) V₀ V₁).part 1 := by
  rw [mem_part_one_iff]; simp [ofProd]

/-- The superspace structure on a module given by complementary submodules `M₀`, `M₁`
(even and odd parts).-/
def ofIsCompl (M : Type u) [AddCommGroup M] [Module k M] (M₀ M₁ : Submodule k M)
    (h : IsCompl M₀ M₁) : SVec k where
  carrier := M
  odd := M₁.subtype ∘ₗ Submodule.projectionOnto M₁ M₀ h.symm
  odd_comp_odd := by
    ext v
    simp

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h4v.s7.06711f0461ab from=translated src=- shape=67932dac vocab=1b7cd5b9
-/
theorem ofIsCompl_part_one (M : Type u) [AddCommGroup M] [Module k M] (M₀ M₁ : Submodule k M)
    (h : IsCompl M₀ M₁) : (ofIsCompl M M₀ M₁ h).part 1 = M₁ := by
  ext v
  rw [mem_part_one_iff]
  simp only [ofIsCompl, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
  constructor
  · intro hv; rw [← hv]; exact Submodule.coe_mem _
  · intro hv; rw [Submodule.projectionOnto_apply_left h.symm ⟨v, hv⟩]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h4v.s7.7f11a282ed9f from=translated src=- shape=6f171ff8 vocab=1b7cd5b9
-/
theorem ofIsCompl_part_zero (M : Type u) [AddCommGroup M] [Module k M] (M₀ M₁ : Submodule k M)
    (h : IsCompl M₀ M₁) : (ofIsCompl M M₀ M₁ h).part 0 = M₀ := by
  ext v
  rw [mem_part_zero_iff]
  simp only [ofIsCompl, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    ZeroMemClass.coe_eq_zero]
  exact Submodule.projectionOnto_apply_eq_zero_iff h.symm

/-! ## The supercategory `SVec` -/

instance : Category (SVec k) where
  Hom V W := V →ₗ[k] W
  id V := LinearMap.id
  comp f g := g ∘ₗ f

instance {V W : SVec k} : FunLike (V ⟶ W) V W := LinearMap.instFunLike

instance {V W : SVec k} : LinearMapClass (V ⟶ W) k V W := LinearMap.semilinearMapClass

/-- A linear map, as a morphism of `SVec k`.-/
def ofHom {V W : SVec k} (f : V →ₗ[k] W) : V ⟶ W := f

/-- The linear map underlying a morphism of `SVec k`.-/
def toLinearMap {V W : SVec k} (f : V ⟶ W) : V →ₗ[k] W := f

/--
@isnad1 id=eq.0h4v.s7.26664638dec8 from=translated src=- shape=63ce4ff5 vocab=0890aaaa
-/
@[simp] theorem toLinearMap_ofHom {V W : SVec k} (f : V →ₗ[k] W) : toLinearMap (ofHom f) = f :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.9c8f37944fd6 from=translated src=- shape=dee64e78 vocab=95fe1f1c
-/
@[simp] theorem ofHom_toLinearMap {V W : SVec k} (f : V ⟶ W) : ofHom (toLinearMap f) = f := rfl

/--
@isnad1 id=eq.0h4v.s7.40f0501e085a from=translated src=- shape=0047c2cd vocab=e47e4259
-/
@[simp] theorem coe_toLinearMap {V W : SVec k} (f : V ⟶ W) : ⇑(toLinearMap f) = ⇑f := rfl

/--
@isnad1 id=eq.0h5v.s7.f8adae99c0f0 from=translated src=- shape=8bc2615e vocab=efee97c3
-/
@[simp] theorem ofHom_apply {V W : SVec k} (f : V →ₗ[k] W) (v : V) : ofHom f v = f v := rfl

/--
@isnad1 id=eq.1h5v.s7.caf651fe9b59 from=translated src=- shape=d0b6abd7 vocab=9611f0ab
-/
@[ext] theorem hom_ext {V W : SVec k} {f g : V ⟶ W} (h : ∀ v, f v = g v) : f = g :=
  LinearMap.ext h

/--
@isnad1 id=eq.0h3v.s6.b42042f767da from=translated src=- shape=87ba62e3 vocab=8b4f55d5
-/
@[simp] theorem id_apply (V : SVec k) (v : V) : (𝟙 V : V ⟶ V) v = v := rfl

/--
@isnad1 id=eq.0h7v.s7.72e9185382f4 from=translated src=- shape=6a74cf2c vocab=da4999af
-/
@[simp] theorem comp_apply {U V W : SVec k} (f : U ⟶ V) (g : V ⟶ W) (u : U) :
    (f ≫ g) u = g (f u) := rfl

/--
@isnad1 id=eq.0h6v.s7.291f1f33f749 from=translated src=- shape=92a01de1 vocab=cb3306c4
-/
theorem toLinearMap_comp {U V W : SVec k} (f : U ⟶ V) (g : V ⟶ W) :
    toLinearMap (f ≫ g) = toLinearMap g ∘ₗ toLinearMap f := rfl

/--
@isnad1 id=eq.0h2v.s6.9e21817532c2 from=translated src=- shape=67df7650 vocab=e8d51278
-/
@[simp] theorem toLinearMap_id (V : SVec k) : toLinearMap (𝟙 V) = LinearMap.id := rfl

instance : Preadditive (SVec k) where
  homGroup V W := inferInstanceAs (AddCommGroup (V →ₗ[k] W))
  add_comp _ _ _ _ _ _ := LinearMap.comp_add _ _ _
  comp_add _ _ _ _ _ _ := LinearMap.add_comp _ _ _

instance : Linear k (SVec k) where
  homModule V W := inferInstanceAs (Module k (V →ₗ[k] W))
  smul_comp _ _ _ r f g := LinearMap.comp_smul g r f
  comp_smul _ _ _ f r g := LinearMap.smul_comp r g f

/--
@isnad1 id=eq.0h6v.s8.c3af57e0b8bc from=translated src=- shape=43d223f3 vocab=d3bd3473
-/
@[simp] theorem add_apply {V W : SVec k} (f g : V ⟶ W) (v : V) : (f + g) v = f v + g v := rfl

/--
@isnad1 id=eq.0h6v.s8.614a46e6c1e9 from=translated src=- shape=43d223f3 vocab=8d57446a
-/
@[simp] theorem sub_apply {V W : SVec k} (f g : V ⟶ W) (v : V) : (f - g) v = f v - g v := rfl

/--
@isnad1 id=eq.0h5v.s8.a12dd4d8b998 from=translated src=- shape=ac9d99b8 vocab=a1eb96ae
-/
@[simp] theorem neg_apply {V W : SVec k} (f : V ⟶ W) (v : V) : (-f) v = -f v := rfl

/--
@isnad1 id=eq.0h4v.s7.014eae1af109 from=translated src=- shape=b9dab785 vocab=9611f0ab
-/
@[simp] theorem zero_apply {V W : SVec k} (v : V) : (0 : V ⟶ W) v = 0 := rfl

/--
@isnad1 id=eq.0h6v.s9.61d6d93ca023 from=translated src=- shape=810d384f vocab=37b439d5
-/
@[simp] theorem smul_apply {V W : SVec k} (r : k) (f : V ⟶ W) (v : V) : (r • f) v = r • f v :=
  rfl

/--
@isnad1 id=eq.0h6v.s8.7da79afa3806 from=translated src=- shape=a20f4426 vocab=d1437a46
-/
@[simp] theorem zsmul_apply {V W : SVec k} (n : ℤ) (f : V ⟶ W) (v : V) : (n • f) v = n • f v :=
  rfl

/--
@isnad1 id=eq.0h5v.s9.9245b61886ce from=translated src=- shape=5aa476b9 vocab=cb5fd42a
-/
@[simp] theorem toLinearMap_add {V W : SVec k} (f g : V ⟶ W) :
    toLinearMap (f + g) = toLinearMap f + toLinearMap g := rfl

/--
@isnad1 id=eq.0h5v.s9.b39248dc8e58 from=translated src=- shape=f20a0e61 vocab=91db8c31
-/
@[simp] theorem toLinearMap_smul {V W : SVec k} (r : k) (f : V ⟶ W) :
    toLinearMap (r • f) = r • toLinearMap f := rfl

/-- A linear map `f : V → W` has parity `p` if it maps `V_q` to `W_{q+p}` for all `q`, i.e.
`f ∘ proj_q = proj_{q+p} ∘ f`.-/
def parityHom (V W : SVec k) (p : ZMod 2) : Submodule k (V ⟶ W) where
  carrier := {f | ∀ q, toLinearMap f ∘ₗ V.proj q = W.proj (q + p) ∘ₗ toLinearMap f}
  add_mem' {f g} hf hg q := by
    simp only [Set.mem_ofPred_eq, toLinearMap_add, LinearMap.add_comp, LinearMap.comp_add] at *
    rw [hf, hg]
  zero_mem' q := by ext; simp [toLinearMap]
  smul_mem' r f hf q := by
    simp only [Set.mem_ofPred_eq, toLinearMap_smul, LinearMap.smul_comp, LinearMap.comp_smul] at *
    rw [hf]

/--
@isnad1 id=eq.1h7v.s9.6fab48036217 from=translated src=- shape=e07fee8a vocab=4a260004
-/
theorem apply_proj_of_mem {V W : SVec k} {p : ZMod 2} {f : V ⟶ W} (hf : f ∈ parityHom V W p)
    (q : ZMod 2) (v : V) : f (V.proj q v) = W.proj (q + p) (f v) :=
  LinearMap.congr_fun (hf q) v

/-- A homogeneous linear map of parity `p` maps `V_q` to `W_{q+p}`.
@isnad1 id=mem.2h7v.s9.1042e8d1ed7e from=translated src=- shape=6bc9d34a vocab=ef4fb37a
-/
theorem apply_mem_part {V W : SVec k} {p q : ZMod 2} {f : V ⟶ W} (hf : f ∈ parityHom V W p)
    {v : V} (hv : v ∈ V.part q) : f v ∈ W.part (q + p) := by
  rw [mem_part_iff] at hv ⊢
  rw [← hv, apply_proj_of_mem hf, proj_proj_apply]

/-- Conversely, a linear map mapping every `V_q` into `W_{q+p}` has parity `p`.
@isnad1 id=mem.1h5v.s9.1b65a7f8603f from=translated src=- shape=4442245b vocab=ef4fb37a
-/
theorem mem_parityHom_of_apply_mem {V W : SVec k} {p : ZMod 2} {f : V ⟶ W}
    (h : ∀ q (v : V), v ∈ V.part q → f v ∈ W.part (q + p)) : f ∈ parityHom V W p := by
  intro q
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply, coe_toLinearMap]
  have hv := h q _ (proj_mem_part V q v)
  have hv' := h (q + 1) _ (proj_mem_part V (q + 1) v)
  have hne : q + p ≠ q + 1 + p := by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      rcases parity_eq_zero_or_one q with rfl | rfl <;> decide
  conv_rhs => rw [← proj_apply_add' V q v]
  rw [map_add, map_add, (mem_part_iff _).1 hv, proj_apply_of_mem_part _ hv', ite_eq_right hne,
    add_zero]

/-- The component of parity `p` of a linear map: `f_p = ∑_q proj_{q+p} ∘ f ∘ proj_q`.-/
def homProj (p : ZMod 2) {V W : SVec k} : (V ⟶ W) →ₗ[k] (V ⟶ W) where
  toFun f := ofHom (W.proj p ∘ₗ toLinearMap f ∘ₗ V.proj 0 +
    W.proj (1 + p) ∘ₗ toLinearMap f ∘ₗ V.proj 1)
  map_add' f g := by
    ext v
    simp only [ofHom_apply, add_apply, LinearMap.add_apply, LinearMap.comp_apply,
      coe_toLinearMap, map_add]
    abel
  map_smul' r f := by
    ext v
    simp only [ofHom_apply, smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
      coe_toLinearMap, map_smul, RingHom.id_apply, smul_add]

/--
@isnad1 id=eq.0h6v.s10.7509620a5e12 from=translated src=- shape=9e0c4b1e vocab=0ff801fa
-/
theorem homProj_apply (p : ZMod 2) {V W : SVec k} (f : V ⟶ W) (v : V) :
    homProj p f v = W.proj p (f (V.proj 0 v)) + W.proj (1 + p) (f (V.proj 1 v)) := rfl

/--
@isnad1 id=mem.0h5v.s9.ccb0dd34ceeb from=translated src=- shape=7dfb99c8 vocab=de0cacb3
-/
theorem homProj_mem (p : ZMod 2) {V W : SVec k} (f : V ⟶ W) : homProj p f ∈ parityHom V W p := by
  refine mem_parityHom_of_apply_mem fun q v hv => ?_
  rw [homProj_apply, proj_apply_of_mem_part _ hv, proj_apply_of_mem_part _ hv]
  rcases parity_eq_zero_or_one q with rfl | rfl
  · simpa using proj_mem_part W p (f v)
  · simpa using proj_mem_part W (1 + p) (f v)

/--
@isnad1 id=eq.0h4v.s10.5167a85c048d from=translated src=- shape=17d62099 vocab=a9842b15
-/
theorem homProj_add_homProj {V W : SVec k} (f : V ⟶ W) : homProj 0 f + homProj 1 f = f := by
  ext v
  simp only [add_apply, homProj_apply, show (1 : ZMod 2) + 0 = 1 from rfl,
    show (1 : ZMod 2) + 1 = 0 from rfl]
  conv_rhs => rw [← proj_apply_add V v, map_add, ← proj_apply_add W (f (V.proj 0 v)),
    ← proj_apply_add W (f (V.proj 1 v))]
  abel

/--
@isnad1 id=eq.1h5v.s9.6ea0c8bf8494 from=translated src=- shape=4654a360 vocab=de0cacb3
-/
theorem homProj_of_mem {p : ZMod 2} {V W : SVec k} {f : V ⟶ W} (hf : f ∈ parityHom V W p) :
    homProj p f = f := by
  ext v
  rw [homProj_apply, apply_proj_of_mem hf, apply_proj_of_mem hf, zero_add, proj_proj_apply,
    proj_proj_apply, add_comm 1 p, proj_apply_add']

/--
@isnad1 id=eq.2h6v.s9.074097ee3fb7 from=translated src=- shape=80cbc5f9 vocab=de0cacb3
-/
theorem homProj_of_mem_ne {p q : ZMod 2} (h : p ≠ q) {V W : SVec k} {f : V ⟶ W}
    (hf : f ∈ parityHom V W q) : homProj p f = 0 := by
  ext v
  rw [homProj_apply, apply_proj_of_mem hf, apply_proj_of_mem hf, zero_apply]
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;> simp_all

/-- **Brundan–Ellis, Example 1.2(i).** `SVec k` is a supercategory: every linear map is uniquely
the sum of an even and an odd linear map.-/
instance instSupercategory : Supercategory k (SVec k) where
  parity := parityHom
  isInternal V W := by
    rw [DirectSum.isInternal_submodule_iff_isCompl (parityHom V W) (i := 0) (j := 1) (by decide)
      (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
    constructor
    · rw [Submodule.disjoint_def]
      intro f h0 h1
      rw [← homProj_of_mem h0, homProj_of_mem_ne (by decide) h1]
    · rw [codisjoint_iff, eq_top_iff]
      intro f _
      rw [← homProj_add_homProj f]
      exact Submodule.add_mem_sup (homProj_mem 0 f) (homProj_mem 1 f)
  id_mem V q := by rw [add_zero]; rfl
  comp_mem {U V W p q f g} hf hg r := by
    rw [toLinearMap_comp, LinearMap.comp_assoc, hf r, ← LinearMap.comp_assoc, hg, add_assoc]
    rfl

/-- The parity components of the supercategory structure are the maps `homProj`.
@isnad1 id=eq.0h5v.s9.04065f3dd66b from=translated src=- shape=8d53146f vocab=e3da7251
-/
theorem proj_eq_homProj (p : ZMod 2) {V W : SVec k} (f : V ⟶ W) :
    Supercategory.proj k p f = homProj p f := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · exact proj_eq_of_add (homProj_add_homProj f).symm (homProj_mem 0 f) (homProj_mem 1 f)
  · exact proj_eq_of_add ((add_comm _ _).trans (homProj_add_homProj f)).symm
      (homProj_mem 1 f) (by simpa using! homProj_mem 0 f)

/--
@isnad1 id=eq.3h7v.s10.1ede38f55a4f from=translated src=- shape=ccd41947 vocab=2595ca05
-/
theorem homProj_eq_of_add {p : ZMod 2} {V W : SVec k} {f g h : V ⟶ W} (e : f = g + h)
    (hg : g ∈ parityHom V W p) (hh : h ∈ parityHom V W (p + 1)) : homProj p f = g := by
  rw [← proj_eq_homProj]; exact proj_eq_of_add e hg hh

/--
@isnad1 id=eq.1h5v.s8.72308d87973b from=translated src=- shape=60eecc8e vocab=34d9d7a2
-/
theorem ext_part {V : SVec k} {M : Type u} [AddCommGroup M] [Module k M] {f g : V →ₗ[k] M}
    (h : ∀ q (v : V), v ∈ V.part q → f v = g v) : f = g := by
  ext v
  rw [← proj_apply_add V v, map_add, map_add, h 0 _ (proj_mem_part V 0 v),
    h 1 _ (proj_mem_part V 1 v)]

/-- An isomorphism of `SVec k` given by a linear equivalence.-/
@[simps]
def isoOfLinearEquiv {V W : SVec k} (e : V ≃ₗ[k] W) : V ≅ W where
  hom := ofHom e.toLinearMap
  inv := ofHom e.symm.toLinearMap
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

/-! ## Signs -/

/-- The map `v ↦ (-1)^{b|v|} v` (the grading involution for `b = 1`).-/
def sgn (V : SVec k) (b : ZMod 2) : V →ₗ[k] V := V.proj 0 + sign k b • V.proj 1

/--
@isnad1 id=eq.0h4v.s9.524abc39f86d from=translated src=- shape=0991ae8b vocab=65851530
-/
theorem sgn_apply (V : SVec k) (b : ZMod 2) (v : V) :
    V.sgn b v = V.proj 0 v + sign k b • V.proj 1 v := rfl

/--
@isnad1 id=eq.0h2v.s7.4d4a7fad403b from=translated src=- shape=87b854f7 vocab=a3de921c
-/
@[simp] theorem sgn_zero (V : SVec k) : V.sgn 0 = LinearMap.id := by
  rw [sgn, sign_zero, one_smul, proj_add_proj]

/--
@isnad1 id=eq.1h5v.s8.eb14212412fd from=translated src=- shape=ca3d4a62 vocab=dcec6abe
-/
theorem sgn_apply_of_mem {V : SVec k} (b : ZMod 2) {q : ZMod 2} {v : V} (hv : v ∈ V.part q) :
    V.sgn b v = sign k (q * b) • v := by
  rw [sgn_apply, proj_apply_of_mem_part _ hv, proj_apply_of_mem_part _ hv]
  rcases parity_eq_zero_or_one q with rfl | rfl <;> simp

/--
@isnad1 id=eq.0h4v.s8.8982e74c309e from=translated src=- shape=94aef732 vocab=62655422
-/
theorem sgn_comp_sgn (V : SVec k) (a b : ZMod 2) : V.sgn a ∘ₗ V.sgn b = V.sgn (a + b) := by
  refine ext_part fun q v hv => ?_
  rw [LinearMap.comp_apply, sgn_apply_of_mem _ hv, map_smul, sgn_apply_of_mem _ hv,
    sgn_apply_of_mem _ hv, smul_smul, ← sign_add, mul_add, add_comm]

/--
@isnad1 id=eq.0h4v.s8.8157545f58e9 from=translated src=- shape=182963dc vocab=fb913a3b
-/
theorem sgn_sgn_apply (V : SVec k) (b : ZMod 2) (v : V) : V.sgn b (V.sgn b v) = v := by
  rw [← LinearMap.comp_apply, sgn_comp_sgn, zmod2_add_self, sgn_zero, LinearMap.id_apply]

/--
@isnad1 id=mem.0h3v.s8.a0a4875bcb09 from=translated src=- shape=849d1db9 vocab=8965edfa
-/
theorem sgn_mem (V : SVec k) (b : ZMod 2) : ofHom (V.sgn b) ∈ parityHom V V 0 := by
  intro q
  refine ext_part fun r v hv => ?_
  simp only [add_zero, LinearMap.comp_apply, toLinearMap_ofHom, proj_apply_of_mem_part _ hv]
  split_ifs <;> simp [sgn_apply_of_mem _ hv, proj_apply_of_mem_part _ hv, *]

/-- A homogeneous linear map of parity `p` commutes with the signs up to `(-1)^{pb}`.
@isnad1 id=eq.1h6v.s9.ec7ac82fffb5 from=translated src=- shape=f5713c82 vocab=dbc377dc
-/
theorem sgn_comp_of_mem {V W : SVec k} {p : ZMod 2} {f : V ⟶ W} (hf : f ∈ parityHom V W p)
    (b : ZMod 2) : W.sgn b ∘ₗ toLinearMap f = sign k (p * b) • (toLinearMap f ∘ₗ V.sgn b) := by
  refine ext_part fun q v hv => ?_
  rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply, sgn_apply_of_mem _ hv,
    coe_toLinearMap, map_smul, sgn_apply_of_mem _ (apply_mem_part hf hv), smul_smul, ← sign_add,
    add_mul, add_comm]

/-! ## The tensor product of superspaces -/

/-- The tensor product of superspaces: `(V ⊗ W)₁ = V₀ ⊗ W₁ ⊕ V₁ ⊗ W₀`.-/
abbrev tensorObj (V W : SVec k) : SVec k where
  carrier := V ⊗[k] W
  odd := map (V.proj 1) (W.proj 0) + map (V.proj 0) (W.proj 1)
  odd_comp_odd := by
    apply TensorProduct.ext'
    intro v w
    simp [map_tmul, proj_proj_apply]

/--
@isnad1 id=eq.0h5v.s10.4c01ef4f4fbb from=translated src=- shape=d7f123c2 vocab=b85fa426
-/
theorem tensorObj_odd_tmul (V W : SVec k) (v : V) (w : W) :
    (tensorObj V W).odd (v ⊗ₜ w) = V.proj 1 v ⊗ₜ W.proj 0 w + V.proj 0 v ⊗ₜ W.proj 1 w := rfl

/-- `(V ⊗ W)_q = V₀ ⊗ W_q ⊕ V₁ ⊗ W_{1+q}`.
@isnad1 id=eq.0h6v.s10.68db515c2a2d from=translated src=- shape=a6b5140f vocab=60361dd2
-/
@[simp] theorem tensorObj_proj_tmul (V W : SVec k) (q : ZMod 2) (v : V) (w : W) :
    (tensorObj V W).proj q (v ⊗ₜ w) =
      V.proj 0 v ⊗ₜ W.proj q w + V.proj 1 v ⊗ₜ W.proj (1 + q) w := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [proj_zero, LinearMap.sub_apply, LinearMap.id_apply, tensorObj_odd_tmul, add_zero]
    have e : v ⊗ₜ[k] w = (V.proj 0 v + V.proj 1 v) ⊗ₜ (W.proj 0 w + W.proj 1 w) := by
      rw [proj_apply_add, proj_apply_add]
    rw [e]
    simp only [add_tmul, tmul_add]
    abel
  · rw [proj_one, tensorObj_odd_tmul, zmod2_one_add_one, add_comm]

/--
@isnad1 id=mem.2h7v.s8.c77303e4300d from=translated src=- shape=a1eafeb2 vocab=00edd001
-/
theorem tmul_mem_part {V W : SVec k} {p q : ZMod 2} {v : V} {w : W} (hv : v ∈ V.part p)
    (hw : w ∈ W.part q) : v ⊗ₜ[k] w ∈ (tensorObj V W).part (p + q) := by
  rw [mem_part_iff, tensorObj_proj_tmul, proj_apply_of_mem_part _ hv, proj_apply_of_mem_part _ hv,
    proj_apply_of_mem_part _ hw, proj_apply_of_mem_part _ hw]
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;> simp

/-- Linear maps out of `V ⊗ W` agreeing on tensors of homogeneous vectors are equal.
@isnad1 id=eq.1h6v.s10.280ba918247b from=translated src=- shape=28197db5 vocab=c61c8985
-/
theorem ext_tensor {V W : SVec k} {M : Type u} [AddCommGroup M] [Module k M]
    {f g : V ⊗[k] W →ₗ[k] M}
    (h : ∀ p q (v : V) (w : W), v ∈ V.part p → w ∈ W.part q → f (v ⊗ₜ w) = g (v ⊗ₜ w)) :
    f = g := by
  apply TensorProduct.ext'
  intro v w
  rw [← proj_apply_add V v, ← proj_apply_add W w]
  simp only [add_tmul, tmul_add, map_add]
  rw [h _ _ _ _ (proj_mem_part V 0 v) (proj_mem_part W 0 w),
    h _ _ _ _ (proj_mem_part V 0 v) (proj_mem_part W 1 w),
    h _ _ _ _ (proj_mem_part V 1 v) (proj_mem_part W 0 w),
    h _ _ _ _ (proj_mem_part V 1 v) (proj_mem_part W 1 w)]

/--
@isnad1 id=eq.0h4v.s7.da5e9ab12b81 from=translated src=- shape=9d7ccb9f vocab=d19eed37
-/
theorem tensorObj_sgn (V W : SVec k) (b : ZMod 2) :
    (tensorObj V W).sgn b = map (V.sgn b) (W.sgn b) := by
  refine ext_tensor fun p q v w hv hw => ?_
  rw [sgn_apply_of_mem _ (tmul_mem_part hv hw), map_tmul, sgn_apply_of_mem _ hv,
    sgn_apply_of_mem _ hw, smul_tmul_smul, ← sign_add, add_mul]

/-- The tensor product of homogeneous linear maps is homogeneous, with parities adding.
@isnad1 id=mem.2h9v.s10.ceb778374d4a from=translated src=- shape=0a423e46 vocab=115fdf24
-/
theorem map_mem {V V' W W' : SVec k} {a b : ZMod 2} {f : V ⟶ V'} {g : W ⟶ W'}
    (hf : f ∈ parityHom V V' a) (hg : g ∈ parityHom W W' b) :
    (ofHom (map (toLinearMap f) (toLinearMap g)) : tensorObj V W ⟶ tensorObj V' W') ∈
      parityHom (tensorObj V W) (tensorObj V' W') (a + b) := by
  intro q
  refine ext_tensor fun p r v w hv hw => ?_
  have hfg : f v ⊗ₜ[k] g w ∈ (tensorObj V' W').part (p + a + (r + b)) :=
    tmul_mem_part (apply_mem_part hf hv) (apply_mem_part hg hw)
  simp only [LinearMap.comp_apply, toLinearMap_ofHom]
  rw [proj_apply_of_mem_part _ (tmul_mem_part hv hw), map_tmul, coe_toLinearMap,
    coe_toLinearMap, proj_apply_of_mem_part _ hfg]
  split_ifs with h1 h2 h2
  · rw [map_tmul]; rfl
  · exact absurd (by rw [h1]; abel) h2
  · refine absurd (add_right_cancel (b := a + b) ?_) h1
    rw [h2]; abel
  · exact map_zero _

/-! ## Whiskering -/

/-- The unit superspace `k`, concentrated in even parity.-/
abbrev unit : SVec k where
  carrier := k
  odd := 0
  odd_comp_odd := by simp

/--
@isnad1 id=eq.0h2v.s7.f17b42303a40 from=translated src=- shape=c8bdbc3d vocab=9d81ac24
-/
@[simp] theorem unit_proj_zero_apply (r : k) : (unit : SVec k).proj 0 r = r := by
  simp [proj_zero]

/--
@isnad1 id=eq.0h2v.s8.33038fff4e4d from=translated src=- shape=e079795b vocab=9d81ac24
-/
@[simp] theorem unit_proj_one_apply (r : k) : (unit : SVec k).proj 1 r = 0 := by
  simp [proj_one]

/--
@isnad1 id=eq.0h2v.s6.983dd6449604 from=translated src=- shape=482b8ca0 vocab=88ec3530
-/
theorem unit_sgn (b : ZMod 2) : (unit : SVec k).sgn b = LinearMap.id :=
  LinearMap.ext fun r => by
    rw [sgn_apply, unit_proj_zero_apply, unit_proj_one_apply, smul_zero, add_zero]; rfl

/-- `1_V ⊗ g`: `v ⊗ w ↦ (-1)^{|g||v|} v ⊗ g(w)`, extended linearly in `g`.-/
def whiskerLeft (V : SVec k) {W W' : SVec k} (g : W ⟶ W') : tensorObj V W ⟶ tensorObj V W' :=
  ofHom (map LinearMap.id (toLinearMap (homProj 0 g)) + map (V.sgn 1) (toLinearMap (homProj 1 g)))

/-- `f ⊗ 1_W`: `v ⊗ w ↦ f(v) ⊗ w`.-/
def whiskerRight {V V' : SVec k} (f : V ⟶ V') (W : SVec k) : tensorObj V W ⟶ tensorObj V' W :=
  ofHom (map (toLinearMap f) LinearMap.id)

/--
@isnad1 id=eq.0h7v.s7.4d33d9ca818b from=translated src=- shape=8f2c1248 vocab=62baeb0e
-/
theorem whiskerRight_tmul {V V' : SVec k} (f : V ⟶ V') (W : SVec k) (v : V) (w : W) :
    whiskerRight f W (v ⊗ₜ w) = f v ⊗ₜ w := rfl

/--
@isnad1 id=eq.1h6v.s8.d1429eae8a5d from=translated src=- shape=945f8f55 vocab=2dd5505e
-/
theorem whiskerLeft_of_mem (V : SVec k) {W W' : SVec k} {b : ZMod 2} {g : W ⟶ W'}
    (hg : g ∈ parityHom W W' b) : whiskerLeft V g = ofHom (map (V.sgn b) (toLinearMap g)) := by
  rcases parity_eq_zero_or_one b with rfl | rfl
  · rw [whiskerLeft, homProj_of_mem hg, homProj_of_mem_ne (by decide) hg, sgn_zero]
    simp [toLinearMap, ofHom]
  · rw [whiskerLeft, homProj_of_mem hg, homProj_of_mem_ne (by decide) hg]
    simp [toLinearMap, ofHom]

/-- **The Koszul sign rule** for `1_V ⊗ g`: `(1 ⊗ g)(v ⊗ w) = (-1)^{|v||g|} v ⊗ g(w)`.
@isnad1 id=eq.2h9v.s9.59750bfc8109 from=translated src=- shape=165764ab vocab=337cb40e
-/
theorem whiskerLeft_tmul {V W W' : SVec k} {p q : ZMod 2} {g : W ⟶ W'}
    (hg : g ∈ parityHom W W' q) {v : V} (hv : v ∈ V.part p) (w : W) :
    whiskerLeft V g (v ⊗ₜ w) = sign k (p * q) • (v ⊗ₜ g w) := by
  rw [whiskerLeft_of_mem V hg, ofHom_apply, map_tmul, sgn_apply_of_mem _ hv, smul_tmul']
  rfl

/--
@isnad1 id=eq.0h6v.s8.6232b50147df from=translated src=- shape=01e54201 vocab=8de988af
-/
theorem whiskerLeft_add (V : SVec k) {W W' : SVec k} (g g' : W ⟶ W') :
    whiskerLeft V (g + g') = whiskerLeft V g + whiskerLeft V g' := by
  simp only [whiskerLeft, map_add, toLinearMap_add, map_add_right]
  ext x
  rw [add_apply, ofHom_apply, ofHom_apply, ofHom_apply]
  simp only [LinearMap.add_apply]
  abel

/--
@isnad1 id=eq.0h6v.s10.712735fcbb2a from=translated src=- shape=0be60c3a vocab=edb3deb6
-/
theorem whiskerLeft_smul (V : SVec k) {W W' : SVec k} (r : k) (g : W ⟶ W') :
    whiskerLeft V (r • g) = r • whiskerLeft V g := by
  simp only [whiskerLeft, map_smul, toLinearMap_smul, map_smul_right]
  ext x
  rw [smul_apply, ofHom_apply, ofHom_apply]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_add]

/--
@isnad1 id=eq.0h4v.s7.2e9b98d09cba from=translated src=- shape=dfd4ab03 vocab=1f9d024e
-/
theorem whiskerLeft_zero (V : SVec k) {W W' : SVec k} : whiskerLeft V (0 : W ⟶ W') = 0 := by
  simpa using whiskerLeft_smul V (0 : k) (0 : W ⟶ W')

/--
@isnad1 id=mem.1h6v.s9.53b9c6bc72dc from=translated src=- shape=df301869 vocab=14a03962
-/
theorem whiskerLeft_mem (V : SVec k) {W W' : SVec k} {b : ZMod 2} {g : W ⟶ W'}
    (hg : g ∈ parityHom W W' b) :
    whiskerLeft V g ∈ parityHom (tensorObj V W) (tensorObj V W') b := by
  rw [whiskerLeft_of_mem V hg]
  simpa using map_mem (sgn_mem V b) hg

/--
@isnad1 id=mem.1h6v.s9.43edef8d8100 from=translated src=- shape=13e56157 vocab=bf8a56dd
-/
theorem whiskerRight_mem {V V' : SVec k} {a : ZMod 2} {f : V ⟶ V'} (hf : f ∈ parityHom V V' a)
    (W : SVec k) : whiskerRight f W ∈ parityHom (tensorObj V W) (tensorObj V' W) a := by
  simpa using! map_mem hf (instSupercategory.id_mem W)

/--
@isnad1 id=eq.0h7v.s7.4ac8538b9bc1 from=translated src=- shape=723885ab vocab=4fdc9f91
-/
theorem whiskerLeft_comp (V : SVec k) {W W' W'' : SVec k} (f : W ⟶ W') (g : W' ⟶ W'') :
    whiskerLeft V (f ≫ g) = whiskerLeft V f ≫ whiskerLeft V g := by
  refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
  · simp only [Limits.zero_comp, whiskerLeft_zero]
  · intro a f hfa
    refine Supercategory.induction_on (R := k) g ?_ ?_ ?_
    · simp only [Limits.comp_zero, whiskerLeft_zero]
    · intro b g hgb
      rw [whiskerLeft_of_mem V (Supercategory.comp_mem hfa hgb), whiskerLeft_of_mem V hfa,
        whiskerLeft_of_mem V hgb, add_comm, ← sgn_comp_sgn]
      exact map_comp _ _ _ _
    · intro g g' hg hg'
      rw [Preadditive.comp_add, whiskerLeft_add, whiskerLeft_add, hg, hg', Preadditive.comp_add]
  · intro f f' hf hf'
    rw [Preadditive.add_comp, whiskerLeft_add, whiskerLeft_add, hf, hf', Preadditive.add_comp]

/--
@isnad1 id=eq.0h3v.s6.aca2ac78f528 from=translated src=- shape=0b432687 vocab=b37b2a74
-/
theorem whiskerLeft_id (V W : SVec k) : whiskerLeft V (𝟙 W) = 𝟙 (tensorObj V W) := by
  rw [whiskerLeft_of_mem V (instSupercategory.id_mem W), sgn_zero]
  exact TensorProduct.map_id

/--
@isnad1 id=eq.0h3v.s6.94f041bed180 from=translated src=- shape=5a70e863 vocab=4ad0c189
-/
theorem whiskerRight_id (V W : SVec k) : whiskerRight (𝟙 V) W = 𝟙 (tensorObj V W) :=
  TensorProduct.map_id

/--
@isnad1 id=eq.0h7v.s7.956dc6801832 from=translated src=- shape=79d8d4f1 vocab=bb93a12e
-/
theorem comp_whiskerRight {U V W : SVec k} (f : U ⟶ V) (g : V ⟶ W) (X : SVec k) :
    whiskerRight (f ≫ g) X = whiskerRight f X ≫ whiskerRight g X :=
  TensorProduct.ext' fun _ _ => rfl

/-- The super interchange law in whiskering form.
@isnad1 id=eq.2h9v.s9.1e17d56b862a from=translated src=- shape=dcf0ddd2 vocab=e546b7d2
-/
theorem super_interchange {V V' W W' : SVec k} {p q : ZMod 2} {f : V ⟶ V'} {g : W ⟶ W'}
    (hf : f ∈ parityHom V V' p) (hg : g ∈ parityHom W W' q) :
    whiskerRight f W ≫ whiskerLeft V' g =
      koszulSign p q • (whiskerLeft V g ≫ whiskerRight f W') := by
  rw [whiskerLeft_of_mem V' hg, whiskerLeft_of_mem V hg, koszulSign_smul (R := k)]
  change map _ _ ∘ₗ map _ _ = sign k (p * q) • (map _ _ ∘ₗ map _ _)
  rw [← map_comp, ← map_comp, sgn_comp_of_mem hf, LinearMap.id_comp, LinearMap.comp_id,
    map_smul_left]

/-! ## The monoidal supercategory `SVec` -/

/-- The associativity isomorphism `(U ⊗ V) ⊗ W ≅ U ⊗ (V ⊗ W)` of `TensorProduct`.-/
def associator (U V W : SVec k) : tensorObj (tensorObj U V) W ≅ tensorObj U (tensorObj V W) :=
  isoOfLinearEquiv (TensorProduct.assoc k U V W)

/-- The left unitor `k ⊗ V ≅ V`.-/
def leftUnitor (V : SVec k) : tensorObj unit V ≅ V := isoOfLinearEquiv (TensorProduct.lid k V)

/-- The right unitor `V ⊗ k ≅ V`.-/
def rightUnitor (V : SVec k) : tensorObj V unit ≅ V := isoOfLinearEquiv (TensorProduct.rid k V)

instance instMonoidalCategoryStruct : MonoidalCategoryStruct (SVec k) where
  tensorObj := tensorObj
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorUnit := unit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

/--
@isnad1 id=eq.0h3v.s5.0f370cb456da from=translated src=- shape=3afaab6f vocab=772756da
-/
theorem tensorObj_def (V W : SVec k) : V ⊗ W = tensorObj V W := rfl

/--
@isnad1 id=eq.0h1v.s4.940eb04ec5a5 from=translated src=- shape=58d3dad9 vocab=87e2acac
-/
theorem tensorUnit_def : 𝟙_ (SVec k) = unit := rfl

/--
@isnad1 id=eq.0h5v.s6.697bca596654 from=translated src=- shape=321833b4 vocab=4d619aa8
-/
theorem whiskerRight_def {V V' : SVec k} (f : V ⟶ V') (W : SVec k) : f ▷ W = whiskerRight f W :=
  rfl

/--
@isnad1 id=eq.0h7v.s9.1442303feee6 from=translated src=- shape=d78406dc vocab=42346f96
-/
@[simp] theorem associator_hom_tmul (U V W : SVec k) (u : U) (v : V) (w : W) :
    (α_ U V W).hom ((u ⊗ₜ v) ⊗ₜ w) = u ⊗ₜ (v ⊗ₜ w) := rfl

/--
@isnad1 id=eq.0h7v.s9.79aaa4feac08 from=translated src=- shape=a7910414 vocab=a4da4ccd
-/
@[simp] theorem associator_inv_tmul (U V W : SVec k) (u : U) (v : V) (w : W) :
    (α_ U V W).inv (u ⊗ₜ (v ⊗ₜ w)) = (u ⊗ₜ v) ⊗ₜ w := rfl

/--
@isnad1 id=eq.0h4v.s8.7cd163ca3616 from=translated src=- shape=b6b48493 vocab=949c0aeb
-/
@[simp] theorem leftUnitor_hom_tmul (V : SVec k) (r : k) (v : V) :
    (λ_ V).hom (r ⊗ₜ v) = r • v := by
  change TensorProduct.lid k V (r ⊗ₜ v) = r • v; simp

/--
@isnad1 id=eq.0h4v.s8.31c97b1232be from=translated src=- shape=9569c446 vocab=210837f9
-/
@[simp] theorem rightUnitor_hom_tmul (V : SVec k) (r : k) (v : V) :
    (ρ_ V).hom (v ⊗ₜ r) = r • v := by
  change TensorProduct.rid k V (v ⊗ₜ r) = r • v; simp

/--
@isnad1 id=eq.0h7v.s8.024e8c46a2e1 from=translated src=- shape=51353769 vocab=fcababa3
-/
@[simp] theorem whiskerRight_tmul' {V V' : SVec k} (f : V ⟶ V') (W : SVec k) (v : V) (w : W) :
    (f ▷ W) (v ⊗ₜ w) = f v ⊗ₜ w := rfl

/--
@isnad1 id=mem.0h4v.s9.c72f6058feab from=translated src=- shape=025581e2 vocab=2bc6d4ae
-/
theorem associator_mem (U V W : SVec k) :
    (associator U V W).hom ∈ parityHom (tensorObj (tensorObj U V) W) (tensorObj U (tensorObj V W)) 0 := by
  intro q
  apply TensorProduct.ext_threefold
  intro u v w
  simp only [add_zero, LinearMap.comp_apply, associator, isoOfLinearEquiv_hom, toLinearMap_ofHom,
    LinearEquiv.coe_coe, assoc_tmul]
  repeat rw [tensorObj_proj_tmul]
  simp only [add_tmul, tmul_add, map_add, assoc_tmul]
  rcases parity_eq_zero_or_one q with rfl | rfl
  · simp only [add_zero, zmod2_one_add_one]; abel
  · simp only [add_zero, zmod2_one_add_one, ← add_assoc]; abel

/--
@isnad1 id=mem.0h2v.s8.ad20801be6f2 from=translated src=- shape=bc33d218 vocab=7907a719
-/
theorem leftUnitor_mem (V : SVec k) : (leftUnitor V).hom ∈ parityHom (tensorObj unit V) V 0 := by
  intro q
  apply TensorProduct.ext'
  intro r v
  change TensorProduct.lid k V ((tensorObj unit V).proj q (r ⊗ₜ v)) =
    V.proj (q + 0) (TensorProduct.lid k V (r ⊗ₜ v))
  rw [tensorObj_proj_tmul, unit_proj_zero_apply, unit_proj_one_apply, zero_tmul, add_zero,
    add_zero]
  simp

/--
@isnad1 id=mem.0h2v.s8.102fe9a302a9 from=translated src=- shape=fdfceeef vocab=c31c7e55
-/
theorem rightUnitor_mem (V : SVec k) : (rightUnitor V).hom ∈ parityHom (tensorObj V unit) V 0 := by
  intro q
  apply TensorProduct.ext'
  intro v r
  change TensorProduct.rid k V ((tensorObj V unit).proj q (v ⊗ₜ r)) =
    V.proj (q + 0) (TensorProduct.rid k V (v ⊗ₜ r))
  rw [tensorObj_proj_tmul, add_zero]
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [unit_proj_zero_apply, add_zero, unit_proj_one_apply, tmul_zero, add_zero]
    simp
  · rw [unit_proj_one_apply, zmod2_one_add_one, unit_proj_zero_apply, tmul_zero, zero_add]
    simp

/--
@isnad1 id=eq.1h5v.s9.3d888f3f0bee from=translated src=- shape=9c2a529a vocab=a9968f5a
-/
theorem whiskerLeft_even (V : SVec k) {W W' : SVec k} {g : W ⟶ W'} (hg : g ∈ parityHom W W' 0) :
    whiskerLeft V g = ofHom (map LinearMap.id (toLinearMap g)) := by
  rw [whiskerLeft_of_mem V hg, sgn_zero]

/--
@isnad1 id=eq.0h6v.s9.45a0f337fe96 from=translated src=- shape=70901c51 vocab=2765758e
-/
theorem homProj_whiskerLeft (p : ZMod 2) (V : SVec k) {W W' : SVec k} (g : W ⟶ W') :
    homProj p (whiskerLeft V g) = whiskerLeft V (homProj p g) := by
  have e : whiskerLeft V g = whiskerLeft V (homProj p g) + whiskerLeft V (homProj (p + 1) g) := by
    rw [← whiskerLeft_add]
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [zero_add, homProj_add_homProj]
    · rw [zmod2_one_add_one, add_comm, homProj_add_homProj]
  exact homProj_eq_of_add e (whiskerLeft_mem V (homProj_mem p g))
    (whiskerLeft_mem V (homProj_mem (p + 1) g))

/--
@isnad1 id=eq.0h6v.s9.6159b3e48b9e from=translated src=- shape=b69e2681 vocab=817d6019
-/
theorem homProj_whiskerRight (p : ZMod 2) {V V' : SVec k} (f : V ⟶ V') (W : SVec k) :
    homProj p (whiskerRight f W) = whiskerRight (homProj p f) W := by
  have e : whiskerRight f W = whiskerRight (homProj p f) W + whiskerRight (homProj (p + 1) f) W := by
    have : f = homProj p f + homProj (p + 1) f := by
      rcases parity_eq_zero_or_one p with rfl | rfl
      · rw [zero_add, homProj_add_homProj]
      · rw [zmod2_one_add_one, add_comm, homProj_add_homProj]
    conv_lhs => rw [this]
    exact map_add_left _ _ _
  exact homProj_eq_of_add e (whiskerRight_mem (homProj_mem p f) W)
    (whiskerRight_mem (homProj_mem (p + 1) f) W)

/--
@isnad1 id=eq.0h6v.s7.d1a8611d1242 from=translated src=- shape=e4d0ca0e vocab=6ded1c1d
-/
theorem associator_naturality_left {U U' : SVec k} (f : U ⟶ U') (V W : SVec k) :
    whiskerRight (whiskerRight f V) W ≫ (associator U' V W).hom =
      (associator U V W).hom ≫ whiskerRight f (tensorObj V W) :=
  TensorProduct.ext_threefold fun _ _ _ => rfl

/--
@isnad1 id=eq.0h6v.s8.3122fc9f3b57 from=translated src=- shape=d6a6f2da vocab=5c9556f9
-/
theorem whiskerRight_add {V V' : SVec k} (f f' : V ⟶ V') (W : SVec k) :
    whiskerRight (f + f') W = whiskerRight f W + whiskerRight f' W :=
  map_add_left _ _ _

/--
@isnad1 id=eq.0h4v.s7.2df485430c30 from=translated src=- shape=a1157481 vocab=b606e005
-/
theorem whiskerRight_zero {V V' : SVec k} (W : SVec k) :
    whiskerRight (0 : V ⟶ V') W = 0 :=
  map_zero_left _

/--
@isnad1 id=eq.0h6v.s7.6b0272391a6a from=translated src=- shape=d35898a7 vocab=8ef9b95a
-/
theorem associator_naturality_middle (U : SVec k) {V V' : SVec k} (g : V ⟶ V') (W : SVec k) :
    whiskerRight (whiskerLeft U g) W ≫ (associator U V' W).hom =
      (associator U V W).hom ≫ whiskerLeft U (whiskerRight g W) := by
  refine Supercategory.induction_on (R := k) g ?_ ?_ ?_
  · rw [whiskerLeft_zero, whiskerRight_zero, whiskerRight_zero, whiskerLeft_zero,
      Limits.zero_comp, Limits.comp_zero]
  · intro b g hg
    rw [whiskerLeft_of_mem U hg, whiskerLeft_of_mem U (whiskerRight_mem hg W)]
    exact TensorProduct.ext_threefold fun _ _ _ => rfl
  · intro g g' hg hg'
    rw [whiskerLeft_add, whiskerRight_add, Preadditive.add_comp, hg, hg', whiskerRight_add,
      whiskerLeft_add, Preadditive.comp_add]

/--
@isnad1 id=eq.0h6v.s7.4675224391ae from=translated src=- shape=7983d430 vocab=f7979f70
-/
theorem associator_naturality_right (U V : SVec k) {W W' : SVec k} (h : W ⟶ W') :
    whiskerLeft (tensorObj U V) h ≫ (associator U V W').hom =
      (associator U V W).hom ≫ whiskerLeft U (whiskerLeft V h) := by
  refine Supercategory.induction_on (R := k) h ?_ ?_ ?_
  · rw [whiskerLeft_zero, whiskerLeft_zero, whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
  · intro c h hh
    rw [whiskerLeft_of_mem _ hh, whiskerLeft_of_mem U (whiskerLeft_mem V hh),
      whiskerLeft_of_mem V hh, tensorObj_sgn]
    exact TensorProduct.ext_threefold fun _ _ _ => rfl
  · intro h h' hh hh'
    rw [whiskerLeft_add, Preadditive.add_comp, hh, hh', whiskerLeft_add, whiskerLeft_add,
      Preadditive.comp_add]

/-- **Brundan–Ellis, Example 1.5(i).** `SVec k` is a monoidal supercategory.
@isnad1 id=monoidal.0h1v.s4.68ef737f8d8f from=translated src=- shape=84bfdc15 vocab=48bbec20
-/
instance instMonoidalSupercategory : MonoidalSupercategory k (SVec k) where
  tensorHom_def _ _ := rfl
  whiskerLeft_id := whiskerLeft_id
  id_whiskerRight := whiskerRight_id
  whiskerLeft_comp := whiskerLeft_comp
  comp_whiskerRight := comp_whiskerRight
  whiskerLeft_add := whiskerLeft_add
  add_whiskerRight f g _ := map_add_left _ _ _
  whiskerLeft_smul := whiskerLeft_smul
  smul_whiskerRight r f _ := map_smul_left r _ _
  whiskerLeft_mem V _ _ _ _ hg := whiskerLeft_mem V hg
  whiskerRight_mem W hf := whiskerRight_mem hf W
  super_interchange hf hg := super_interchange hf hg
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := by
    change (whiskerRight (whiskerRight f₁ X₂ ≫ whiskerLeft Y₁ f₂) X₃ ≫
        whiskerLeft (tensorObj Y₁ Y₂) f₃) ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫
        (whiskerRight f₁ (tensorObj X₂ X₃) ≫ whiskerLeft Y₁ (whiskerRight f₂ X₃ ≫ whiskerLeft Y₂ f₃))
    rw [comp_whiskerRight, Category.assoc, Category.assoc, associator_naturality_right,
      ← Category.assoc (whiskerRight (whiskerLeft Y₁ f₂) X₃), associator_naturality_middle]
    simp only [Category.assoc]
    rw [← Category.assoc (whiskerRight (whiskerRight f₁ X₂) X₃), associator_naturality_left,
      whiskerLeft_comp]
    simp only [Category.assoc]
  leftUnitor_naturality {V W} f := by
    change whiskerLeft unit f ≫ (leftUnitor W).hom = (leftUnitor V).hom ≫ f
    apply TensorProduct.ext'
    intro r v
    change TensorProduct.lid k W ((map LinearMap.id (toLinearMap (homProj 0 f)) +
      map (unit.sgn 1) (toLinearMap (homProj 1 f)) : k ⊗[k] V →ₗ[k] k ⊗[k] W) (r ⊗ₜ v)) =
        f (TensorProduct.lid k V (r ⊗ₜ v))
    rw [unit_sgn, LinearMap.add_apply, map_tmul, map_tmul, ← tmul_add, lid_tmul, lid_tmul,
      coe_toLinearMap, coe_toLinearMap, ← add_apply, homProj_add_homProj, map_smul]
    rfl
  rightUnitor_naturality {V W} f := by
    apply TensorProduct.ext'
    intro v r
    change TensorProduct.rid k W (f v ⊗ₜ r) = f (TensorProduct.rid k V (v ⊗ₜ r))
    rw [rid_tmul, rid_tmul, map_smul]
  pentagon U V W X := by
    change whiskerRight (associator U V W).hom X ≫ (associator U (tensorObj V W) X).hom ≫
        whiskerLeft U (associator V W X).hom = _
    rw [whiskerLeft_even U (associator_mem V W X)]
    exact TensorProduct.ext_fourfold fun _ _ _ _ => rfl
  triangle V W := by
    change (associator V unit W).hom ≫ whiskerLeft V (leftUnitor W).hom =
      whiskerRight (rightUnitor V).hom W
    rw [whiskerLeft_even V (leftUnitor_mem W)]
    refine TensorProduct.ext_threefold fun v r w => ?_
    change v ⊗ₜ TensorProduct.lid k W (r ⊗ₜ w) = TensorProduct.rid k V (v ⊗ₜ r) ⊗ₜ w
    rw [lid_tmul, rid_tmul, smul_tmul]
  associator_hom_mem := associator_mem
  leftUnitor_hom_mem := leftUnitor_mem
  rightUnitor_hom_mem := rightUnitor_mem

/-! ## The parity shift -/

/-- The parity shift `Π V`: the module `V` with the opposite grading.-/
def piObj (V : SVec k) : SVec k where
  carrier := V
  odd := LinearMap.id - V.odd
  odd_comp_odd := by
    ext v
    simp [odd_apply_odd]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s7.730955035c60 from=translated src=- shape=10ae8526 vocab=4e6b4173
-/
theorem piObj_proj (V : SVec k) (p : ZMod 2) : (piObj V).proj p = V.proj (p + 1) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [proj_zero, zero_add, proj_one]
    ext v; simp [piObj]
  · rw [proj_one, zmod2_one_add_one, proj_zero]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s7.e76c328457e7 from=translated src=- shape=c7980c73 vocab=c9854ebc
-/
theorem piObj_part (V : SVec k) (p : ZMod 2) : (piObj V).part p = V.part (p + 1) := by
  simp only [part, piObj_proj]

/-- The odd isomorphism `ζ_V : Π V → V`, the identity function.-/
def ζIso (V : SVec k) : piObj V ≅ V where
  hom := ofHom LinearMap.id
  inv := ofHom LinearMap.id
  hom_inv_id := rfl
  inv_hom_id := rfl

/--
@isnad1 id=mem.0h2v.s8.db320866e68f from=translated src=- shape=d39c8ce3 vocab=02f43a18
-/
theorem ζIso_hom_mem (V : SVec k) : (ζIso V).hom ∈ parityHom (piObj V) V 1 := by
  intro q
  rw [piObj_proj]
  rfl

/-- **Brundan–Ellis, Example 1.8 (for `A = B = k`).** `SVec k` is a Π-supercategory, with
`Π V` the module `V` with the opposite grading and `ζ_V : Π V → V` the identity function.-/
instance instPiSupercategory : PiSupercategory k (SVec k) :=
  PiSupercategory.ofIso piObj ζIso ζIso_hom_mem

/-- A linear map `V → W`, viewed as a linear map `Π V → Π W` (the same function).-/
def piHom {V W : SVec k} : (V ⟶ W) →ₗ[k] (piObj V ⟶ piObj W) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
@isnad1 id=eq.0h6v.s10.bc11965644cc from=translated src=- shape=1c0f375d vocab=180c4e25
-/
@[simp] theorem piHom_comp {U V W : SVec k} (f : U ⟶ V) (g : V ⟶ W) :
    piHom (f ≫ g) = piHom f ≫ piHom g := rfl

/--
@isnad1 id=eq.0h2v.s8.47b5be9f0c8b from=translated src=- shape=fefda21f vocab=b415dde5
-/
@[simp] theorem piHom_id (V : SVec k) : piHom (𝟙 V) = 𝟙 (piObj V) := rfl

/--
@isnad1 id=eq.0h5v.s9.032844a3c7eb from=translated src=- shape=b7a65452 vocab=2057692e
-/
@[simp] theorem piHom_apply {V W : SVec k} (f : V ⟶ W) (v : V) : piHom f v = f v := rfl

/-- A linear map has the same parity as a map `V → W` and as a map `Π V → Π W`.
@isnad1 id=iff.0h5v.s10.e641ef5cfdb2 from=translated src=- shape=e3fc6346 vocab=21838a00
-/
theorem piHom_mem_iff {V W : SVec k} {p : ZMod 2} {f : V ⟶ W} :
    piHom f ∈ parityHom (piObj V) (piObj W) p ↔ f ∈ parityHom V W p := by
  constructor
  · intro h q
    have := h (q + 1)
    rw [piObj_proj, piObj_proj] at this
    have e1 : q + 1 + 1 = q := by rw [add_assoc, zmod2_one_add_one, add_zero]
    have e2 : q + 1 + p + 1 = q + p := by rw [add_right_comm, e1]
    rw [e1, e2] at this
    exact this
  · intro h q
    rw [piObj_proj, piObj_proj, show q + p + 1 = q + 1 + p by rw [add_right_comm]]
    exact h (q + 1)

/-- **Brundan–Ellis, Example 1.13(i) (for `A = k`).** `SVec k` is a monoidal Π-supercategory
with `π := Π k` and `ζ : Π k → k` the identity function.-/
instance instMonoidalPiSupercategory : MonoidalPiSupercategory k (SVec k) where
  pi := piObj unit
  ζ := ζIso unit
  ζ_hom_mem := ζIso_hom_mem unit

/-! ## Graded subspaces -/

section Sub

variable (V : SVec k) (U : Submodule k V) (hU : ∀ v ∈ U, V.odd v ∈ U)

/-- A graded submodule `U ⊆ V` (one stable under the projection onto `V₁`), as a superspace.-/
abbrev sub : SVec k where
  carrier := U
  odd := V.odd.restrict hU
  odd_comp_odd := by
    ext v
    simp [odd_apply_odd]

/--
@isnad1 id=eq.1h4v.s9.28dc729db450 from=translated src=- shape=7a068b55 vocab=950c66b1
-/
theorem sub_odd_apply (v : U) : ((sub V U hU).odd v : V) = V.odd v := rfl

/--
@isnad1 id=eq.1h5v.s9.8dd4800fe88f from=translated src=- shape=d02aac6c vocab=1bc2c5d5
-/
theorem sub_proj_apply (q : ZMod 2) (v : U) : ((sub V U hU).proj q v : V) = V.proj q v := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · simp [proj_zero]
  · simp [proj_one]

/--
@isnad1 id=iff.1h5v.s9.196ace8a93cb from=translated src=- shape=06d733c5 vocab=f1c044e3
-/
theorem mem_sub_part_iff {q : ZMod 2} {v : U} : v ∈ (sub V U hU).part q ↔ (v : V) ∈ V.part q := by
  rw [mem_part_iff, mem_part_iff, ← sub_proj_apply V U hU, Subtype.ext_iff]

variable {V U hU} {W : SVec k} {U' : Submodule k W} {hU' : ∀ w ∈ U', W.odd w ∈ U'}

/-- The restriction of a linear map to graded submodules.-/
def restrictHom (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') : sub V U hU ⟶ sub W U' hU' :=
  ofHom ((toLinearMap f).restrict hf)

/--
@isnad1 id=eq.3h7v.s10.8f69269ed023 from=translated src=- shape=7f158e9e vocab=b3ed1deb
-/
@[simp] theorem restrictHom_apply (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') (v : U) :
    (restrictHom (hU := hU) (hU' := hU') f hf v : W) = f v := rfl

/--
@isnad1 id=mem.4h7v.s10.51a5bce554bd from=translated src=- shape=a597bd40 vocab=18a6c6ba
-/
theorem restrictHom_mem {p : ZMod 2} {f : V ⟶ W} (hfp : f ∈ parityHom V W p)
    (hf : ∀ v ∈ U, f v ∈ U') : restrictHom (hU := hU) (hU' := hU') f hf ∈
      parityHom (sub V U hU) (sub W U' hU') p := by
  intro q
  ext v
  show f ((sub V U hU).proj q v : V) = ((sub W U' hU').proj (q + p) ⟨f v, hf v v.2⟩ : W)
  rw [sub_proj_apply, sub_proj_apply]
  exact apply_proj_of_mem hfp q v

end Sub

/-! ## Dimensions -/

section Dim

/-- The decomposition `V ≅ V₀ × V₁` of a superspace.-/
def partEquiv (V : SVec k) : V ≃ₗ[k] V.part 0 × V.part 1 where
  toFun v := (⟨V.proj 0 v, proj_mem_part V 0 v⟩, ⟨V.proj 1 v, proj_mem_part V 1 v⟩)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  invFun x := x.1 + x.2
  left_inv v := proj_apply_add V v
  right_inv x := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := x
    ext
    · simp [proj_apply_of_mem_part _ ha, proj_apply_of_mem_part _ hb]
    · simp [proj_apply_of_mem_part _ ha, proj_apply_of_mem_part _ hb]

/-- An even linear map sends `V_q` to `W_q`.-/
def partMap {V W : SVec k} (f : V ⟶ W) (hf : f ∈ parityHom V W 0) (q : ZMod 2) :
    V.part q →ₗ[k] W.part q :=
  (toLinearMap f).restrict fun v hv => by simpa using apply_mem_part hf hv

/--
@isnad1 id=eq.1h6v.s10.bbec6f865f1b from=translated src=- shape=eaee12bf vocab=3b8e19f7
-/
@[simp] theorem partMap_apply {V W : SVec k} (f : V ⟶ W) (hf : f ∈ parityHom V W 0) (q : ZMod 2)
    (v : V.part q) : (partMap f hf q v : W) = f v := rfl

/-- An even isomorphism of superspaces restricts to isomorphisms of the homogeneous
components.-/
def partEquivOfIso {V W : SVec k} (e : V ≅ W) (he : e.hom ∈ parityHom V W 0) (q : ZMod 2) :
    V.part q ≃ₗ[k] W.part q :=
  LinearEquiv.ofLinearMap (partMap e.hom he q) (partMap e.inv (inv_mem e he) q)
    (by ext v; simp [← comp_apply]) (by ext v; simp [← comp_apply])

/-- Superspaces with isomorphic homogeneous components are evenly isomorphic.-/
def isoOfPartEquiv {V W : SVec k} (e₀ : V.part 0 ≃ₗ[k] W.part 0) (e₁ : V.part 1 ≃ₗ[k] W.part 1) :
    V ≅ W :=
  isoOfLinearEquiv (V.partEquiv ≪≫ₗ e₀.prodCongr e₁ ≪≫ₗ W.partEquiv.symm)

/-- The homogeneous components of a biproduct (given by even maps satisfying the biproduct
equations) are the products of the components.-/
def partEquivOfBiprod {V X Y : SVec k} (i₁ : X ⟶ V) (i₂ : Y ⟶ V) (p₁ : V ⟶ X) (p₂ : V ⟶ Y)
    (hi₁ : i₁ ∈ parityHom X V 0) (hi₂ : i₂ ∈ parityHom Y V 0) (hp₁ : p₁ ∈ parityHom V X 0)
    (hp₂ : p₂ ∈ parityHom V Y 0) (h₁ : i₁ ≫ p₁ = 𝟙 X) (h₂ : i₂ ≫ p₂ = 𝟙 Y)
    (h₁₂ : i₁ ≫ p₂ = 0) (h₂₁ : i₂ ≫ p₁ = 0) (htot : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 V) (q : ZMod 2) :
    V.part q ≃ₗ[k] X.part q × Y.part q where
  toFun v := (partMap p₁ hp₁ q v, partMap p₂ hp₂ q v)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  invFun x := partMap i₁ hi₁ q x.1 + partMap i₂ hi₂ q x.2
  left_inv v := by
    apply Subtype.ext
    have := congrArg (fun φ : V ⟶ V => φ v) htot
    simpa using this
  right_inv x := by
    have e1 := fun (x : X) => congrArg (fun φ : X ⟶ X => φ x) h₁
    have e2 := fun (y : Y) => congrArg (fun φ : Y ⟶ Y => φ y) h₂
    have e3 := fun (x : X) => congrArg (fun φ : X ⟶ Y => φ x) h₁₂
    have e4 := fun (y : Y) => congrArg (fun φ : Y ⟶ X => φ y) h₂₁
    simp only [comp_apply, id_apply, zero_apply] at e1 e2 e3 e4
    ext <;> simp [e1, e2, e3, e4]

end Dim

section DimField

variable {K : Type u} [Field K]

/--
@isnad1 id=eq.9h9v.s11.3aa8bccea129 from=translated src=- shape=3d85421a vocab=464d42c0
-/
theorem finrank_part_of_biprod {V X Y : SVec K} (i₁ : X ⟶ V) (i₂ : Y ⟶ V) (p₁ : V ⟶ X)
    (p₂ : V ⟶ Y) (hi₁ : i₁ ∈ parityHom X V 0) (hi₂ : i₂ ∈ parityHom Y V 0)
    (hp₁ : p₁ ∈ parityHom V X 0) (hp₂ : p₂ ∈ parityHom V Y 0) (h₁ : i₁ ≫ p₁ = 𝟙 X)
    (h₂ : i₂ ≫ p₂ = 𝟙 Y) (h₁₂ : i₁ ≫ p₂ = 0) (h₂₁ : i₂ ≫ p₁ = 0)
    (htot : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 V) (q : ZMod 2) [Module.Finite K (X.part q)]
    [Module.Finite K (Y.part q)] :
    Module.finrank K (V.part q) = Module.finrank K (X.part q) + Module.finrank K (Y.part q) := by
  rw [(partEquivOfBiprod i₁ i₂ p₁ p₂ hi₁ hi₂ hp₁ hp₂ h₁ h₂ h₁₂ h₂₁ htot q).finrank_eq,
    Module.finrank_prod]

end DimField

end SVec

end StringDiagrams
