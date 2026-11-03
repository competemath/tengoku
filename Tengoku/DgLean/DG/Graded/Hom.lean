import Tengoku.DgLean.DG.Graded.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Graded maps of degree `n` and the graded `Hom`

Let `M` and `N` be additive groups graded by an additive monoid `ι` (in the rest of the library
`ι = ℤ`) in Mathlib's internal style: families `ℳ : ι → σ`, `𝒩 : ι → τ` of subobjects with
`[SetLike σ M]`, `[SetLike τ N]` and the closure assumptions `AddSubgroupClass`,
`AddSubmonoidClass`, `SMulMemClass` where needed, so that both gradings by additive subgroups
and gradings by submodules are covered.

## Main definitions

* `DG.HasDegree ℳ 𝒩 n f`: an additive map `f : M →+ N` has degree `n` if it sends `ℳ i` into
  `𝒩 (i + n)` for every `i`.
* `DG.GradedHom ℳ 𝒩 n`: the additive maps of degree `n`, bundled as a structure extending
  `M →+ N`, with `FunLike` and `AddMonoidHomClass` instances. It is an additive group, and an
  `R`-module whenever `N` is an `R`-module whose grading consists of `R`-submodules (no
  `R`-linearity of the maps is assumed). Composition `g.comp f` of maps of degrees `m` and `n`
  has degree `m + n`, and `GradedHom.id ℳ` has degree `0`.
* `DG.GradedHom.lift`, `DG.GradedHom.component`, `DG.GradedHom.liftEquiv`: a graded map of
  degree `n` is the same as a family of additive maps `ℳ i →+ 𝒩 (i + n)` (when `ℳ` is a
  `DirectSum.Decomposition`); `DG.GradedHom.ext_homogeneous`: two graded maps of the same degree
  agreeing on homogeneous elements are equal.
* `DG.GradedHOM ℳ 𝒩 := ⨁ n, GradedHom ℳ 𝒩 n`: the total graded `Hom`, with its canonical
  grading `DG.GradedHOM.grading ℳ 𝒩` (a `DirectSum.Decomposition`), the evaluation
  `DG.GradedHOM.eval ℳ 𝒩 : GradedHOM ℳ 𝒩 →+ (M →+ N)` and the biadditive composition
  `DG.GradedHOM.compHom`.
* `DG.GradedEND ℳ := GradedHOM ℳ ℳ`: the graded endomorphism ring, a `Ring` (through
  `DirectSum.GRing`) which is a `GradedRing` for its canonical grading `DG.GradedEND.grading ℳ`.

## Conventions

* A map of degree `n` sends degree `i` to degree `i + n` (not `n + i`); the distinction only
  matters for a non-commutative index monoid.
* If `f` has degree `m` and `g` has degree `n` then `g.comp f` (apply `f` first) has degree
  `m + n`. Consequently the product of the graded endomorphism ring is composition in
  diagrammatic order: `f * g = g.comp f`, that is `(f * g) x = g (f x)`; see
  `DG.GradedEND.of_mul_of` and `DG.GradedEND.eval_mul`. With this convention `GradedEND ℳ` acts on
  `M` on the right, and evaluation `DG.GradedEND.evalRingHom` is a ring homomorphism to the
  multiplicative opposite of `AddMonoid.End M`.
* No Koszul signs appear here: composition of graded maps is unsigned. Signs enter only in the
  compatibility of graded maps with graded actions, treated in later files.
-/

namespace DG

open DirectSum

variable {ι M N P σ τ υ : Type*}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [SetLike σ M] [SetLike τ N] [SetLike υ P]
variable (ℳ : ι → σ) (𝒩 : ι → τ) (𝒪 : ι → υ)

/-! ### Additive maps of degree `n` -/

section HasDegree

variable [Add ι]

/-- An additive map `f : M →+ N` has degree `n` with respect to the gradings `ℳ` and `𝒩` if it
sends the homogeneous component `ℳ i` into `𝒩 (i + n)` for every `i`.-/
def HasDegree (n : ι) (f : M →+ N) : Prop :=
  ∀ i, ∀ m ∈ ℳ i, f m ∈ 𝒩 (i + n)

variable {ℳ 𝒩}

/--
@isnad1 id=hasdegre.1h11v.s8.b3b11df7c555 from=translated src=- shape=22917da5 vocab=11954dbf
-/
theorem HasDegree.smul {R : Type*} [Monoid R] [DistribMulAction R N] [SMulMemClass τ R N]
    {n : ι} {f : M →+ N} (hf : HasDegree ℳ 𝒩 n f) (r : R) : HasDegree ℳ 𝒩 n (r • f) :=
  fun i m hm => SMulMemClass.smul_mem r (hf i m hm)

variable [AddSubgroupClass τ N]

/--
@isnad1 id=hasdegre.0h8v.s7.4adc086ebbeb from=translated src=- shape=764be623 vocab=7e977ad3
-/
theorem HasDegree.zero (n : ι) : HasDegree ℳ 𝒩 n 0 := fun _ _ _ => zero_mem _

/--
@isnad1 id=hasdegre.2h10v.s8.f19af0ef695a from=translated src=- shape=60e07200 vocab=2282cdb6
-/
theorem HasDegree.add {n : ι} {f g : M →+ N} (hf : HasDegree ℳ 𝒩 n f) (hg : HasDegree ℳ 𝒩 n g) :
    HasDegree ℳ 𝒩 n (f + g) := fun i m hm => add_mem (hf i m hm) (hg i m hm)

/--
@isnad1 id=hasdegre.1h9v.s7.fa2d4d7f1b7b from=translated src=- shape=a23d475b vocab=afcf31f1
-/
theorem HasDegree.neg {n : ι} {f : M →+ N} (hf : HasDegree ℳ 𝒩 n f) : HasDegree ℳ 𝒩 n (-f) :=
  fun i m hm => neg_mem (hf i m hm)

/--
@isnad1 id=hasdegre.2h10v.s8.f282c2d2c646 from=translated src=- shape=60e07200 vocab=67331a1f
-/
theorem HasDegree.sub {n : ι} {f g : M →+ N} (hf : HasDegree ℳ 𝒩 n f) (hg : HasDegree ℳ 𝒩 n g) :
    HasDegree ℳ 𝒩 n (f - g) := fun i m hm => sub_mem (hf i m hm) (hg i m hm)

/--
@isnad1 id=hasdegre.1h10v.s7.aa3ab456577b from=translated src=- shape=0b3798c6 vocab=18315f70
-/
theorem HasDegree.nsmul {n : ι} {f : M →+ N} (hf : HasDegree ℳ 𝒩 n f) (k : ℕ) :
    HasDegree ℳ 𝒩 n (k • f) := fun i m hm => nsmul_mem (hf i m hm) k

/--
@isnad1 id=hasdegre.1h10v.s7.ab8eda0ea4ee from=translated src=- shape=0b3798c6 vocab=90857e38
-/
theorem HasDegree.zsmul {n : ι} {f : M →+ N} (hf : HasDegree ℳ 𝒩 n f) (k : ℤ) :
    HasDegree ℳ 𝒩 n (k • f) := fun i m hm => zsmul_mem (hf i m hm) k

/--
@isnad1 id=hasdegre.1h11v.s7.4ac6d4a99c4b from=translated src=- shape=05f0fd78 vocab=b4799a69
-/
theorem HasDegree.sum {α : Type*} (s : Finset α) {n : ι} {f : α → M →+ N}
    (hf : ∀ a ∈ s, HasDegree ℳ 𝒩 n (f a)) : HasDegree ℳ 𝒩 n (∑ a ∈ s, f a) := fun i m hm => by
  rw [AddMonoidHom.finsetSum_apply]
  exact sum_mem fun a ha => hf a ha i m hm

end HasDegree

/--
@isnad1 id=hasdegre.2h14v.s7.e404119de68f from=translated src=- shape=9cf626ce vocab=d2ef3130
-/
theorem HasDegree.comp [AddSemigroup ι] {ℳ : ι → σ} {𝒩 : ι → τ} {𝒪 : ι → υ} {m n : ι}
    {f : M →+ N} {g : N →+ P} (hf : HasDegree ℳ 𝒩 m f) (hg : HasDegree 𝒩 𝒪 n g) :
    HasDegree ℳ 𝒪 (m + n) (g.comp f) := fun i x hx => by
  rw [AddMonoidHom.comp_apply, ← add_assoc]
  exact hg _ _ (hf i x hx)

/--
@isnad1 id=hasdegre.0h4v.s5.b4756701fb5b from=translated src=- shape=b62efe96 vocab=21e2bce8
-/
theorem HasDegree.id [AddZeroClass ι] (ℳ : ι → σ) : HasDegree ℳ ℳ 0 (AddMonoidHom.id M) :=
  fun i m hm => by simpa using hm

/-! ### Bundled maps of degree `n` -/

section GradedHom

variable [Add ι]

/-- The type of additive maps `M →+ N` of degree `n` with respect to the gradings `ℳ` and `𝒩`:
maps sending `ℳ i` into `𝒩 (i + n)` for every `i`.-/
structure GradedHom (n : ι) extends M →+ N where
  /-- A map of degree `n` sends degree `i` to degree `i + n`.-/
  map_mem' : ∀ i, ∀ m ∈ ℳ i, toFun m ∈ 𝒩 (i + n)

end GradedHom

namespace GradedHom

section Basic

variable [Add ι] {ℳ 𝒩} {n : ι}

set_option backward.isDefEq.respectTransparency false in
instance : FunLike (GradedHom ℳ 𝒩 n) M N where
  coe f := f.toFun
  coe_injective := by
    rintro ⟨_, _⟩ ⟨_, _⟩ h
    congr 1
    exact DFunLike.coe_injective h

instance : AddMonoidHomClass (GradedHom ℳ 𝒩 n) M N where
  map_add f := f.map_add'
  map_zero f := f.map_zero'

/--
@isnad1 id=eq.1h10v.s7.a2efab18b962 from=translated src=- shape=f9a71223 vocab=736b2662
-/
@[ext]
theorem ext {f g : GradedHom ℳ 𝒩 n} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/--
@isnad1 id=eq.1h9v.s8.f9c48406bb42 from=translated src=- shape=810c5a66 vocab=30b49344
-/
@[simp]
theorem coe_mk (f : M →+ N) (h) : ⇑(mk (ℳ := ℳ) (𝒩 := 𝒩) (n := n) f h) = f := rfl

/--
@isnad1 id=eq.0h9v.s7.cbbdd94c1291 from=translated src=- shape=7bac0f95 vocab=73655ddd
-/
@[simp]
theorem coe_toAddMonoidHom (f : GradedHom ℳ 𝒩 n) : ⇑f.toAddMonoidHom = f := rfl

/--
@isnad1 id=eq.1h9v.s7.c0b0a88cb32a from=translated src=- shape=50e3e678 vocab=f66d8a98
-/
@[simp]
theorem toAddMonoidHom_mk (f : M →+ N) (h) :
    (mk (ℳ := ℳ) (𝒩 := 𝒩) (n := n) f h).toAddMonoidHom = f := rfl

/--
@isnad1 id=injectiv.0h8v.s6.9a3112fd8d15 from=translated src=- shape=70006063 vocab=f18b72b9
-/
theorem toAddMonoidHom_injective :
    Function.Injective (toAddMonoidHom : GradedHom ℳ 𝒩 n → M →+ N) := fun _ _ h =>
  ext fun x => congrArg (fun k : M →+ N => k x) h

/--
@isnad1 id=mem.1h11v.s6.f0772018a1ce from=translated src=- shape=130b5e42 vocab=a749ced4
-/
theorem map_mem (f : GradedHom ℳ 𝒩 n) {i : ι} {m : M} (hm : m ∈ ℳ i) : f m ∈ 𝒩 (i + n) :=
  f.map_mem' i m hm

/--
@isnad1 id=hasdegre.0h9v.s6.55bf9e2b9de0 from=translated src=- shape=5f81274b vocab=233c0650
-/
theorem hasDegree (f : GradedHom ℳ 𝒩 n) : HasDegree ℳ 𝒩 n f.toAddMonoidHom := f.map_mem'

/-- Bundle an additive map of degree `n` as a `GradedHom`.-/
def ofHasDegree {f : M →+ N} (hf : HasDegree ℳ 𝒩 n f) : GradedHom ℳ 𝒩 n := ⟨f, hf⟩

/--
@isnad1 id=eq.1h9v.s7.b39a588a29c6 from=translated src=- shape=96bd9b93 vocab=fd165b28
-/
@[simp]
theorem toAddMonoidHom_ofHasDegree {f : M →+ N} (hf : HasDegree ℳ 𝒩 n f) :
    (ofHasDegree hf).toAddMonoidHom = f := rfl

/--
@isnad1 id=eq.1h9v.s7.05b84f672743 from=translated src=- shape=a54f3371 vocab=56d32cd4
-/
@[simp]
theorem coe_ofHasDegree {f : M →+ N} (hf : HasDegree ℳ 𝒩 n f) : ⇑(ofHasDegree hf) = f := rfl

/-- The map `f : M →+ N` has degree `n` if and only if it is the underlying additive map of a
`GradedHom ℳ 𝒩 n`.
@isnad1 id=iff.0h9v.s7.5473490d5bfd from=translated src=- shape=97ac5b01 vocab=0eacedec
-/
theorem hasDegree_iff {f : M →+ N} :
    HasDegree ℳ 𝒩 n f ↔ ∃ g : GradedHom ℳ 𝒩 n, g.toAddMonoidHom = f :=
  ⟨fun h => ⟨ofHasDegree h, rfl⟩, fun ⟨g, hg⟩ => hg ▸ g.hasDegree⟩

/-- The linear map underlying a graded map which commutes with the scalars.-/
@[simps]
def toLinearMap {R : Type*} [Semiring R] [Module R M] [Module R N] (f : GradedHom ℳ 𝒩 n)
    (hf : ∀ (r : R) (x : M), f (r • x) = r • f x) : M →ₗ[R] N where
  toFun := f
  map_add' := map_add f
  map_smul' := hf

end Basic

section Component

variable [Add ι] {ℳ 𝒩} {n : ι} [AddSubmonoidClass σ M] [AddSubmonoidClass τ N]

/-- The homogeneous component of a graded map of degree `n`: its restriction to `ℳ i`, with
values in `𝒩 (i + n)`.-/
def component (f : GradedHom ℳ 𝒩 n) (i : ι) : ℳ i →+ 𝒩 (i + n) where
  toFun m := ⟨f m, f.map_mem m.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

/--
@isnad1 id=eq.0h11v.s9.4ae1f86f4c9f from=translated src=- shape=fdfce56d vocab=5cb95c03
-/
@[simp]
theorem coe_component_apply (f : GradedHom ℳ 𝒩 n) (i : ι) (m : ℳ i) :
    (f.component i m : N) = f m := rfl

end Component

/-! #### The additive group structure -/

section AddCommGroup

variable [Add ι] {ℳ 𝒩} {n : ι} [AddSubgroupClass τ N]

instance : Zero (GradedHom ℳ 𝒩 n) := ⟨ofHasDegree (HasDegree.zero n)⟩
instance : Add (GradedHom ℳ 𝒩 n) := ⟨fun f g => ofHasDegree (f.hasDegree.add g.hasDegree)⟩
instance : Neg (GradedHom ℳ 𝒩 n) := ⟨fun f => ofHasDegree f.hasDegree.neg⟩
instance : Sub (GradedHom ℳ 𝒩 n) := ⟨fun f g => ofHasDegree (f.hasDegree.sub g.hasDegree)⟩
instance : SMul ℕ (GradedHom ℳ 𝒩 n) := ⟨fun k f => ofHasDegree (f.hasDegree.nsmul k)⟩
instance : SMul ℤ (GradedHom ℳ 𝒩 n) := ⟨fun k f => ofHasDegree (f.hasDegree.zsmul k)⟩

/--
@isnad1 id=eq.0h8v.s7.b5b8eac41577 from=translated src=- shape=ad9eee26 vocab=39860c5c
-/
@[simp] theorem toAddMonoidHom_zero : (0 : GradedHom ℳ 𝒩 n).toAddMonoidHom = 0 := rfl
/--
@isnad1 id=eq.0h10v.s8.53387d21c9bc from=translated src=- shape=dc118e1c vocab=f099003a
-/
@[simp] theorem toAddMonoidHom_add (f g : GradedHom ℳ 𝒩 n) :
    (f + g).toAddMonoidHom = f.toAddMonoidHom + g.toAddMonoidHom := rfl
/--
@isnad1 id=eq.0h9v.s7.c0fad7ef2258 from=translated src=- shape=3563ec0e vocab=3b22697c
-/
@[simp] theorem toAddMonoidHom_neg (f : GradedHom ℳ 𝒩 n) :
    (-f).toAddMonoidHom = -f.toAddMonoidHom := rfl
/--
@isnad1 id=eq.0h10v.s8.da1a24abd91c from=translated src=- shape=dc118e1c vocab=1b43cb93
-/
@[simp] theorem toAddMonoidHom_sub (f g : GradedHom ℳ 𝒩 n) :
    (f - g).toAddMonoidHom = f.toAddMonoidHom - g.toAddMonoidHom := rfl
/--
@isnad1 id=eq.0h10v.s8.dbfcb703fb66 from=translated src=- shape=458902c1 vocab=7bb5f458
-/
@[simp] theorem toAddMonoidHom_nsmul (k : ℕ) (f : GradedHom ℳ 𝒩 n) :
    (k • f).toAddMonoidHom = k • f.toAddMonoidHom := rfl
/--
@isnad1 id=eq.0h10v.s8.45335a51d70e from=translated src=- shape=458902c1 vocab=375adeb7
-/
@[simp] theorem toAddMonoidHom_zsmul (k : ℤ) (f : GradedHom ℳ 𝒩 n) :
    (k • f).toAddMonoidHom = k • f.toAddMonoidHom := rfl

/--
@isnad1 id=eq.0h8v.s7.fd1a75550eeb from=translated src=- shape=8654a99c vocab=aa58c1a1
-/
@[simp] theorem coe_zero : ⇑(0 : GradedHom ℳ 𝒩 n) = 0 := rfl
/--
@isnad1 id=eq.0h10v.s8.1d06d3adc894 from=translated src=- shape=1ce6b10f vocab=ed270fd8
-/
@[simp] theorem coe_add (f g : GradedHom ℳ 𝒩 n) : ⇑(f + g) = ⇑f + ⇑g := rfl
/--
@isnad1 id=eq.0h9v.s7.178a647b40f4 from=translated src=- shape=9a842733 vocab=14bfbd08
-/
@[simp] theorem coe_neg (f : GradedHom ℳ 𝒩 n) : ⇑(-f) = -⇑f := rfl
/--
@isnad1 id=eq.0h10v.s8.b8fde129f502 from=translated src=- shape=1ce6b10f vocab=1714e752
-/
@[simp] theorem coe_sub (f g : GradedHom ℳ 𝒩 n) : ⇑(f - g) = ⇑f - ⇑g := rfl
/--
@isnad1 id=eq.0h10v.s7.8c160031a22a from=translated src=- shape=be96179a vocab=c559e2a6
-/
@[simp] theorem coe_nsmul (k : ℕ) (f : GradedHom ℳ 𝒩 n) : ⇑(k • f) = k • ⇑f := rfl
/--
@isnad1 id=eq.0h10v.s7.ddb35e0a7fae from=translated src=- shape=be96179a vocab=c57b0395
-/
@[simp] theorem coe_zsmul (k : ℤ) (f : GradedHom ℳ 𝒩 n) : ⇑(k • f) = k • ⇑f := rfl

/--
@isnad1 id=eq.0h9v.s7.9f6457b7ae30 from=translated src=- shape=94b88fe4 vocab=aa58c1a1
-/
theorem zero_apply (x : M) : (0 : GradedHom ℳ 𝒩 n) x = 0 := rfl
/--
@isnad1 id=eq.0h11v.s8.60bb416f42f8 from=translated src=- shape=f4de15fc vocab=ed270fd8
-/
theorem add_apply (f g : GradedHom ℳ 𝒩 n) (x : M) : (f + g) x = f x + g x := rfl
/--
@isnad1 id=eq.0h10v.s7.1347eccee6de from=translated src=- shape=2037b5d9 vocab=14bfbd08
-/
theorem neg_apply (f : GradedHom ℳ 𝒩 n) (x : M) : (-f) x = -f x := rfl
/--
@isnad1 id=eq.0h11v.s8.905cf985a2d8 from=translated src=- shape=f4de15fc vocab=1714e752
-/
theorem sub_apply (f g : GradedHom ℳ 𝒩 n) (x : M) : (f - g) x = f x - g x := rfl
/--
@isnad1 id=eq.0h11v.s7.a200ec970364 from=translated src=- shape=1d9f9f33 vocab=c559e2a6
-/
theorem nsmul_apply (k : ℕ) (f : GradedHom ℳ 𝒩 n) (x : M) : (k • f) x = k • f x := rfl
/--
@isnad1 id=eq.0h11v.s7.dbddbd641680 from=translated src=- shape=1d9f9f33 vocab=c57b0395
-/
theorem zsmul_apply (k : ℤ) (f : GradedHom ℳ 𝒩 n) (x : M) : (k • f) x = k • f x := rfl

instance : AddCommGroup (GradedHom ℳ 𝒩 n) :=
  toAddMonoidHom_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

variable (ℳ 𝒩 n) in
/-- The underlying additive map, as an additive map `GradedHom ℳ 𝒩 n →+ (M →+ N)`.-/
@[simps]
def coeAddMonoidHom : GradedHom ℳ 𝒩 n →+ (M →+ N) where
  toFun := toAddMonoidHom
  map_zero' := rfl
  map_add' _ _ := rfl

/--
@isnad1 id=injectiv.0h8v.s9.1de2b977a449 from=translated src=- shape=3f10bd6e vocab=8f1f3554
-/
theorem coeAddMonoidHom_injective : Function.Injective (coeAddMonoidHom ℳ 𝒩 n) :=
  toAddMonoidHom_injective

end AddCommGroup

/-! #### Scalar multiplication -/

section SMul

variable [Add ι] {ℳ 𝒩} {n : ι}
variable {R : Type*} [Monoid R] [DistribMulAction R N] [SMulMemClass τ R N]

instance : SMul R (GradedHom ℳ 𝒩 n) := ⟨fun r f => ofHasDegree (f.hasDegree.smul r)⟩

/--
@isnad1 id=eq.0h11v.s8.b36b620a9d9f from=translated src=- shape=6aa0c2c4 vocab=cb0bdccc
-/
@[simp] theorem toAddMonoidHom_smul (r : R) (f : GradedHom ℳ 𝒩 n) :
    (r • f).toAddMonoidHom = r • f.toAddMonoidHom := rfl
/--
@isnad1 id=eq.0h11v.s8.5805b28c7ac2 from=translated src=- shape=e01eeeed vocab=dffbfacb
-/
@[simp] theorem coe_smul (r : R) (f : GradedHom ℳ 𝒩 n) : ⇑(r • f) = r • ⇑f := rfl
/--
@isnad1 id=eq.0h12v.s8.baffce62f601 from=translated src=- shape=d33fcceb vocab=dffbfacb
-/
theorem smul_apply (r : R) (f : GradedHom ℳ 𝒩 n) (x : M) : (r • f) x = r • f x := rfl

variable [AddSubgroupClass τ N]

instance : DistribMulAction R (GradedHom ℳ 𝒩 n) :=
  toAddMonoidHom_injective.distribMulAction (coeAddMonoidHom ℳ 𝒩 n) fun _ _ => rfl

end SMul

section Module

variable [Add ι] {ℳ 𝒩} {n : ι} [AddSubgroupClass τ N]
variable {R : Type*} [Semiring R] [Module R N] [SMulMemClass τ R N]

/-- Graded maps of degree `n` into an `R`-module `N` whose grading consists of `R`-submodules form
an `R`-module. (No `R`-linearity of the maps is assumed.)-/
instance : Module R (GradedHom ℳ 𝒩 n) :=
  toAddMonoidHom_injective.module R (coeAddMonoidHom ℳ 𝒩 n) fun _ _ => rfl

end Module

/-! #### Composition and identity -/

section Comp

variable [AddSemigroup ι] {ℳ 𝒩 𝒪}

/-- Composition of graded maps: if `f` has degree `m` and `g` has degree `n` then `g.comp f` has
degree `m + n`.-/
def comp {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) : GradedHom ℳ 𝒪 (m + n) :=
  ofHasDegree (f.hasDegree.comp g.hasDegree)

/--
@isnad1 id=eq.0h14v.s7.3ca5cd9fb06a from=translated src=- shape=f106e776 vocab=4904eae9
-/
@[simp] theorem toAddMonoidHom_comp {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    (g.comp f).toAddMonoidHom = g.toAddMonoidHom.comp f.toAddMonoidHom := rfl
/--
@isnad1 id=eq.0h14v.s7.7239696eeb8e from=translated src=- shape=2412993c vocab=5f2bc514
-/
@[simp] theorem coe_comp {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    ⇑(g.comp f) = g ∘ f := rfl
/--
@isnad1 id=eq.0h15v.s7.9906ebc7b02b from=translated src=- shape=15136c64 vocab=e5baf5e0
-/
theorem comp_apply {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) (x : M) :
    g.comp f x = g (f x) := rfl

/-- Graded maps of possibly different degrees are heterogeneously equal as soon as their degrees
agree and they agree pointwise.
@isnad1 id=heq.2h11v.s7.ff976e2d2138 from=translated src=- shape=75d2addd vocab=2230a3eb
-/
theorem heq_of_forall {m n : ι} {f : GradedHom ℳ 𝒩 m} {g : GradedHom ℳ 𝒩 n} (hmn : m = n)
    (h : ∀ x, f x = g x) : HEq f g := by
  subst hmn
  exact heq_of_eq (ext h)

/--
@isnad1 id=heq.0h19v.s8.8cdf6a1b72d2 from=translated src=- shape=223c2a69 vocab=c2538625
-/
theorem comp_assoc {Q ω : Type*} [AddCommGroup Q] [SetLike ω Q] {𝒬 : ι → ω} {m n p : ι}
    (h : GradedHom 𝒪 𝒬 p) (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    HEq ((h.comp g).comp f) (h.comp (g.comp f)) :=
  heq_of_forall (add_assoc m n p).symm fun _ => rfl

/--
@isnad1 id=eq.0h19v.s8.8fca529560e1 from=translated src=- shape=e4d1f339 vocab=9d664c1a
-/
theorem toAddMonoidHom_comp_assoc {Q ω : Type*} [AddCommGroup Q] [SetLike ω Q] {𝒬 : ι → ω}
    {m n p : ι} (h : GradedHom 𝒪 𝒬 p) (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    ((h.comp g).comp f).toAddMonoidHom = (h.comp (g.comp f)).toAddMonoidHom := rfl

variable [AddSubgroupClass υ P]

/--
@isnad1 id=eq.0h13v.s8.ac977eff7cb8 from=translated src=- shape=166a6762 vocab=dd3c574a
-/
@[simp] theorem zero_comp {m n : ι} (f : GradedHom ℳ 𝒩 m) :
    (0 : GradedHom 𝒩 𝒪 n).comp f = 0 := rfl
/--
@isnad1 id=eq.0h15v.s8.be4629bf9689 from=translated src=- shape=18f118cc vocab=dd3c574a
-/
theorem add_comp {m n : ι} (g₁ g₂ : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f := rfl
/--
@isnad1 id=eq.0h14v.s8.a04c66ca32c7 from=translated src=- shape=e4e5b5f2 vocab=c288dd8d
-/
theorem neg_comp {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    (-g).comp f = -g.comp f := rfl
/--
@isnad1 id=eq.0h15v.s8.729f17218f56 from=translated src=- shape=3d916028 vocab=24ac659c
-/
theorem sub_comp {m n : ι} (g₁ g₂ : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    (g₁ - g₂).comp f = g₁.comp f - g₂.comp f := rfl

variable [AddSubgroupClass τ N]

/--
@isnad1 id=eq.0h13v.s8.5b2abb91a01e from=translated src=- shape=99b06350 vocab=dd3c574a
-/
@[simp] theorem comp_zero {m n : ι} (g : GradedHom 𝒩 𝒪 n) :
    g.comp (0 : GradedHom ℳ 𝒩 m) = 0 := ext fun _ => map_zero g
/--
@isnad1 id=eq.0h15v.s8.2a8b46199e74 from=translated src=- shape=f77fb3af vocab=dd3c574a
-/
theorem comp_add {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f₁ f₂ : GradedHom ℳ 𝒩 m) :
    g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ := ext fun _ => map_add g _ _
/--
@isnad1 id=eq.0h14v.s8.1586ca72083a from=translated src=- shape=0e56342f vocab=c288dd8d
-/
theorem comp_neg {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    g.comp (-f) = -g.comp f := ext fun _ => map_neg g _
/--
@isnad1 id=eq.0h15v.s8.fa4a2b31d4c7 from=translated src=- shape=67fba07b vocab=24ac659c
-/
theorem comp_sub {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f₁ f₂ : GradedHom ℳ 𝒩 m) :
    g.comp (f₁ - f₂) = g.comp f₁ - g.comp f₂ := ext fun _ => map_sub g _ _

/-- Composition as a biadditive map on the homogeneous pieces `GradedHom`.-/
@[simps]
def compAddMonoidHom (m n : ι) :
    GradedHom 𝒩 𝒪 n →+ GradedHom ℳ 𝒩 m →+ GradedHom ℳ 𝒪 (m + n) where
  toFun g := AddMonoidHom.mk' g.comp (comp_add g)
  map_zero' := AddMonoidHom.ext fun f => zero_comp f
  map_add' g₁ g₂ := AddMonoidHom.ext fun f => add_comp g₁ g₂ f

end Comp

section Id

variable [AddZeroClass ι]

/-- The identity as a graded map of degree `0`.-/
def id : GradedHom ℳ ℳ 0 := ofHasDegree (HasDegree.id ℳ)

/--
@isnad1 id=eq.0h4v.s6.8f02ae636998 from=translated src=- shape=82a06f51 vocab=ee20c5c3
-/
@[simp] theorem toAddMonoidHom_id : (id ℳ).toAddMonoidHom = AddMonoidHom.id M := rfl
/--
@isnad1 id=eq.0h4v.s6.57e2310a8e85 from=translated src=- shape=ac9906b4 vocab=d9af359b
-/
@[simp] theorem coe_id : ⇑(id ℳ) = _root_.id := rfl
/--
@isnad1 id=eq.0h5v.s6.06afdfcbbc86 from=translated src=- shape=304681d7 vocab=21bc90ce
-/
theorem id_apply (x : M) : id ℳ x = x := rfl

end Id

section Monoid

variable [AddMonoid ι] {ℳ 𝒩}

/--
@isnad1 id=heq.0h9v.s7.f3d33255f0f5 from=translated src=- shape=11b01b6a vocab=2014f3b0
-/
theorem comp_id {m : ι} (f : GradedHom ℳ 𝒩 m) : HEq (f.comp (id ℳ)) f :=
  heq_of_forall (zero_add m) fun _ => rfl

/--
@isnad1 id=heq.0h9v.s7.a833f973c077 from=translated src=- shape=66c8841f vocab=2014f3b0
-/
theorem id_comp {m : ι} (f : GradedHom ℳ 𝒩 m) : HEq ((id 𝒩).comp f) f :=
  heq_of_forall (add_zero m) fun _ => rfl

/--
@isnad1 id=eq.0h9v.s7.9fb21c4fea33 from=translated src=- shape=9932b802 vocab=20834b42
-/
@[simp] theorem toAddMonoidHom_comp_id {m : ι} (f : GradedHom ℳ 𝒩 m) :
    (f.comp (id ℳ)).toAddMonoidHom = f.toAddMonoidHom := rfl
/--
@isnad1 id=eq.0h9v.s7.aed83c733669 from=translated src=- shape=480b7886 vocab=20834b42
-/
@[simp] theorem toAddMonoidHom_id_comp {m : ι} (f : GradedHom ℳ 𝒩 m) :
    ((id 𝒩).comp f).toAddMonoidHom = f.toAddMonoidHom := rfl

end Monoid

/-! #### Graded maps out of a decomposed object -/

section Decomposition

variable [Add ι] [DecidableEq ι] {ℳ 𝒩} {n : ι} [AddSubmonoidClass σ M] [Decomposition ℳ]

/-- Two graded maps of the same degree agreeing on homogeneous elements are equal.
@isnad1 id=eq.1h10v.s7.c1c3fd6a4770 from=translated src=- shape=5fa0b505 vocab=5ef16f2e
-/
theorem ext_homogeneous {f g : GradedHom ℳ 𝒩 n} (h : ∀ (i : ι) (m : ℳ i), f m = g m) : f = g :=
  toAddMonoidHom_injective (decompose_addHom_ext ℳ h)

section Lift

variable [AddSubmonoidClass τ N]

/-- The graded map of degree `n` extending a family of additive maps `ℳ i →+ 𝒩 (i + n)` on the
homogeneous components.-/
def lift (φ : ∀ i, ℳ i →+ 𝒩 (i + n)) : GradedHom ℳ 𝒩 n :=
  ofHasDegree (f := liftHomogeneous ℳ fun i => (AddSubmonoidClass.subtype _).comp (φ i))
    fun i m hm => by
      rw [liftHomogeneous_of_mem ℳ _ hm]
      exact (φ i ⟨m, hm⟩).2

/--
@isnad1 id=eq.0h11v.s9.f02027e757d2 from=translated src=- shape=d2eb4da7 vocab=4974c7a2
-/
@[simp]
theorem lift_coe (φ : ∀ i, ℳ i →+ 𝒩 (i + n)) {i : ι} (m : ℳ i) : lift φ m = φ i m :=
  liftHomogeneous_coe ℳ _ m

/--
@isnad1 id=eq.1h11v.s9.ac9d6a36f938 from=translated src=- shape=e9a089ed vocab=0fb81e64
-/
theorem lift_of_mem (φ : ∀ i, ℳ i →+ 𝒩 (i + n)) {i : ι} {m : M} (hm : m ∈ ℳ i) :
    lift φ m = φ i ⟨m, hm⟩ :=
  lift_coe φ ⟨m, hm⟩

/--
@isnad1 id=eq.0h10v.s10.29e9328566eb from=translated src=- shape=3b00876a vocab=471bd755
-/
theorem lift_apply (φ : ∀ i, ℳ i →+ 𝒩 (i + n)) (m : M) :
    lift φ m = DirectSum.toAddMonoid (fun i => (AddSubmonoidClass.subtype _).comp (φ i))
      (decompose ℳ m) := rfl

/--
@isnad1 id=eq.0h10v.s8.a1306f6fbe46 from=translated src=- shape=b017fa60 vocab=30d1760a
-/
@[simp]
theorem component_lift (φ : ∀ i, ℳ i →+ 𝒩 (i + n)) (i : ι) : (lift φ).component i = φ i :=
  AddMonoidHom.ext fun m => Subtype.ext (lift_coe φ m)

/--
@isnad1 id=eq.0h9v.s7.f0a465db88eb from=translated src=- shape=de3b2e1d vocab=a6668664
-/
@[simp]
theorem lift_component (f : GradedHom ℳ 𝒩 n) : lift f.component = f :=
  ext_homogeneous fun _ _ => lift_coe _ _

end Lift

section LiftEquiv

variable (ℳ 𝒩 n) [AddSubgroupClass τ N]

/-- Graded maps of degree `n` are the same as families of additive maps `ℳ i →+ 𝒩 (i + n)`.-/
def liftEquiv : (∀ i, ℳ i →+ 𝒩 (i + n)) ≃+ GradedHom ℳ 𝒩 n where
  toFun := lift
  invFun := component
  left_inv φ := funext (component_lift φ)
  right_inv := lift_component
  map_add' φ ψ := ext_homogeneous fun _ _ => by simp

end LiftEquiv

end Decomposition

end GradedHom

/-! ### The total graded `Hom` -/

section GradedHOM

variable [Add ι] [DecidableEq ι] [AddSubgroupClass τ N]

/-- The total graded `Hom` from `ℳ` to `𝒩`: the direct sum over all degrees `n` of the maps of
degree `n`.-/
abbrev GradedHOM : Type _ := ⨁ n : ι, GradedHom ℳ 𝒩 n

namespace GradedHOM

/-- The canonical grading of the total graded `Hom`: the degree-`n` component is the image of
`GradedHom ℳ 𝒩 n`.-/
abbrev grading : ι → AddSubgroup (GradedHOM ℳ 𝒩) := summand fun n => GradedHom ℳ 𝒩 n

/-- Evaluation of the total graded `Hom` on `M`: the additive map `GradedHOM ℳ 𝒩 →+ (M →+ N)`
which is the underlying additive map on each summand.-/
def eval : GradedHOM ℳ 𝒩 →+ (M →+ N) :=
  DirectSum.toAddMonoid fun n => GradedHom.coeAddMonoidHom ℳ 𝒩 n

/--
@isnad1 id=eq.0h9v.s10.716c0355aac8 from=translated src=- shape=0383a4b8 vocab=4c18387a
-/
@[simp]
theorem eval_of (n : ι) (f : GradedHom ℳ 𝒩 n) :
    eval ℳ 𝒩 (DirectSum.of (fun n => GradedHom ℳ 𝒩 n) n f) = f.toAddMonoidHom :=
  DirectSum.toAddMonoid_of _ _ _

/--
@isnad1 id=eq.0h10v.s10.aa452a6b2fbe from=translated src=- shape=e1da6055 vocab=2a3e1a3c
-/
theorem eval_of_apply (n : ι) (f : GradedHom ℳ 𝒩 n) (x : M) :
    eval ℳ 𝒩 (DirectSum.of (fun n => GradedHom ℳ 𝒩 n) n f) x = f x := by simp

end GradedHOM

end GradedHOM

section GradedHOMComp

variable [AddSemigroup ι] [DecidableEq ι] [AddSubgroupClass τ N] [AddSubgroupClass υ P]
variable {ℳ 𝒩 𝒪}

namespace GradedHOM

/-- Composition on the total graded `Hom`, as a biadditive map: on the summands it is the
composition `GradedHom.comp`, of degree `m + n` on maps of degrees `m` and `n`.-/
def compHom : GradedHOM 𝒩 𝒪 →+ GradedHOM ℳ 𝒩 →+ GradedHOM ℳ 𝒪 :=
  DirectSum.toAddMonoid fun n =>
    AddMonoidHom.mk'
      (fun g => DirectSum.toAddMonoid fun m =>
        (DirectSum.of (fun k => GradedHom ℳ 𝒪 k) (m + n)).comp (GradedHom.compAddMonoidHom m n g))
      fun g₁ g₂ => DirectSum.addHom_ext fun m f => by simp [GradedHom.add_comp]

/--
@isnad1 id=eq.0h14v.s12.eba15ab1edd6 from=translated src=- shape=d8982ea3 vocab=8d1ad8e4
-/
@[simp]
theorem compHom_of_of {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    compHom (DirectSum.of (fun n => GradedHom 𝒩 𝒪 n) n g)
        (DirectSum.of (fun m => GradedHom ℳ 𝒩 m) m f) =
      DirectSum.of (fun k => GradedHom ℳ 𝒪 k) (m + n) (g.comp f) := by
  simp [compHom]

/-- Evaluation is compatible with composition: `eval (compHom g f) = (eval g).comp (eval f)`.
@isnad1 id=eq.0h12v.s12.858956da596e from=translated src=- shape=64a6c38d vocab=e7343be5
-/
theorem eval_compHom (g : GradedHOM 𝒩 𝒪) (f : GradedHOM ℳ 𝒩) :
    eval ℳ 𝒪 (compHom g f) = (eval 𝒩 𝒪 g).comp (eval ℳ 𝒩 f) := by
  induction g using DirectSum.induction_on with
  | zero => simp
  | of n g =>
    induction f using DirectSum.induction_on with
    | zero => simp
    | of m f => simp
    | add f₁ f₂ h₁ h₂ => simp [map_add, h₁, h₂, AddMonoidHom.comp_add]
  | add g₁ g₂ h₁ h₂ => simp [map_add, h₁, h₂, AddMonoidHom.add_comp]

/--
@isnad1 id=eq.0h13v.s12.347770e88a6d from=translated src=- shape=89e0f68c vocab=f5b0b65a
-/
theorem eval_compHom_apply (g : GradedHOM 𝒩 𝒪) (f : GradedHOM ℳ 𝒩) (x : M) :
    eval ℳ 𝒪 (compHom g f) x = eval 𝒩 𝒪 g (eval ℳ 𝒩 f x) := by
  rw [eval_compHom]; rfl

end GradedHOM

end GradedHOMComp

/-! ### The graded endomorphism ring -/

section GradedEND

namespace GradedEND

variable [AddMonoid ι]

instance instGOne : GradedMonoid.GOne fun n => GradedHom ℳ ℳ n := ⟨GradedHom.id ℳ⟩

/-- The graded multiplication on `GradedEND ℳ` is composition in diagrammatic order: for `f` of
degree `m` and `g` of degree `n`, `f * g = g.comp f` has degree `m + n`.-/
instance instGMul : GradedMonoid.GMul fun n => GradedHom ℳ ℳ n := ⟨fun f g => g.comp f⟩

/--
@isnad1 id=eq.0h4v.s6.1c6e78ec803a from=translated src=- shape=b260c2fc vocab=eaead79c
-/
theorem gOne_eq : (GradedMonoid.GOne.one : GradedHom ℳ ℳ 0) = GradedHom.id ℳ := rfl

/--
@isnad1 id=eq.0h8v.s7.3aa34b92d7b6 from=translated src=- shape=2af6eb32 vocab=b7a426b1
-/
theorem gMul_eq {m n : ι} (f : GradedHom ℳ ℳ m) (g : GradedHom ℳ ℳ n) :
    (GradedMonoid.GMul.mul f g : GradedHom ℳ ℳ (m + n)) = g.comp f := rfl

end GradedEND

variable [AddMonoid ι] [DecidableEq ι] [AddSubgroupClass σ M]

/-- The graded endomorphism ring of a graded additive group: the total graded `Hom` from `ℳ` to
itself. Its product is composition in diagrammatic order, `f * g = g.comp f`.-/
abbrev GradedEND : Type _ := GradedHOM ℳ ℳ

namespace GradedEND

instance instGRing : DirectSum.GRing fun n => GradedHom ℳ ℳ n where
  mul_zero _ := GradedHom.zero_comp _
  zero_mul _ := GradedHom.comp_zero _
  mul_add _ _ _ := GradedHom.add_comp _ _ _
  add_mul _ _ _ := GradedHom.comp_add _ _ _
  one_mul _ := Sigma.ext (zero_add _) (GradedHom.comp_id _)
  mul_one _ := Sigma.ext (add_zero _) (GradedHom.id_comp _)
  mul_assoc _ _ _ := Sigma.ext (add_assoc _ _ _) (GradedHom.comp_assoc _ _ _).symm
  natCast k := k • GradedHom.id ℳ
  natCast_zero := zero_nsmul _
  natCast_succ k := succ_nsmul _ k
  intCast k := k • GradedHom.id ℳ
  intCast_ofNat k := natCast_zsmul _ k
  intCast_negSucc_ofNat k := negSucc_zsmul _ k

/-- The canonical grading of the graded endomorphism ring.-/
abbrev grading : ι → AddSubgroup (GradedEND ℳ) := GradedHOM.grading ℳ ℳ

/-- The graded endomorphism ring is a graded ring with respect to its canonical grading.-/
noncomputable instance instGradedRing : GradedRing (grading ℳ) := inferInstance

variable {ℳ}

/--
@isnad1 id=eq.0h4v.s10.c60d1320e7f8 from=translated src=- shape=722ae177 vocab=23a98111
-/
theorem one_def :
    (1 : GradedEND ℳ) = DirectSum.of (fun n => GradedHom ℳ ℳ n) 0 (GradedHom.id ℳ) :=
  rfl

/--
@isnad1 id=eq.0h8v.s11.0c97f661735c from=translated src=- shape=6cfa4d16 vocab=a0399c4a
-/
theorem of_mul_of {m n : ι} (f : GradedHom ℳ ℳ m) (g : GradedHom ℳ ℳ n) :
    DirectSum.of (fun n => GradedHom ℳ ℳ n) m f * DirectSum.of (fun n => GradedHom ℳ ℳ n) n g =
      DirectSum.of (fun n => GradedHom ℳ ℳ n) (m + n) (g.comp f) :=
  DirectSum.of_mul_of f g

/-- The product on `GradedEND ℳ` is the composition `GradedHOM.compHom` in diagrammatic order.
@isnad1 id=eq.0h6v.s12.d9c89b0e2617 from=translated src=- shape=5f125aad vocab=d4a7da12
-/
theorem mul_eq_compHom (f g : GradedEND ℳ) : f * g = GradedHOM.compHom g f := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | of m f =>
    induction g using DirectSum.induction_on with
    | zero => simp
    | of n g => simp [of_mul_of]
    | add g₁ g₂ h₁ h₂ => simp [mul_add, h₁, h₂]
  | add f₁ f₂ h₁ h₂ => simp [add_mul, h₁, h₂]

/--
@isnad1 id=eq.0h4v.s9.5f19c79fd2dd from=translated src=- shape=0ac8e169 vocab=8a7a6c40
-/
@[simp]
theorem eval_one : GradedHOM.eval ℳ ℳ (1 : GradedEND ℳ) = AddMonoidHom.id M := by
  simp [one_def]

/-- Evaluation is anti-multiplicative: `eval (f * g) = (eval g).comp (eval f)`.
@isnad1 id=eq.0h6v.s11.1a0181dc688c from=translated src=- shape=05768390 vocab=29a2ba47
-/
theorem eval_mul (f g : GradedEND ℳ) :
    GradedHOM.eval ℳ ℳ (f * g) = (GradedHOM.eval ℳ ℳ g).comp (GradedHOM.eval ℳ ℳ f) := by
  rw [mul_eq_compHom, GradedHOM.eval_compHom]

/--
@isnad1 id=eq.0h7v.s11.e43cbde28c36 from=translated src=- shape=f9db76bf vocab=5ad37e80
-/
theorem eval_mul_apply (f g : GradedEND ℳ) (x : M) :
    GradedHOM.eval ℳ ℳ (f * g) x = GradedHOM.eval ℳ ℳ g (GradedHOM.eval ℳ ℳ f x) := by
  rw [eval_mul]; rfl

set_option backward.isDefEq.respectTransparency false in
variable (ℳ) in
/-- Evaluation as a ring homomorphism from `GradedEND ℳ` to the multiplicative opposite of the
endomorphism ring `AddMonoid.End M`: the graded endomorphism ring acts on `M` on the right.-/
def evalRingHom : GradedEND ℳ →+* (AddMonoid.End M)ᵐᵒᵖ where
  toFun f := MulOpposite.op (GradedHOM.eval ℳ ℳ f)
  map_one' := by simp; rfl
  map_mul' f g := by
    rw [eval_mul, ← MulOpposite.op_mul]
    rfl
  map_zero' := by simp
  map_add' f g := by simp

/--
@isnad1 id=eq.0h5v.s10.1db792024086 from=translated src=- shape=493d8417 vocab=d88dd111
-/
@[simp]
theorem evalRingHom_apply (f : GradedEND ℳ) :
    evalRingHom ℳ f = MulOpposite.op (GradedHOM.eval ℳ ℳ f) := rfl

end GradedEND

end GradedEND

end DG
