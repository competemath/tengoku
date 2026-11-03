import Tengoku.Seed.Algebra.DirectSum.Module
import Tengoku.DgLean.DG.Graded.Basic
import Tengoku.DgLean.DG.Homotopy.Forget

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The dg abelian group of a cochain complex

For a cochain complex `K` of `R`-modules (`R` any ring), `DG.ComplexSum K` is the external direct sum
`⨁ n, Kⁿ`, internally graded by its summands (`DG.summand`) and with the differential acting
componentwise, `d (ι_n x) = ι_{n+1} (d x)`. This is the inverse construction to the underlying
cochain complex of a dg module (`DG.DGModuleCat.toComplex`):

* `DG.ComplexSum.of K n : K.X n →ₗ[R] ComplexSum K` and `DG.ComplexSum.component K n` are the
  inclusion of and the projection onto the summand `Kⁿ`, and `DG.ComplexSum.d_of` computes the
  differential;
* if `ComplexSum K` carries a dg module structure over a dg `R`-algebra `A` whose `R`-module
  structure (through `algebraMap R A`) is the componentwise one, then its underlying cochain
  complex is isomorphic to `K` (`DG.ComplexSum.toComplexIso`). This is used for both the
  comparison of dg algebras with monoid objects and of dg modules with module objects in
  `CochainComplex (ModuleCat R) ℤ`.
-/

open scoped DG

open CategoryTheory DirectSum

universe u

noncomputable section

namespace DG

section Ring

variable {R : Type u} [Ring R]

/-- The external direct sum `⨁ n, Kⁿ` of the components of a cochain complex of modules.-/
def ComplexSum (K : CochainComplex (ModuleCat.{u} R) ℤ) : Type u :=
  ⨁ n, K.X n

namespace ComplexSum

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

instance : AddCommGroup (ComplexSum K) :=
  inferInstanceAs (AddCommGroup (⨁ n, K.X n))

instance : Module R (ComplexSum K) :=
  inferInstanceAs (Module R (⨁ n, K.X n))

/-- The inclusion of the summand `Kⁿ`.-/
def of (n : ℤ) : K.X n →ₗ[R] ComplexSum K :=
  DirectSum.lof R ℤ (fun n => K.X n) n

/-- The projection onto the summand `Kⁿ`.-/
def component (n : ℤ) : ComplexSum K →ₗ[R] K.X n :=
  DirectSum.component R ℤ (fun n => K.X n) n

variable {K}

/--
@isnad1 id=eq.0h4v.s10.1c0055c35771 from=translated src=- shape=59f83f14 vocab=c10f9735
-/
@[simp]
theorem component_of_same (n : ℤ) (x : K.X n) : component K n (of K n x) = x :=
  DirectSum.component.lof_self (M := fun n => K.X n) R n x

/-- Induction on `ComplexSum K`: a predicate holding for `0` and the image of every summand and
closed under addition holds everywhere.
@isnad1 id=var.0h7v.s9.60fb6f513534 from=translated src=- shape=7ae4fc22 vocab=830b48b1
-/
@[elab_as_elim]
theorem induction_on {motive : ComplexSum K → Prop} (z : ComplexSum K) (zero : motive 0)
    (of : ∀ (n : ℤ) (x : K.X n), motive (of K n x))
    (add : ∀ z z', motive z → motive z' → motive (z + z')) : motive z :=
  DirectSum.induction_on (β := fun n => K.X n) z zero of add

/-- Additive maps out of `ComplexSum K` agreeing on every summand are equal.
@isnad1 id=eq.1h5v.s10.ed410e00f266 from=translated src=- shape=b07957e0 vocab=0d5a7a0a
-/
theorem addHom_ext {B : Type*} [AddCommGroup B] {f g : ComplexSum K →+ B}
    (h : ∀ (n : ℤ) (x : K.X n), f (of K n x) = g (of K n x)) : f = g :=
  DirectSum.addHom_ext (β := fun n => K.X n) h

/-- The differential of `ComplexSum K`, acting componentwise.-/
def dAux : ComplexSum K →+ ComplexSum K :=
  DirectSum.toAddMonoid fun n =>
    (of K (n + 1)).toAddMonoidHom.comp (K.d n (n + 1)).hom.toAddMonoidHom

/--
@isnad1 id=eq.0h4v.s11.7c535c33b17b from=translated src=- shape=a3b456bd vocab=7466b492
-/
theorem dAux_of (n : ℤ) (x : K.X n) : dAux (of K n x) = of K (n + 1) (K.d n (n + 1) x) :=
  DirectSum.toAddMonoid_of (β := fun n => K.X n) _ n x

variable (K) in
/-- The dg abelian group structure on `ComplexSum K`: graded by the summands, with the
componentwise differential.-/
instance : DGAddCommGroup (ComplexSum K) where
  grading := summand (fun n => K.X n)
  decomposition := instDecompositionSummand (fun n => K.X n)
  d := dAux
  d_mem' := by
    rintro n _ ⟨x, rfl⟩
    exact ⟨K.d n (n + 1) x, (dAux_of n x).symm⟩
  d_d' z := by
    induction z using induction_on with
    | zero => simp
    | of n x =>
      rw [dAux_of, dAux_of]
      have : K.d (n + 1) (n + 1 + 1) (K.d n (n + 1) x) = 0 := by
        rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
        rfl
      rw [this, map_zero]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', add_zero]

/--
@isnad1 id=eq.0h4v.s11.52194c5c1bcc from=translated src=- shape=834dd847 vocab=de7c832e
-/
@[simp]
theorem d_of (n : ℤ) (x : K.X n) : d (of K n x) = of K (n + 1) (K.d n (n + 1) x) :=
  dAux_of n x

/--
@isnad1 id=iff.0h4v.s9.7a823231d66f from=translated src=- shape=41ba7286 vocab=965d9bd6
-/
theorem mem_grading_iff {n : ℤ} {z : ComplexSum K} :
    z ∈ grading (M := ComplexSum K) n ↔ ∃ x, of K n x = z :=
  Iff.rfl

/--
@isnad1 id=mem.0h4v.s9.e2cd85faf7e0 from=translated src=- shape=c2a025c3 vocab=965d9bd6
-/
theorem of_mem_grading (n : ℤ) (x : K.X n) : of K n x ∈ grading (M := ComplexSum K) n :=
  ⟨x, rfl⟩

/--
@isnad1 id=eq.1h4v.s10.e0d63311c9de from=translated src=- shape=e1d0f9da vocab=56b164a0
-/
theorem of_component_of_mem {n : ℤ} {z : ComplexSum K} (hz : z ∈ grading (M := ComplexSum K) n) :
    of K n (component K n z) = z := by
  obtain ⟨x, rfl⟩ := mem_grading_iff.mp hz
  rw [component_of_same]

/-! ### Functoriality -/

section Map

variable {L M : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The map `ComplexSum K → ComplexSum L` induced by a morphism of complexes, acting
componentwise. It has degree `0` and commutes with the differentials.-/
def map (φ : K ⟶ L) : ComplexSum K →ₗ[R] ComplexSum L :=
  DirectSum.toModule R ℤ _ fun n => (of L n).comp (φ.f n).hom

/--
@isnad1 id=eq.0h6v.s11.476aec1042a7 from=translated src=- shape=84aba284 vocab=ab868045
-/
@[simp]
theorem map_of (φ : K ⟶ L) (n : ℤ) (x : K.X n) : map φ (of K n x) = of L n (φ.f n x) :=
  DirectSum.toModule_lof (M := fun n => K.X n) R n x

/--
@isnad1 id=mem.1h6v.s8.6a30c7a900b8 from=translated src=- shape=855af3a4 vocab=9992c89b
-/
theorem map_mem (φ : K ⟶ L) {n : ℤ} {z : ComplexSum K} (hz : z ∈ grading (M := ComplexSum K) n) :
    map φ z ∈ grading (M := ComplexSum L) n := by
  obtain ⟨x, rfl⟩ := mem_grading_iff.mp hz
  rw [map_of]
  exact of_mem_grading n _

/--
@isnad1 id=eq.0h5v.s9.afa8736f77f5 from=translated src=- shape=d2e1ff14 vocab=79bb2fa8
-/
theorem map_d (φ : K ⟶ L) (z : ComplexSum K) : map φ (d z) = d (map φ z) := by
  induction z using induction_on with
  | zero => simp
  | of n x =>
    rw [d_of, map_of, map_of, d_of, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.comm]
  | add z z' hz hz' => rw [d_add, map_add, map_add, hz, hz', d_add]

/--
@isnad1 id=eq.0h3v.s8.38ade4959a24 from=translated src=- shape=6741e51f vocab=00a38bae
-/
@[simp]
theorem map_id (z : ComplexSum K) : map (𝟙 K) z = z := by
  induction z using induction_on with
  | zero => simp
  | of n x => rw [map_of]; rfl
  | add z z' hz hz' => rw [map_add, hz, hz']

/--
@isnad1 id=eq.0h7v.s9.c4db71bd2b28 from=translated src=- shape=8509bb30 vocab=a22869db
-/
theorem map_comp (φ : K ⟶ L) (ψ : L ⟶ M) (z : ComplexSum K) :
    map (φ ≫ ψ) z = map ψ (map φ z) := by
  induction z using induction_on with
  | zero => simp
  | of n x => rw [map_of, map_of, map_of]; rfl
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']

end Map

end ComplexSum

end Ring

namespace ComplexSum

variable {R : Type u} [CommRing R] {K : CochainComplex (ModuleCat.{u} R) ℤ}

/-! ### The underlying cochain complex -/

section ToComplex

open DGModuleCat.Algebra

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Algebra R A] [DGAlgebra R A]
  [Module A (ComplexSum K)] [DGModule A (ComplexSum K)]
  (hsmul : ∀ (r : R) (n : ℤ) (x : K.X n), algebraMap R A r • of K n x = of K n (r • x))

include hsmul

/-- The degree-`n` component of the underlying complex of `ComplexSum K` is `Kⁿ`.-/
def toComplexXEquiv (n : ℤ) :
    (DGModuleCat.toComplex R (DGModuleCat.of A (ComplexSum K))).X n ≃ₗ[R] K.X n where
  toFun z := component K n z.1
  map_add' z z' := map_add (component K n) z.1 z'.1
  map_smul' r z := by
    obtain ⟨_, x, rfl⟩ := z
    change component K n (algebraMap R A r • of K n x) = r • component K n (of K n x)
    rw [hsmul, component_of_same, component_of_same]
  invFun x := ⟨of K n x, of_mem_grading n x⟩
  left_inv z := Subtype.ext (of_component_of_mem z.2)
  right_inv x := component_of_same n x

/-- The underlying cochain complex of `ComplexSum K` (as a dg `A`-module) is `K`.-/
def toComplexIso : DGModuleCat.toComplex R (DGModuleCat.of A (ComplexSum K)) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (toComplexXEquiv hsmul n).toModuleIso) (by
      rintro n _ rfl
      rw [DGModuleCat.toComplex_d]
      ext ⟨_, x, rfl⟩
      change K.d n (n + 1) (component K n (of K n x)) = component K (n + 1) (d (of K n x))
      rw [d_of, component_of_same, component_of_same])

/--
@isnad1 id=eq.1h5v.s12.87352c4e5fd9 from=translated src=- shape=5b90fed2 vocab=fac23462
-/
@[simp]
theorem toComplexIso_hom_f_apply (n : ℤ)
    (z : (DGModuleCat.toComplex R (DGModuleCat.of A (ComplexSum K))).X n) :
    (toComplexIso hsmul).hom.f n z = component K n z.1 :=
  rfl

/--
@isnad1 id=eq.1h5v.s12.63544db237b3 from=translated src=- shape=c85eddb9 vocab=072a82bb
-/
@[simp]
theorem coe_toComplexIso_inv_f_apply (n : ℤ) (x : K.X n) :
    ((toComplexIso hsmul).inv.f n x).1 = of K n x :=
  rfl

end ToComplex

end ComplexSum

end DG

end
