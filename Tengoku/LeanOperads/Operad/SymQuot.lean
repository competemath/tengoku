/-
# Quotients of symmetric operads

The quotient of a symmetric operad by an ideal is a symmetric operad (`SymOperadIdeal.Quot`): each
component is the quotient module, and relabelling and partial composition descend because the
ideal is stable under both. Every axiom is the corresponding axiom upstairs, pushed through the
quotient map. The quotient map is a morphism whose kernel is the ideal
(`SymOperadIdeal.mem_ker_projHom`), and a morphism vanishing on the ideal factors through it,
uniquely (`SymOperadIdeal.liftHom`, `liftHom_proj`, `liftHom_unique`). In particular a morphism
factors injectively through the quotient by its kernel (`SymOperadHom.kerLift`,
`kerLift_injective`), and bijectively when it is surjective: the first isomorphism theorem
(`kerLift_bijective`).
-/
import Tengoku.LeanOperads.Operad.SymIdeal
import Tengoku.Seed.LinearAlgebra.Quotient.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v w

namespace Operad

open Sym

namespace SymOperadIdeal

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  (I : SymOperadIdeal R P)

/-- **The quotient of a symmetric operad by an ideal**, input set by input set.-/
def Quot (A : Type) [Fintype A] [DecidableEq A] : Type v := P A ⧸ I.sub A

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (I.Quot A) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (I.Quot A) :=
  inferInstanceAs (Module R (_ ⧸ _))

variable {A B C D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

/-- The quotient map.-/
def proj (A : Type) [Fintype A] [DecidableEq A] : P A →ₗ[R] I.Quot A := (I.sub A).mkQ

/--
@isnad1 id=eq.0h5v.s8.67e366aedcbe from=translated src=- shape=bc573657 vocab=5c024f99
-/
@[simp] lemma proj_apply (x : P A) : I.proj A x = Submodule.Quotient.mk x := rfl

/--
@isnad1 id=surjecti.0h4v.s8.766823aeab0f from=translated src=- shape=fd651445 vocab=788c583e
-/
lemma proj_surjective (A : Type) [Fintype A] [DecidableEq A] : Function.Surjective (I.proj A) :=
  Submodule.mkQ_surjective _

/--
@isnad1 id=iff.0h5v.s9.69e5403b6827 from=translated src=- shape=04cb597e vocab=d1de96b8
-/
lemma proj_eq_zero_iff (x : P A) : I.proj A x = 0 ↔ x ∈ I.sub A :=
  Submodule.Quotient.mk_eq_zero _

/-- Relabelling, descended to the quotient.-/
def mapQ (e : A ≃ B) : I.Quot A →ₗ[R] I.Quot B :=
  Submodule.mapQ _ _ (SymOperad.map (R := R) e) fun _ hx => I.map_mem e hx

/--
@isnad1 id=eq.0h7v.s9.fd48440345fb from=translated src=- shape=c7dd2ab2 vocab=4c2e957c
-/
@[simp] lemma mapQ_mk (e : A ≃ B) (x : P A) :
    I.mapQ e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (SymOperad.map (R := R) e x) :=
  rfl

/-- Composition with a fixed outer operation, descended to the quotient.-/
def compRight (i : A) (x : P A) : I.Quot B →ₗ[R] I.Quot (Without A i ⊕ B) :=
  Submodule.mapQ _ _ (SymOperad.comp (R := R) i x) fun _ hy => I.comp_mem_right i x hy

/--
@isnad1 id=eq.0h8v.s12.fa78c92e9b59 from=translated src=- shape=c138f875 vocab=16cb00a2
-/
lemma compRight_proj (i : A) (x : P A) (y : P B) :
    I.compRight i x (I.proj B y) = I.proj _ (SymOperad.comp (R := R) i x y) := rfl

/--
@isnad1 id=eq.0h8v.s12.ce57e3287c85 from=translated src=- shape=44d4d90c vocab=e78d407c
-/
@[simp] lemma compRight_mk (i : A) (x : P A) (y : P B) :
    I.compRight i x (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (SymOperad.comp (R := R) i x y) := rfl

/-- Partial composition on the quotient.-/
def compQ (i : A) : I.Quot A →ₗ[R] I.Quot B →ₗ[R] I.Quot (Without A i ⊕ B) :=
  Submodule.liftQ _
    { toFun := fun x => I.compRight i x
      map_add' := fun x x' => by
        refine LinearMap.ext fun z => ?_
        obtain ⟨y, rfl⟩ := I.proj_surjective B z
        simp only [compRight_proj, LinearMap.add_apply, map_add]
      map_smul' := fun r x => by
        refine LinearMap.ext fun z => ?_
        obtain ⟨y, rfl⟩ := I.proj_surjective B z
        simp only [compRight_proj, LinearMap.smul_apply, RingHom.id_apply, map_smul] }
    (by
      intro x hx
      refine LinearMap.ext fun z => ?_
      obtain ⟨y, rfl⟩ := I.proj_surjective B z
      show I.proj _ (SymOperad.comp (R := R) i x y) = 0
      exact (I.proj_eq_zero_iff _).2 (I.comp_mem_left i y hx))

/--
@isnad1 id=eq.0h8v.s13.54fe4e8259ff from=translated src=- shape=ef9c617d vocab=cb87d550
-/
@[simp] lemma compQ_mk (i : A) (x : P A) (y : P B) :
    I.compQ i (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (SymOperad.comp (R := R) i x y) := rfl

/-- **The quotient of a symmetric operad by an ideal is a symmetric operad.**-/
instance instSymOperad : SymOperad R I.Quot where
  map e := I.mapQ e
  map_refl x := by
    obtain ⟨y, rfl⟩ := I.proj_surjective _ x
    exact congrArg (I.proj _) (SymOperad.map_refl (R := R) y)
  map_trans e f x := by
    obtain ⟨y, rfl⟩ := I.proj_surjective _ x
    exact congrArg (I.proj _) (SymOperad.map_trans (R := R) e f y)
  one := I.proj Unit (SymOperad.one R)
  comp i := I.compQ i
  map_comp σ τ i x y := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ x
    obtain ⟨y, rfl⟩ := I.proj_surjective _ y
    exact congrArg (I.proj _) (SymOperad.map_comp (R := R) σ τ i x y)
  comp_one i x := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ x
    exact congrArg (I.proj _) (SymOperad.comp_one (R := R) i x)
  one_comp y := by
    obtain ⟨y, rfl⟩ := I.proj_surjective _ y
    exact congrArg (I.proj _) (SymOperad.one_comp (R := R) y)
  comp_assoc_seq i j x y z := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ x
    obtain ⟨y, rfl⟩ := I.proj_surjective _ y
    obtain ⟨z, rfl⟩ := I.proj_surjective _ z
    exact congrArg (I.proj _) (SymOperad.comp_assoc_seq (R := R) i j x y z)
  comp_assoc_par hik x y z := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ x
    obtain ⟨y, rfl⟩ := I.proj_surjective _ y
    obtain ⟨z, rfl⟩ := I.proj_surjective _ z
    exact congrArg (I.proj _) (SymOperad.comp_assoc_par (R := R) hik x y z)

/-- **The quotient map is a morphism of symmetric operads.**-/
def projHom : SymOperadHom R P I.Quot where
  app A _ _ := I.proj A
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

/--
@isnad1 id=eq.0h5v.s9.1149a3c5c841 from=translated src=- shape=8ad4828f vocab=e2bf0b0f
-/
@[simp] lemma projHom_app (x : P A) : I.projHom.app A x = I.proj A x := rfl

section Lift

variable {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **The universal property of the quotient**: a morphism vanishing on the ideal factors through
the quotient.-/
def liftHom (φ : SymOperadHom R P Q)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], ∀ x ∈ I.sub A, φ.app A x = 0) :
    SymOperadHom R I.Quot Q where
  app A _ _ := Submodule.liftQ (I.sub A) (φ.app A) fun x hx => h A x hx
  app_map e x := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ x
    exact φ.app_map e x
  app_one := φ.app_one
  app_comp i x y := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ x
    obtain ⟨y, rfl⟩ := I.proj_surjective _ y
    exact φ.app_comp i x y

/--
@isnad1 id=eq.1h7v.s10.f17a9d36a232 from=translated src=- shape=d3c79043 vocab=fa08af4e
-/
lemma liftHom_proj (φ : SymOperadHom R P Q)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], ∀ x ∈ I.sub A, φ.app A x = 0) (x : P A) :
    (I.liftHom φ h).app A (I.proj A x) = φ.app A x := rfl

/--
@isnad1 id=eq.1h7v.s9.869f285a0083 from=translated src=- shape=48651f31 vocab=32506ae9
-/
@[simp] lemma liftHom_mk (φ : SymOperadHom R P Q)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], ∀ x ∈ I.sub A, φ.app A x = 0) (x : P A) :
    (I.liftHom φ h).app A (Submodule.Quotient.mk x) = φ.app A x := rfl

/-- The factorization through the quotient composes back to the morphism.
@isnad1 id=eq.1h5v.s9.8d09eed1db2c from=translated src=- shape=5c03127f vocab=824f3660
-/
lemma liftHom_comp_projHom (φ : SymOperadHom R P Q)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], ∀ x ∈ I.sub A, φ.app A x = 0) :
    (I.liftHom φ h).comp I.projHom = φ :=
  SymOperadHom.ext fun _ _ _ _ => rfl

/-- **The factorization is unique.**
@isnad1 id=eq.2h6v.s9.334fbb49c929 from=translated src=- shape=a04118b9 vocab=824f3660
-/
lemma liftHom_unique (φ : SymOperadHom R P Q)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], ∀ x ∈ I.sub A, φ.app A x = 0)
    (ψ : SymOperadHom R I.Quot Q) (hψ : ψ.comp I.projHom = φ) : ψ = I.liftHom φ h := by
  refine SymOperadHom.ext fun A _ _ x => ?_
  obtain ⟨x, rfl⟩ := I.proj_surjective _ x
  rw [liftHom_proj, ← hψ]
  rfl

end Lift

end SymOperadIdeal

namespace SymOperadHom

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **A morphism factors through the quotient by its kernel.**-/
def kerLift (φ : SymOperadHom R P Q) : SymOperadHom R φ.ker.Quot Q :=
  φ.ker.liftHom φ fun _ _ _ _ hx => hx

/--
@isnad1 id=eq.0h6v.s9.11bf2091244b from=translated src=- shape=15a345a6 vocab=43dbcff8
-/
@[simp] lemma kerLift_mk (φ : SymOperadHom R P Q) {A : Type} [Fintype A] [DecidableEq A]
    (x : P A) : φ.kerLift.app A (Submodule.Quotient.mk x) = φ.app A x := rfl

end SymOperadHom

end Operad
