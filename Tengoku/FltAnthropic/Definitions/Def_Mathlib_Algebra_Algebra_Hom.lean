import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

section

section semialghom

/-- Let `φ : R →+* S` be a ring homomorphism, let `A` be an `R`-algebra and let `B` be
an `S`-algebra. Then `SemialgHom φ A B` or `A →ₛₐ[φ] B` is the ring homomorphisms `ψ : A →+* B`
making lying above `φ` (i.e. such that `ψ (r • a) = φ r • ψ a`).-/
structure SemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*)  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends A →ₛₗ[φ] B, RingHom A B

/-- Reinterpret a `SemialgHom` as a `RingHom`.-/
add_decl_doc SemialgHom.toRingHom

@[inherit_doc SemialgHom]
local infixr:25 " →ₛₐ " => SemialgHom _

@[inherit_doc]
local notation:25 A " →ₛₐ[" φ:25 "] " B:0 => SemialgHom φ A B

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

instance instFunLike : FunLike (A →ₛₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

variable {φ} {A} {B} in
/--
@isnad1 id=eq.0h8v.s7.8b8fe8bd92b5 from=translated src=- shape=ac313bcb vocab=ae7257cd
-/
lemma SemialgHom.map_smul (ψ : A →ₛₐ[φ] B) (m : R) (x : A) : ψ (m • x) = φ m • ψ x :=
  LinearMap.map_smul' ψ.toLinearMap m x

/--
@isnad1 id=eq.3h6v.s9.ec0c2ed66919 from=translated src=- shape=afd5bf60 vocab=b6ace79f
-/
@[simp]
theorem coe_mk (f : A →ₛₗ[φ] B) (h₁ h₂ h₃) : ((⟨f, h₁, h₂, h₃⟩ : A →ₛₐ[φ] B) : A → B) = f :=
  rfl

end semialghom
local infixr:25 " →ₛₐ " => SemialgHom _
local notation:25 A " →ₛₐ[" φ:25 "] " B:0 => SemialgHom φ A B

section semialghomclass

class SemialgHomClass (F : Type*) {R S : outParam Type*}
  [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] extends SemilinearMapClass F φ A B, RingHomClass F A B

variable (F : Type*) {R S : Type*}
  [CommSemiring R] [CommSemiring S] (φ : R →+* S) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [SemialgHomClass F φ A B]

/--
@isnad1 id=semialgh.0h5v.s6.3dc69a27526f from=translated src=- shape=1f65c29e vocab=fe214dc6
-/
instance SemialgHomClass.instSemialgHom : SemialgHomClass (A →ₛₐ[φ] B) φ A B where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero

variable {F} {φ} {A} {B} in

def SemialgHomClass.toSemialgHom (f : F) : A →ₛₐ[φ] B :=
  { (f : A →ₛₗ[φ] B), (f : A →+* B) with }

instance : CoeTC F (A →ₛₐ[φ] B) :=
  ⟨SemialgHomClass.toSemialgHom⟩

/--
@isnad1 id=eq.0h7v.s7.e3737b1aaf81 from=translated src=- shape=d813dcf9 vocab=3c8a6e4b
-/
@[simp]
theorem SemialgHom.coe_coe (f : F) : ⇑(f : A →ₛₐ[φ] B) = f :=
  rfl

end semialghomclass

section semialghom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

/--
@isnad1 id=eq.0h7v.s7.155710d518cb from=translated src=- shape=16f7390c vocab=0aaa55c0
-/
lemma SemialgHom.commutes (ψ : A →ₛₐ[φ] B) (r : R) :
    ψ (algebraMap R A r) = algebraMap S B (φ r) := by
  have := ψ.map_smul r 1
  rw [Algebra.smul_def, mul_one, map_one] at this
  rw [this, Algebra.smul_def, mul_one]

/--
@isnad1 id=eq.0h6v.s7.6524fce20e1e from=translated src=- shape=fd3ac4d3 vocab=fd46dbc9
-/
theorem SemialgHom.toLinearMap_eq_coe (f : A →ₛₐ[φ] B) : f.toLinearMap = f :=
  rfl

/--
@isnad1 id=eq.0h6v.s6.5b4367f2a3ef from=translated src=- shape=487ce2ea vocab=6f052bda
-/
theorem SemialgHom.toRingHom_eq_coe (f : A →ₛₐ[φ] B) : f.toRingHom = f :=
  rfl

/--
@isnad1 id=eq.0h7v.s7.28940b708bdc from=translated src=- shape=59229c98 vocab=05379840
-/
theorem SemialgHom.algebraMap_apply {A B : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra S B] (f : A →ₛₐ[φ] B) (a : A) :
    letI := f.toAlgebra
    algebraMap A B a = f a := rfl

def SemialgHom.comp {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
    [Algebra T C] {ψ : S →+* T} {ξ : R →+* T} [RingHomCompTriple φ ψ ξ]
    (g : B →ₛₐ[ψ] C) (f : A →ₛₐ[φ] B) :
    A →ₛₐ[ξ] C where
  __ := LinearMap.comp (SemialgHom.toLinearMap g) (SemialgHom.toLinearMap f)
  __ := RingHom.comp g.toRingHom f.toRingHom

def AlgHom.toSemialgHom {R : Type*} [CommSemiring R] {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    A →ₛₐ[RingHom.id R] B where
  __ := f
  map_smul' _ _ := by simp

def SemialgHom.compAlgHom {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
    [Algebra T C] {ψ : S →+* T} [Algebra S A] (g : B →ₛₐ[ψ] C) (f : A →ₐ[S] B) :
    A →ₛₐ[ψ] C :=
  g.comp f.toSemialgHom

def SemialgHom.prod {C : Type*} [Semiring C] [Algebra S C] (f : A →ₛₐ[φ] B)
    (g : A →ₛₐ[φ] C) :
    A →ₛₐ[φ] B × C where
  __ := RingHom.prod f.toRingHom g.toRingHom
  map_smul' r x := by simp

def SemialgHom.prodMap {C D : Type*} [Semiring C] [Semiring D]
    [Algebra S C] [Algebra S D] [Algebra R B] (f : A →ₛₐ[φ] C) (g : B →ₛₐ[φ] D) :
    A × B →ₛₐ[φ] C × D :=
  (f.compAlgHom (AlgHom.fst R A B)).prod (g.compAlgHom (AlgHom.snd R A B))

@[simps!]
def SemialgHom.restrictScalars {R S R' S' : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring R'] [CommSemiring S'] [Algebra R R'] [Algebra S S'] {φ : R →+* S}
    (ψ : R' →ₛₐ[φ] S') {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    [Algebra R' A] [Algebra S' B] [IsScalarTower R R' A] [IsScalarTower S S' B]
    (f : A →ₛₐ[ψ.toRingHom] B) : A →ₛₐ[φ] B where
  __ := f.toRingHom
  map_smul' r a := by
    have := f.map_smul (algebraMap R R' r) a
    simp_all [SemialgHom.toLinearMap_eq_coe, Algebra.algebraMap_eq_smul_one, ψ.map_smul]

end semialghom
-- Tengoku: 2 notation(s) of this module made local so they do not change other libraries (generated)
