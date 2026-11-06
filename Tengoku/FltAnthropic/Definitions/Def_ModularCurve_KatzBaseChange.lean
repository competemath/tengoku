import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_KatzLevelOne
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_KatzLevelP

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

noncomputable section

open WeierstrassCurve

@[reducible] def KatzModularForm.algebraThrough (R₀ : Type u) [CommRing R₀] (R₁ : Type u)
    [CommRing R₁] [Algebra R₀ R₁] (A : Type u) [CommRing A] [Algebra R₁ A] : Algebra R₀ A :=
  ((algebraMap R₁ A).comp (algebraMap R₀ R₁)).toAlgebra

/--
@isnad1 id=eq.0h3v.s6.56380f017353 from=translated src=- shape=89171ff2 vocab=fabf9d2e
-/
theorem KatzModularForm.algebraThrough_eq (R₀ : Type u) [CommRing R₀] (R₁ : Type u) [CommRing R₁]
    [Algebra R₀ R₁] (A : Type u) [CommRing A] [Algebra R₁ A] [h : Algebra R₀ A]
    [IsScalarTower R₀ R₁ A] : KatzModularForm.algebraThrough R₀ R₁ A = h :=
  Algebra.algebra_ext _ _ fun r => (IsScalarTower.algebraMap_apply R₀ R₁ A r).symm

def KatzModularForm.algHomThrough (R₀ : Type u) [CommRing R₀] (R₁ : Type u) [CommRing R₁]
    [Algebra R₀ R₁] {A B : Type u} [CommRing A] [Algebra R₁ A] [CommRing B] [Algebra R₁ B]
    (f : A →ₐ[R₁] B) :
    letI := KatzModularForm.algebraThrough R₀ R₁ A
    letI := KatzModularForm.algebraThrough R₀ R₁ B
    A →ₐ[R₀] B :=
  letI := KatzModularForm.algebraThrough R₀ R₁ A
  letI := KatzModularForm.algebraThrough R₀ R₁ B
  { (f : A →+* B) with
    commutes' := fun r => by
      show f ((algebraMap R₁ A) (algebraMap R₀ R₁ r)) = (algebraMap R₁ B) (algebraMap R₀ R₁ r)
      exact f.commutes _ }

namespace KatzModularForm

variable {R₀ : Type u} [CommRing R₀] {k : ℤ}

def baseChange (g : KatzModularForm R₀ k) (R₁ : Type u) [CommRing R₁] [Algebra R₀ R₁] :
    KatzModularForm R₁ k where
  toFun A _ _ W hW := @KatzModularForm.toFun R₀ _ k g A _ (algebraThrough R₀ R₁ A) W hW
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    exact @KatzModularForm.map_toFun R₀ _ k g A B _ (algebraThrough R₀ R₁ A) _
      (algebraThrough R₀ R₁ B) (algHomThrough R₀ R₁ f) W hW hW'
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    exact @KatzModularForm.toFun_variableChange R₀ _ k g A _ (algebraThrough R₀ R₁ A) C W hW hW'

variable (R₁ : Type u) [CommRing R₁] [Algebra R₀ R₁]

/--
@isnad1 id=eq.0h3v.s6.809f15a510eb from=translated src=- shape=3b1a2761 vocab=d4689cf8
-/
@[simp] theorem baseChange_zero : (0 : KatzModularForm R₀ k).baseChange R₁ = 0 := rfl

/--
@isnad1 id=eq.0h5v.s6.af4c4e3ccf2c from=translated src=- shape=92ce2d4d vocab=420b65ca
-/
@[simp] theorem baseChange_add (g h : KatzModularForm R₀ k) :
    (g + h).baseChange R₁ = g.baseChange R₁ + h.baseChange R₁ := rfl

/--
@isnad1 id=eq.0h4v.s6.c4174fbc84d2 from=translated src=- shape=d7319137 vocab=7981f0cf
-/
@[simp] theorem baseChange_neg (g : KatzModularForm R₀ k) : (-g).baseChange R₁ = -g.baseChange R₁ :=
  rfl

/--
@isnad1 id=eq.0h5v.s6.44ea38d8d9a5 from=translated src=- shape=92ce2d4d vocab=5be2cb26
-/
@[simp] theorem baseChange_sub (g h : KatzModularForm R₀ k) :
    (g - h).baseChange R₁ = g.baseChange R₁ - h.baseChange R₁ := rfl

/--
@isnad1 id=eq.0h5v.s7.393b7885799e from=translated src=- shape=5d522c0f vocab=1378b0c4
-/
@[simp] theorem baseChange_smul (c : R₀) (g : KatzModularForm R₀ k) :
    (c • g).baseChange R₁ = algebraMap R₀ R₁ c • g.baseChange R₁ := by
  ext A _ _ W hW
  letI := algebraThrough R₀ R₁ A
  show (c • g).toFun W hW = algebraMap R₀ R₁ c • g.toFun W hW
  rw [smul_toFun, Algebra.smul_def, Algebra.smul_def]
  rfl

end KatzModularForm

namespace ModularCurve

namespace KatzLevelPForm

open KatzModularForm (algebraThrough algebraThrough_eq algHomThrough)

variable {R₀ : Type u} [CommRing R₀] {p : ℕ} {k : ℤ}

def baseChange (F : KatzLevelPForm R₀ p k) (R₁ : Type u) [CommRing R₁] [Algebra R₀ R₁] :
    KatzLevelPForm R₁ p k where
  toFun A _ _ W hW D hD := @KatzLevelPForm.toFun R₀ _ p k F A _ (algebraThrough R₀ R₁ A) W hW D hD
  map_toFun := by
    intro A B _ _ _ _ f W hW hW' D hD hD'
    exact @KatzLevelPForm.map_toFun R₀ _ p k F A B _ (algebraThrough R₀ R₁ A) _
      (algebraThrough R₀ R₁ B) (algHomThrough R₀ R₁ f) W hW hW' D hD hD'
  toFun_variableChange := by
    intro A _ _ C W hW hW' D hD hD'
    exact @KatzLevelPForm.toFun_variableChange R₀ _ p k F A _ (algebraThrough R₀ R₁ A) C W hW hW'
      D hD hD'

variable (R₁ : Type u) [CommRing R₁] [Algebra R₀ R₁]

/--
@isnad1 id=eq.0h4v.s6.373ef76e0d3e from=translated src=- shape=d268393b vocab=69c187eb
-/
@[simp] theorem baseChange_zero : (0 : KatzLevelPForm R₀ p k).baseChange R₁ = 0 := rfl

/--
@isnad1 id=eq.0h6v.s6.60c171774827 from=translated src=- shape=8c7386a9 vocab=4378ca32
-/
@[simp] theorem baseChange_add (F G : KatzLevelPForm R₀ p k) :
    (F + G).baseChange R₁ = F.baseChange R₁ + G.baseChange R₁ := rfl

/--
@isnad1 id=eq.0h5v.s6.1ff6aa51156d from=translated src=- shape=a8675c8a vocab=d8c027e5
-/
@[simp] theorem baseChange_neg (F : KatzLevelPForm R₀ p k) :
    (-F).baseChange R₁ = -F.baseChange R₁ := rfl

/--
@isnad1 id=eq.0h6v.s6.35dd0f35f9e8 from=translated src=- shape=8c7386a9 vocab=0e2326bb
-/
@[simp] theorem baseChange_sub (F G : KatzLevelPForm R₀ p k) :
    (F - G).baseChange R₁ = F.baseChange R₁ - G.baseChange R₁ := rfl

/--
@isnad1 id=eq.0h6v.s7.898d408e9daf from=translated src=- shape=cada06ac vocab=0a1365ce
-/
@[simp] theorem baseChange_smul (c : R₀) (F : KatzLevelPForm R₀ p k) :
    (c • F).baseChange R₁ = algebraMap R₀ R₁ c • F.baseChange R₁ := by
  ext A _ _ W hW D hD
  letI := algebraThrough R₀ R₁ A
  show (c • F).toFun W hW D hD = algebraMap R₀ R₁ c • F.toFun W hW D hD
  rw [smul_toFun, Algebra.smul_def, Algebra.smul_def]
  rfl

/--
@isnad1 id=eq.0h5v.s6.a36859c8aadc from=translated src=- shape=fda96821 vocab=dc661f6a
-/
@[simp] theorem baseChange_swap (F : KatzLevelPForm R₀ p k) :
    F.swap.baseChange R₁ = (F.baseChange R₁).swap := rfl

/--
@isnad1 id=dependso.1h5v.s5.6755009a2788 from=translated src=- shape=b5a589f8 vocab=e25bf475
-/
theorem DependsOnlyOnSndLine.baseChange {F : KatzLevelPForm R₀ p k} (h : F.DependsOnlyOnSndLine) :
    (F.baseChange R₁).DependsOnlyOnSndLine :=
  fun A _ _ W hW D D' hD hD' hQ =>
    @h A _ (algebraThrough R₀ R₁ A) W hW D D' hD hD' hQ

end KatzLevelPForm

namespace KatzGamma0Form

variable {R₀ : Type u} [CommRing R₀] {p : ℕ} {k : ℤ}

def baseChange (φ : KatzGamma0Form R₀ p k) (R₁ : Type u) [CommRing R₁] [Algebra R₀ R₁] :
    KatzGamma0Form R₁ p k :=
  ⟨φ.toKatzLevelPForm.baseChange R₁, φ.dependsOnlyOnSndLine.baseChange R₁⟩

variable (R₁ : Type u) [CommRing R₁] [Algebra R₀ R₁]

/--
@isnad1 id=eq.0h5v.s6.a7752c2ba3fb from=translated src=- shape=beb9625f vocab=bc8d697e
-/
@[simp] theorem baseChange_toKatzLevelPForm (φ : KatzGamma0Form R₀ p k) :
    (φ.baseChange R₁).toKatzLevelPForm = φ.toKatzLevelPForm.baseChange R₁ := rfl

/--
@isnad1 id=eq.0h4v.s6.3e5832bcd9cd from=translated src=- shape=d268393b vocab=bcc14bf1
-/
@[simp] theorem baseChange_zero : (0 : KatzGamma0Form R₀ p k).baseChange R₁ = 0 := rfl

/--
@isnad1 id=eq.0h6v.s6.ae2b798d695d from=translated src=- shape=8c7386a9 vocab=5020cc5c
-/
@[simp] theorem baseChange_add (φ ψ : KatzGamma0Form R₀ p k) :
    (φ + ψ).baseChange R₁ = φ.baseChange R₁ + ψ.baseChange R₁ := rfl

/--
@isnad1 id=eq.0h5v.s6.3811cd7a3563 from=translated src=- shape=a8675c8a vocab=747c6c10
-/
@[simp] theorem baseChange_neg (φ : KatzGamma0Form R₀ p k) :
    (-φ).baseChange R₁ = -φ.baseChange R₁ := rfl

/--
@isnad1 id=eq.0h6v.s6.e38fa09d5f7a from=translated src=- shape=8c7386a9 vocab=a1b0daf6
-/
@[simp] theorem baseChange_sub (φ ψ : KatzGamma0Form R₀ p k) :
    (φ - ψ).baseChange R₁ = φ.baseChange R₁ - ψ.baseChange R₁ := rfl

/--
@isnad1 id=eq.0h6v.s7.d47d7e34126a from=translated src=- shape=cada06ac vocab=cef8961e
-/
@[simp] theorem baseChange_smul (c : R₀) (φ : KatzGamma0Form R₀ p k) :
    (c • φ).baseChange R₁ = algebraMap R₀ R₁ c • φ.baseChange R₁ := by
  ext1; simp

end KatzGamma0Form

end ModularCurve

namespace KatzModularForm

variable {R₀ : Type u} [CommRing R₀] {k : ℤ} (R₁ : Type u) [CommRing R₁] [Algebra R₀ R₁]

end KatzModularForm

end
