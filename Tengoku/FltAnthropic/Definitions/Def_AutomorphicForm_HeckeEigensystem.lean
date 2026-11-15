import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

structure HeckeEigensystem (F : Type*) [Field F] [NumberField F]
    (R : Type*) [CommRing R] where

  level : Ideal (𝓞 F)

  level_ne_bot : level ≠ ⊥

  a : HeightOneSpectrum (𝓞 F) → R

  b : HeightOneSpectrum (𝓞 F) → R

namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F] {R : Type*} [CommRing R]

def twist (Φ : HeckeEigensystem F R) (χ : HeightOneSpectrum (𝓞 F) → R) :
    HeckeEigensystem F R where
  level := Φ.level
  level_ne_bot := Φ.level_ne_bot
  a := fun v => χ v * Φ.a v
  b := fun v => χ v ^ 2 * Φ.b v

/--
@isnad1 id=eq.0h5v.s6.7ad856fb2e5f from=translated src=- shape=4078cb38 vocab=9073cd01
-/
@[simp] theorem twist_a (Φ : HeckeEigensystem F R) (χ : HeightOneSpectrum (𝓞 F) → R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.twist χ).a v = χ v * Φ.a v := rfl

/--
@isnad1 id=eq.0h5v.s6.869fd59468e2 from=translated src=- shape=b6c09bb2 vocab=e3b5d376
-/
@[simp] theorem twist_b (Φ : HeckeEigensystem F R) (χ : HeightOneSpectrum (𝓞 F) → R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.twist χ).b v = χ v ^ 2 * Φ.b v := rfl

def AgreesAwayFromFinite (Φ Φ' : HeckeEigensystem F R) : Prop :=
  ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
    ∀ v ∉ S, Φ.a v = Φ'.a v ∧ Φ.b v = Φ'.b v

end HeckeEigensystem

def satakePow {R : Type*} [CommRing R] (n : ℕ) (s e : R) : R :=
  match n with
  | 0 => 2
  | 1 => s
  | (n + 2) => s * satakePow (n + 1) s e - e * satakePow n s e

/--
@isnad1 id=eq.0h3v.s5.8d4f46088b5c from=translated src=- shape=9be6e7be vocab=46445240
-/
@[simp] theorem satakePow_zero {R : Type*} [CommRing R] (s e : R) : satakePow 0 s e = 2 := rfl

/--
@isnad1 id=eq.0h3v.s4.37ba91e4bc56 from=translated src=- shape=b3a42331 vocab=46445240
-/
@[simp] theorem satakePow_one {R : Type*} [CommRing R] (s e : R) : satakePow 1 s e = s := rfl

/--
@isnad1 id=eq.0h4v.s6.a8ffcf72b003 from=translated src=- shape=b1df394c vocab=c735785e
-/
theorem satakePow_add_two {R : Type*} [CommRing R] (n : ℕ) (s e : R) :
    satakePow (n + 2) s e = s * satakePow (n + 1) s e - e * satakePow n s e := rfl

section Transfer

variable {E L : Type*} [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)]
  {R : Type*} [CommRing R]

end Transfer

structure CuspidalityNotion (R : Type*) [CommRing R] where

  IsCusp : ∀ (F : Type) [Field F] [NumberField F], HeckeEigensystem F R → Prop

end AutomorphicForm

end
