/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.Seed.CategoryTheory.Preadditive.AdditiveFunctor
import Tengoku.Seed.CategoryTheory.Linear.LinearFunctor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integer powers of an autoequivalence

The integer-shift core used by the orbit construction (Brundan–Ellis,
*Monoidal supercategories*, arXiv:1603.05928v3, §6) and by Laurent
Krull–Schmidt bases (Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, §11).
-/

namespace StringDiagrams.EquivalencePowers
open CategoryTheory
variable {C : Type*} [Category C] (e : C ≌ C)

/-- Positive powers, with the equivalence applied last.-/
def powNat : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => powNat n ⋙ e.functor

/-- Negative powers, with the inverse equivalence applied last.-/
def powNeg : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => powNeg n ⋙ e.inverse

/-- Integer powers of an autoequivalence.-/
def pow : ℤ → C ⥤ C
  | Int.ofNat n => powNat e n
  | Int.negSucc n => powNeg e (n + 1)

/--
@isnad1 id=eq.0h2v.s4.cf57393b8bf7 from=translated src=- shape=2c589ea4 vocab=ca49281e
-/
@[simp] theorem pow_zero : pow e 0 = 𝟭 C := rfl
/--
@isnad1 id=eq.0h2v.s4.bc1c59f7ba09 from=translated src=- shape=2c589ea4 vocab=15f065b4
-/
@[simp] theorem powNat_zero : powNat e 0 = 𝟭 C := rfl
/--
@isnad1 id=eq.0h3v.s5.10ef61f0d2eb from=translated src=- shape=a3145c29 vocab=eaa468d7
-/
@[simp] theorem powNat_succ (n : ℕ) : powNat e (n + 1) = powNat e n ⋙ e.functor := rfl
/--
@isnad1 id=eq.0h2v.s4.27d5d3881172 from=translated src=- shape=2c589ea4 vocab=86813414
-/
@[simp] theorem powNeg_zero : powNeg e 0 = 𝟭 C := rfl
/--
@isnad1 id=eq.0h3v.s5.54dafb595db7 from=translated src=- shape=a3145c29 vocab=486037ba
-/
@[simp] theorem powNeg_succ (n : ℕ) : powNeg e (n + 1) = powNeg e n ⋙ e.inverse := rfl

/-- Composing an integer power with the equivalence increments the exponent.-/
def succ : ∀ i : ℤ, pow e i ⋙ e.functor ≅ pow e (i + 1)
  | Int.ofNat _ => Iso.refl _
  | Int.negSucc 0 => e.counitIso
  | Int.negSucc (n + 1) => Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (powNeg e (n + 1)) e.counitIso ≪≫ Functor.rightUnitor _

variable [Preadditive C] [e.functor.Additive] [e.inverse.Additive]
/--
@isnad1 id=additive.0h3v.s5.7b9692cd333b from=translated src=- shape=12bf8f9e vocab=ba14dfa6
-/
instance powNat_additive : ∀ n, (powNat e n).Additive
  | 0 => inferInstanceAs (𝟭 C).Additive
  | n + 1 => by have := powNat_additive n; exact inferInstanceAs (powNat e n ⋙ e.functor).Additive
/--
@isnad1 id=additive.0h3v.s5.68cf304959e0 from=translated src=- shape=12bf8f9e vocab=f241273b
-/
instance powNeg_additive : ∀ n, (powNeg e n).Additive
  | 0 => inferInstanceAs (𝟭 C).Additive
  | n + 1 => by have := powNeg_additive n; exact inferInstanceAs (powNeg e n ⋙ e.inverse).Additive
/--
@isnad1 id=additive.0h3v.s5.eeb4c3dcf8b0 from=translated src=- shape=df97eb6c vocab=2f7b9374
-/
instance pow_additive : ∀ n, (pow e n).Additive
  | Int.ofNat n => powNat_additive e n
  | Int.negSucc n => powNeg_additive e (n + 1)

end StringDiagrams.EquivalencePowers
