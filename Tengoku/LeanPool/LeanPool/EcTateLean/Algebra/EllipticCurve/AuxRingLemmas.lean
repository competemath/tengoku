/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Tengoku

/-!
# LeanPool.EcTateLean.Algebra.EllipticCurve.AuxRingLemmas

Imported Lean Pool material for `LeanPool.EcTateLean.Algebra.EllipticCurve.AuxRingLemmas`.
-/

@[expose] public section

section ring_lemmas

variable {R : Type u} [CommRing R]

/--
@isnad1 id=eq.0h5v.s8.e64a363c2e1c from=translated src=- shape=64005cf0 vocab=a1216c81
-/
lemma factorize1 (root b p : R) (q : ℕ) :
    root * p ^ q * (p ^ q * b) + root * p ^ q * (root * p ^ q) =
      p ^ q * p ^ q * ((root + b) * root) := by ring

/--
@isnad1 id=eq.0h5v.s8.62d2c5603f64 from=translated src=- shape=09a876c2 vocab=99545b96
-/
lemma factorize2 (root a p : R) (q : ℕ) :
    2 * (root * p ^ q) * (p ^ 1 * a) = p ^ q * p ^ 1 * (2 * a * root) := by ring

/--
@isnad1 id=eq.0h4v.s7.6d00d73429f9 from=translated src=- shape=a7b350a2 vocab=99545b96
-/
lemma factorize3 (root p : R) (q : ℕ) :
    3 * (root * p ^ q * (root * p ^ q)) = p ^ q * p ^ q * (3 * root * root) := by ring

/--
@isnad1 id=eq.0h7v.s9.5405bba75da9 from=translated src=- shape=17ca2a39 vocab=a1216c81
-/
lemma factorize4 (root a b c p : R) (q : ℕ) :
    p ^ (2 * q + 1) * c + root * p ^ q * (p ^ (q + 1) * b) + (root * p ^ q) ^ 2 * (p ^ 1 * a) =
      p ^ q * p ^ q * p ^ 1 * (a * root ^ 2) + p ^ q * p ^ (q + 1) * (b * root) +
        p ^ (2 * q + 1) * c := by ring

/--
@isnad1 id=eq.0h4v.s8.858a856b7d6b from=translated src=- shape=4064ea31 vocab=a1216c81
-/
lemma factorize5 (b c p : R) :
    p ^ 1 * b * (p ^ 1 * b) + 4 * (p ^ 2 * c) = p ^ 2 * (b * b + 4 * c) := by ring

/--
@isnad1 id=eq.0h5v.s8.bc76a282bb5a from=translated src=- shape=7c2e38f6 vocab=17974e62
-/
lemma factorize6 (p x b c : R) :
    p ^ 2 * x ^ 2 + p * x * (p ^ 1 * b) + p ^ 2 * -c = p ^ 2 * (1 * x ^ 2 + b * x + -c) := by ring

/--
@isnad1 id=eq.0h5v.s8.32ab34121464 from=translated src=- shape=67aaa32c vocab=a1216c81
-/
lemma factorize7 (a b r p : R) :
    p ^ 2 * a + 2 * (p * r) * (p ^ 1 * b) + 3 * (p * r) ^ 2 =
      p ^ 2 * (a + 2 * r * b + 3 * r ^ 2) := by ring

/--
@isnad1 id=eq.0h6v.s8.e134368890be from=translated src=- shape=bfad3b68 vocab=a1216c81
-/
lemma factorize8 (a b c r p : R) :
    (p ^ 3 * a) + (p * r) * (p ^ 2 * b) + (p * r) ^ 2 * (p ^ 1 * c) + (p * r) ^ 3 =
      p ^ 3 * (a + r * b + r ^ 2 * c + r ^ 3) := by ring

/--
@isnad1 id=eq.0h8v.s9.8cf31f163b60 from=translated src=- shape=ce9ec21d vocab=17974e62
-/
lemma factorize9 (a1 a2 a3 a4 a6 b8 p : R) :
    p ^ 1 * a1 * (p ^ 1 * a1) * (p ^ 3 * a6) + p ^ 1 * a1 * (p ^ 2 * a3) * -a4 +
        4 * a2 * (p ^ 3 * a6) + a2 * (p ^ 2 * a3) * (p ^ 2 * a3) + p ^ 3 * -b8 =
      p ^ 3 * (p ^ 1 * a1 * (p ^ 1 * a1) * a6 + a1 * a3 * -a4 + 4 * a2 * a6 +
        a2 * a3 * (p ^ 1 * a3) + -b8) := by ring

end ring_lemmas
