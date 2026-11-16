import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeGalois_EichlerShimura

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def eisensteinEval (N : ℕ) : HeckeAlg →ₐ[ℤ] ℤ :=
  MvPolynomial.aeval (eisensteinSystem N)

/--
@isnad1 id=eq.0h2v.s6.af7f4bbb4533 from=translated src=- shape=dc10a450 vocab=5ead1ca9
-/
@[simp] lemma eisensteinEval_heckeGen (N : ℕ) (ℓ : Nat.Primes) :
    eisensteinEval N (heckeGen ℓ) = eisensteinSystem N ℓ := by
  simp [eisensteinEval, heckeGen]

def eisensteinMaximalIdeal (N p : ℕ) : Ideal HeckeAlg :=
  Ideal.comap (eisensteinEval N) (Ideal.span {(p : ℤ)})

/--
@isnad1 id=iff.0h3v.s7.5281ae2b367e from=translated src=- shape=9cf9ffe6 vocab=b7b6ee1e
-/
lemma mem_eisensteinMaximalIdeal_iff (N p : ℕ) (t : HeckeAlg) :
    t ∈ eisensteinMaximalIdeal N p ↔ (p : ℤ) ∣ eisensteinEval N t := by
  rw [eisensteinMaximalIdeal, Ideal.mem_comap, Ideal.mem_span_singleton]

/--
@isnad1 id=mem.0h2v.s6.d9d6ceabb476 from=translated src=- shape=14cc363d vocab=7269ba7b
-/
lemma natCast_mem_eisensteinMaximalIdeal (N p : ℕ) :
    (p : HeckeAlg) ∈ eisensteinMaximalIdeal N p := by
  rw [mem_eisensteinMaximalIdeal_iff, map_natCast]

def IsEisensteinCongruent (m : ℕ) (N : ℕ) (a : Nat.Primes → ℤ) : Prop :=
  ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ N → ((a ℓ : ZMod m)) = ((ℓ : ℕ) : ZMod m) + 1

def modSystem (m : ℕ) (a : Nat.Primes → ℤ) : Nat.Primes → ZMod m :=
  fun ℓ => (a ℓ : ZMod m)

/--
@isnad1 id=eq.0h3v.s5.eb8e2fb2e2f8 from=translated src=- shape=016e7207 vocab=8150119c
-/
@[simp] lemma modSystem_apply (m : ℕ) (a : Nat.Primes → ℤ) (ℓ : Nat.Primes) :
    modSystem m a ℓ = (a ℓ : ZMod m) := rfl

end ModularCurve
