import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Tunnell's representation sets

This file formalizes the two ternary quadratic forms in the paper and the
immediate even-coordinate branch.  An even source is parametrized by its
half-coordinate `w`; this makes the equivalence computational and avoids a
choice of a witness to divisibility by two.
-/

namespace TunnellMap

structure Triple where
  x : ℤ
  y : ℤ
  z : ℤ
deriving DecidableEq

/--
@isnad1 id=eq.3h2v.s4.aa25db4c5347 from=translated src=- shape=966c8f3f vocab=c59e3632
-/
@[ext] theorem Triple.ext {p q : Triple} (hx : p.x = q.x) (hy : p.y = q.y)
    (hz : p.z = q.z) : p = q := by
  cases p
  cases q
  simp_all

def bForm (p : Triple) : ℤ :=
  2 * p.x ^ 2 + p.y ^ 2 + 8 * p.z ^ 2

def aForm (p : Triple) : ℤ :=
  2 * p.x ^ 2 + p.y ^ 2 + 32 * p.z ^ 2

def BRep (n : ℤ) := {p : Triple // bForm p = n}

def ARep (n : ℤ) := {p : Triple // aForm p = n}

def BOddRep (n : ℤ) :=
  {p : Triple // bForm p = n ∧ Odd p.z}

/-- A source representation whose third coordinate is written as `2 * w`.-/
structure BEvenParam (n : ℤ) where
  x : ℤ
  y : ℤ
  w : ℤ
  equation : bForm ⟨x, y, 2 * w⟩ = n

def BEvenParam.asBRep {n : ℤ} (p : BEvenParam n) : BRep n :=
  ⟨⟨p.x, p.y, 2 * p.w⟩, p.equation⟩

def evenToA {n : ℤ} (p : BEvenParam n) : ARep n := by
  refine ⟨⟨p.x, p.y, p.w⟩, ?_⟩
  change 2 * p.x ^ 2 + p.y ^ 2 + 32 * p.w ^ 2 = n
  have h := p.equation
  change 2 * p.x ^ 2 + p.y ^ 2 + 8 * (2 * p.w) ^ 2 = n at h
  nlinarith

def aToEven {n : ℤ} (p : ARep n) : BEvenParam n := by
  refine ⟨p.1.x, p.1.y, p.1.z, ?_⟩
  change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 8 * (2 * p.1.z) ^ 2 = n
  have h := p.2
  change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 32 * p.1.z ^ 2 = n at h
  nlinarith

/-- The paper's even branch `(x,y,2w) ↦ (x,y,w)`.-/
def evenEquiv (n : ℤ) : BEvenParam n ≃ ARep n where
  toFun := evenToA
  invFun := aToEven
  left_inv := by
    intro p
    cases p
    rfl
  right_inv := by
    intro p
    apply Subtype.ext
    rfl

/--
@isnad1 id=eq.0h2v.s5.43e2faed1264 from=translated src=- shape=d6ff88c1 vocab=16b591e4
-/
@[simp] theorem evenEquiv_apply (n : ℤ) (p : BEvenParam n) :
    (evenEquiv n p).1 = ⟨p.x, p.y, p.w⟩ :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.c435d14f5dfd from=translated src=- shape=fb36cceb vocab=03aed563
-/
@[simp] theorem evenEquiv_symm_apply (n : ℤ) (p : ARep n) :
    (evenEquiv n).symm p = aToEven p :=
  rfl

end TunnellMap
