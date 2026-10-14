/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Tengoku.LeanPool.LeanPool.CompositionAlgebras.Composition.Defs
public import Tengoku

/-!
# The Cayley–Dickson double as an external type former

`Composition/Doubling.lean` doubles *inside* a composition algebra `C`: given a composition
subalgebra `A ≤ C` and a unit `u ⊥ A`, the submodule `A ⊕ A u` is again a composition
subalgebra. That is all Hurwitz's *dimension* bound needs, and it is cheap because the
composition law of `C` is already available.

The *classification* needs the other half: a functor `D ↦ CD D` producing a **new** algebra,
so that the chain of subalgebras can be identified with concrete carriers rather than merely
counted. This file builds it.

## Main definitions

* `CompositionAlgebra.CD D` — the double `D × D` with
  `(a,b)(c,d) = (a c - d* b, d a + b c*)` and `1 = (1,0)`.
* `CompositionAlgebra.CD.bilin` — the form `⟪(a,b), (c,d)⟫ = ⟪a,c⟫ + ⟪b,d⟫`.

## Main results

* `CD.instNonAssocRing`, `CD.instModule`, and the two bilinearity classes — `CD D` is a
  bilinear unital ring over `ℝ` whenever `D` is.
* `CD.instCompositionAlgebra` — **`CD D` is a Euclidean composition algebra when `D` is
  nontrivial and associative.** Associativity is used exactly once, in the cross term of the
  composition law:
  expanding `N((a,b)(c,d)) = N(a,b) N(c,d)` leaves the residue
  `⟪d a, b c*⟫ = ⟪a c, d* b⟫`, and the two adjoint identities turn each side into
  `⟪a, (d* b) c*⟫` and `⟪a, d* (b c*)⟫` respectively.

★ This is the same mechanism as `IsCompSubalgebra.forced_assoc`, read in the other direction:
there, multiplicativity of the norm on `A ⊕ A u` is free (it is inherited from `C`) and forces
`A` associative; here, `D` associative is a hypothesis and buys multiplicativity of the norm on
the new type.

## Note on the conjugation

`CD` is built over `CompositionAlgebra D`, whose conjugation `cstar` is *derived* from the form
rather than supplied as a `Star` structure. An upstreamed version would take `[Star D]` and a
`StarRing` hypothesis; here the derived conjugation keeps the four concrete instantiations free
of bridging lemmas.

## Scope

Substrate for the classification. The headline declaration is the instance
`CD.instCompositionAlgebra`; the classification itself is
`Composition/Classification.lean`.
-/

@[expose] public section

namespace CompositionAlgebra

universe u

/-- The **Cayley–Dickson double** of `D`: the module `D × D` with the product
`(a,b)(c,d) = (a c - d* b, d a + b c*)` and unit `(1,0)`.

Kept as a type synonym rather than a structure so that the additive and `ℝ`-module structure
transfer from `Prod` verbatim; the product and the unit are the only new data. -/
def CD (D : Type u) : Type u := D × D

namespace CD

variable {D : Type u} [NonAssocRing D] [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D]

instance instAddCommGroup : AddCommGroup (CD D) := inferInstanceAs (AddCommGroup (D × D))

instance instModule : Module ℝ (CD D) := inferInstanceAs (Module ℝ (D × D))

/-- Assemble an element of the double from its two components. -/
def mk (a b : D) : CD D := (a, b)

/-- The first component of an element of the double. -/
def fst (x : CD D) : D := Prod.fst (α := D) (β := D) x

/-- The second component of an element of the double. -/
def snd (x : CD D) : D := Prod.snd (α := D) (β := D) x

omit [NonAssocRing D] [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] in
/--
@isnad1 id=eq.0h3v.s3.4049c107c6b1 from=translated src=- shape=bb87f601 vocab=bac8b8d5
-/
@[simp] theorem fst_mk (a b : D) : (mk a b).fst = a := rfl

omit [NonAssocRing D] [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] in
/--
@isnad1 id=eq.0h3v.s3.5dd482930925 from=translated src=- shape=25a5fd41 vocab=a8b7d179
-/
@[simp] theorem snd_mk (a b : D) : (mk a b).snd = b := rfl

omit [NonAssocRing D] [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] in
/--
@isnad1 id=eq.2h3v.s4.ca8f0cf7947c from=translated src=- shape=46590be3 vocab=6d7d2e18
-/
@[ext] theorem ext {x y : CD D} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  Prod.ext (α := D) (β := D) h1 h2

omit [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] in
/--
@isnad1 id=eq.0h1v.s5.d4d0fa370632 from=translated src=- shape=c6b7a0b8 vocab=c1e12d7d
-/
@[simp] theorem fst_zero : (0 : CD D).fst = 0 := rfl

omit [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] in
/--
@isnad1 id=eq.0h1v.s5.6c644bf55514 from=translated src=- shape=c6b7a0b8 vocab=476a0324
-/
@[simp] theorem snd_zero : (0 : CD D).snd = 0 := rfl

omit [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] in
/--
@isnad1 id=eq.0h3v.s5.9c7087c38f16 from=translated src=- shape=0090f101 vocab=0101f82d
-/
@[simp] theorem fst_add (x y : CD D) : (x + y).fst = x.fst + y.fst := rfl

omit [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] in
/--
@isnad1 id=eq.0h3v.s5.be534fc8f8a1 from=translated src=- shape=0090f101 vocab=fa7f51e2
-/
@[simp] theorem snd_add (x y : CD D) : (x + y).snd = x.snd + y.snd := rfl

omit [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] in
/--
@isnad1 id=eq.0h2v.s5.512861b03496 from=translated src=- shape=58efbbcf vocab=7440d37b
-/
@[simp] theorem fst_neg (x : CD D) : (-x).fst = -x.fst := rfl

omit [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] in
/--
@isnad1 id=eq.0h2v.s5.05a82f403035 from=translated src=- shape=58efbbcf vocab=2fe639c5
-/
@[simp] theorem snd_neg (x : CD D) : (-x).snd = -x.snd := rfl

omit [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] in
/--
@isnad1 id=eq.0h3v.s5.707e17939872 from=translated src=- shape=0090f101 vocab=0531c07b
-/
@[simp] theorem fst_sub (x y : CD D) : (x - y).fst = x.fst - y.fst := rfl

omit [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] in
/--
@isnad1 id=eq.0h3v.s5.56c6f78be3df from=translated src=- shape=0090f101 vocab=f9464437
-/
@[simp] theorem snd_sub (x y : CD D) : (x - y).snd = x.snd - y.snd := rfl

omit [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] in
/--
@isnad1 id=eq.0h3v.s7.82ec707b4839 from=translated src=- shape=8ed60837 vocab=5e455858
-/
@[simp] theorem fst_smul (r : ℝ) (x : CD D) : (r • x).fst = r • x.fst := rfl

omit [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] in
/--
@isnad1 id=eq.0h3v.s7.1d6349b72549 from=translated src=- shape=8ed60837 vocab=3d652a55
-/
@[simp] theorem snd_smul (r : ℝ) (x : CD D) : (r • x).snd = r • x.snd := rfl

variable [CompositionAlgebra D]

instance instOne : One (CD D) := ⟨mk 1 0⟩

omit [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] [CompositionAlgebra D] in
/--
@isnad1 id=eq.0h1v.s5.49ff566cc6ba from=translated src=- shape=c6b7a0b8 vocab=c1e12d7d
-/
@[simp] theorem fst_one : (1 : CD D).fst = 1 := rfl

omit [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] [CompositionAlgebra D] in
/--
@isnad1 id=eq.0h1v.s5.98fe8d961182 from=translated src=- shape=c6b7a0b8 vocab=476a0324
-/
@[simp] theorem snd_one : (1 : CD D).snd = 0 := rfl

instance instMul : Mul (CD D) :=
  ⟨fun x y => mk (x.fst * y.fst - cstar y.snd * x.snd) (y.snd * x.fst + x.snd * cstar y.fst)⟩

/--
@isnad1 id=eq.0h3v.s8.13f5c01e43d7 from=translated src=- shape=ceb38962 vocab=6535c3c1
-/
@[simp] theorem fst_mul (x y : CD D) :
    (x * y).fst = x.fst * y.fst - cstar y.snd * x.snd := rfl

/--
@isnad1 id=eq.0h3v.s8.fa55650e80d2 from=translated src=- shape=775ee312 vocab=a587a845
-/
@[simp] theorem snd_mul (x y : CD D) :
    (x * y).snd = y.snd * x.fst + x.snd * cstar y.fst := rfl

/--
@isnad1 id=eq.0h5v.s8.e2f710c6c858 from=translated src=- shape=5d249e54 vocab=edd61d2e
-/
theorem mul_def (a b c d : D) :
    mk a b * mk c d = mk (a * c - cstar d * b) (d * a + b * cstar c) := rfl

/-! ### The ring structure -/

variable [Nontrivial D]

instance instNonAssocRing : NonAssocRing (CD D) :=
  { (inferInstance : AddCommGroup (CD D)) with
    one := 1
    mul := (· * ·)
    left_distrib := by
      intro x y z
      ext <;> simp [cstar_add, mul_add, add_mul] <;> abel
    right_distrib := by
      intro x y z
      ext <;> simp [mul_add, add_mul] <;> abel
    zero_mul := by intro x; ext <;> simp
    mul_zero := by intro x; ext <;> simp [cstar_zero]
    one_mul := by intro x; ext <;> simp
    mul_one := by intro x; ext <;> simp [cstar_zero] }

/--
@isnad1 id=isscalar.0h1v.s8.e4b873ee1568 from=translated src=- shape=3a496db4 vocab=433d4f07
-/
instance instIsScalarTower : IsScalarTower ℝ (CD D) (CD D) where
  smul_assoc r x y := by
    ext <;> simp [smul_mul_assoc, mul_smul_comm, smul_sub, smul_add]

/--
@isnad1 id=smulcomm.0h1v.s8.e92238733bd9 from=translated src=- shape=3163aaf1 vocab=433d4f07
-/
instance instSMulCommClass : SMulCommClass ℝ (CD D) (CD D) where
  smul_comm r x y := by
    ext <;> simp [cstar_smul, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add]

/-! ### The form -/

/-- The form of the double: `⟪(a,b), (c,d)⟫ = ⟪a,c⟫ + ⟪b,d⟫`. -/
def bilin : CD D →ₗ[ℝ] CD D →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ip x.fst y.fst + ip x.snd y.snd)
    (by intro x y z; simp; ring)
    (by intro c x y; simp; ring)
    (by intro x y z; simp; ring)
    (by intro c x y; simp; ring)

/--
@isnad1 id=eq.0h3v.s9.95b0f72dc70a from=translated src=- shape=84600ae6 vocab=6abcd98b
-/
@[simp] theorem bilin_apply (x y : CD D) :
    bilin x y = ip x.fst y.fst + ip x.snd y.snd := rfl

/-! ### The composition law

Associativity of `D` enters exactly here, and exactly once: in `cross`. -/

omit [Nontrivial D] in
/-- The cross term of the composition law. This is the *only* step of
`compositionAlgebraOfAssoc` that uses associativity of `D`, and it is the same identity that
`IsCompSubalgebra.forced_assoc` reads in the opposite direction.
@isnad1 id=eq.1h5v.s8.99fe209d98d2 from=translated src=- shape=63c27ebf vocab=b863bdb7
-/
theorem cross (hassoc : ∀ p q r : D, (p * q) * r = p * (q * r)) (a b c d : D) :
    ip (d * a) (b * cstar c) = ip (a * c) (cstar d * b) := by
  rw [ip_mul_adj_left, ip_mul_adj_right, hassoc]

/-- **The Cayley–Dickson double of an associative composition algebra is a composition
algebra.** Stated as a `def` taking associativity as an explicit hypothesis; the instance for
`[Ring D]` is `instCompositionAlgebra` below. -/
def compositionAlgebraOfAssoc (hassoc : ∀ p q r : D, (p * q) * r = p * (q * r)) :
    CompositionAlgebra (CD D) where
  B := bilin
  B_symm x y := by simp [ip_symm x.fst y.fst, ip_symm x.snd y.snd]
  B_pos x hx := by
    have hne : x.fst ≠ 0 ∨ x.snd ≠ 0 := by
      by_contra hc
      rw [not_or, not_not, not_not] at hc
      exact hx (CD.ext hc.1 hc.2)
    simp only [bilin_apply, ← nf_eq_ip]
    rcases hne with h | h
    · exact add_pos_of_pos_of_nonneg (nf_pos h) (nf_nonneg _)
    · exact add_pos_of_nonneg_of_pos (nf_nonneg _) (nf_pos h)
  B_comp x y := by
    simp only [bilin_apply, ← nf_eq_ip, fst_mul, snd_mul]
    rw [nf_sub, nf_add, comp, comp, comp, comp, nf_cstar, nf_cstar,
      cross hassoc x.fst x.snd y.fst y.snd]
    ring

end CD

/-! ### The double of an associative composition algebra -/

section Assoc

variable {D : Type u} [Ring D] [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D]
  [CompositionAlgebra D] [Nontrivial D]

/-- **`CD D` is a Euclidean composition algebra whenever `D` is an associative one.** -/
instance CD.instCompositionAlgebra : CompositionAlgebra (CD D) :=
  CD.compositionAlgebraOfAssoc (fun p q r => mul_assoc p q r)

/--
@isnad1 id=eq.0h2v.s8.ae5afdb71a46 from=translated src=- shape=f27cadbd vocab=7abab7dd
-/
@[simp] theorem CD.nf_eq (x : CD D) : nf x = nf x.fst + nf x.snd := rfl

/--
@isnad1 id=eq.0h3v.s8.5bac61d894c5 from=translated src=- shape=d6dc95cf vocab=5a468cec
-/
@[simp] theorem CD.ip_eq (x y : CD D) : ip x y = ip x.fst y.fst + ip x.snd y.snd := rfl

end Assoc

end CompositionAlgebra
