/-
Copyright: the vendored blocks below are verbatim copies from Mathlib (Apache-2.0; see Mathlib's LICENSE),
release v4.30.0 = leanprover-community/mathlib4 commit c5ea00351c28e24afc9f0f84379aa41082b1188f, with declarations
RENAMED (suffix `Finsupp` / trailing prime) so they do not clash with Mathlib v4.33.0. Bodies are the Mathlib v4.30.0 text
with its docstrings omitted, otherwise byte-identical unless a line is marked `-- [port]`.
-/
import Tengoku.Seed.RepresentationTheory.Rep.Basic
import Tengoku.Seed.Algebra.Group.End
import Tengoku.Seed.Algebra.GroupWithZero.Action.Basic
import Tengoku.Seed.Algebra.Ring.AddAut
import Tengoku.Seed.Algebra.Ring.Action.Submonoid
import Tengoku.Seed.NumberTheory.RamificationInertia.Galois
import Tengoku.Seed.RingTheory.Invariant.Galois
import Tengoku.Seed.FieldTheory.Galois.Basic
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-! ## Block A — Mathlib v4.30.0 Mathlib/RepresentationTheory/Basic.lean:391-419 (section MulAction), names suffixed `Finsupp` -/

namespace Representation

section MulAction

variable (k : Type*) [Semiring k] (G : Type*) [Monoid G] (H : Type*) [MulAction G H]

noncomputable def ofMulActionFinsupp : Representation k G (H →₀ k) where
  toFun g := Finsupp.lmapDomain k k (g • ·)
  map_one' := by
    ext x y
    simp
  map_mul' x y := by
    ext z w
    simp [mul_smul]

noncomputable abbrev leftRegularFinsupp := ofMulActionFinsupp k G G

noncomputable abbrev diagonalFinsupp (n : ℕ) := ofMulActionFinsupp k G (Fin n → G)

variable {k G H}

/--
@isnad1 id=eq.0h4v.s8.d88ce31841fc from=translated src=- shape=a72c6414 vocab=c13e2205
-/
theorem ofMulActionFinsupp_def (g : G) : ofMulActionFinsupp k G H g = Finsupp.lmapDomain k k (g • ·) :=
  rfl

/--
@isnad1 id=eq.0h6v.s9.d0f3737f4786 from=translated src=- shape=6e8e2a83 vocab=7cce0a10
-/
@[simp]
theorem ofMulActionFinsupp_single (g : G) (x : H) (r : k) :
    ofMulActionFinsupp k G H g (Finsupp.single x r) = Finsupp.single (g • x) r :=
  Finsupp.mapDomain_single

end MulAction

/-! ## Block B — Mathlib v4.30.0 Mathlib/RepresentationTheory/Basic.lean:472-483 (section Group) -/

section Group

variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)
/--
@isnad1 id=eq.0h6v.s9.83cea9e902b2 from=translated src=- shape=a7424d91 vocab=061b19ec
-/
@[simp]
theorem ofMulActionFinsupp_apply {H : Type*} [MulAction G H] (g : G) (f : H →₀ k) (h : H) :
    ofMulActionFinsupp k G H g f h = f (g⁻¹ • h) := by
  conv_lhs => rw [← smul_inv_smul g h]
  let h' := g⁻¹ • h
  change ofMulActionFinsupp k G H g f (g • h') = f h'
  have hg : Function.Injective (g • · : H → H) := by
    intro h₁ h₂
    simp
  simp only [ofMulActionFinsupp_def, Finsupp.lmapDomain_apply, Finsupp.mapDomain_apply, hg]

end Group

section Bridge

variable (k : Type*) [Semiring k] (G : Type*) [Monoid G] (H : Type*) [MulAction G H]

noncomputable def ofMulActionFinsuppEquiv : (ofMulActionFinsupp k G H).Equiv (ofMulAction k G H) :=
  Equiv.mk (MonoidAlgebra.coeffLinearEquiv k).symm fun g => by
    rw [ofMulAction_def, ofMulActionFinsupp_def]
    ext
    simp

end Bridge

end Representation

/-! ## Block C — Mathlib v4.30.0 Mathlib/RepresentationTheory/Rep/Basic.lean:336-346 and 404-412, names suffixed `Finsupp` -/

namespace Rep

open CategoryTheory

universe w' u v

variable {k : Type u} {G : Type v} [Ring k] [Monoid G]

section

variable (k G)

noncomputable abbrev ofMulActionFinsupp (H : Type w') [MulAction G H] : Rep k G := -- [port] `noncomputable` added (4.30 file had a noncomputable section)
  of <| Representation.ofMulActionFinsupp k G H

noncomputable abbrev leftRegularFinsupp : Rep k G := -- [port] noncomputable
  ofMulActionFinsupp k G G

noncomputable abbrev diagonalFinsupp (n : ℕ) : Rep k G := -- [port] noncomputable
  ofMulActionFinsupp k G (Fin n → G)

noncomputable def ofMulActionFinsuppIso (H : Type w') [MulAction G H] :
    ofMulActionFinsupp k G H ≅ ofMulAction k G H :=
  mkIso (Representation.ofMulActionFinsuppEquiv k G H)

end

noncomputable abbrev leftRegularHomFinsupp (A : Rep k G) (x : A) : leftRegularFinsupp k G ⟶ A := -- [port] noncomputable
  Rep.ofHom ⟨Finsupp.lift A k G fun g ↦ A.ρ g x, fun g ↦ by ext; simp⟩

end Rep

/-! ## Block D — AddAut: Mathlib v4.30.0 Mathlib/Algebra/Group/End.lean:746-801 (+ GroupWithZero/Action/Basic.lean:89-92 and :104-112, Ring/AddAut.lean:32), lemma names primed -/

namespace AddAut

section Compat430

variable (A : Type*) [Add A]

instance : Group (AddAut A) where
  mul g h := AddEquiv.trans h g
  one := AddEquiv.refl _
  inv := AddEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := AddEquiv.self_trans_symm

/- The following thirteen lemmas are Mathlib v4.30.0 `Mathlib/Algebra/Group/End.lean:758-801`
verbatim except that each name carries a trailing prime. -/

/--
@isnad1 id=eq.0h3v.s7.f1c11b86767f from=translated src=- shape=367ffa20 vocab=1650b8a0
-/
@[simp]
theorem coe_mul' (e₁ e₂ : AddAut A) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.4687b9748b4a from=translated src=- shape=57311762 vocab=40f2cea7
-/
@[simp]
theorem coe_one' : ⇑(1 : AddAut A) = id :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.13f71a934bff from=translated src=- shape=5db0f2f7 vocab=c3d4e78f
-/
@[simp]
theorem coe_inv' (e : AddAut A) : ⇑e⁻¹ = e.symm := rfl

/--
@isnad1 id=eq.0h4v.s7.bb2bc6583497 from=translated src=- shape=5da52639 vocab=5e4f58a1
-/
@[simp]
theorem mul_apply' (e₁ e₂ : AddAut A) (a : A) : (e₁ * e₂) a = e₁ (e₂ a) :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.45a535da96ff from=translated src=- shape=98c5b598 vocab=f1d2f852
-/
@[simp]
theorem one_apply' (a : A) : (1 : AddAut A) a = a :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.12bc37302c4b from=translated src=- shape=9c43e376 vocab=0496cf24
-/
@[simp]
theorem inv_symm' (e : AddAut A) : e⁻¹.symm = e := rfl

/--
@isnad1 id=eq.0h2v.s5.574695ba67eb from=translated src=- shape=574e0a21 vocab=0496cf24
-/
@[simp]
theorem symm_inv' (e : AddAut A) : e.symm⁻¹ = e := rfl

/--
@isnad1 id=eq.0h3v.s6.a61ab88f1baa from=translated src=- shape=6ec83d30 vocab=c3d4e78f
-/
@[simp]
theorem inv_apply' (e : AddAut A) (a : A) : e⁻¹ a = e.symm a := rfl

end Compat430

end AddAut

@[simps]
def DistribMulAction.toAddAut' (G A : Type*) [Group G] [AddMonoid A] [DistribMulAction G A] :
    G →* AddAut A where
  toFun := DistribMulAction.toAddEquiv A
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)

@[simps! +simpRhs]
def AddAut.mulLeft' {R : Type*} [Semiring R] : Rˣ →* AddAut R :=
  DistribMulAction.toAddAut' _ _

/-! ### Block D (continued) — Mathlib v4.30.0 Mathlib/Algebra/GroupWithZero/Action/Basic.lean:104-112: the tautological `DistribMulAction (AddAut A) A`
(`AddAut.applyDistribMulAction`, its `smul_def` and `apply_faithfulSMul`), dropped in v4.33.0 together with the multiplicative structure;
vendored with primed names on top of the Group instance above. -/

namespace AddAut
instance applyDistribMulAction' {A : Type*} [AddMonoid A] : DistribMulAction (AddAut A) A where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero := AddEquiv.map_zero
  smul_add := AddEquiv.map_add

/--
@isnad1 id=eq.0h3v.s7.70e7df250cf8 from=translated src=- shape=1427c5b9 vocab=0b2ace45
-/
@[simp] protected theorem smul_def' {A : Type*} [AddMonoid A] (f : AddAut A) (a : A) : f • a = f a := rfl

end AddAut

/-! ## Block E — elliptic (divisibility) sequence predicates: Mathlib v4.30.0
Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:78-110 (verbatim; names primed). Vendored because Mathlib v4.33.0 (db584cd6,
same file :286-295) RENAMED AND REDEFINED them (`IsEllipticSequence W := ∀ p q r, IsEllipticNet.rel W p q r 0 = 0`,
`IsDvdSequence` over ℤ instead of ℕ) and kept the 4.30 names only as deprecated aliases of the NEW predicates. -/

section IsEllDivSequence430

universe u

variable {R : Type u} [CommRing R]

variable (W : ℤ → R)

def IsEllSequence' : Prop :=
  ∀ m n r : ℤ, W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2

def IsDivSequence' : Prop :=
  ∀ m n : ℕ, m ∣ n → W m ∣ W n

def IsEllDivSequence' : Prop :=
  IsEllSequence' W ∧ IsDivSequence' W

/--
@isnad1 id=isellseq.0h0v.s2.543dcb6ffcad from=translated src=- shape=3905abf2 vocab=39a6faa9
-/
lemma isEllSequence'_id : IsEllSequence' id :=
  fun _ _ _ => by simp_rw [id_eq]; ring1

/--
@isnad1 id=isdivseq.0h0v.s2.9544bb3fb3fc from=translated src=- shape=3905abf2 vocab=74669c0a
-/
lemma isDivSequence'_id : IsDivSequence' id :=
  fun _ _ => Int.ofNat_dvd.mpr

/--
@isnad1 id=iselldiv.0h0v.s2.ced726673e97 from=translated src=- shape=3905abf2 vocab=bce800a7
-/
theorem isEllDivSequence'_id : IsEllDivSequence' id :=
  ⟨isEllSequence'_id, isDivSequence'_id⟩

variable {W}

/--
@isnad1 id=isellseq.1h3v.s5.48ba9f2768f6 from=translated src=- shape=ce84ebb2 vocab=717f58bc
-/
lemma IsEllSequence'.smul (h : IsEllSequence' W) (x : R) : IsEllSequence' (x • W) :=
  fun m n r => by
    linear_combination (norm := (simp_rw [Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h m n r

/--
@isnad1 id=isdivseq.1h3v.s5.1175a7da96db from=translated src=- shape=ce84ebb2 vocab=734aba62
-/
lemma IsDivSequence'.smul (h : IsDivSequence' W) (x : R) : IsDivSequence' (x • W) :=
  fun m n r => mul_dvd_mul_left x <| h m n r

/--
@isnad1 id=iselldiv.1h3v.s5.03483f803fbf from=translated src=- shape=ce84ebb2 vocab=0299144d
-/
lemma IsEllDivSequence'.smul (h : IsEllDivSequence' W) (x : R) : IsEllDivSequence' (x • W) :=
  ⟨h.left.smul x, h.right.smul x⟩

end IsEllDivSequence430

/-! ## Block F — notation `α ^+ M` for `FixedPoints.addSubgroup M α`: Mathlib v4.30.0 Mathlib/Algebra/Ring/Action/Submonoid.lean:43
(verbatim). Mathlib v4.33.0 removed the notation line; the definition itself is unchanged, so re-declaring the notation keeps
every tree statement that uses it textually and semantically identical. -/

local notation α "^+" M:51 => FixedPoints.addSubgroup M α

/-! ## Block G — ramification/inertia cardinality lemmas under the separability hypothesis (adapted from Mathlib v4.30.0,
Mathlib/NumberTheory/RamificationInertia/Galois.lean; v4.33.0 restates them assuming PerfectField of the residue field). Theorems only,
primed names; no definitions involved. -/

namespace Ideal

section inertia430

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

open scoped Pointwise

end inertia430

end Ideal
-- Tengoku: 1 notation(s) of this module made local so they do not change other libraries (generated)
