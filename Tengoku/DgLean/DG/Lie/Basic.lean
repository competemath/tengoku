import Tengoku.Seed.Algebra.Lie.Basic
import Tengoku.DgLean.DG.Algebra.Constructions
import Tengoku.DgLean.DG.Module.HomLinear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differential graded Lie algebras

A *dg Lie algebra* over a commutative ring `R` is a complex of `R`-modules `L` (a dg abelian group
whose graded pieces are `R`-submodules and whose differential is `R`-linear) with an `R`-bilinear
bracket `[-, -]` of degree `0` such that, for homogeneous `x ∈ Lⁱ`, `y ∈ Lʲ`,
* graded antisymmetry: `[x, y] = -(-1)^(i j) • [y, x]`;
* graded Jacobi identity, in Leibniz form: `[x, [y, z]] = [[x, y], z] + (-1)^(i j) • [y, [x, z]]`
  (`ad x` is a derivation of degree `i`); the cyclic form is `DG.DGLieAlgebra.jacobi_cyclic`;
* the differential is a derivation of the bracket: `d [x, y] = [d x, y] + (-1)^i • [x, d y]`.

Mathlib's `LieRing` is ungraded, so a dg Lie algebra is not a `LieRing`; we define it as a class
`DG.DGLieAlgebra R L` on a type with `[AddCommGroup L] [Module R L] [DGAddCommGroup L]`, carrying
the bracket as an `R`-bilinear map.

## Main definitions and results

* `DG.DGLieAlgebra R L`, with the bracket `DG.DGLieAlgebra.bracket R x y`; the axioms
  `bracket_mem`, `bracket_comm`, `jacobi`, `d_bracket`, and the cyclic Jacobi identity
  `DG.DGLieAlgebra.jacobi_cyclic`.
* `DG.DGAlgebra.commutator R A`: the graded commutator `[a, b] = a b - (-1)^(|a||b|) b a` on a dg
  `R`-algebra, as an `R`-bilinear map (`DG.DGAlgebra.commutator_of_mem`).
* `DG.DGLieAlgebra.ofDGAlgebra R A`: every dg `R`-algebra is a dg Lie algebra under the graded
  commutator. In particular `END_A(M)` is a dg Lie algebra
  (`DG.DGModule.END.dgLieAlgebra`), with bracket `[f, g] = f g - (-1)^(|f||g|) g f` for the
  product of `END_A(M)`.
* `DG.DGLieAlgebra.ofLieAlgebra R L`: an ordinary Lie algebra, concentrated in degree `0` with
  zero differential.

## Conventions

Signs are Koszul signs `koszulSign n = Int.negOnePow n : ℤˣ` (see `docs/CONVENTIONS.md`). Gradings
are cohomological: `d` has degree `+1`.
-/

open scoped DG

open DirectSum

namespace DG

/-! ### The odd part of a dg algebra -/

section OddPart

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A]
  [DGAlgebra R A]

open Classical in
/-- The projection of a dg `R`-algebra onto its odd part `⨁ᵢ A²ⁱ⁺¹`, an `R`-linear map.-/
noncomputable def DGAlgebra.oddPart : A →ₗ[R] A :=
  DirectSum.toModule R ℤ A
      (fun i => if Odd i then (DGAlgebra.gradingSubmodule R A i).subtype else 0) ∘ₗ
    (decomposeLinearEquiv (DGAlgebra.gradingSubmodule R A)).toLinearMap

variable {R A}

/--
@isnad1 id=eq.2h4v.s7.638532a2ac30 from=translated src=- shape=3a9de7d6 vocab=923906ec
-/
theorem DGAlgebra.oddPart_of_odd {i : ℤ} {a : A} (ha : a ∈ grading i) (hi : Odd i) :
    DGAlgebra.oddPart R A a = a := by
  rw [DGAlgebra.oddPart, LinearMap.comp_apply, LinearEquiv.coe_coe, decomposeLinearEquiv_apply,
    decompose_of_mem (DGAlgebra.gradingSubmodule R A) (i := i) ha, ← lof_eq_of R,
    toModule_lof, ite_eq_left hi, Submodule.subtype_apply]

/--
@isnad1 id=eq.2h4v.s7.34670297d3be from=translated src=- shape=b1f3f9d7 vocab=1a699dc0
-/
theorem DGAlgebra.oddPart_of_even {i : ℤ} {a : A} (ha : a ∈ grading i) (hi : Even i) :
    DGAlgebra.oddPart R A a = 0 := by
  rw [DGAlgebra.oddPart, LinearMap.comp_apply, LinearEquiv.coe_coe, decomposeLinearEquiv_apply,
    decompose_of_mem (DGAlgebra.gradingSubmodule R A) (i := i) ha, ← lof_eq_of R,
    toModule_lof, ite_eq_right (Int.not_odd_iff_even.mpr hi), LinearMap.zero_apply]

end OddPart

/-! ### dg Lie algebras -/

/-- A differential graded Lie algebra over `R`: a dg abelian group `L` with an `R`-module
structure for which the graded pieces are submodules and `d` is `R`-linear, together with an
`R`-bilinear bracket of degree `0` which is graded antisymmetric, satisfies the graded Jacobi
identity, and for which `d` is a derivation.-/
class DGLieAlgebra (R : Type*) (L : Type*) [CommRing R] [AddCommGroup L] [Module R L]
    [DGAddCommGroup L] where
  /-- The bracket, as an `R`-bilinear map.-/
  bracketₗ : L →ₗ[R] L →ₗ[R] L
  smul_mem' : ∀ (r : R) {n : ℤ} {x : L}, x ∈ grading n → r • x ∈ grading n
  d_smul' : ∀ (r : R) (x : L), d (r • x) = r • d x
  bracket_mem' : ∀ {i j : ℤ} {x y : L}, x ∈ grading i → y ∈ grading j →
    bracketₗ x y ∈ grading (i + j)
  bracket_comm' : ∀ {i j : ℤ} {x y : L}, x ∈ grading i → y ∈ grading j →
    bracketₗ x y = -(koszulSign (i * j) • bracketₗ y x)
  jacobi' : ∀ {i j : ℤ} {x y : L}, x ∈ grading i → y ∈ grading j → ∀ z : L,
    bracketₗ x (bracketₗ y z) =
      bracketₗ (bracketₗ x y) z + koszulSign (i * j) • bracketₗ y (bracketₗ x z)
  d_bracket' : ∀ {i : ℤ} {x : L}, x ∈ grading i → ∀ y : L,
    d (bracketₗ x y) = bracketₗ (d x) y + koszulSign i • bracketₗ x (d y)

namespace DGLieAlgebra

variable (R : Type*) {L : Type*} [CommRing R] [AddCommGroup L] [Module R L] [DGAddCommGroup L]
  [DGLieAlgebra R L]

/-- The bracket `[x, y]` of a dg Lie algebra.-/
def bracket (x y : L) : L := bracketₗ (R := R) x y

/--
@isnad1 id=eq.0h4v.s8.70c73961f809 from=translated src=- shape=6cd44bf0 vocab=ed3e9b01
-/
theorem bracketₗ_apply (x y : L) : bracketₗ (R := R) x y = bracket R x y := rfl

variable {R}

/--
@isnad1 id=mem.1h5v.s7.427927284f13 from=translated src=- shape=ef6257ec vocab=c8c611af
-/
theorem smul_mem (r : R) {n : ℤ} {x : L} (hx : x ∈ grading n) : r • x ∈ grading n :=
  smul_mem' r hx

/--
@isnad1 id=eq.0h4v.s8.f7bb0416dc17 from=translated src=- shape=b4102a46 vocab=7ba900f7
-/
theorem d_smul (r : R) (x : L) : d (r • x) = r • d x := d_smul' r x

/--
@isnad1 id=mem.2h6v.s7.c939d5034e61 from=translated src=- shape=58b64ffc vocab=5975ad2c
-/
theorem bracket_mem {i j : ℤ} {x y : L} (hx : x ∈ grading i) (hy : y ∈ grading j) :
    bracket R x y ∈ grading (i + j) :=
  bracket_mem' hx hy

/-- Graded antisymmetry: `[x, y] = -(-1)^(i j) • [y, x]`.
@isnad1 id=eq.2h6v.s7.1c05310a91b7 from=translated src=- shape=7b68b102 vocab=06667c40
-/
theorem bracket_comm {i j : ℤ} {x y : L} (hx : x ∈ grading i) (hy : y ∈ grading j) :
    bracket R x y = -(koszulSign (i * j) • bracket R y x) :=
  bracket_comm' hx hy

/-- The graded Jacobi identity, in Leibniz form:
`[x, [y, z]] = [[x, y], z] + (-1)^(i j) • [y, [x, z]]`.
@isnad1 id=eq.2h7v.s7.e4b60e723a70 from=translated src=- shape=b1fbd50e vocab=df56c2b0
-/
theorem jacobi {i j : ℤ} {x y : L} (hx : x ∈ grading i) (hy : y ∈ grading j) (z : L) :
    bracket R x (bracket R y z) =
      bracket R (bracket R x y) z + koszulSign (i * j) • bracket R y (bracket R x z) :=
  jacobi' hx hy z

/-- The differential is a derivation of the bracket: `d [x, y] = [d x, y] + (-1)^i • [x, d y]`.
@isnad1 id=eq.1h5v.s8.ab7073c7c5a8 from=translated src=- shape=67aed379 vocab=9352e833
-/
theorem d_bracket {i : ℤ} {x : L} (hx : x ∈ grading i) (y : L) :
    d (bracket R x y) = bracket R (d x) y + koszulSign i • bracket R x (d y) :=
  d_bracket' hx y

/--
@isnad1 id=eq.0h4v.s6.a4464a4c55f6 from=translated src=- shape=d61d5c3d vocab=60688cfc
-/
@[simp] theorem bracket_neg (x y : L) : bracket R x (-y) = -bracket R x y := map_neg _ _

/--
@isnad1 id=eq.0h3v.s6.dacb5721d41b from=translated src=- shape=84e78afa vocab=cddfc657
-/
@[simp] theorem bracket_zero (x : L) : bracket R x 0 = 0 := map_zero _
/--
@isnad1 id=eq.0h3v.s6.3ba64f89de5b from=translated src=- shape=412c674a vocab=cddfc657
-/
@[simp] theorem zero_bracket (y : L) : bracket R 0 y = 0 := by
  rw [bracket, map_zero, LinearMap.zero_apply]

/--
@isnad1 id=eq.0h5v.s6.b9cad425303d from=translated src=- shape=9dc54c7b vocab=f6fe7406
-/
theorem bracket_add (x y y' : L) : bracket R x (y + y') = bracket R x y + bracket R x y' :=
  map_add _ _ _
/--
@isnad1 id=eq.0h5v.s6.760cee7df1bc from=translated src=- shape=8a488621 vocab=f6fe7406
-/
theorem add_bracket (x x' y : L) : bracket R (x + x') y = bracket R x y + bracket R x' y := by
  rw [bracket, map_add, LinearMap.add_apply]; rfl

/--
@isnad1 id=eq.0h5v.s7.062f0cfbf053 from=translated src=- shape=cef79c01 vocab=b5c802f3
-/
theorem bracket_smul (r : R) (x y : L) : bracket R x (r • y) = r • bracket R x y :=
  map_smul _ _ _
/--
@isnad1 id=eq.0h5v.s7.eb5713a1aa7e from=translated src=- shape=1d303365 vocab=b5c802f3
-/
theorem smul_bracket (r : R) (x y : L) : bracket R (r • x) y = r • bracket R x y := by
  rw [bracket, map_smul, LinearMap.smul_apply]; rfl

/--
@isnad1 id=eq.0h5v.s6.7d68889c473b from=translated src=- shape=934bf5e3 vocab=5b79dca4
-/
theorem bracket_units_smul (u : ℤˣ) (x y : L) : bracket R x (u • y) = u • bracket R x y := by
  rw [Units.smul_def, Units.smul_def, bracket, map_zsmul]; rfl
/--
@isnad1 id=eq.0h5v.s6.ba79bd16f0c0 from=translated src=- shape=a5a5949a vocab=5b79dca4
-/
theorem units_smul_bracket (u : ℤˣ) (x y : L) : bracket R (u • x) y = u • bracket R x y := by
  rw [Units.smul_def, Units.smul_def, bracket, map_zsmul, LinearMap.smul_apply]; rfl

/-- For `x` of even degree, `[x, x] = -[x, x]`.
@isnad1 id=eq.2h4v.s6.f72076e587e5 from=translated src=- shape=8670738d vocab=f469412d
-/
theorem bracket_self_of_even {i : ℤ} {x : L} (hx : x ∈ grading i) (hi : Even i) :
    bracket R x x = -bracket R x x := by
  conv_lhs => rw [bracket_comm hx hx, koszulSign_even (hi.mul_right i), one_smul]

private theorem units_cases (u : ℤˣ) : u = 1 ∨ u = -1 := Int.units_eq_one_or u

/-- The graded Jacobi identity in cyclic form:
`(-1)^(i k) [x, [y, z]] + (-1)^(j i) [y, [z, x]] + (-1)^(k j) [z, [x, y]] = 0`.
@isnad1 id=eq.3h8v.s8.79d26a6c2ab8 from=translated src=- shape=f06e5032 vocab=df56c2b0
-/
theorem jacobi_cyclic {i j k : ℤ} {x y z : L} (hx : x ∈ grading i) (hy : y ∈ grading j)
    (hz : z ∈ grading k) :
    koszulSign (i * k) • bracket R x (bracket R y z) +
      koszulSign (j * i) • bracket R y (bracket R z x) +
        koszulSign (k * j) • bracket R z (bracket R x y) = 0 := by
  rw [jacobi hx hy, bracket_comm (bracket_mem hx hy) hz, bracket_comm hx hz, bracket_neg,
    bracket_units_smul, add_mul, koszulSign_add, mul_comm j i, mul_comm k j]
  rcases units_cases (koszulSign (i * j)) with h₁ | h₁ <;>
  rcases units_cases (koszulSign (i * k)) with h₂ | h₂ <;>
  rcases units_cases (koszulSign (j * k)) with h₃ | h₃ <;>
  simp only [h₁, h₂, h₃, smul_add, smul_neg, mul_one, mul_neg, neg_neg,
    Units.neg_smul, one_smul] <;>
  abel

end DGLieAlgebra

/-! ### The graded commutator of a dg algebra -/

section Commutator

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A]
  [DGAlgebra R A]

/-- The graded commutator of a dg `R`-algebra, the `R`-bilinear map with
`[a, b] = a * b - (-1)^(|a||b|) • (b * a)` for homogeneous `a`, `b`
(`DG.DGAlgebra.commutator_of_mem`). It is defined as `a * b - b * a + 2 • (b₁ * a₁)`, where `x₁`
is the odd part of `x`.-/
noncomputable def DGAlgebra.commutator : A →ₗ[R] A →ₗ[R] A :=
  LinearMap.mul R A - (LinearMap.mul R A).flip +
    (2 : R) • (LinearMap.mul R A).flip.compl₁₂ (DGAlgebra.oddPart R A) (DGAlgebra.oddPart R A)

variable {R A}

/--
@isnad1 id=eq.0h4v.s9.560b32e31e2c from=translated src=- shape=51aeac86 vocab=ba710512
-/
theorem DGAlgebra.commutator_apply (a b : A) :
    DGAlgebra.commutator R A a b =
      a * b - b * a + (2 : R) • (DGAlgebra.oddPart R A b * DGAlgebra.oddPart R A a) :=
  rfl

/-- The graded commutator on homogeneous elements: `[a, b] = a * b - (-1)^(i j) • (b * a)`.
@isnad1 id=eq.2h6v.s9.b9c60398f64a from=translated src=- shape=6d8daa92 vocab=a4219a9c
-/
theorem DGAlgebra.commutator_of_mem {i j : ℤ} {a b : A} (ha : a ∈ grading i)
    (hb : b ∈ grading j) :
    DGAlgebra.commutator R A a b = a * b - koszulSign (i * j) • (b * a) := by
  rw [DGAlgebra.commutator_apply]
  rcases Int.even_or_odd i with hi | hi
  · rw [DGAlgebra.oddPart_of_even ha hi, mul_zero, smul_zero, add_zero,
      koszulSign_even (hi.mul_right j), one_smul]
  · rcases Int.even_or_odd j with hj | hj
    · rw [DGAlgebra.oddPart_of_even hb hj, zero_mul, smul_zero, add_zero,
        koszulSign_even (hj.mul_left i), one_smul]
    · rw [DGAlgebra.oddPart_of_odd ha hi, DGAlgebra.oddPart_of_odd hb hj,
        koszulSign_odd (hi.mul hj), two_smul, Units.neg_smul, one_smul]
      abel

/--
@isnad1 id=mem.2h6v.s9.1210298c38fc from=translated src=- shape=08c85d68 vocab=900dc35d
-/
theorem DGAlgebra.commutator_mem {i j : ℤ} {a b : A} (ha : a ∈ grading i)
    (hb : b ∈ grading j) : DGAlgebra.commutator R A a b ∈ grading (i + j) := by
  rw [DGAlgebra.commutator_of_mem ha hb, Units.smul_def]
  exact sub_mem (mul_mem_grading ha hb)
    (zsmul_mem (by rw [add_comm]; exact mul_mem_grading hb ha) _)

private theorem units_cases (u : ℤˣ) : u = 1 ∨ u = -1 := Int.units_eq_one_or u

private theorem mul_units_smul {T : Type*} [Ring T] (x y : T) (u : ℤˣ) :
    x * (u • y) = u • (x * y) := by
  rw [Units.smul_def, Units.smul_def, mul_smul_comm]

private theorem units_smul_mul {T : Type*} [Ring T] (x y : T) (u : ℤˣ) :
    (u • x) * y = u • (x * y) := by
  rw [Units.smul_def, Units.smul_def, smul_mul_assoc]

/--
@isnad1 id=eq.2h7v.s11.66dcceed2035 from=translated src=- shape=046f8f18 vocab=1ad704f0
-/
theorem DGAlgebra.commutator_jacobi {i j : ℤ} {a b : A} (ha : a ∈ grading i)
    (hb : b ∈ grading j) (c : A) :
    DGAlgebra.commutator R A a (DGAlgebra.commutator R A b c) =
      DGAlgebra.commutator R A (DGAlgebra.commutator R A a b) c +
        koszulSign (i * j) • DGAlgebra.commutator R A b (DGAlgebra.commutator R A a c) := by
  induction c using induction_on with
  | h_zero => simp
  | h_add c c' hc hc' => simp only [map_add, hc, hc', smul_add]; abel
  | h_homogeneous c =>
    obtain ⟨c, hc⟩ := c
    rename_i k
    simp only
    rw [DGAlgebra.commutator_of_mem ha (DGAlgebra.commutator_mem hb hc),
      DGAlgebra.commutator_of_mem (DGAlgebra.commutator_mem ha hb) hc,
      DGAlgebra.commutator_of_mem hb (DGAlgebra.commutator_mem ha hc),
      DGAlgebra.commutator_of_mem hb hc, DGAlgebra.commutator_of_mem ha hc,
      DGAlgebra.commutator_of_mem ha hb]
    simp only [mul_sub, sub_mul, mul_units_smul, units_smul_mul, smul_sub, smul_smul, mul_assoc,
      mul_add, add_mul, koszulSign_add, mul_comm j i]
    rcases units_cases (koszulSign (i * j)) with h₁ | h₁ <;>
    rcases units_cases (koszulSign (i * k)) with h₂ | h₂ <;>
    rcases units_cases (koszulSign (j * k)) with h₃ | h₃ <;>
    simp only [h₁, h₂, h₃, mul_one, mul_neg,
      neg_neg, Units.neg_smul, one_smul] <;>
    abel

/--
@isnad1 id=eq.1h5v.s11.225595fe2e88 from=translated src=- shape=87d0ae49 vocab=7cb53995
-/
theorem DGAlgebra.d_commutator {i : ℤ} {a : A} (ha : a ∈ grading i) (b : A) :
    d (DGAlgebra.commutator R A a b) =
      DGAlgebra.commutator R A (d a) b + koszulSign i • DGAlgebra.commutator R A a (d b) := by
  induction b using induction_on with
  | h_zero => simp
  | h_add b b' hb hb' => simp only [map_add, hb, hb', smul_add]; abel
  | h_homogeneous b =>
    obtain ⟨b, hb⟩ := b
    rename_i j
    simp only
    rw [DGAlgebra.commutator_of_mem ha hb, DGAlgebra.commutator_of_mem (d_mem ha) hb,
      DGAlgebra.commutator_of_mem ha (d_mem hb), d_sub, d_units_smul, d_mul ha, d_mul hb]
    simp only [smul_sub, smul_add, smul_smul, add_mul, mul_add, one_mul, mul_one,
      koszulSign_add]
    rcases units_cases (koszulSign (i * j)) with h₁ | h₁ <;>
    rcases units_cases (koszulSign i) with h₂ | h₂ <;>
    rcases units_cases (koszulSign j) with h₃ | h₃ <;>
    simp only [h₁, h₂, h₃, mul_one, mul_neg,
      neg_neg, Units.neg_smul, one_smul] <;>
    abel

variable (R A)

/-- A dg `R`-algebra is a dg Lie algebra under the graded commutator
`[a, b] = a * b - (-1)^(|a||b|) • (b * a)`. Not an instance: a dg algebra may carry other dg Lie
algebra structures.-/
@[instance_reducible]
noncomputable def DGLieAlgebra.ofDGAlgebra : DGLieAlgebra R A where
  bracketₗ := DGAlgebra.commutator R A
  smul_mem' r _ _ hx := DGAlgebra.smul_mem r hx
  d_smul' := d_smul_algebra
  bracket_mem' := DGAlgebra.commutator_mem
  bracket_comm' {i j x y} hx hy := by
    rw [DGAlgebra.commutator_of_mem hx hy, DGAlgebra.commutator_of_mem hy hx, smul_sub,
      smul_smul, mul_comm j i, Int.units_mul_self, one_smul, neg_sub]
  jacobi' := DGAlgebra.commutator_jacobi
  d_bracket' := DGAlgebra.d_commutator

variable {R A}

/--
@isnad1 id=eq.0h4v.s9.901d290b08d2 from=translated src=- shape=c5c2c806 vocab=07a142b4
-/
theorem DGLieAlgebra.ofDGAlgebra_bracket (a b : A) :
    letI := DGLieAlgebra.ofDGAlgebra R A
    DGLieAlgebra.bracket R a b = DGAlgebra.commutator R A a b :=
  rfl

end Commutator

/-! ### The endomorphism dg Lie algebra -/

namespace DGModule.END

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A]
  [DGAlgebra R A] (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [Module R M] [IsScalarTower R A M]

/-- `END_A(M)` is a dg Lie algebra under the graded commutator of its product.-/
@[instance_reducible]
noncomputable def dgLieAlgebra : DGLieAlgebra R (END A M) :=
  DGLieAlgebra.ofDGAlgebra R (END A M)

variable {R A M}

/-- The bracket of `END_A(M)` on homogeneous elements: `[f, g] = f * g - (-1)^(i j) • (g * f)`,
where `f * g = (-1)^(i j) • g ∘ f` is the product of `END_A(M)` (`DG.DGModule.END.of_mul_of`).
@isnad1 id=eq.2h7v.s10.d0a97be5790c from=translated src=- shape=bd9a1223 vocab=de61798c
-/
theorem dgLieAlgebra_bracket_of_mem {i j : ℤ} {f g : END A M} (hf : f ∈ grading i)
    (hg : g ∈ grading j) :
    letI := dgLieAlgebra R A M
    DGLieAlgebra.bracket R f g = f * g - koszulSign (i * j) • (g * f) :=
  DGAlgebra.commutator_of_mem hf hg

end DGModule.END

/-! ### Ordinary Lie algebras -/

section LieAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- An ordinary Lie algebra, concentrated in degree `0` with zero differential
(`DG.DGAddCommGroup.degreeZero`), as a dg Lie algebra.-/
@[instance_reducible]
def DGLieAlgebra.ofLieAlgebra :
    letI := DGAddCommGroup.degreeZero L
    DGLieAlgebra R L :=
  letI := DGAddCommGroup.degreeZero L
  { bracketₗ := LinearMap.mk₂ R (fun x y => ⁅x, y⁆) add_lie smul_lie lie_add lie_smul
    smul_mem' := fun r n x hx => by
      change r • x ∈ degreeZeroGrading L n
      change x ∈ degreeZeroGrading L n at hx
      rw [mem_degreeZeroGrading_iff] at hx ⊢
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [h, smul_zero])
    d_smul' := fun r x => (smul_zero r).symm
    bracket_mem' := fun {i j x y} hx hy => by
      change ⁅x, y⁆ ∈ degreeZeroGrading L (i + j)
      change x ∈ degreeZeroGrading L i at hx
      change y ∈ degreeZeroGrading L j at hy
      rw [mem_degreeZeroGrading_iff] at hx hy ⊢
      rcases hx with rfl | rfl
      · rcases hy with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (lie_zero _)
      · exact Or.inr (zero_lie _)
    bracket_comm' := fun {i j x y} hx hy => by
      change x ∈ degreeZeroGrading L i at hx
      change y ∈ degreeZeroGrading L j at hy
      change ⁅x, y⁆ = -(koszulSign (i * j) • ⁅y, x⁆)
      rw [mem_degreeZeroGrading_iff] at hx hy
      rcases hx with rfl | rfl
      · rcases hy with rfl | rfl
        · rw [zero_mul, koszulSign_zero, one_smul, ← lie_skew]
        · simp
      · simp
    jacobi' := fun {i j x y} hx hy z => by
      change x ∈ degreeZeroGrading L i at hx
      change y ∈ degreeZeroGrading L j at hy
      change ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + koszulSign (i * j) • ⁅y, ⁅x, z⁆⁆
      rw [mem_degreeZeroGrading_iff] at hx hy
      rcases hx with rfl | rfl
      · rcases hy with rfl | rfl
        · rw [zero_mul, koszulSign_zero, one_smul, leibniz_lie]
        · simp
      · simp
    d_bracket' := fun _ _ => by
      change (0 : L) = ⁅(0 : L), _⁆ + _ • ⁅_, (0 : L)⁆
      simp }

end LieAlgebra

end DG
