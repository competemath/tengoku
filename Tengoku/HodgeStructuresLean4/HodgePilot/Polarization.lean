import Tengoku.HodgeStructuresLean4.HodgePilot.Tier8

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Polarizations of pure rational Hodge structures

A **polarization** of a pure rational Hodge structure of weight `n` on `V` is a
rational bilinear form `B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ` that is `(-1)^n`-symmetric,
whose complexification `B_ℂ` (the base change `B.baseChange ℂ`) satisfies the
Hodge–Riemann bilinear relations: it is *orthogonal* to all pieces
`H^{p',q'}` with `(p',q') ≠ (q,p)`, and the associated Hermitian form
`i^{p-q} · B_ℂ(x, σ x)` is real and positive-definite on each `H^{p,q}`.

The `i^{p-q}` coefficient is packaged as `Iexp (p - q)`, a total function of an
integer exponent built from the 4-periodicity of `Complex.I` (§3 of the design
memo): `Iexp` never introduces a `zpow` of `Complex.I` (for which Mathlib has no
periodicity lemmas), only `ℕ`-powers, which reduce by `I_sq` / `pow_succ`.

Two worked examples are discharged sorry-free:
* `tatePolarization`  — the Tate structure `ℚ(m)`, form `B(x,y) = x*y`;
* `weightOnePolarization` — the weight-one elliptic-curve structure on `ℚ²`,
  the standard symplectic form `[[0,1],[-1,0]]`. -/

open scoped TensorProduct

noncomputable section

namespace HodgePilot

/-! ### The integer-exponent power `i^k` via 4-periodicity -/

/-- `i^k` for an integer exponent `k`, defined through the 4-periodicity of
`Complex.I`. `Int.emod` is nonnegative for a positive modulus, so `.toNat` is
faithful; this is total in `k` and agrees with `Complex.I ^ k` for every integer
(since `I` has order 4), reducing to `ℕ`-powers of `I` in computations
(`Iexp 0 = 1`, `Iexp 1 = i`, `Iexp 2 = -1`, `Iexp (-1) = -i`, `Iexp (-2) = -1`).-/
def Iexp (k : ℤ) : ℂ := Complex.I ^ (k.emod 4).toNat

/--
@isnad1 id=eq.0h0v.s3.7a03201cf86a from=translated src=- shape=1ac31801 vocab=b9534249
-/
@[simp] theorem Iexp_zero : Iexp 0 = 1 := by
  rw [Iexp, show ((0 : ℤ).emod 4).toNat = 0 from by decide, pow_zero]

/--
@isnad1 id=eq.0h0v.s3.9e8ece3c27d6 from=translated src=- shape=d3a93718 vocab=9c5fddf2
-/
@[simp] theorem Iexp_one : Iexp 1 = Complex.I := by
  rw [Iexp, show ((1 : ℤ).emod 4).toNat = 1 from by decide, pow_one]

/--
@isnad1 id=eq.0h0v.s4.872eafa0e944 from=translated src=- shape=b5968027 vocab=892ab1dc
-/
@[simp] theorem Iexp_two : Iexp 2 = -1 := by
  rw [Iexp, show ((2 : ℤ).emod 4).toNat = 2 from by decide, Complex.I_sq]

/--
@isnad1 id=eq.0h0v.s3.79171af922d3 from=translated src=- shape=4256389d vocab=1c31397c
-/
@[simp] theorem Iexp_neg_one : Iexp (-1) = -Complex.I := by
  rw [Iexp, show ((-1 : ℤ).emod 4).toNat = 3 from by decide,
    show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Complex.I_sq, neg_one_mul]

/--
@isnad1 id=eq.0h0v.s4.d7e5a7a0dd8d from=translated src=- shape=5b7a101b vocab=892ab1dc
-/
@[simp] theorem Iexp_neg_two : Iexp (-2) = -1 := by
  rw [Iexp, show ((-2 : ℤ).emod 4).toNat = 2 from by decide, Complex.I_sq]

/-- Validation: `Iexp` agrees with the integer power `Complex.I ^ k` for every
`k : ℤ` — the `emod 4` definition is not a convention but the standard value,
by the 4-periodicity of `i`. Computations never need this lemma (that is the
point of `Iexp`); it pins the definition to the textbook meaning once.
@isnad1 id=eq.0h1v.s4.5725525aa724 from=translated src=- shape=b217b3a9 vocab=a363a8fb
-/
theorem Iexp_eq_zpow (k : ℤ) : Iexp k = Complex.I ^ k := by
  have h4 : (Complex.I : ℂ) ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, Complex.I_pow_four]
  have hnn : 0 ≤ k % 4 := Int.emod_nonneg k (by norm_num)
  calc Iexp k = Complex.I ^ ((k % 4).toNat : ℤ) := (zpow_natCast _ _).symm
    _ = Complex.I ^ (k % 4) := by rw [Int.toNat_of_nonneg hnn]
    _ = Complex.I ^ (4 * (k / 4)) * Complex.I ^ (k % 4) := by
        rw [zpow_mul, h4, one_zpow, one_mul]
    _ = Complex.I ^ (4 * (k / 4) + k % 4) := (zpow_add₀ Complex.I_ne_zero _ _).symm
    _ = Complex.I ^ k := by rw [Int.mul_ediv_add_emod]

/-! ### The complexified bilinear form -/

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- The complexification `B_ℂ : (ℂ ⊗ V) →ₗ[ℂ] (ℂ ⊗ V) →ₗ[ℂ] ℂ` of a rational
bilinear form `B`, via the Mathlib base change.-/
abbrev baseChangeℂ (B : LinearMap.BilinForm ℚ V) :
    LinearMap.BilinForm ℂ (ℂ ⊗[ℚ] V) := B.baseChange ℂ

omit [Module.Finite ℚ V] in
/-- Base change on the tensor basis is the rational entry, cast to `ℂ`.
Mirrors Tier 8's `sigmaQR_bc`: `B.baseChange ℂ (1 ⊗ₜ bᵢ) (1 ⊗ₜ bⱼ)
= (B bᵢ bⱼ) • ((1 : ℂ) * 1) = ((B bᵢ bⱼ : ℚ) : ℂ)`.
@isnad1 id=eq.0h6v.s11.23cbf547a1b8 from=translated src=- shape=62ea63c1 vocab=06fcbe40
-/
theorem baseChange_bc {ι : Type*} (B : LinearMap.BilinForm ℚ V)
    (b : Module.Basis ι ℚ V) (i j : ι) :
    baseChangeℂ B (Algebra.TensorProduct.basis ℂ b i)
        (Algebra.TensorProduct.basis ℂ b j) = ((B (b i) (b j) : ℚ) : ℂ) := by
  simp only [baseChangeℂ, Algebra.TensorProduct.basis_apply,
    LinearMap.BilinForm.baseChange_tmul, mul_one, Rat.smul_one_eq_cast]

/-! ### The polarization structure -/

/-- A polarization of a pure rational Hodge structure `h` of weight `n` on `V`:
a `(-1)^n`-symmetric rational bilinear form whose complexification satisfies the
Hodge–Riemann bilinear relations (orthogonality + positivity of the associated
Hermitian form `i^{p-q} B_ℂ(x, σ x)`).-/
structure Polarization {n : ℤ} (h : QHodgeStructure n V) where
  /-- The underlying rational bilinear form.-/
  form : LinearMap.BilinForm ℚ V
  /-- `(-1)^n`-symmetry, stated on `ℚ` directly.-/
  symm : ∀ x y, form x y = (-1) ^ n * form y x
  /-- Hodge–Riemann orthogonality: `B_ℂ` pairs `H^{p,q}` trivially with every
  piece other than `H^{q,p}`.-/
  orthogonal : ∀ p q p' q' : ℤ, (p', q') ≠ (q, p) →
    ∀ x ∈ h.H (p, q), ∀ y ∈ h.H (p', q'),
      baseChangeℂ form x y = 0
  /-- The Hermitian value `i^{p-q} B_ℂ(x, σ x)` is real on each piece.-/
  hermitian_real : ∀ (p q : ℤ), p + q = n → ∀ x ∈ h.H (p, q),
    (Iexp (p - q) * baseChangeℂ form x (sigmaQ V x)).im = 0
  /-- Positivity: `Re (i^{p-q} B_ℂ(x, σ x)) > 0` for `0 ≠ x ∈ H^{p,q}`.-/
  positive : ∀ (p q : ℤ), p + q = n → ∀ x ∈ h.H (p, q), x ≠ 0 →
    0 < (Iexp (p - q) * baseChangeℂ form x (sigmaQ V x)).re

/-! ### Example 1: the Tate structure `ℚ(m)`, form `B(x, y) = x * y` -/

/-- Every element of `ℂ ⊗[ℚ] ℚ` is `c ⊗ₜ 1` for a unique `c : ℂ`, exhibited by
`TensorProduct.rid`.
@isnad1 id=ex.0h1v.s7.16df41a84648 from=translated src=- shape=aa9b1274 vocab=c369667e
-/
theorem exists_rid_tmul (x : ℂ ⊗[ℚ] ℚ) : ∃ c : ℂ, x = c ⊗ₜ[ℚ] (1 : ℚ) :=
  ⟨TensorProduct.rid ℚ ℂ x, by
    rw [← TensorProduct.rid_symm_apply, LinearEquiv.symm_apply_apply]⟩

/-- Membership in a Tate piece off the sole bidegree `(-m,-m)` forces the
vector to vanish.
@isnad1 id=eq.2h4v.s9.2ad187d903f5 from=translated src=- shape=ded776f4 vocab=113b4740
-/
theorem tate_mem_eq_zero {m p q : ℤ} (hpq : (p, q) ≠ (-m, -m))
    {x : ℂ ⊗[ℚ] ℚ} (hx : x ∈ (tate m).H (p, q)) : x = 0 := by
  have : x ∈ (⊥ : Submodule ℂ (ℂ ⊗[ℚ] ℚ)) := by
    simpa [tate, hpq] using hx
  simpa using this

/-- The Tate Hermitian value on `x = c ⊗ₜ 1` in the sole piece: with `p = q`,
`Iexp (p - q) = 1` and `B_ℂ(x, σ x) = c · conj c = normSq c`.
@isnad1 id=eq.0h2v.s11.bc5825cd85c7 from=translated src=- shape=232b99a5 vocab=e61b8278
-/
theorem tate_hermitian_value (m : ℤ) (c : ℂ) :
    Iexp (-m - -m) *
        baseChangeℂ (LinearMap.mul ℚ ℚ) (c ⊗ₜ[ℚ] (1 : ℚ))
          (sigmaQ ℚ (c ⊗ₜ[ℚ] (1 : ℚ)))
      = (Complex.normSq c : ℂ) := by
  rw [sub_self, Iexp_zero, one_mul, sigmaQ_apply, sigmaQR_tmul]
  simp only [baseChangeℂ, LinearMap.BilinForm.baseChange_tmul, LinearMap.mul_apply',
    mul_one, one_smul]
  rw [Complex.mul_conj]

/-- The polarization of the Tate structure `ℚ(m)`: the form `B(x, y) = x * y`
on `ℚ`. Weight `-2m` is even, so `B` is symmetric; the single piece sits in
bidegree `(-m,-m)` where `i^{p-q} = i^0 = 1`, and
`B_ℂ(c ⊗ₜ 1, σ(c ⊗ₜ 1)) = c · conj c = normSq c`, positive for `c ≠ 0`.-/
def tatePolarization (m : ℤ) : Polarization (tate m) where
  form := LinearMap.mul ℚ ℚ
  symm := by
    intro x y
    have heven : Even (-(2 * m)) := ⟨-m, by ring⟩
    rw [heven.neg_one_zpow, one_mul, LinearMap.mul_apply', LinearMap.mul_apply',
      mul_comm]
  orthogonal := by
    intro p q p' q' hne x hx y hy
    -- If either piece is off bidegree `(-m,-m)` it is `⊥`, so the vector is `0`.
    by_cases hpq : (p, q) = (-m, -m)
    · by_cases hpq' : (p', q') = (-m, -m)
      · -- Both in bidegree `(-m,-m)`; but then `(p',q') = (-m,-m) = (q,p)`,
        -- contradicting `hne`.
        obtain ⟨hp, hq⟩ : p = -m ∧ q = -m := by rw [Prod.mk.injEq] at hpq; exact hpq
        exact absurd (by rw [hpq', hp, hq]) hne
      · rw [tate_mem_eq_zero hpq' hy, map_zero]
    · rw [tate_mem_eq_zero hpq hx, map_zero, LinearMap.zero_apply]
  hermitian_real := by
    intro p q hpq x hx
    by_cases hb : (p, q) = (-m, -m)
    · obtain ⟨hp, hq⟩ : p = -m ∧ q = -m := by
        rw [Prod.mk.injEq] at hb; exact hb
      subst hp; subst hq
      obtain ⟨c, rfl⟩ := exists_rid_tmul x
      rw [tate_hermitian_value, Complex.ofReal_im]
    · rw [tate_mem_eq_zero hb hx, map_zero, LinearMap.zero_apply, mul_zero,
        Complex.zero_im]
  positive := by
    intro p q hpq x hx hxne
    have hb : (p, q) = (-m, -m) := by
      by_contra hb
      exact hxne (tate_mem_eq_zero hb hx)
    obtain ⟨hp, hq⟩ : p = -m ∧ q = -m := by
      rw [Prod.mk.injEq] at hb; exact hb
    subst hp; subst hq
    obtain ⟨c, rfl⟩ := exists_rid_tmul x
    rw [tate_hermitian_value, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr fun hc => hxne (by rw [hc]; simp)

/-! ### Example 2: the weight-one elliptic-curve structure on `V = ℚ²` -/

/-- The `H^{1,0}` piece of `weightOne` is `ℂ ∙ w₁`.
@isnad1 id=eq.0h0v.s9.ace55b45031c from=translated src=- shape=4f844da7 vocab=7295f44c
-/
theorem weightOne_H_10 : weightOne.H (1, 0) = ℂ ∙ w1 := by simp [weightOne]

/-- The `H^{0,1}` piece of `weightOne` is `ℂ ∙ w₂`.
@isnad1 id=eq.0h0v.s9.e8ba97ee8ca3 from=translated src=- shape=4f844da7 vocab=829e92d1
-/
theorem weightOne_H_01 : weightOne.H (0, 1) = ℂ ∙ w2 := by simp [weightOne]

/-- Off the two bidegrees `(1,0)` and `(0,1)`, the piece of `weightOne` is `⊥`.
@isnad1 id=eq.2h2v.s9.20ab8e8372c6 from=translated src=- shape=69da1d12 vocab=32adff68
-/
theorem weightOne_H_bot {p q : ℤ} (h10 : (p, q) ≠ (1, 0)) (h01 : (p, q) ≠ (0, 1)) :
    weightOne.H (p, q) = ⊥ := by simp [weightOne, h10, h01]

/-- The standard symplectic form `[[0,1],[-1,0]]` on `V2 = Fin 2 → ℚ`:
`B(x, y) = x₀ y₁ - x₁ y₀`.-/
def symplectic2 : LinearMap.BilinForm ℚ V2 :=
  LinearMap.mk₂ ℚ (fun x y => x 0 * y 1 - x 1 * y 0)
    (fun x₁ x₂ y => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y₁ y₂ => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

/--
@isnad1 id=eq.0h2v.s9.b3d6c1ec0823 from=translated src=- shape=7e458b15 vocab=95833053
-/
@[simp] theorem symplectic2_apply (x y : V2) :
    symplectic2 x y = x 0 * y 1 - x 1 * y 0 := rfl

/-- The four values of `B_ℂ = baseChangeℂ symplectic2` on the base-changed
basis `bc` of Tier 8, as explicit `@[simp]` lemmas (no `if`-branching).-/
private theorem bc_eq :
    bc = Algebra.TensorProduct.basis ℂ (Pi.basisFun ℚ (Fin 2)) := rfl

/--
@isnad1 id=eq.0h0v.s11.26d550eac196 from=translated src=- shape=a0d32c3a vocab=6c728f7c
-/
@[simp] theorem baseChange_bc_00 : baseChangeℂ symplectic2 (bc 0) (bc 0) = 0 := by
  rw [bc_eq, baseChange_bc symplectic2 (Pi.basisFun ℚ (Fin 2)) 0 0]
  norm_num [symplectic2_apply, Pi.basisFun_apply, Pi.single_apply]

/--
@isnad1 id=eq.0h0v.s11.1c64d1210afa from=translated src=- shape=a0d32c3a vocab=6c728f7c
-/
@[simp] theorem baseChange_bc_01 : baseChangeℂ symplectic2 (bc 0) (bc 1) = 1 := by
  rw [bc_eq, baseChange_bc symplectic2 (Pi.basisFun ℚ (Fin 2)) 0 1]
  norm_num [symplectic2_apply, Pi.basisFun_apply, Pi.single_apply]

/--
@isnad1 id=eq.0h0v.s11.eeb2843d39e8 from=translated src=- shape=ea4367b8 vocab=bb52eb4a
-/
@[simp] theorem baseChange_bc_10 : baseChangeℂ symplectic2 (bc 1) (bc 0) = -1 := by
  rw [bc_eq, baseChange_bc symplectic2 (Pi.basisFun ℚ (Fin 2)) 1 0]
  norm_num [symplectic2_apply, Pi.basisFun_apply, Pi.single_apply]

/--
@isnad1 id=eq.0h0v.s11.f4e123a42e65 from=translated src=- shape=a0d32c3a vocab=6c728f7c
-/
@[simp] theorem baseChange_bc_11 : baseChangeℂ symplectic2 (bc 1) (bc 1) = 0 := by
  rw [bc_eq, baseChange_bc symplectic2 (Pi.basisFun ℚ (Fin 2)) 1 1]
  norm_num [symplectic2_apply, Pi.basisFun_apply, Pi.single_apply]

/-- `B_ℂ(w₁, w₂) = -2i`. The sign-critical value of §4.2.
@isnad1 id=eq.0h0v.s11.3257bb6f68b5 from=translated src=- shape=668e539f vocab=2fa0ac9e
-/
theorem baseChange_w1_w2 : baseChangeℂ symplectic2 w1 w2 = -2 * Complex.I := by
  simp only [w1, w2, map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, baseChange_bc_00,
    baseChange_bc_01, baseChange_bc_10, baseChange_bc_11]
  ring

/-- `B_ℂ(w₁, w₁) = 0`: the Hodge–Riemann orthogonality of `H^{1,0}` with itself.
@isnad1 id=eq.0h0v.s11.78e74e9fa095 from=translated src=- shape=5dc0371b vocab=9af8b73a
-/
theorem baseChange_w1_w1 : baseChangeℂ symplectic2 w1 w1 = 0 := by
  simp only [w1, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, baseChange_bc_00, baseChange_bc_01, baseChange_bc_10,
    baseChange_bc_11]
  ring

/-- `B_ℂ(w₂, w₂) = 0`: the Hodge–Riemann orthogonality of `H^{0,1}` with itself.
@isnad1 id=eq.0h0v.s11.080a41e0c4ba from=translated src=- shape=5dc0371b vocab=3598e157
-/
theorem baseChange_w2_w2 : baseChangeℂ symplectic2 w2 w2 = 0 := by
  simp only [w2, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, baseChange_bc_00, baseChange_bc_01, baseChange_bc_10,
    baseChange_bc_11]
  ring

/-- `B_ℂ(w₂, w₁) = +2i` (antisymmetry of the symplectic form).
@isnad1 id=eq.0h0v.s11.2e37555cf62a from=translated src=- shape=8fed1205 vocab=a97c9ae6
-/
theorem baseChange_w2_w1 : baseChangeℂ symplectic2 w2 w1 = 2 * Complex.I := by
  simp only [w1, w2, map_add, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, baseChange_bc_00,
    baseChange_bc_01, baseChange_bc_10, baseChange_bc_11]
  ring

/-- Bilinearity: a complex bilinear form pulls scalars out of both slots.
@isnad1 id=eq.0h5v.s12.ee432efd2051 from=translated src=- shape=35541df7 vocab=c13dd4f5
-/
theorem baseChange_smul_smul (B : LinearMap.BilinForm ℚ V2) (a b : ℂ)
    (u v : ℂ ⊗[ℚ] V2) :
    baseChangeℂ B (a • u) (b • v) = a * b * baseChangeℂ B u v := by
  rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_smul, smul_eq_mul]

/-- On `H^{1,0} = ℂ ∙ w₁`, the Hermitian value is `2 · normSq a` for `x = a•w₁`.
`i^{p-q} = i^1 = i` and `B_ℂ(w₁, σ w₁) = a·conj a·(-2i) = normSq a·(-2i)`, so
`i · normSq a · (-2i) = -2 i² normSq a = 2 normSq a`.
@isnad1 id=eq.0h1v.s12.f86b70deab24 from=translated src=- shape=35e0d204 vocab=2bca5a16
-/
theorem hermitian_w1 (a : ℂ) :
    Iexp (1 - 0) *
        baseChangeℂ symplectic2 (a • w1) (sigmaQ V2 (a • w1))
      = ((2 * Complex.normSq a : ℝ) : ℂ) := by
  rw [map_smulₛₗ (sigmaQ V2), sigmaQ_w1, baseChange_smul_smul, baseChange_w1_w2,
    Complex.mul_conj, sub_zero, Iexp_one]
  rw [show Complex.I * ((Complex.normSq a : ℂ) * (-2 * Complex.I))
      = (-2) * (Complex.normSq a : ℂ) * (Complex.I * Complex.I) from by ring,
    Complex.I_mul_I]
  push_cast; ring

/-- On `H^{0,1} = ℂ ∙ w₂`, the Hermitian value is `2 · normSq a` for `x = a•w₂`.
`i^{p-q} = i^{-1} = -i` and `B_ℂ(w₂, σ w₂) = normSq a·(2i)`, so
`(-i) · normSq a · (2i) = -2 i² normSq a = 2 normSq a`.
@isnad1 id=eq.0h1v.s12.a55e14cc935c from=translated src=- shape=35e0d204 vocab=15867f24
-/
theorem hermitian_w2 (a : ℂ) :
    Iexp (0 - 1) *
        baseChangeℂ symplectic2 (a • w2) (sigmaQ V2 (a • w2))
      = ((2 * Complex.normSq a : ℝ) : ℂ) := by
  rw [map_smulₛₗ (sigmaQ V2), sigmaQ_w2, baseChange_smul_smul, baseChange_w2_w1,
    Complex.mul_conj, show (0 : ℤ) - 1 = -1 from by ring, Iexp_neg_one]
  rw [show (-Complex.I) * ((Complex.normSq a : ℂ) * (2 * Complex.I))
      = (-2) * (Complex.normSq a : ℂ) * (Complex.I * Complex.I) from by ring,
    Complex.I_mul_I]
  push_cast; ring

/-- The polarization of the weight-one elliptic-curve Hodge structure: the
standard symplectic form `[[0,1],[-1,0]]`.-/
def weightOnePolarization : Polarization weightOne where
  form := symplectic2
  symm := by
    intro x y
    have hodd : Odd (1 : ℤ) := ⟨0, by ring⟩
    rw [hodd.neg_one_zpow, symplectic2_apply, symplectic2_apply]
    ring
  orthogonal := by
    intro p q p' q' hne x hx y hy
    -- Reduce both membership facts through the three cases of `weightOne.H`.
    by_cases h10 : (p, q) = ((1 : ℤ), (0 : ℤ))
    · -- `x ∈ ℂ ∙ w₁`, so `(q,p) = (0,1)`; the only non-`⊥` `y`-piece other than
      -- the excluded `(0,1)` is `(1,0)`, giving `B_ℂ(w₁,w₁) = 0`.
      obtain ⟨hp, hq⟩ : p = 1 ∧ q = 0 := by rw [Prod.mk.injEq] at h10; exact h10
      subst hp; subst hq
      rw [weightOne_H_10] at hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      by_cases h10' : (p', q') = ((1 : ℤ), (0 : ℤ))
      · obtain ⟨hp', hq'⟩ : p' = 1 ∧ q' = 0 := by
          rw [Prod.mk.injEq] at h10'; exact h10'
        subst hp'; subst hq'
        rw [weightOne_H_10] at hy
        obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [baseChange_smul_smul, baseChange_w1_w1, mul_zero]
      · by_cases h01' : (p', q') = ((0 : ℤ), (1 : ℤ))
        · exact absurd h01' hne
        · have hy0 : y = 0 := by
            rw [weightOne_H_bot h10' h01'] at hy; simpa using hy
          rw [hy0, map_zero]
    · by_cases h01 : (p, q) = ((0 : ℤ), (1 : ℤ))
      · obtain ⟨hp, hq⟩ : p = 0 ∧ q = 1 := by rw [Prod.mk.injEq] at h01; exact h01
        subst hp; subst hq
        rw [weightOne_H_01] at hx
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        by_cases h01' : (p', q') = ((0 : ℤ), (1 : ℤ))
        · obtain ⟨hp', hq'⟩ : p' = 0 ∧ q' = 1 := by
            rw [Prod.mk.injEq] at h01'; exact h01'
          subst hp'; subst hq'
          rw [weightOne_H_01] at hy
          obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
          rw [baseChange_smul_smul, baseChange_w2_w2, mul_zero]
        · by_cases h10' : (p', q') = ((1 : ℤ), (0 : ℤ))
          · exact absurd h10' hne
          · have hy0 : y = 0 := by
              rw [weightOne_H_bot h10' h01'] at hy; simpa using hy
            rw [hy0, map_zero]
      · have hx0 : x = 0 := by
          rw [weightOne_H_bot h10 h01] at hx; simpa using hx
        rw [hx0, map_zero, LinearMap.zero_apply]
  hermitian_real := by
    intro p q hpq x hx
    by_cases h10 : (p, q) = ((1 : ℤ), (0 : ℤ))
    · obtain ⟨hp, hq⟩ : p = 1 ∧ q = 0 := by rw [Prod.mk.injEq] at h10; exact h10
      subst hp; subst hq
      rw [weightOne_H_10] at hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [hermitian_w1, Complex.ofReal_im]
    · by_cases h01 : (p, q) = ((0 : ℤ), (1 : ℤ))
      · obtain ⟨hp, hq⟩ : p = 0 ∧ q = 1 := by rw [Prod.mk.injEq] at h01; exact h01
        subst hp; subst hq
        rw [weightOne_H_01] at hx
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [hermitian_w2, Complex.ofReal_im]
      · have hx0 : x = 0 := by
          rw [weightOne_H_bot h10 h01] at hx; simpa using hx
        rw [hx0, map_zero, LinearMap.zero_apply, mul_zero, Complex.zero_im]
  positive := by
    intro p q hpq x hx hxne
    by_cases h10 : (p, q) = ((1 : ℤ), (0 : ℤ))
    · obtain ⟨hp, hq⟩ : p = 1 ∧ q = 0 := by rw [Prod.mk.injEq] at h10; exact h10
      subst hp; subst hq
      rw [weightOne_H_10] at hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [hermitian_w1, Complex.ofReal_re]
      have ha : a ≠ 0 := by
        intro h; exact hxne (by rw [h, zero_smul])
      have := Complex.normSq_pos.mpr ha
      linarith
    · by_cases h01 : (p, q) = ((0 : ℤ), (1 : ℤ))
      · obtain ⟨hp, hq⟩ : p = 0 ∧ q = 1 := by rw [Prod.mk.injEq] at h01; exact h01
        subst hp; subst hq
        rw [weightOne_H_01] at hx
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [hermitian_w2, Complex.ofReal_re]
        have ha : a ≠ 0 := by
          intro h; exact hxne (by rw [h, zero_smul])
        have := Complex.normSq_pos.mpr ha
        linarith
      · exfalso
        apply hxne
        rw [weightOne_H_bot h10 h01] at hx
        simpa using hx

end HodgePilot
