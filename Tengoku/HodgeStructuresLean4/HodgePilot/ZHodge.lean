import Tengoku.HodgeStructuresLean4.HodgePilot.Tier7
import Tengoku.HodgeStructuresLean4.HodgePilot.Internal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#check @ZHodgeStructure` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#check @zTate` (it only prints; the queue checks the axioms of every declaration). -/

/-! ZHodge: the INTEGRAL variant of the Tier 5–7 stack. Conjugation
`σ = conj ⊗ id` on the complexification `ℂ ⊗[ℤ] V` of a finite free ℤ-module
`V`, as a `starRingEnd ℂ`-semilinear involution; the pure INTEGRAL Hodge
structure record `ZHodgeStructure`; and the integral Tate structure `ℤ(m)`.

This mirrors `Tier5.sigmaQ` / `Tier6.QHodgeStructure` / `Tier7.tate` over ℤ,
using the ℤ-linear conjugation trick from `Tier5.sigmaZR`
(`(starRingEnd ℂ).toAddMonoidHom.toIntLinearMap`). -/

open scoped TensorProduct

noncomputable section

namespace HodgePilot

variable (V : Type*) [AddCommGroup V]

/-! ### The semilinear conjugation `σ` on `ℂ ⊗[ℤ] V`

`sigmaZR` itself (with its `tmul` computation rule and involutivity) is
already provided by Tier 5's integral smoke test; here we upgrade it to a
semilinear map, mirroring the ℚ story. -/

/--
@isnad1 id=eq.0h3v.s9.86261234f307 from=translated src=- shape=d5206943 vocab=089b713e
-/
theorem sigmaZR_smul (c : ℂ) (x : ℂ ⊗[ℤ] V) :
    sigmaZR V (c • x) = (starRingEnd ℂ) c • sigmaZR V x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c' v =>
      rw [TensorProduct.smul_tmul', sigmaZR_tmul, sigmaZR_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy =>
      rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- Conjugation on `ℂ ⊗[ℤ] V` as a `starRingEnd ℂ`-semilinear map (integral
analogue of `sigmaQ`).-/
def sigmaZ : (ℂ ⊗[ℤ] V) →ₛₗ[starRingEnd ℂ] (ℂ ⊗[ℤ] V) where
  toFun := sigmaZR V
  map_add' := map_add (sigmaZR V)
  map_smul' := sigmaZR_smul V

/--
@isnad1 id=eq.0h2v.s9.a693ff1023ba from=translated src=- shape=54eccb20 vocab=194cce30
-/
@[simp] theorem sigmaZ_apply (x : ℂ ⊗[ℤ] V) : sigmaZ V x = sigmaZR V x := rfl

/--
@isnad1 id=eq.0h3v.s8.fbffea39bcc6 from=translated src=- shape=ce3af522 vocab=3655ad7a
-/
@[simp] theorem sigmaZ_tmul (c : ℂ) (v : V) :
    sigmaZ V (c ⊗ₜ[ℤ] v) = (starRingEnd ℂ) c ⊗ₜ[ℤ] v := rfl

/-- `σ` is an involution (integral analogue of `sigmaQ_sigmaQ`).
@isnad1 id=eq.0h2v.s9.3a3770dac09a from=translated src=- shape=dd3fd035 vocab=c6266ec2
-/
theorem sigmaZ_sigmaZ (x : ℂ ⊗[ℤ] V) : sigmaZ V (sigmaZ V x) = x := by
  simp [sigmaZR_involutive]

/--
@isnad1 id=surjecti.0h1v.s8.993d1c2c6851 from=translated src=- shape=a2d68275 vocab=c619acd6
-/
theorem sigmaZ_surjective : Function.Surjective (sigmaZ V) :=
  fun x => ⟨sigmaZ V x, sigmaZ_sigmaZ V x⟩

/-- `σ` as a semilinear equivalence of `ℂ ⊗[ℤ] V` with itself.-/
def sigmaZEquiv : (ℂ ⊗[ℤ] V) ≃ₛₗ[starRingEnd ℂ] (ℂ ⊗[ℤ] V) :=
  { sigmaZ V with
    invFun := sigmaZ V
    left_inv := sigmaZ_sigmaZ V
    right_inv := sigmaZ_sigmaZ V }

/-! ### `Submodule.map` simp lemmas for `σ` (mirroring Tier 7) -/

/--
@isnad1 id=eq.0h1v.s8.ec9c96015e09 from=translated src=- shape=159fb2ec vocab=30eae1da
-/
@[simp] theorem range_sigmaZ : LinearMap.range (sigmaZ V) = ⊤ :=
  LinearMap.range_eq_top.mpr (sigmaZ_surjective V)

/--
@isnad1 id=eq.0h1v.s8.636e77932111 from=translated src=- shape=c6905ddf vocab=354fbae5
-/
@[simp] theorem map_top_sigmaZ :
    (⊤ : Submodule ℂ (ℂ ⊗[ℤ] V)).map (sigmaZ V) = ⊤ := by
  rw [Submodule.map_top, range_sigmaZ]

/--
@isnad1 id=eq.0h1v.s8.5ac9ce603e77 from=translated src=- shape=c6905ddf vocab=8b353758
-/
@[simp] theorem map_bot_sigmaZ :
    (⊥ : Submodule ℂ (ℂ ⊗[ℤ] V)).map (sigmaZ V) = ⊥ :=
  Submodule.map_bot _

/-! ### The integral Hodge structure record -/

/-- A pure INTEGRAL Hodge structure of weight `n` on a finite free ℤ-module
`V`: a `(p,q)`-indexed internal direct-sum decomposition of the
complexification `ℂ ⊗[ℤ] V`, supported on `p + q = n`, with
`σ(H^{p,q}) = H^{q,p}` (integral analogue of `QHodgeStructure`).-/
structure ZHodgeStructure (n : ℤ) (V : Type*) [AddCommGroup V]
    [Module.Free ℤ V] [Module.Finite ℤ V] where
  H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℤ] V)
  supported : ∀ pq : ℤ × ℤ, pq.1 + pq.2 ≠ n → H pq = ⊥
  isInternal : DirectSum.IsInternal H
  conj_symm : ∀ p q : ℤ, (H (p, q)).map (sigmaZ V) = H (q, p)

/-! ### The integral Tate structure `ℤ(m)` -/

/-- The integral Tate Hodge structure `ℤ(m)`: pure of weight `-2m`,
one-dimensional, concentrated in bidegree `(-m, -m)` (integral analogue of
`tate`).-/
def zTate (m : ℤ) : ZHodgeStructure (-(2 * m)) ℤ where
  H := fun pq => if pq = (-m, -m) then ⊤ else ⊥
  supported := by
    intro pq hpq
    have hne : pq ≠ (-m, -m) := by
      rintro rfl
      exact hpq (by omega)
    simp [hne]
  isInternal := isInternal_of_eq_bot (fun i hi => ite_eq_right hi) (ite_eq_left rfl)
  conj_symm := by
    intro p q
    by_cases h : (p, q) = ((-m : ℤ), (-m : ℤ))
    · have hp : p = -m := (Prod.mk.injEq .. ▸ h).1
      have hq : q = -m := (Prod.mk.injEq .. ▸ h).2
      subst hp; subst hq
      simp
    · have h' : (q, p) ≠ ((-m : ℤ), (-m : ℤ)) := by
        intro hqp
        exact h (by
          have hq : q = -m := (Prod.mk.injEq .. ▸ hqp).1
          have hp : p = -m := (Prod.mk.injEq .. ▸ hqp).2
          subst hp; subst hq; rfl)
      simp [h, h']

end HodgePilot
