/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.AdicEval
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.PointGroup
import Tengoku.Seed.RingTheory.MvPowerSeries.PiTopology
import Tengoku.Seed.RingTheory.MvPowerSeries.LinearTopology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The abelian group `Ê(𝔪)` of a formal group over a complete local ring

Let `A` be a commutative ring that is `I`-adically complete (`IsAdicComplete I A`; the case of a
complete DVR with maximal ideal `𝔪` is `I = 𝔪`) and let `F : FormalGroup A` be a one
dimensional formal group law over `A`.  Following Silverman (AEC IV.3, VII.2.2), the ideal `I`
carries a new abelian group structure `Ê(𝔪)` in which the addition is the `I`-adic substitution
of the formal group law, `x ⊕ y = F(x, y)`, the identity is `0`, and the negation is the `I`-adic
substitution of the formal inverse `i(X)`.

The operation lands inside `I` because `F` (and `i`) have vanishing constant coefficient
(`PowerSeries.adicEvalMv_mem` / `adicEval_mem`), and the group axioms are transported from the
identities of the formal group law (`assoc'`, `comm'`, `Xzero_eq_X`, `zeroX_eq_X`,
`subst_formalInv`) through the *transport lemma* `PowerSeries.adicEvalMv_subst`:
substituting into a power series and then evaluating `I`-adically is the same as evaluating the
substituents first and then substituting.  The transport is proved by continuity and uniqueness of
`A`-algebra homomorphisms (`MvPowerSeries.comp_aeval`), *not* through
`MvPowerSeries.substAlgHom_eq_aeval`, which would require the coefficient ring to carry the discrete
topology — impossible here, since the coefficient ring and the evaluation target are the same type
`A`, which must carry the `I`-adic topology.

## Main definitions / results

* `FormalGroup.OnIdeal F I` — the carrier `↥I` with the formal-group addition.
* `PowerSeries.adicEvalMv_subst` — the transport lemma `ev (F.subst g) = ev' F`.
* `instance : AddGroup (F.OnIdeal I)` and `instance [F.IsComm] : AddCommGroup (F.OnIdeal I)`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.3, VII.2.
-/

open scoped Topology
open MvPowerSeries MvPowerSeries.WithPiTopology

noncomputable section

namespace PowerSeries

variable {A : Type*} [CommRing A]

/-- The multivariate `I`-adic evaluation depends only on the underlying family (the membership
proof is irrelevant), so two evaluations at equal families agree. -/
theorem adicEvalMv_congr (I : Ideal A) [IsAdicComplete I A] {σ : Type*} [Finite σ]
    {a b : σ → A} (hab : a = b) (ha : ∀ s, a s ∈ I) (hb : ∀ s, b s ∈ I)
    (f : MvPowerSeries σ A) : adicEvalMv I ha f = adicEvalMv I hb f := by
  subst hab; rfl

/-- Univariate `I`-adic evaluation is the multivariate one over `Unit`.  Both are the underlying
`MvPowerSeries.eval₂` at the identity coefficient map and the constant family `fun _ ↦ x`. -/
theorem adicEval_eq_adicEvalMv (I : Ideal A) [IsAdicComplete I A] {x : A} (hx : x ∈ I)
    (f : PowerSeries A) :
    adicEval I hx f = adicEvalMv I (a := fun _ : Unit => x) (fun _ => hx) f := by
  letI : WithIdeal A := ⟨I⟩
  have h1 := congrFun (coe_adicEval hx) f
  have h2 := congrFun (coe_adicEvalMv I (a := fun _ : Unit => x) (fun _ => hx)) f
  rw [h1, h2, PowerSeries.eval₂]

/-- The transport lemma for the `I`-adic evaluation.  If `g : σ → MvPowerSeries τ A` is a
substitution family whose entries have vanishing constant coefficient, then substituting `g` into
`F` and evaluating `I`-adically at `a` equals evaluating `F` `I`-adically at the family of the
evaluated substituents `s ↦ (g s)(a)`.

Concretely `(F ∘ g)(a) = F(s ↦ (g s)(a))`.  The proof composes the *adic* evaluation algebra
homomorphism `ev = aeval` with the *adic* substitution algebra homomorphism `aeval hg.hasEval`
(evaluation into the power-series ring under `WithPiTopology`), using `MvPowerSeries.comp_aeval`,
after reconciling that adic substitution with Mathlib's `MvPowerSeries.subst`. -/
theorem adicEvalMv_subst (I : Ideal A) [IsAdicComplete I A] {τ : Type*} [Finite τ]
    {σ : Type*} [Finite σ] {a : τ → A} (ha : ∀ s, a s ∈ I)
    {g : σ → MvPowerSeries τ A} (hg : MvPowerSeries.HasSubst g)
    (hgc : ∀ s, (g s).constantCoeff = 0) (F : MvPowerSeries σ A) :
    adicEvalMv I ha (MvPowerSeries.subst g F) =
      adicEvalMv I (a := fun s => adicEvalMv I ha (g s))
        (fun s => adicEvalMv_mem I ha (hgc s)) F := by
  classical
  letI : WithIdeal A := ⟨I⟩
  haveI : CompleteSpace A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).1
  haveI : T2Space A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).2
  have hev : MvPowerSeries.HasEval a :=
    ⟨fun s => WithIdeal.isTopologicallyNilpotent_of_mem (ha s), by
      rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  set ev : MvPowerSeries τ A →ₐ[A] A := MvPowerSeries.aeval hev with hev_def
  have hevc : Continuous ev := MvPowerSeries.continuous_aeval hev
  have hev_eq : ⇑ev = ⇑(adicEvalMv I ha) := by
    rw [hev_def, MvPowerSeries.coe_aeval, coe_adicEvalMv I ha, Algebra.algebraMap_self]
  -- Reconciliation: Mathlib's `subst g F` is the adic `aeval hg.hasEval F`.
  have hrecon : MvPowerSeries.subst g F = MvPowerSeries.aeval hg.hasEval F := by
    ext e
    have hfin := MvPowerSeries.coeff_subst_finite hg F e
    have hs : HasSum
        (fun d => MvPowerSeries.coeff d F •
          MvPowerSeries.coeff (R := A) e (d.prod fun s ex => (g s) ^ ex))
        (MvPowerSeries.coeff (R := A) e (MvPowerSeries.aeval hg.hasEval F)) := by
      have h0 := (MvPowerSeries.hasSum_aeval hg.hasEval F).map
        (MvPowerSeries.coeff (R := A) e) (continuous_coeff (R := A) e)
      simpa only [Function.comp_def, map_smul] using h0
    rw [MvPowerSeries.coeff_subst hg F e, ← hs.tsum_eq, tsum_eq_finsum hfin]
  -- Transport via `comp_aeval`.
  have hcomp : ev.comp (MvPowerSeries.aeval hg.hasEval)
      = MvPowerSeries.aeval (hg.hasEval.map hevc) :=
    MvPowerSeries.comp_aeval hg.hasEval hevc
  have key : ev (MvPowerSeries.subst g F)
      = MvPowerSeries.aeval (hg.hasEval.map hevc) F := by
    rw [hrecon, ← AlgHom.comp_apply, hcomp]
  have hfun : ⇑(MvPowerSeries.aeval (hg.hasEval.map hevc)) =
      ⇑(adicEvalMv I (a := fun s => adicEvalMv I ha (g s))
        (fun s => adicEvalMv_mem I ha (hgc s))) := by
    rw [MvPowerSeries.coe_aeval, coe_adicEvalMv, Algebra.algebraMap_self]
    exact congrArg (MvPowerSeries.eval₂ (RingHom.id A)) (funext fun s => congrFun hev_eq (g s))
  calc adicEvalMv I ha (MvPowerSeries.subst g F)
      = ev (MvPowerSeries.subst g F) := by rw [hev_eq]
    _ = MvPowerSeries.aeval (hg.hasEval.map hevc) F := key
    _ = adicEvalMv I (a := fun s => adicEvalMv I ha (g s))
          (fun s => adicEvalMv_mem I ha (hgc s)) F := congrFun hfun F

end PowerSeries

namespace FormalGroup

variable {A : Type*} [CommRing A]

open PowerSeries

/-- The abelian group `Ê(𝔪)` of a formal group law `F` over an `I`-adically complete ring `A`:
its carrier is (a copy of) the ideal `I`, with addition the `I`-adic substitution
`x ⊕ y = F(x, y)`, identity `0`, and negation the substitution of the formal inverse `i(X)`. -/
@[ext]
structure OnIdeal (F : FormalGroup A) (I : Ideal A) [IsAdicComplete I A] : Type _ where
  /-- The underlying element of `A`. -/
  val : A
  /-- Membership in the ideal `I`. -/
  property : val ∈ I

namespace OnIdeal

variable (F : FormalGroup A) (I : Ideal A) [IsAdicComplete I A]

omit [IsAdicComplete I A] in
/-- The two-element evaluation family `![x, y]` stays inside `I`. -/
theorem memFin2 {x y : A} (hx : x ∈ I) (hy : y ∈ I) : ∀ s : Fin 2, ![x, y] s ∈ I := by
  intro s
  fin_cases s
  · exact hx
  · exact hy

instance : Zero (OnIdeal F I) := ⟨⟨0, I.zero_mem⟩⟩

instance : Add (OnIdeal F I) where
  add x y := ⟨adicEvalMv I (memFin2 I x.property y.property) F.toPowerSeries,
    adicEvalMv_mem I _ F.zero_constantCoeff⟩

instance : Neg (OnIdeal F I) where
  neg x := ⟨adicEval I x.property (formalInv F),
    adicEval_mem x.property (constantCoeff_formalInv F)⟩

variable {F I}

@[simp] theorem zero_val : (0 : OnIdeal F I).val = 0 := rfl

@[simp] theorem add_val (x y : OnIdeal F I) :
    (x + y).val = adicEvalMv I (memFin2 I x.property y.property) F.toPowerSeries := rfl

@[simp] theorem neg_val (x : OnIdeal F I) :
    (-x).val = adicEval I x.property (formalInv F) := rfl

/-- Folding one binary substitution level: evaluating `F(p, q)` `I`-adically equals substituting
the evaluated arguments into `F`.  This is the workhorse behind every group axiom. -/
theorem fold {τ : Type*} [Finite τ] {b : τ → A} (hb : ∀ s, b s ∈ I)
    {p q : MvPowerSeries τ A} (hpq : MvPowerSeries.HasSubst ![p, q])
    (hp : MvPowerSeries.constantCoeff p = 0) (hq : MvPowerSeries.constantCoeff q = 0) :
    adicEvalMv I hb (MvPowerSeries.subst ![p, q] F.toPowerSeries) =
      adicEvalMv I (a := ![adicEvalMv I hb p, adicEvalMv I hb q])
        (memFin2 I (adicEvalMv_mem I hb hp) (adicEvalMv_mem I hb hq)) F.toPowerSeries := by
  rw [adicEvalMv_subst I hb hpq (fun s => by fin_cases s <;> assumption) F.toPowerSeries]
  apply adicEvalMv_congr
  funext s
  fin_cases s <;> rfl

/-- Two-variable evaluation of the base series: substituting `![X i, X j]` and evaluating at `b`
gives `F` evaluated at `![b i, b j]`. -/
theorem evalXX {n : ℕ} {b : Fin n → A} (hb : ∀ s, b s ∈ I) (i j : Fin n) :
    adicEvalMv I hb (MvPowerSeries.subst
        ![(MvPowerSeries.X i : MvPowerSeries (Fin n) A), MvPowerSeries.X j] F.toPowerSeries)
      = adicEvalMv I (a := ![b i, b j]) (memFin2 I (hb i) (hb j)) F.toPowerSeries := by
  rw [fold (F := F) hb MvPowerSeries.HasSubst.X_X (by simp) (by simp)]
  apply adicEvalMv_congr
  funext t
  fin_cases t
  · exact adicEvalMv_X I hb i
  · exact adicEvalMv_X I hb j

/-- Associativity of `⊕`, transported from `F.assoc'`. -/
protected theorem add_assoc (x y z : OnIdeal F I) : x + y + z = x + (y + z) := by
  apply OnIdeal.ext
  have hb : ∀ s : Fin 3, ![x.val, y.val, z.val] s ∈ I := by
    intro s; fin_cases s
    · exact x.property
    · exact y.property
    · exact z.property
  have hcc01 : MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) A), MvPowerSeries.X 1] F.toPowerSeries) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero MvPowerSeries.HasSubst.X_X
      (fun s => by fin_cases s <;> simp) F.zero_constantCoeff
  have hcc12 : MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) A), MvPowerSeries.X 2] F.toPowerSeries) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero MvPowerSeries.HasSubst.X_X
      (fun s => by fin_cases s <;> simp) F.zero_constantCoeff
  have hsL : MvPowerSeries.HasSubst
      ![MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) A), MvPowerSeries.X 1]
          F.toPowerSeries, MvPowerSeries.X 2] := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
    intro s
    fin_cases s
    · exact hcc01
    · simp
  have hsR : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) A),
        MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 2] F.toPowerSeries] := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
    intro s
    fin_cases s
    · simp
    · exact hcc12
  have hassoc := F.assoc' (f₀ := (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) A))
    (f₁ := MvPowerSeries.X 1) (f₂ := MvPowerSeries.X 2)
    (PowerSeries.HasSubst.X 0) (PowerSeries.HasSubst.X 1) (PowerSeries.HasSubst.X 2)
  have hL : (x + y + z).val = adicEvalMv I hb
      (MvPowerSeries.subst ![MvPowerSeries.subst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) A), MvPowerSeries.X 1] F.toPowerSeries,
        MvPowerSeries.X 2] F.toPowerSeries) := by
    rw [fold (F := F) hb hsL hcc01 (by simp)]
    simp only [add_val]
    apply adicEvalMv_congr
    funext s
    fin_cases s
    · exact (evalXX (F := F) hb 0 1).symm
    · exact (adicEvalMv_X I hb 2).symm
  have hR : (x + (y + z)).val = adicEvalMv I hb
      (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) A),
        MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 2] F.toPowerSeries]
        F.toPowerSeries) := by
    rw [fold (F := F) hb hsR (by simp) hcc12]
    simp only [add_val]
    apply adicEvalMv_congr
    funext s
    fin_cases s
    · exact (adicEvalMv_X I hb 0).symm
    · exact (evalXX (F := F) hb 1 2).symm
  rw [hL, hR, hassoc]

/-- `0 ⊕ y = y`, transported from `F(0, Y) = Y` (`F.zeroX_eq_X`). -/
protected theorem zero_add (y : OnIdeal F I) : 0 + y = y := by
  apply OnIdeal.ext
  have hb : ∀ _ : Unit, y.val ∈ I := fun _ => y.property
  have hsub : MvPowerSeries.HasSubst ![(0 : PowerSeries A), PowerSeries.X] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
      fin_cases s <;> simp [PowerSeries.X_apply])
  have heq : MvPowerSeries.subst ![(0 : PowerSeries A), PowerSeries.X] F.toPowerSeries
      = PowerSeries.X := F.zeroX_eq_X
  have hlhs : adicEvalMv I hb
      (MvPowerSeries.subst ![(0 : PowerSeries A), PowerSeries.X] F.toPowerSeries) = y.val := by
    rw [heq, PowerSeries.X_apply, adicEvalMv_X I hb ()]
  rw [add_val]
  refine Eq.trans ?_ hlhs
  rw [fold (F := F) hb hsub (by simp) (by simp [PowerSeries.X_apply])]
  apply adicEvalMv_congr
  funext s
  fin_cases s
  · simp
  · simp [PowerSeries.X_apply, adicEvalMv_X I hb ()]

/-- `y ⊕ 0 = y`, transported from `F(Y, 0) = Y` (`F.Xzero_eq_X`). -/
protected theorem add_zero (y : OnIdeal F I) : y + 0 = y := by
  apply OnIdeal.ext
  have hb : ∀ _ : Unit, y.val ∈ I := fun _ => y.property
  have hsub : MvPowerSeries.HasSubst ![PowerSeries.X, (0 : PowerSeries A)] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
      fin_cases s <;> simp [PowerSeries.X_apply])
  have heq : MvPowerSeries.subst ![PowerSeries.X, (0 : PowerSeries A)] F.toPowerSeries
      = PowerSeries.X := F.Xzero_eq_X
  have hlhs : adicEvalMv I hb
      (MvPowerSeries.subst ![PowerSeries.X, (0 : PowerSeries A)] F.toPowerSeries) = y.val := by
    rw [heq, PowerSeries.X_apply, adicEvalMv_X I hb ()]
  rw [add_val]
  refine Eq.trans ?_ hlhs
  rw [fold (F := F) hb hsub (by simp [PowerSeries.X_apply]) (by simp)]
  apply adicEvalMv_congr
  funext s
  fin_cases s
  · simp [PowerSeries.X_apply, adicEvalMv_X I hb ()]
  · simp

/-- `x ⊕ (-x) = 0`, transported from `F(X, i(X)) = 0` (`subst_formalInv`). -/
protected theorem add_neg (x : OnIdeal F I) : x + -x = 0 := by
  apply OnIdeal.ext
  have hb : ∀ _ : Unit, x.val ∈ I := fun _ => x.property
  have hsub : MvPowerSeries.HasSubst ![PowerSeries.X, formalInv F] :=
    hasSubst_X_cons (constantCoeff_formalInv F)
  have hlhs : adicEvalMv I hb
      (MvPowerSeries.subst ![PowerSeries.X, formalInv F] F.toPowerSeries) = 0 := by
    rw [subst_formalInv, map_zero]
  rw [add_val, zero_val]
  refine Eq.trans ?_ hlhs
  rw [fold (F := F) hb hsub (by simp [PowerSeries.X_apply]) (constantCoeff_formalInv F)]
  apply adicEvalMv_congr
  funext s
  fin_cases s
  · simp [PowerSeries.X_apply, adicEvalMv_X I hb ()]
  · rw [neg_val]
    exact adicEval_eq_adicEvalMv I x.property (formalInv F)

/-- `x ⊕ y = y ⊕ x` for a commutative formal group law, transported from `F.comm'`. -/
protected theorem add_comm [F.IsComm] (x y : OnIdeal F I) : x + y = y + x := by
  apply OnIdeal.ext
  have hb : ∀ s : Fin 2, ![x.val, y.val] s ∈ I := memFin2 I x.property y.property
  have hcomm := F.comm' (f := (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A))
    (g := MvPowerSeries.X 1) (PowerSeries.HasSubst.X 0) (PowerSeries.HasSubst.X 1)
  have hxy : (x + y).val = adicEvalMv I hb (MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1] F.toPowerSeries) := by
    rw [add_val]
    exact (evalXX (F := F) hb 0 1).symm
  have hyx : (y + x).val = adicEvalMv I hb (MvPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 0] F.toPowerSeries) := by
    rw [add_val]
    exact (evalXX (F := F) hb 1 0).symm
  rw [hxy, hyx, hcomm]

instance : AddMonoid (OnIdeal F I) where
  add_assoc := OnIdeal.add_assoc
  zero_add := OnIdeal.zero_add
  add_zero := OnIdeal.add_zero
  nsmul := nsmulRec

instance : AddGroup (OnIdeal F I) :=
  { (inferInstance : AddMonoid (OnIdeal F I)), (inferInstance : Neg (OnIdeal F I)) with
    zsmul := zsmulRec
    neg_add_cancel := neg_add_cancel_of_add_neg_cancel OnIdeal.add_neg }

instance [F.IsComm] : AddCommGroup (OnIdeal F I) :=
  { (inferInstance : AddGroup (OnIdeal F I)) with
    add_comm := OnIdeal.add_comm }

end OnIdeal

end FormalGroup

end
