import Tengoku.Seed.Data.Matrix.Mul
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin
import Tengoku.Seed.LinearAlgebra.Dual.Lemmas
import Tengoku.Seed.Logic.Relation
import Tengoku.Seed.Order.Antichain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Certificate soundness: dual-witness refutation, primal-witness membership, and minimality from covers

This module machine-checks, at full abstraction, the *logic* of a
certificate-based verification pipeline.

* A **dual witness** for a finite linear system `M *ᵥ x = b` is a row vector `y`
  with `y ᵥ* M = 0` and `y ⬝ᵥ b ≠ 0`; over a commutative ring it refutes
  solvability (`infeasible_of_dualWitness`), and over a field the format is
  *complete*: every infeasible system admits one (`exists_dualWitness_of_infeasible`),
  packaged as the two-sided criterion `feasible_iff_forall_dual`.
* A **primal witness** is a solution; exhibiting one certifies solvability
  (`feasible_of_witness`).  The two certificate kinds never coexist on a single
  system (`no_certificate_conflict`).
* For a predicate `C` **step-closed** under a one-step reduction relation `R`,
  an element failing `C` all of whose one-step reducts satisfy `C` is a
  **minimal non-member** (`isMinimalNonmember_of_covers`); any two minimal
  non-members are mutually non-descendant, so the minimal non-members form an
  antichain for the descent relation (`isAntichain_isMinimalNonmember`).
* The composite theorem `isMinimalNonmember_of_certificates` welds these: a dual
  certificate at `x`, a primal certificate at every one-step reduct of `x`, and
  step-closedness of the induced membership predicate together certify that `x`
  is a minimal non-member.

## Scope and disclaimers

* This module certifies the verification *principles* only.  It does not model,
  execute, or verify any external checker or implementation; no numerical
  computation, no specific matrix, system, graph, or geometric object appears;
  every statement is over an arbitrary field or commutative ring, arbitrary
  finite index types, and an arbitrary relation.
* The dual-witness principle here is the elementary annihilator direction of
  linear solvability together with its converse over a field (a
  Fredholm-alternative statement for finite linear systems).  It is *not*
  Farkas' lemma in the ordered-field/inequality sense; no optimization or LP
  duality is stated or claimed.
* Minimality is relative to the *named* relation `R` and predicate `C`; no
  claim is made that any particular relation or predicate instantiates them.
* No Hodge-theoretic content appears in this module; nothing here makes the
  Hodge conjecture statable.

## Repo-internal tie-in

This is the abstract certificate logic that the development's exclusion modules
(`ExclusionEngine`, `ExclusionStaircase`, `ExclusionDegree`) exercise on
constructed carriers — membership by exhibited witness, exclusion by proven
certificate, hardness relative to a named family — recorded here together with
the underlying minimal-counterexample principle in its abstract form.
-/

open scoped Matrix

namespace HodgePilot

namespace CertificateSoundness

/-! ### Primal and dual certificates over a commutative ring -/

section Refutation

variable {K : Type*} {m n : Type*} [Fintype m] [Fintype n] [CommRing K]

/-- `x` is a primal witness (a solution) for the linear system `M *ᵥ x = b`.-/
def IsSolution (M : Matrix m n K) (b : m → K) (x : n → K) : Prop := M *ᵥ x = b

/-- The system `M *ᵥ x = b` is feasible: some primal witness exists.-/
def Feasible (M : Matrix m n K) (b : m → K) : Prop := ∃ x, IsSolution M b x

/-- Infeasibility of the system `M *ᵥ x = b`, as its own name (the negation of
feasibility).-/
def Infeasible (M : Matrix m n K) (b : m → K) : Prop := ¬ Feasible M b

omit [Fintype m] in
/-- Being a solution is, by definition, satisfying the system.-/
theorem isSolution_iff (M : Matrix m n K) (b : m → K) (x : n → K) :
    IsSolution M b x ↔ M *ᵥ x = b := Iff.rfl

omit [Fintype m] in
/-- Feasibility spelled with the underlying system equation.-/
theorem feasible_iff_exists (M : Matrix m n K) (b : m → K) :
    Feasible M b ↔ ∃ x, M *ᵥ x = b := Iff.rfl

omit [Fintype m] in
/-- Infeasibility is exactly the negation of feasibility.-/
theorem infeasible_iff (M : Matrix m n K) (b : m → K) :
    Infeasible M b ↔ ¬ Feasible M b := Iff.rfl

omit [Fintype m] in
/-- The primal principle: exhibiting a solution certifies feasibility.  This is
trivial by design — feasibility *is* the existence of a solution — and it is the
membership half of the certificate pair.-/
theorem feasible_of_witness {M : Matrix m n K} {b : m → K} (x : n → K)
    (hx : M *ᵥ x = b) : Feasible M b := ⟨x, hx⟩

omit [Fintype m] in
/-- A solution witnesses feasibility.-/
theorem IsSolution.feasible {M : Matrix m n K} {b : m → K} {x : n → K}
    (hx : IsSolution M b x) : Feasible M b := ⟨x, hx⟩

/-- A dual (refutation) certificate for `M *ᵥ x = b`: a row vector `y` that
annihilates the columns of `M` yet pairs nontrivially with `b`.-/
structure DualWitness (M : Matrix m n K) (b : m → K) where
  /-- The row vector of the certificate.-/
  y : m → K
  /-- The certificate annihilates the coefficient matrix: `y ᵥ* M = 0`.-/
  annihilates : y ᵥ* M = 0
  /-- The certificate pairs nontrivially with the right-hand side: `y ⬝ᵥ b ≠ 0`.-/
  pays : y ⬝ᵥ b ≠ 0

/-- A dual witness pairs to zero with the right-hand side of any system it
solves; the crux of refutation soundness.-/
theorem DualWitness.dot_eq_zero_of_isSolution {M : Matrix m n K} {b : m → K}
    (w : DualWitness M b) {x : n → K} (hx : IsSolution M b x) : w.y ⬝ᵥ b = 0 := by
  have hx' : M *ᵥ x = b := hx
  calc w.y ⬝ᵥ b = w.y ⬝ᵥ (M *ᵥ x) := by rw [hx']
    _ = (w.y ᵥ* M) ⬝ᵥ x := Matrix.dotProduct_mulVec w.y M x
    _ = (0 : n → K) ⬝ᵥ x := by rw [w.annihilates]
    _ = 0 := zero_dotProduct x

/-- A dual witness refutes every candidate solution.-/
theorem DualWitness.not_isSolution {M : Matrix m n K} {b : m → K}
    (w : DualWitness M b) (x : n → K) : ¬ IsSolution M b x :=
  fun hx => w.pays (w.dot_eq_zero_of_isSolution hx)

/-- A dual witness certifies infeasibility.-/
theorem DualWitness.infeasible {M : Matrix m n K} {b : m → K}
    (w : DualWitness M b) : Infeasible M b := by
  rintro ⟨x, hx⟩
  exact w.not_isSolution x hx

/-- A dual witness rules out feasibility (the unfolded spelling of
`DualWitness.infeasible`).-/
theorem DualWitness.not_feasible {M : Matrix m n K} {b : m → K}
    (w : DualWitness M b) : ¬ Feasible M b := w.infeasible

/-- The unbundled refutation principle: a row vector annihilating `M` that pairs
nontrivially with `b` shows the system `M *ᵥ x = b` has no solution.  This is the
exact statement a dual certificate discharges.-/
theorem infeasible_of_dualWitness {M : Matrix m n K} {b : m → K} (y : m → K)
    (hy : y ᵥ* M = 0) (hyb : y ⬝ᵥ b ≠ 0) : ¬ ∃ x, M *ᵥ x = b := by
  rintro ⟨x, hx⟩
  apply hyb
  calc y ⬝ᵥ b = y ⬝ᵥ (M *ᵥ x) := by rw [hx]
    _ = (y ᵥ* M) ⬝ᵥ x := Matrix.dotProduct_mulVec y M x
    _ = (0 : n → K) ⬝ᵥ x := by rw [hy]
    _ = 0 := zero_dotProduct x

/-- The consistency receipt for the certificate pair: a dual witness and a
primal witness can never coexist on one system.-/
theorem no_certificate_conflict {M : Matrix m n K} {b : m → K}
    (w : DualWitness M b) (x : n → K) (hx : M *ᵥ x = b) : False :=
  w.not_isSolution x hx

/-- The bundled consistency receipt: a feasible system admits no dual witness.-/
theorem not_nonempty_dualWitness_of_feasible {M : Matrix m n K} {b : m → K}
    (hf : Feasible M b) : ¬ Nonempty (DualWitness M b) :=
  fun ⟨w⟩ => w.infeasible hf

end Refutation

/-! ### Certificate rescaling and completeness over a field -/

section Field

variable {K : Type*} {m n : Type*} [Fintype m] [Fintype n] [Field K]

/-- Over a field, a dual witness may be rescaled by any nonzero scalar.-/
def DualWitness.smul {M : Matrix m n K} {b : m → K} (w : DualWitness M b) {c : K}
    (hc : c ≠ 0) : DualWitness M b where
  y := c • w.y
  annihilates := by rw [Matrix.smul_vecMul, w.annihilates, smul_zero]
  pays := by rw [smul_dotProduct, smul_eq_mul]; exact mul_ne_zero hc w.pays

omit [Fintype n] in
/-- The rescaled certificate has the expected row vector.-/
theorem DualWitness.smul_y {M : Matrix m n K} {b : m → K} (w : DualWitness M b)
    {c : K} (hc : c ≠ 0) : (w.smul hc).y = c • w.y := rfl

/-- Over a field the dual-witness format is complete: every infeasible system
admits a dual witness.  Existence is delivered in `Nonempty` form.  The field
hypothesis is needed only for this converse direction; refutation soundness
holds over any commutative ring.-/
theorem exists_dualWitness_of_infeasible {M : Matrix m n K} {b : m → K}
    (h : ¬ Feasible M b) : Nonempty (DualWitness M b) := by
  classical
  have hb : b ∉ LinearMap.range M.mulVecLin := by
    intro hmem
    rw [LinearMap.mem_range] at hmem
    obtain ⟨x, hx⟩ := hmem
    rw [Matrix.mulVecLin_apply] at hx
    exact h ⟨x, hx⟩
  obtain ⟨f, hfb, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hb inferInstance
  set y : m → K := fun i => f (fun j => if i = j then (1 : K) else 0) with hy
  have bridge : ∀ v : m → K, f v = v ⬝ᵥ y := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ f v]
    simp only [dotProduct, smul_eq_mul, hy]
  refine ⟨⟨y, ?_, ?_⟩⟩
  · funext j
    show y ⬝ᵥ (fun i => M i j) = (0 : K)
    have hmem : (fun i => M i j) ∈ LinearMap.range M.mulVecLin := by
      rw [LinearMap.mem_range]
      refine ⟨Pi.single j 1, ?_⟩
      rw [Matrix.mulVecLin_apply]
      funext i
      show (fun k => M i k) ⬝ᵥ Pi.single j (1 : K) = M i j
      rw [dotProduct_single, mul_one]
    have hf0 : f (fun i => M i j) = 0 := by
      have hmem2 : f (fun i => M i j) ∈ Submodule.map f (LinearMap.range M.mulVecLin) :=
        Submodule.mem_map_of_mem hmem
      rw [hmap] at hmem2
      simpa using hmem2
    rw [dotProduct_comm, ← bridge (fun i => M i j)]
    exact hf0
  · rw [dotProduct_comm, ← bridge b]
    exact hfb

/-- The full soundness-and-completeness package over a field: a system is
feasible iff every annihilator of `M` pairs to zero with `b`.  The forward
direction is refutation soundness; the backward direction needs completeness.-/
theorem feasible_iff_forall_dual {M : Matrix m n K} {b : m → K} :
    Feasible M b ↔ ∀ y : m → K, y ᵥ* M = 0 → y ⬝ᵥ b = 0 := by
  constructor
  · rintro ⟨x, hx⟩ y hy
    have hx' : M *ᵥ x = b := hx
    calc y ⬝ᵥ b = y ⬝ᵥ (M *ᵥ x) := by rw [hx']
      _ = (y ᵥ* M) ⬝ᵥ x := Matrix.dotProduct_mulVec y M x
      _ = (0 : n → K) ⬝ᵥ x := by rw [hy]
      _ = 0 := zero_dotProduct x
  · intro hall
    by_contra hinf
    obtain ⟨w⟩ := exists_dualWitness_of_infeasible hinf
    exact w.pays (hall w.y w.annihilates)

end Field

/-! ### Minimality from covers for a step-closed predicate -/

section Minimality

variable {α : Type*} (R : α → α → Prop) (C : α → Prop)

/-- A predicate `C` is step-closed under a one-step reduction relation `R`
(read `R x y` as "`y` is a one-step reduct of `x`") when each step preserves
`C`.  This is the abstract shape of closedness of a membership predicate under a
one-step reduction.-/
def StepClosed : Prop := ∀ ⦃x y⦄, R x y → C x → C y

/-- `x` is a minimal non-member of `C` for the reduction `R`: it fails `C`, yet
every proper descendant (reachable in one or more steps) satisfies `C`.-/
def IsMinimalNonmember (x : α) : Prop :=
  ¬ C x ∧ ∀ y, Relation.TransGen R x y → C y

/-- Minimal non-membership spelled as its defining conjunction.-/
theorem isMinimalNonmember_iff {x : α} :
    IsMinimalNonmember R C x ↔ ¬ C x ∧ ∀ y, Relation.TransGen R x y → C y := Iff.rfl

variable {R C}

/-- Step-closedness propagates `C` along any reflexive-transitive descent.-/
theorem StepClosed.of_reflTransGen (hC : StepClosed R C) {x y : α}
    (h : Relation.ReflTransGen R x y) (hx : C x) : C y := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih => exact hC hbc ih

/-- Step-closedness propagates `C` along any proper (transitive) descent.-/
theorem StepClosed.of_transGen (hC : StepClosed R C) {x y : α}
    (h : Relation.TransGen R x y) (hx : C x) : C y :=
  hC.of_reflTransGen h.to_reflTransGen hx

/-- The induction core: if every one-step reduct of `x` satisfies a step-closed
`C`, then so does every proper descendant of `x`.  (`¬ C x` is not needed here.)-/
theorem mem_of_transGen_of_covers (hC : StepClosed R C) {x : α}
    (hcov : ∀ y, R x y → C y) {z : α} (h : Relation.TransGen R x z) : C z := by
  obtain ⟨w, hxw, hwz⟩ := Relation.TransGen.head'_iff.mp h
  exact hC.of_reflTransGen hwz (hcov w hxw)

/-- The headline: an element failing a step-closed predicate, all of whose
one-step reducts satisfy it, is a minimal non-member.-/
theorem isMinimalNonmember_of_covers (hC : StepClosed R C) {x : α} (hx : ¬ C x)
    (hcov : ∀ y, R x y → C y) : IsMinimalNonmember R C x :=
  ⟨hx, fun _y hy => mem_of_transGen_of_covers hC hcov hy⟩

/-- Accessor: a minimal non-member fails the predicate.-/
theorem IsMinimalNonmember.notMem {x : α} (h : IsMinimalNonmember R C x) : ¬ C x :=
  h.1

/-- Accessor: every proper descendant of a minimal non-member satisfies the
predicate.-/
theorem IsMinimalNonmember.mem_of_transGen {x : α} (h : IsMinimalNonmember R C x)
    {y : α} (hy : Relation.TransGen R x y) : C y := h.2 y hy

/-- Two minimal non-members are never in proper descent: no such element reduces
to another.  This holds with no distinctness hypothesis — a proper self-descent
would already force membership.-/
theorem IsMinimalNonmember.not_transGen {x₁ x₂ : α}
    (h₁ : IsMinimalNonmember R C x₁) (h₂ : IsMinimalNonmember R C x₂) :
    ¬ Relation.TransGen R x₁ x₂ :=
  fun hstep => h₂.notMem (h₁.mem_of_transGen hstep)

/-- Minimal non-members are pairwise mutually non-descendant.-/
theorem IsMinimalNonmember.independent {x₁ x₂ : α}
    (h₁ : IsMinimalNonmember R C x₁) (h₂ : IsMinimalNonmember R C x₂) :
    ¬ Relation.TransGen R x₁ x₂ ∧ ¬ Relation.TransGen R x₂ x₁ :=
  ⟨h₁.not_transGen h₂, h₂.not_transGen h₁⟩

/-- The minimal non-members of `C` form an antichain for the proper-descent
relation.-/
theorem isAntichain_isMinimalNonmember :
    IsAntichain (Relation.TransGen R) {x | IsMinimalNonmember R C x} := by
  intro x₁ hx₁ x₂ hx₂ _hne
  show ¬ Relation.TransGen R x₁ x₂
  exact IsMinimalNonmember.not_transGen hx₁ hx₂

end Minimality

/-! ### The composite excluded-element principle -/

section Composite

variable {K : Type*} [CommRing K] {α : Type*}

/-- The membership predicate induced by a family of linear systems: `a` is a
member exactly when its system is feasible.-/
def familyMem {row col : α → Type*} [∀ a, Fintype (row a)] [∀ a, Fintype (col a)]
    (M : ∀ a, Matrix (row a) (col a) K) (b : ∀ a, row a → K) : α → Prop :=
  fun a => Feasible (M a) (b a)

/-- Induced membership is exactly feasibility of the system at that index.-/
theorem familyMem_apply {row col : α → Type*} [∀ a, Fintype (row a)]
    [∀ a, Fintype (col a)] (M : ∀ a, Matrix (row a) (col a) K)
    (b : ∀ a, row a → K) (a : α) : familyMem M b a ↔ Feasible (M a) (b a) := Iff.rfl

/-- The composite principle: a dual certificate at `x`, a primal certificate at
every one-step reduct of `x`, and step-closedness of the induced membership
predicate together certify that `x` is a minimal non-member for the reduction.-/
theorem isMinimalNonmember_of_certificates (R : α → α → Prop) {row col : α → Type*}
    [∀ a, Fintype (row a)] [∀ a, Fintype (col a)]
    (M : ∀ a, Matrix (row a) (col a) K) (b : ∀ a, row a → K)
    (hC : StepClosed R (familyMem M b)) {x : α} (w : DualWitness (M x) (b x))
    (prim : ∀ y, R x y → ∃ z, IsSolution (M y) (b y) z) :
    IsMinimalNonmember R (familyMem M b) x := by
  refine isMinimalNonmember_of_covers hC ?_ ?_
  · exact w.infeasible
  · intro y hy
    obtain ⟨z, hz⟩ := prim y hy
    exact hz.feasible

end Composite

end CertificateSoundness

end HodgePilot
