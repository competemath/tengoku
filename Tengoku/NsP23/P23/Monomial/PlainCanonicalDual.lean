import Tengoku.NsP23.P23.Monomial.PlainArtin
import Tengoku.Seed.LinearAlgebra.Dual.Basis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical dual of the finite standard-monomial algebra

This is the direct linear dual of `PlainMonomialArtin`; no polynomial quotient or
trace construction is used here.
-/

namespace P23.Monomial

noncomputable section

variable {k : Type*} [Field k]

/-- The canonical module in the finite direct model.-/
abbrev PlainOmega (k : Type*) [Field k] (S : Finset PlainExp) :=
  Module.Dual k (PlainMonomialArtin k S)

namespace PlainOmega

variable {S : Finset PlainExp}

/-- Contragradient action: `(r • φ)(x) = φ(rx)`.-/
def act (r : PlainMonomialArtin k S) (φ : PlainOmega k S) : PlainOmega k S where
  toFun x := φ (r * x)
  map_add' x y := by simp [mul_add]
  map_smul' t x := by simp [PlainMonomialArtin.mul_smul_comm']

instance : SMul (PlainMonomialArtin k S) (PlainOmega k S) := ⟨act⟩

/--
@isnad1 id=eq.0h5v.s8.db88123594ab from=translated src=- shape=986c7439 vocab=2cce8dd6
-/
@[simp]
theorem smul_apply (r : PlainMonomialArtin k S) (φ : PlainOmega k S)
    (x : PlainMonomialArtin k S) : (r • φ) x = φ (r * x) := rfl

instance : Module (PlainMonomialArtin k S) (PlainOmega k S) where
  one_smul φ := by
    ext x
    simp
  mul_smul r s φ := by
    ext x
    simp [mul_assoc, mul_left_comm]
  smul_zero r := by
    ext x
    simp
  smul_add r φ ψ := by
    ext x
    simp
  zero_smul φ := by
    ext x
    simp
  add_smul r s φ := by
    ext x
    simp [add_mul]

instance : IsScalarTower k (PlainMonomialArtin k S) (PlainOmega k S) where
  smul_assoc r a φ := by
    ext x
    change φ ((r • a) * x) = r • φ (a * x)
    rw [PlainMonomialArtin.smul_mul_assoc']
    exact φ.map_smul r (a * x)

/-- Kronecker dual of a surviving standard monomial.-/
def PU (S : Finset PlainExp) (p : PlainMonomialIndex S) : PlainOmega k S :=
  (PlainMonomialArtin.monomialBasis k S).dualBasis p

/--
@isnad1 id=eq.0h4v.s7.fc93843ee330 from=translated src=- shape=20680bbe vocab=7d39686f
-/
@[simp]
theorem PU_apply_PX (S : Finset PlainExp) (p q : PlainMonomialIndex S) :
    PU (k := k) S p (PX (k := k) S q.1 q.2) = if p = q then 1 else 0 := by
  simpa [PU] using
    (Module.Basis.dualBasis_apply_self (PlainMonomialArtin.monomialBasis k S) p q)
      |>.trans (by simp [eq_comm])

/-- Exact coefficient formula for the action of a monomial basis vector on a
dual basis vector.
@isnad1 id=eq.0h5v.s8.f09a323ff942 from=translated src=- shape=03f39c84 vocab=ea59221c
-/
theorem PX_smul_PU_apply_PX (S : Finset PlainExp)
    (m q s : PlainMonomialIndex S) :
    (PX (k := k) S m.1 m.2 • PU (k := k) S s)
        (PX (k := k) S q.1 q.2) =
      if m.1 + q.1 = s.1 then 1 else 0 := by
  classical
  rw [smul_apply, PlainMonomialArtin.PX_mul_PX]
  by_cases hmq : m.1 + q.1 ∈ plainStandardFinset S
  · simp only [dite_eq_left hmq]
    let t : PlainMonomialIndex S := ⟨m.1 + q.1, hmq⟩
    change PU (k := k) S s (PX (k := k) S t.1 t.2) = _
    rw [PU_apply_PX]
    simp [t, Subtype.ext_iff, eq_comm]
  · have hne : m.1 + q.1 ≠ s.1 := by
      intro h
      apply hmq
      simpa [h] using s.2
    simp [hmq, hne]

/-- Cancellativity upgrades the coefficient formula to an exact dual-basis
action.
@isnad1 id=eq.1h5v.s7.ff83788283fb from=translated src=- shape=e2dd3f6f vocab=4a3fb92d
-/
theorem PX_smul_PU_eq_PU (S : Finset PlainExp)
    (m q s : PlainMonomialIndex S) (h : m.1 + q.1 = s.1) :
    PX (k := k) S m.1 m.2 • PU (k := k) S s = PU (k := k) S q := by
  apply (PlainMonomialArtin.monomialBasis k S).ext
  intro r
  simp only [PlainMonomialArtin.monomialBasis_apply]
  rw [PX_smul_PU_apply_PX, PU_apply_PX]
  have hiff : m.1 + r.1 = s.1 ↔ r = q := by
    constructor
    · intro hr
      apply Subtype.ext
      apply add_left_cancel
      exact hr.trans h.symm
    · rintro rfl
      exact h
  simp [hiff, eq_comm]

/--
@isnad1 id=ne.0h3v.s6.0681532c570f from=translated src=- shape=dc1128e4 vocab=adce6326
-/
theorem PU_ne_zero (S : Finset PlainExp) (p : PlainMonomialIndex S) :
    PU (k := k) S p ≠ 0 := by
  intro h
  have hc := congrArg (fun φ : PlainOmega k S ↦
    φ (PX (k := k) S p.1 p.2)) h
  simpa [PU_apply_PX] using hc

/-- A selected root, regarded as a surviving standard-monomial index.-/
def plainRootIndex (S : Finset PlainExp) (s : PlainExp) (hs : s ∈ S) :
    PlainMonomialIndex S :=
  ⟨s, (mem_plainStandardFinset S s).2 ⟨s, hs, plainDivides_refl s⟩⟩

/-- The set of dual basis vectors indexed by selected roots.-/
def plainRootDualSet (k : Type*) [Field k] (S : Finset PlainExp) :
    Set (PlainOmega k S) :=
  {φ | ∃ (s : PlainExp) (hs : s ∈ S),
    φ = PU (k := k) S (plainRootIndex S s hs)}

private theorem PU_mem_plainRootDual_span (S : Finset PlainExp)
    (p : PlainMonomialIndex S) :
    PU (k := k) S p ∈ Submodule.span (PlainMonomialArtin k S) (plainRootDualSet k S) := by
  obtain ⟨s,hs,hps⟩ := (mem_plainStandardFinset S p.1).mp p.2
  have hle : p.1 ≤ s := hps
  obtain ⟨w,hw⟩ := le_iff_exists_add.mp hle
  have hwstd : w ∈ plainStandardFinset S := by
    apply PlainMonomialArtin.mem_plainStandardFinset_of_add_mem_right S (p := p.1)
    rw [←hw]
    exact (plainRootIndex S s hs).2
  let wi : PlainMonomialIndex S := ⟨w,hwstd⟩
  have hprod : wi.1 + p.1 = (plainRootIndex S s hs).1 := by
    simpa [wi,plainRootIndex,add_comm] using hw.symm
  have hroot : PU (k := k) S (plainRootIndex S s hs) ∈
      Submodule.span (PlainMonomialArtin k S) (plainRootDualSet k S) :=
    Submodule.subset_span ⟨s,hs,rfl⟩
  rw [←PX_smul_PU_eq_PU (k := k) S wi p (plainRootIndex S s hs) hprod]
  exact Submodule.smul_mem _ _ hroot

/-- The selected-root duals generate the entire canonical module.
@isnad1 id=eq.0h2v.s8.15532a84de8f from=translated src=- shape=1a48e1f4 vocab=4e1af92d
-/
theorem plainRootDual_span_eq_top (S : Finset PlainExp) :
    Submodule.span (PlainMonomialArtin k S) (plainRootDualSet k S) = ⊤ := by
  let P := Submodule.span (PlainMonomialArtin k S) (plainRootDualSet k S)
  apply top_unique
  intro φ _
  have hspan : Submodule.span k
      (Set.range (PlainMonomialArtin.monomialBasis k S).dualBasis) ≤
      P.restrictScalars k := by
    apply Submodule.span_le.2
    rintro _ ⟨p, rfl⟩
    exact PU_mem_plainRootDual_span (k := k) S p
  rw [(PlainMonomialArtin.monomialBasis k S).dualBasis.span_eq] at hspan
  exact hspan (Submodule.mem_top)

/-- Exact monomial annihilator of a selected-root dual.
@isnad1 id=iff.1h4v.s7.4b91fbcc2197 from=translated src=- shape=4dcecbf5 vocab=6cc434e8
-/
theorem PX_smul_plainRootDual_eq_zero_iff (S : Finset PlainExp)
    (s : PlainExp) (hs : s ∈ S) (w : PlainMonomialIndex S) :
    PX (k := k) S w.1 w.2 • PU (k := k) S (plainRootIndex S s hs) = 0 ↔
      ¬ plainDivides w.1 s := by
  constructor
  · intro hzero hdiv
    have hle : w.1 ≤ s := hdiv
    obtain ⟨q,hq⟩ := le_iff_exists_add.mp hle
    have hqstd : q ∈ plainStandardFinset S := by
      apply PlainMonomialArtin.mem_plainStandardFinset_of_add_mem_right S (p := w.1)
      rw [←hq]
      exact (plainRootIndex S s hs).2
    let qi : PlainMonomialIndex S := ⟨q,hqstd⟩
    have hprod : w.1 + qi.1 = (plainRootIndex S s hs).1 := hq.symm
    rw [PX_smul_PU_eq_PU S w qi (plainRootIndex S s hs) hprod] at hzero
    exact PU_ne_zero S qi hzero
  · intro hndiv
    apply (PlainMonomialArtin.monomialBasis k S).ext
    intro q
    simp only [PlainMonomialArtin.monomialBasis_apply]
    rw [PX_smul_PU_apply_PX]
    have hne : w.1 + q.1 ≠ (plainRootIndex S s hs).1 := by
      intro heq
      apply hndiv
      intro j
      have hc := congrArg (fun p : PlainExp => p j) heq
      change w.1 j ≤ s j
      change w.1 j + q.1 j = s j at hc
      omega
    simp [hne]

end PlainOmega

export PlainOmega (PU smul_apply PU_apply_PX PX_smul_PU_apply_PX PX_smul_PU_eq_PU
  PU_ne_zero plainRootIndex plainRootDualSet plainRootDual_span_eq_top
  PX_smul_plainRootDual_eq_zero_iff)

end

end P23.Monomial
