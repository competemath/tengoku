import Tengoku.NsP23.P23.Artin.MonomialAlgebra
import Tengoku.Seed.LinearAlgebra.Dual.Basis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical dual of the finite standard-monomial algebra

This is the direct linear dual of `MonomialArtin`; no polynomial quotient or
trace construction is used here.
-/

namespace P23.Artin

noncomputable section

open P23.OneTie

variable {a b c : ℕ} [NeZero a]
variable {k : Type*} [Field k]

/-- The canonical module in the finite direct model.-/
abbrev Omega (k : Type*) [Field k] (S : Finset (Normal a b c)) :=
  Module.Dual k (MonomialArtin k S)

namespace Omega

variable {S : Finset (Normal a b c)}

/-- Contragradient action: `(r • φ)(x) = φ(rx)`.-/
def act (r : MonomialArtin k S) (φ : Omega k S) : Omega k S where
  toFun x := φ (r * x)
  map_add' x y := by simp [mul_add]
  map_smul' t x := by simp [MonomialArtin.mul_smul_comm']

instance : SMul (MonomialArtin k S) (Omega k S) := ⟨act⟩

@[simp]
theorem smul_apply (r : MonomialArtin k S) (φ : Omega k S)
    (x : MonomialArtin k S) : (r • φ) x = φ (r * x) := rfl

instance : Module (MonomialArtin k S) (Omega k S) where
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

instance : IsScalarTower k (MonomialArtin k S) (Omega k S) where
  smul_assoc r a φ := by
    ext x
    change φ ((r • a) * x) = r • φ (a * x)
    rw [MonomialArtin.smul_mul_assoc']
    exact φ.map_smul r (a * x)

/-- Kronecker dual of a surviving standard monomial.-/
def U (S : Finset (Normal a b c)) (p : MonomialIndex S) : Omega k S :=
  (MonomialArtin.monomialBasis k S).dualBasis p

@[simp]
theorem U_apply_X (S : Finset (Normal a b c)) (p q : MonomialIndex S) :
    U (k := k) S p (X (k := k) S q.1 q.2) = if p = q then 1 else 0 := by
  simpa [U] using
    (Module.Basis.dualBasis_apply_self (MonomialArtin.monomialBasis k S) p q)
      |>.trans (by simp [eq_comm])

/-- Exact coefficient formula for the action of a monomial basis vector on a
dual basis vector.-/
theorem X_smul_U_apply_X (S : Finset (Normal a b c))
    (m q s : MonomialIndex S) :
    (X (k := k) S m.1 m.2 • U (k := k) S s)
        (X (k := k) S q.1 q.2) =
      if m.1 * q.1 = s.1 then 1 else 0 := by
  classical
  rw [smul_apply, MonomialArtin.X_mul_X]
  by_cases hmq : m.1 * q.1 ∈ standardFinset S
  · simp only [dite_eq_left hmq]
    let t : MonomialIndex S := ⟨m.1 * q.1, hmq⟩
    change U (k := k) S s (X (k := k) S t.1 t.2) = _
    rw [U_apply_X]
    simp [t, Subtype.ext_iff, eq_comm]
  · have hne : m.1 * q.1 ≠ s.1 := by
      intro h
      apply hmq
      simpa [h] using s.2
    simp [hmq, hne]

/-- Cancellativity upgrades the coefficient formula to an exact dual-basis
action.-/
theorem X_smul_U_eq_U (S : Finset (Normal a b c))
    (m q s : MonomialIndex S) (h : m.1 * q.1 = s.1) :
    X (k := k) S m.1 m.2 • U (k := k) S s = U (k := k) S q := by
  apply (MonomialArtin.monomialBasis k S).ext
  intro r
  simp only [MonomialArtin.monomialBasis_apply]
  rw [X_smul_U_apply_X, U_apply_X]
  have hiff : m.1 * r.1 = s.1 ↔ r = q := by
    constructor
    · intro hr
      apply Subtype.ext
      apply Normal.mul_left_cancel
      exact hr.trans h.symm
    · rintro rfl
      exact h
  simp [hiff, eq_comm]

theorem U_ne_zero (S : Finset (Normal a b c)) (p : MonomialIndex S) :
    U (k := k) S p ≠ 0 := by
  intro h
  have hc := congrArg (fun φ : Omega k S ↦
    φ (X (k := k) S p.1 p.2)) h
  simpa [U_apply_X] using hc

/-- A selected root, regarded as a surviving standard-monomial index.-/
def rootIndex (S : Finset (Normal a b c)) (s : Normal a b c) (hs : s ∈ S) :
    MonomialIndex S :=
  ⟨s, (mem_standardFinset_iff_standardSet S s).2 ⟨s, hs, dvd_rfl⟩⟩

/-- The set of dual basis vectors indexed by selected roots.-/
def rootDualSet (k : Type*) [Field k] (S : Finset (Normal a b c)) :
    Set (Omega k S) :=
  {φ | ∃ (s : Normal a b c) (hs : s ∈ S),
    φ = U (k := k) S (rootIndex S s hs)}

private theorem U_mem_rootDual_span (S : Finset (Normal a b c))
    (p : MonomialIndex S) :
    U (k := k) S p ∈ Submodule.span (MonomialArtin k S) (rootDualSet k S) := by
  have hpstd : p.1 ∈ standardSet S :=
    (mem_standardFinset_iff_standardSet S p.1).1 p.2
  rcases hpstd with ⟨s, hs, hpdiv⟩
  rcases hpdiv with ⟨w, hw⟩
  have hsstd : s ∈ standardSet S := ⟨s, hs, dvd_rfl⟩
  have hwstd : w ∈ standardSet S :=
    standardSet_dvd_closed S hsstd ⟨p.1, by simpa [mul_comm] using hw⟩
  let wi : MonomialIndex S :=
    ⟨w, (mem_standardFinset_iff_standardSet S w).2 hwstd⟩
  have hprod : wi.1 * p.1 = (rootIndex S s hs).1 := by
    simpa [wi, rootIndex, mul_comm] using hw.symm
  have hroot : U (k := k) S (rootIndex S s hs) ∈
      Submodule.span (MonomialArtin k S) (rootDualSet k S) :=
    Submodule.subset_span ⟨s, hs, rfl⟩
  rw [← X_smul_U_eq_U (k := k) S wi p (rootIndex S s hs) hprod]
  exact Submodule.smul_mem _ _ hroot

/-- The selected-root duals generate the entire canonical module.-/
theorem rootDual_span_eq_top (S : Finset (Normal a b c)) :
    Submodule.span (MonomialArtin k S) (rootDualSet k S) = ⊤ := by
  let P := Submodule.span (MonomialArtin k S) (rootDualSet k S)
  apply top_unique
  intro φ _
  have hspan : Submodule.span k
      (Set.range (MonomialArtin.monomialBasis k S).dualBasis) ≤
      P.restrictScalars k := by
    apply Submodule.span_le.2
    rintro _ ⟨p, rfl⟩
    exact U_mem_rootDual_span (k := k) S p
  rw [(MonomialArtin.monomialBasis k S).dualBasis.span_eq] at hspan
  exact hspan (Submodule.mem_top)

/-- Exact monomial annihilator of a selected-root dual.-/
theorem X_smul_rootDual_eq_zero_iff (S : Finset (Normal a b c))
    (s : Normal a b c) (hs : s ∈ S) (w : MonomialIndex S) :
    X (k := k) S w.1 w.2 • U (k := k) S (rootIndex S s hs) = 0 ↔
      ¬ w.1 ∣ s := by
  constructor
  · intro hzero hdiv
    rcases hdiv with ⟨q, hq⟩
    have hsstd : s ∈ standardSet S := ⟨s, hs, dvd_rfl⟩
    have hqstd : q ∈ standardSet S :=
      standardSet_dvd_closed S hsstd ⟨w.1, by simpa [mul_comm] using hq⟩
    let qi : MonomialIndex S :=
      ⟨q, (mem_standardFinset_iff_standardSet S q).2 hqstd⟩
    have hprod : w.1 * qi.1 = (rootIndex S s hs).1 := by
      simpa [qi, rootIndex, mul_comm] using hq.symm
    have hact := X_smul_U_eq_U (k := k) S w qi (rootIndex S s hs) hprod
    rw [hact] at hzero
    exact U_ne_zero (k := k) S qi hzero
  · intro hndiv
    apply (MonomialArtin.monomialBasis k S).ext
    intro q
    simp only [MonomialArtin.monomialBasis_apply]
    rw [X_smul_U_apply_X]
    have hne : w.1 * q.1 ≠ (rootIndex S s hs).1 := by
      intro heq
      apply hndiv
      exact ⟨q.1, by simpa [rootIndex] using heq.symm⟩
    simp [hne]

end Omega

export Omega (U smul_apply U_apply_X X_smul_U_apply_X X_smul_U_eq_U
  U_ne_zero rootIndex rootDualSet rootDual_span_eq_top
  X_smul_rootDual_eq_zero_iff)

end

end P23.Artin
