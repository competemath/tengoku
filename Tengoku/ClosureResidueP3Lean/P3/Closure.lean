import Tengoku.ClosureResidueP3Lean.P3.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open scoped BigOperators
open Matrix

namespace P3

section Closure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A complex-linear finite dynamics on the full matrix algebra.-/
abbrev Dynamics (V : Type*) [Fintype V] := Module.End ℂ (A V)

/--
Finite-depth closure filtration
  M_k = span { φ^ℓ(d) : d ∈ D, ℓ ≤ k }.
This is the paper's linear span, not an algebraic closure.-/
def closure (φ : Dynamics V) (k : ℕ) : Submodule ℂ (A V) :=
  Submodule.span ℂ
    {x | ∃ d : diagonalSubmodule (V := V), ∃ l : ℕ, l ≤ k ∧ (φ ^ l) d.1 = x}

/-- Every diagonal observable lies in every finite-depth closure.
@isnad1 id=le.0h3v.s6.a5d85f67bd17 from=translated src=- shape=6052b0eb vocab=691b4f55
-/
theorem diagonalSubmodule_le_closure (φ : Dynamics V) (k : ℕ) :
    diagonalSubmodule (V := V) ≤ closure φ k := by
  intro x hx
  apply Submodule.subset_span
  refine ⟨⟨x, hx⟩, 0, Nat.zero_le k, ?_⟩
  simp

/-- B1: M_0 = D.
@isnad1 id=eq.0h2v.s5.135e142a7751 from=translated src=- shape=8b8d228d vocab=082f39dc
-/
@[simp]
theorem closure_zero (φ : Dynamics V) :
    closure φ 0 = diagonalSubmodule (V := V) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨d, l, hl, rfl⟩
    have : l = 0 := Nat.eq_zero_of_le_zero hl
    subst l
    simp
  · exact diagonalSubmodule_le_closure φ 0

/-- B1: the closure filtration is monotone in depth.
@isnad1 id=le.1h4v.s6.c0747ec062e3 from=translated src=- shape=7bcbca21 vocab=9de86c97
-/
theorem closure_mono (φ : Dynamics V) {i j : ℕ} (hij : i ≤ j) :
    closure φ i ≤ closure φ j := by
  apply Submodule.span_mono
  intro x hx
  rcases hx with ⟨d, l, hli, rfl⟩
  exact ⟨d, l, hli.trans hij, rfl⟩

/-- The hidden defect filtration H_k = Q M_k.-/
def hidden (φ : Dynamics V) (k : ℕ) : Submodule ℂ (A V) :=
  (closure φ k).map (offProjection (V := V))

/-- Delta annihilates every Q-component.
@isnad1 id=eq.0h2v.s7.341ebc8361fb from=translated src=- shape=1bbcc3d5 vocab=695b30df
-/
theorem delta_offProjection_eq_zero (x : A V) :
    delta (V := V) (offProjection (V := V) x) = 0 := by
  ext i j
  simp [offProjection, delta_apply]

/-- Delta fixes every element of the diagonal observational subspace.
@isnad1 id=eq.1h2v.s7.f73dbf75e7ad from=translated src=- shape=aa817a39 vocab=2ee90169
-/
theorem delta_eq_self_of_mem_diagonalSubmodule {x : A V}
    (hx : x ∈ diagonalSubmodule (V := V)) :
    delta (V := V) x = x := by
  rcases hx with ⟨d, rfl⟩
  simp

/-- H_k is contained in the off-diagonal kernel of Delta.
@isnad1 id=le.0h3v.s6.dee89c07f518 from=translated src=- shape=fb2c70dc vocab=1bb52140
-/
theorem hidden_le_OffDiag (φ : Dynamics V) (k : ℕ) :
    hidden φ k ≤ OffDiag (V := V) := by
  rintro x ⟨y, hy, rfl⟩
  exact delta_offProjection_eq_zero (V := V) y

/-- H_k is also a subspace of M_k, not an external enlargement.
@isnad1 id=le.0h3v.s6.ea4a1fa30552 from=translated src=- shape=7ff282e8 vocab=d2e9c98c
-/
theorem hidden_le_closure (φ : Dynamics V) (k : ℕ) :
    hidden φ k ≤ closure φ k := by
  rintro x ⟨y, hy, rfl⟩
  rw [offProjection_apply]
  exact (closure φ k).sub_mem hy
    (diagonalSubmodule_le_closure φ k
      (show delta (V := V) y ∈ diagonalSubmodule (V := V) from
        ⟨diagonalCoordinates (V := V) y, rfl⟩))

/-- B2: H_0 = 0.
@isnad1 id=eq.0h2v.s6.506339517cc5 from=translated src=- shape=fe871dd8 vocab=c4a82ab3
-/
@[simp]
theorem hidden_zero (φ : Dynamics V) :
    hidden φ 0 = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hxD : x ∈ diagonalSubmodule (V := V) := by
      simpa [closure_zero] using hidden_le_closure (V := V) φ 0 hx
    have hxQ : x ∈ OffDiag (V := V) := hidden_le_OffDiag (V := V) φ 0 hx
    have hfix := delta_eq_self_of_mem_diagonalSubmodule (V := V) hxD
    change delta (V := V) x = 0 at hxQ
    rw [hfix] at hxQ
    simpa using hxQ
  · exact bot_le

/-- B2: the hidden filtration is monotone.
@isnad1 id=le.1h4v.s6.9ec6603255a3 from=translated src=- shape=7bcbca21 vocab=a2a9f851
-/
theorem hidden_mono (φ : Dynamics V) {i j : ℕ} (hij : i ≤ j) :
    hidden φ i ≤ hidden φ j := by
  exact Submodule.map_mono (closure_mono φ hij)

/-- The diagonal and hidden sectors intersect trivially.
@isnad1 id=disjoint.0h3v.s6.fe41b3dac917 from=translated src=- shape=6052b0eb vocab=1b846d0a
-/
theorem diagonal_disjoint_hidden (φ : Dynamics V) (k : ℕ) :
    Disjoint (diagonalSubmodule (V := V)) (hidden φ k) := by
  rw [Submodule.disjoint_def]
  intro x hxD hxH
  have hfix := delta_eq_self_of_mem_diagonalSubmodule (V := V) hxD
  have hzero : delta (V := V) x = 0 := hidden_le_OffDiag (V := V) φ k hxH
  rw [hfix] at hzero
  exact hzero

/-- B3, equality part of Proposition 4.1: M_k = D + H_k.
@isnad1 id=eq.0h3v.s7.c4d5977b0fae from=translated src=- shape=a00304d5 vocab=bfe0968f
-/
theorem closure_eq_sup_diagonal_hidden (φ : Dynamics V) (k : ℕ) :
    closure φ k = diagonalSubmodule (V := V) ⊔ hidden φ k := by
  apply le_antisymm
  · intro x hx
    rw [← delta_add_offProjection (V := V) x]
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left
        (show delta (V := V) x ∈ diagonalSubmodule (V := V) from
          ⟨diagonalCoordinates (V := V) x, rfl⟩)
    · exact Submodule.mem_sup_right
        (show offProjection (V := V) x ∈ hidden φ k from
          ⟨x, hx, rfl⟩)
  · exact sup_le
      (diagonalSubmodule_le_closure φ k)
      (hidden_le_closure (V := V) φ k)

/-- B4: inside A, H_k = M_k ∩ ker Delta.
@isnad1 id=eq.0h3v.s6.0b0eec1618a6 from=translated src=- shape=0aba5ffa vocab=c3409d36
-/
theorem hidden_eq_inf_ker (φ : Dynamics V) (k : ℕ) :
    hidden φ k = closure φ k ⊓ OffDiag (V := V) := by
  apply le_antisymm
  · intro x hx
    exact ⟨hidden_le_closure (V := V) φ k hx,
      hidden_le_OffDiag (V := V) φ k hx⟩
  · rintro x ⟨hxM, hxK⟩
    change delta (V := V) x = 0 at hxK
    refine ⟨x, hxM, ?_⟩
    simp [offProjection, hxK]

/-- Every first iterate of a diagonal observable belongs to `M₁`.
@isnad1 id=mem.0h3v.s8.7d7dbd03c11e from=translated src=- shape=cde4499e vocab=d8f75227
-/
theorem map_diagonal_mem_closure_one (φ : Dynamics V)
    (d : diagonalSubmodule (V := V)) :
    φ d.1 ∈ closure φ 1 := by
  apply Submodule.subset_span
  refine ⟨d, 1, le_rfl, ?_⟩
  simp

/-- B1: recursive form `M_{k+1} = D ⊔ φ(M_k)`.
@isnad1 id=eq.0h3v.s7.020f08c18dcf from=translated src=- shape=73c455c2 vocab=345b6f8c
-/
theorem closure_succ (φ : Dynamics V) (k : ℕ) :
    closure φ (k + 1) =
      diagonalSubmodule (V := V) ⊔ (closure φ k).map φ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨d, l, hl, rfl⟩
    cases l with
    | zero =>
        exact Submodule.mem_sup_left d.property
    | succ l =>
        have hlk : l ≤ k := Nat.le_of_succ_le_succ hl
        apply Submodule.mem_sup_right
        refine ⟨(φ ^ l) d.1, ?_, ?_⟩
        · apply Submodule.subset_span
          exact ⟨d, l, hlk, rfl⟩
        · simp [pow_succ']
  · apply sup_le
    · exact diagonalSubmodule_le_closure φ (k + 1)
    · rw [Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro x ⟨d, l, hl, rfl⟩
      change φ ((φ ^ l) d.1) ∈ closure φ (k + 1)
      apply Submodule.subset_span
      refine ⟨d, l + 1, Nat.succ_le_succ hl, ?_⟩
      simp [pow_succ']

/-- The dynamics preserves the observational diagonal algebra.-/
def PreservesDiagonal (φ : Dynamics V) : Prop :=
  ∀ d : diagonalSubmodule (V := V),
    φ d.1 ∈ diagonalSubmodule (V := V)

/-- If the dynamics preserves `D`, then the first closure is still `D`.
@isnad1 id=eq.1h2v.s5.1ef392a1e26c from=translated src=- shape=87e1b564 vocab=b4fd3dec
-/
theorem closure_one_eq_diagonal_of_preservesDiagonal (φ : Dynamics V)
    (hφ : PreservesDiagonal (V := V) φ) :
    closure φ 1 = diagonalSubmodule (V := V) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨d, l, hl, rfl⟩
    cases l with
    | zero => simp
    | succ l =>
        have hl0 : l = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hl)
        subst l
        simpa using hφ d
  · exact diagonalSubmodule_le_closure φ 1

/-- Vanishing hidden sector is equivalent to no enlargement of the diagonal closure.
@isnad1 id=iff.0h3v.s6.71be86247ad7 from=translated src=- shape=3b9c150e vocab=c6f67fd1
-/
theorem closure_eq_diagonal_iff_hidden_eq_bot (φ : Dynamics V) (k : ℕ) :
    closure φ k = diagonalSubmodule (V := V) ↔ hidden φ k = ⊥ := by
  constructor
  · intro hM
    apply le_antisymm
    · intro x hxH
      have hxD : x ∈ diagonalSubmodule (V := V) := by
        rw [← hM]
        exact hidden_le_closure (V := V) φ k hxH
      have hfix := delta_eq_self_of_mem_diagonalSubmodule (V := V) hxD
      have hzero : delta (V := V) x = 0 :=
        hidden_le_OffDiag (V := V) φ k hxH
      rw [hfix] at hzero
      exact hzero
    · exact bot_le
  · intro hH
    rw [closure_eq_sup_diagonal_hidden (V := V) φ k, hH, sup_bot_eq]

/-- Preservation of `D` is exactly vanishing of the first hidden defect.
@isnad1 id=iff.0h2v.s6.e1ebd4ee84bc from=translated src=- shape=9d32dd9a vocab=479062a4
-/
theorem preservesDiagonal_iff_hidden_one_eq_bot (φ : Dynamics V) :
    PreservesDiagonal (V := V) φ ↔ hidden φ 1 = ⊥ := by
  constructor
  · intro hφ
    exact (closure_eq_diagonal_iff_hidden_eq_bot (V := V) φ 1).1
      (closure_one_eq_diagonal_of_preservesDiagonal (V := V) φ hφ)
  · intro hH d
    have hQmem : offProjection (V := V) (φ d.1) ∈ hidden φ 1 :=
      ⟨φ d.1, map_diagonal_mem_closure_one (V := V) φ d, rfl⟩
    have hQzero : offProjection (V := V) (φ d.1) = 0 := by
      have : offProjection (V := V) (φ d.1) ∈ (⊥ : Submodule ℂ (A V)) := by
        rw [← hH]
        exact hQmem
      simpa using this
    rw [offProjection_apply] at hQzero
    have hdiag : φ d.1 = delta (V := V) (φ d.1) := sub_eq_zero.mp hQzero
    rw [hdiag]
    exact ⟨diagonalCoordinates (V := V) (φ d.1), rfl⟩

/-- B5, first-step form: dynamical non-invariance iff `H₁ ≠ 0`.
@isnad1 id=iff.0h2v.s6.e3697971080e from=translated src=- shape=724e053a vocab=479062a4
-/
theorem noninvariant_iff_hidden_one_ne_bot (φ : Dynamics V) :
    (¬ PreservesDiagonal (V := V) φ) ↔ hidden φ 1 ≠ ⊥ := by
  exact not_congr (preservesDiagonal_iff_hidden_one_eq_bot (V := V) φ)

/-- B5, Definition 4.2: nonzero hidden kernel iff the closure strictly contains `D`.
@isnad1 id=iff.0h3v.s7.cf2d64fab5cb from=translated src=- shape=af8ecfd7 vocab=281f5723
-/
theorem diagonal_lt_closure_iff_hidden_ne_bot (φ : Dynamics V) (k : ℕ) :
    diagonalSubmodule (V := V) < closure φ k ↔ hidden φ k ≠ ⊥ := by
  constructor
  · intro hlt hH
    have hEq : closure φ k = diagonalSubmodule (V := V) :=
      (closure_eq_diagonal_iff_hidden_eq_bot (V := V) φ k).2 hH
    rw [hEq] at hlt
    exact (lt_irrefl _ hlt)
  · intro hH
    refine lt_of_le_of_ne (diagonalSubmodule_le_closure φ k) ?_
    intro hEq
    apply hH
    apply (closure_eq_diagonal_iff_hidden_eq_bot (V := V) φ k).1
    exact hEq.symm

/-- The closure filtration as a bundled monotone map into the submodule lattice.-/
def closureOrderHom (φ : Dynamics V) : ℕ →o Submodule ℂ (A V) where
  toFun := closure φ
  monotone' := by
    intro i j hij
    exact closure_mono φ hij

/-- B6: finite-dimensionality forces the increasing closure filtration to stabilize.
@isnad1 id=ex.0h2v.s5.ee327a784440 from=translated src=- shape=4328da3a vocab=9de86c97
-/
theorem closure_eventually_constant (φ : Dynamics V) :
    ∃ s : ℕ, ∀ k : ℕ, s ≤ k → closure φ k = closure φ s := by
  let a : ℕ →o Submodule ℂ (A V) := closureOrderHom (V := V) φ
  obtain ⟨s, hs⟩ := WellFoundedGT.monotone_chain_condition a
  refine ⟨s, ?_⟩
  intro k hsk
  exact (hs k hsk).symm

/-- If one successive closure step is stationary, that closure is φ-invariant.
@isnad1 id=mem.2h4v.s8.36ddbc08adb1 from=translated src=- shape=a4162d97 vocab=4e474c7f
-/
theorem closure_invariant_of_succ_eq (φ : Dynamics V) {s : ℕ}
    (hstable : closure φ (s + 1) = closure φ s) :
    ∀ x ∈ closure φ s, φ x ∈ closure φ s := by
  intro x hx
  have hmap : (closure φ s).map φ ≤ closure φ (s + 1) := by
    rw [closure_succ]
    exact le_sup_right
  have hxmap : φ x ∈ (closure φ s).map φ := ⟨x, hx, rfl⟩
  have hxnext : φ x ∈ closure φ (s + 1) := hmap hxmap
  rw [hstable] at hxnext
  exact hxnext

/-- Any φ-invariant subspace containing D contains every finite closure M_k.
@isnad1 id=le.2h4v.s8.095debb606d0 from=translated src=- shape=57cc4e7e vocab=9ae7e14d
-/
theorem closure_le_of_diagonal_le_of_invariant (φ : Dynamics V)
    (S : Submodule ℂ (A V))
    (hD : diagonalSubmodule (V := V) ≤ S)
    (hInv : ∀ x ∈ S, φ x ∈ S)
    (k : ℕ) :
    closure φ k ≤ S := by
  apply Submodule.span_le.mpr
  rintro x ⟨d, l, hl, rfl⟩
  have hiter : ∀ n : ℕ, (φ ^ n) d.1 ∈ S := by
    intro n
    induction n with
    | zero =>
        simpa using hD d.property
    | succ n ih =>
        simpa [pow_succ'] using hInv ((φ ^ n) d.1) ih
  exact hiter l

/-- B6, packaged form: some finite closure is stationary thereafter and φ-invariant.
@isnad1 id=ex.0h2v.s8.0802e58912f0 from=translated src=- shape=7131f547 vocab=45d99f7f
-/
theorem exists_stable_invariant_closure (φ : Dynamics V) :
    ∃ s : ℕ,
      (∀ k : ℕ, s ≤ k → closure φ k = closure φ s) ∧
      (∀ x ∈ closure φ s, φ x ∈ closure φ s) := by
  obtain ⟨s, hs⟩ := closure_eventually_constant (V := V) φ
  refine ⟨s, hs, ?_⟩
  apply closure_invariant_of_succ_eq (V := V) φ
  exact hs (s + 1) (Nat.le_succ s)

/-- A stabilized closure is the minimal φ-invariant subspace containing D.
@isnad1 id=le.2h4v.s8.66bcddde112f from=translated src=- shape=d3fc338a vocab=9ae7e14d
-/
theorem stable_closure_minimal (φ : Dynamics V) {s : ℕ}
    (S : Submodule ℂ (A V))
    (hD : diagonalSubmodule (V := V) ≤ S)
    (hInv : ∀ x ∈ S, φ x ∈ S) :
    closure φ s ≤ S := by
  exact closure_le_of_diagonal_le_of_invariant (V := V) φ S hD hInv s

end Closure

end P3
