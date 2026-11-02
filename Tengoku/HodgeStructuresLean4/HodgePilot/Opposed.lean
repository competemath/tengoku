import Tengoku.HodgeStructuresLean4.HodgePilot.Filtration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Opposed filtrations and the converse construction

**Theorem 3** (`OpposedFiltration.toQHodgeStructure`): a decreasing,
exhaustive filtration `F` on `ℂ ⊗[ℚ] V` that is `n`-opposed to its conjugate
(Deligne, Théorie de Hodge II, §1.2) determines a pure Hodge structure of
weight `n` with pieces `H^{p,q} = F^p ∩ σ(F^q)`.

Together with Theorem 1 (`H_eq_filtration_inf_conj`) and Theorem 2
(`isCompl_filtration_conj`) of `Filtration.lean`, this completes the
equivalence between the decomposition and filtration presentations of a pure
Hodge structure.

The proof is element-free lattice theory: independence of the pieces is two
applications of the modular law (`sup_inf_assoc_of_le`) plus opposedness,
and spanning is a descending induction along the one-step splitting
`F^p = (F^p ⊓ σF^{n-p}) ⊔ F^{p+1}`. -/

open scoped TensorProduct

noncomputable section

namespace HodgePilot

variable {n : ℤ} {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-! ### Two more facts about `σ` -/

theorem sigmaQ_injective (V : Type*) [AddCommGroup V] [Module ℚ V] :
    Function.Injective (sigmaQ V) :=
  Function.Involutive.injective (sigmaQ_sigmaQ V)

/-- Applying `σ` twice to a submodule returns the submodule.-/
@[simp] theorem map_sigmaQ_map_sigmaQ (V : Type*) [AddCommGroup V]
    [Module ℚ V] (S : Submodule ℂ (ℂ ⊗[ℚ] V)) :
    (S.map (sigmaQ V)).map (sigmaQ V) = S := by
  ext x
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rw [sigmaQ_sigmaQ]
    exact hz
  · intro hx
    exact ⟨sigmaQ V x, ⟨x, hx, rfl⟩, sigmaQ_sigmaQ V x⟩

/-! ### Opposed filtrations -/

/-- A decreasing, exhaustive, `n`-opposed filtration on `ℂ ⊗[ℚ] V`: the
filtration-side presentation of a pure Hodge structure of weight `n`
(Deligne, Théorie de Hodge II, §1.2).-/
structure OpposedFiltration (n : ℤ) (V : Type*) [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] where
  F : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  antitone : Antitone F
  exhaustive_top : ∃ a, F a = ⊤
  exhaustive_bot : ∃ b, F b = ⊥
  opposed : ∀ p q : ℤ, p + q = n + 1 → IsCompl (F p) ((F q).map (sigmaQ V))

namespace OpposedFiltration

variable (Φ : OpposedFiltration n V)

/-- The candidate Hodge pieces: `H^{p,q} = F^p ⊓ σ(F^q)` on the weight-`n`
antidiagonal, `⊥` elsewhere.-/
def piece (pq : ℤ × ℤ) : Submodule ℂ (ℂ ⊗[ℚ] V) :=
  if pq.1 + pq.2 = n then Φ.F pq.1 ⊓ (Φ.F pq.2).map (sigmaQ V) else ⊥

theorem piece_of_ne (pq : ℤ × ℤ) (h : pq.1 + pq.2 ≠ n) : Φ.piece pq = ⊥ :=
  ite_eq_right h

theorem piece_of_eq (p q : ℤ) (h : p + q = n) :
    Φ.piece (p, q) = Φ.F p ⊓ (Φ.F q).map (sigmaQ V) :=
  ite_eq_left h

theorem piece_le_F (p q : ℤ) (h : p + q = n) : Φ.piece (p, q) ≤ Φ.F p := by
  rw [Φ.piece_of_eq p q h]
  exact inf_le_left

theorem piece_le_conj (p q : ℤ) (h : p + q = n) :
    Φ.piece (p, q) ≤ (Φ.F q).map (sigmaQ V) := by
  rw [Φ.piece_of_eq p q h]
  exact inf_le_right

/-- The crux disjointness, by pure modular-lattice algebra: for `p + q = n`,
`(F^p ⊓ σF^q) ⊓ (F^{p+1} ⊔ σF^{q+1}) = ⊥`. Both opposedness hypotheses at
level `n + 1` enter once each.-/
theorem inf_step (p q : ℤ) (hpq : p + q = n) :
    (Φ.F p ⊓ (Φ.F q).map (sigmaQ V)) ⊓
      (Φ.F (p + 1) ⊔ (Φ.F (q + 1)).map (sigmaQ V)) = ⊥ := by
  set A := Φ.F p
  set A' := Φ.F (p + 1)
  set B := (Φ.F q).map (sigmaQ V)
  set B' := (Φ.F (q + 1)).map (sigmaQ V)
  have hA'B : A' ⊓ B = ⊥ :=
    disjoint_iff.mp (Φ.opposed (p + 1) q (by omega)).disjoint
  have hAB' : A ⊓ B' = ⊥ :=
    disjoint_iff.mp (Φ.opposed p (q + 1) (by omega)).disjoint
  have hB'B : B' ≤ B := Submodule.map_mono (Φ.antitone (by omega))
  calc (A ⊓ B) ⊓ (A' ⊔ B')
      = A ⊓ ((B' ⊔ A') ⊓ B) := by
        rw [inf_assoc, inf_comm B (A' ⊔ B'), sup_comm A' B']
    _ = A ⊓ (B' ⊔ A' ⊓ B) := by rw [sup_inf_assoc_of_le _ hB'B]
    _ = A ⊓ B' := by rw [hA'B, sup_bot_eq]
    _ = ⊥ := hAB'

/-- The one-step splitting of the filtration: for any `p`,
`F^p = (F^p ⊓ σF^{n-p}) ⊔ F^{p+1}` — the top Hodge piece splits off, by the
modular law and opposedness at `(p+1) + (n-p) = n+1`.-/
theorem F_eq_piece_sup_succ (p : ℤ) :
    Φ.F p = (Φ.F p ⊓ (Φ.F (n - p)).map (sigmaQ V)) ⊔ Φ.F (p + 1) := by
  set A := Φ.F p
  set A' := Φ.F (p + 1)
  set B := (Φ.F (n - p)).map (sigmaQ V)
  have htop : A' ⊔ B = ⊤ :=
    codisjoint_iff.mp (Φ.opposed (p + 1) (n - p) (by omega)).codisjoint
  have hA'A : A' ≤ A := Φ.antitone (by omega)
  calc A = (A' ⊔ B) ⊓ A := by rw [htop, top_inf_eq]
    _ = A' ⊔ B ⊓ A := by rw [sup_inf_assoc_of_le _ hA'A]
    _ = (A ⊓ B) ⊔ A' := by rw [inf_comm B A, sup_comm]

/-- The pieces of an opposed filtration are independent. Element-free:
the sup of all other pieces is bounded by `F^{p+1} ⊔ σF^{q+1}`, which meets
`H^{p,q}` trivially by `inf_step`.-/
theorem iSupIndep_piece : iSupIndep Φ.piece := by
  intro pq
  obtain ⟨a, b⟩ := pq
  by_cases hn : a + b = n
  · have hrest : (⨆ (pq') (_ : pq' ≠ (a, b)), Φ.piece pq') ≤
        Φ.F (a + 1) ⊔ (Φ.F (b + 1)).map (sigmaQ V) := by
      refine iSup₂_le ?_
      rintro ⟨a', b'⟩ hne
      by_cases hn' : a' + b' = n
      · rcases lt_trichotomy a' a with hlt | heq | hgt
        · refine le_sup_of_le_right ?_
          refine (Φ.piece_le_conj a' b' hn').trans (Submodule.map_mono ?_)
          exact Φ.antitone (by omega)
        · exfalso
          apply hne
          subst heq
          have : b' = b := by omega
          subst this
          rfl
        · refine le_sup_of_le_left ?_
          refine (Φ.piece_le_F a' b' hn').trans ?_
          exact Φ.antitone (by omega)
      · rw [Φ.piece_of_ne (a', b') hn']
        exact bot_le
    refine Disjoint.mono_right hrest ?_
    rw [disjoint_iff, Φ.piece_of_eq a b hn, Φ.inf_step a b hn]
  · rw [Φ.piece_of_ne (a, b) hn]
    exact disjoint_bot_left

/-- The pieces of an opposed filtration span, by descending induction along
the filtration from the exhaustion bounds.-/
theorem iSup_piece_eq_top : ⨆ pq, Φ.piece pq = ⊤ := by
  obtain ⟨a, ha⟩ := Φ.exhaustive_top
  obtain ⟨b, hb⟩ := Φ.exhaustive_bot
  have key : ∀ k : ℕ, Φ.F (b - k) ≤ ⨆ pq, Φ.piece pq := by
    intro k
    induction k with
    | zero =>
        have h0 : b - ((0 : ℕ) : ℤ) = b := by omega
        rw [h0, hb]
        exact bot_le
    | succ k ih =>
        have harg : b - ((k : ℤ) + 1) + 1 = b - (k : ℤ) := by ring
        have hstep := Φ.F_eq_piece_sup_succ (b - ((k : ℤ) + 1))
        rw [harg] at hstep
        have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
        rw [hcast, hstep]
        refine sup_le ?_ ih
        have hpiece : Φ.F (b - ((k : ℤ) + 1)) ⊓
            (Φ.F (n - (b - ((k : ℤ) + 1)))).map (sigmaQ V) =
            Φ.piece (b - ((k : ℤ) + 1), n - (b - ((k : ℤ) + 1))) :=
          (Φ.piece_of_eq _ _ (by omega)).symm
        rw [hpiece]
        exact le_iSup Φ.piece _
  refine eq_top_iff.mpr ?_
  calc (⊤ : Submodule ℂ (ℂ ⊗[ℚ] V)) = Φ.F a := ha.symm
    _ ≤ Φ.F (b - ((b - a).toNat : ℤ)) := Φ.antitone (by omega)
    _ ≤ ⨆ pq, Φ.piece pq := key _

/-- **Theorem 3** (filtration ⇒ decomposition): an exhaustive `n`-opposed
filtration determines a pure Hodge structure of weight `n`, with pieces
`H^{p,q} = F^p ⊓ σ(F^q)`. Converse of Theorems 1–2; together they show the
decomposition and opposed-filtration presentations are equivalent.-/
def toQHodgeStructure : QHodgeStructure n V where
  H := Φ.piece
  supported := fun pq hpq => Φ.piece_of_ne pq hpq
  isInternal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    exact ⟨Φ.iSupIndep_piece, Φ.iSup_piece_eq_top⟩
  conj_symm := by
    intro p q
    by_cases hpq : p + q = n
    · rw [Φ.piece_of_eq p q hpq, Φ.piece_of_eq q p (by omega),
        Submodule.map_inf _ (sigmaQ_injective V), map_sigmaQ_map_sigmaQ,
        inf_comm]
    · rw [Φ.piece_of_ne (p, q) hpq, Φ.piece_of_ne (q, p) (by omega),
        Submodule.map_bot]

@[simp] theorem toQHodgeStructure_H (pq : ℤ × ℤ) :
    Φ.toQHodgeStructure.H pq = Φ.piece pq := rfl

end OpposedFiltration

/-! ### The converse packaging and the round trip -/

/-- Two Hodge structures with the same pieces are equal (the remaining
fields are propositional).-/
theorem QHodgeStructure.ext_H {h₁ h₂ : QHodgeStructure n V}
    (hH : h₁.H = h₂.H) : h₁ = h₂ := by
  cases h₁
  cases h₂
  cases hH
  rfl

/-- The opposed filtration attached to a pure Hodge structure. Antitonicity,
opposedness (Theorem 2), and — via finite-dimensionality — exhaustiveness:
an independent family in a Noetherian module has only finitely many nonzero
members, so the filtration stabilizes at `⊤` below and `⊥` above the finite
support of the decomposition.-/
def QHodgeStructure.toOpposedFiltration (h : QHodgeStructure n V) :
    OpposedFiltration n V where
  F := h.filtration
  antitone := h.filtration_antitone
  exhaustive_top := by
    have hfin : {pq : ℤ × ℤ | h.H pq ≠ ⊥}.Finite :=
      WellFoundedGT.finite_ne_bot_of_iSupIndep
        h.isInternal.submodule_iSupIndep
    obtain ⟨a, ha⟩ := (hfin.image Prod.fst).bddBelow
    refine ⟨a, eq_top_iff.mpr ?_⟩
    rw [← h.isInternal.submodule_iSup_eq_top]
    refine iSup_le fun pq => ?_
    by_cases hpq : h.H pq = ⊥
    · rw [hpq]
      exact bot_le
    · exact le_iSup₂ (f := fun pq' (_ : a ≤ pq'.1) => h.H pq') pq
        (ha ⟨pq, hpq, rfl⟩)
  exhaustive_bot := by
    have hfin : {pq : ℤ × ℤ | h.H pq ≠ ⊥}.Finite :=
      WellFoundedGT.finite_ne_bot_of_iSupIndep
        h.isInternal.submodule_iSupIndep
    obtain ⟨B, hB⟩ := (hfin.image Prod.fst).bddAbove
    refine ⟨B + 1, ?_⟩
    rw [show h.filtration (B + 1)
        = ⨆ (pq : ℤ × ℤ) (_ : B + 1 ≤ pq.1), h.H pq from rfl]
    refine iSup_eq_bot.mpr fun pq => iSup_eq_bot.mpr fun hpq => ?_
    by_contra hne
    exact absurd (hB ⟨pq, hne, rfl⟩) (by omega)
  opposed := fun _ _ hpq => h.isCompl_filtration_conj hpq

/-- **The round trip**: passing from a pure Hodge structure to its opposed
filtration and back recovers the Hodge structure on the nose. This is
Theorem 1 speaking through the two constructions: the decomposition and
opposed-filtration presentations carry the same data.-/
theorem QHodgeStructure.toOpposedFiltration_toQHodgeStructure
    (h : QHodgeStructure n V) :
    h.toOpposedFiltration.toQHodgeStructure = h := by
  refine QHodgeStructure.ext_H (funext fun pq => ?_)
  obtain ⟨p, q⟩ := pq
  by_cases hpq : p + q = n
  · rw [OpposedFiltration.toQHodgeStructure_H,
      OpposedFiltration.piece_of_eq _ p q hpq]
    exact (h.H_eq_filtration_inf_conj hpq).symm
  · rw [OpposedFiltration.toQHodgeStructure_H,
      OpposedFiltration.piece_of_ne _ (p, q) hpq]
    exact (h.supported (p, q) hpq).symm

/-! ### The filtration-side round trip -/

namespace OpposedFiltration

variable (Φ : OpposedFiltration n V)

/-- Two opposed filtrations with the same underlying filtration are equal
(the remaining fields are propositional).-/
theorem ext_F {Φ₁ Φ₂ : OpposedFiltration n V} (hF : Φ₁.F = Φ₂.F) :
    Φ₁ = Φ₂ := by
  cases Φ₁
  cases Φ₂
  cases hF
  rfl

theorem filtration_le_F (p : ℤ) :
    Φ.toQHodgeStructure.filtration p ≤ Φ.F p := by
  rw [show Φ.toQHodgeStructure.filtration p
      = ⨆ (pq : ℤ × ℤ) (_ : p ≤ pq.1), Φ.piece pq from rfl]
  refine iSup₂_le ?_
  rintro ⟨a, b⟩ hpa
  by_cases hn : a + b = n
  · exact (Φ.piece_le_F a b hn).trans (Φ.antitone hpa)
  · rw [Φ.piece_of_ne (a, b) hn]
    exact bot_le

theorem F_le_filtration (p : ℤ) :
    Φ.F p ≤ Φ.toQHodgeStructure.filtration p := by
  rw [show Φ.toQHodgeStructure.filtration p
      = ⨆ (pq : ℤ × ℤ) (_ : p ≤ pq.1), Φ.piece pq from rfl]
  obtain ⟨b, hb⟩ := Φ.exhaustive_bot
  have key : ∀ k : ℕ, Φ.F (b - k) ≤
      ⨆ (pq : ℤ × ℤ) (_ : b - (k : ℤ) ≤ pq.1), Φ.piece pq := by
    intro k
    induction k with
    | zero =>
        have h0 : b - ((0 : ℕ) : ℤ) = b := by norm_num
        rw [h0, hb]
        exact bot_le
    | succ k ih =>
        have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
        rw [hcast]
        have hstep := Φ.F_eq_piece_sup_succ (b - ((k : ℤ) + 1))
        have harg : b - ((k : ℤ) + 1) + 1 = b - (k : ℤ) := by ring
        rw [harg] at hstep
        rw [hstep]
        refine sup_le ?_ (ih.trans (iSup₂_le fun pq hpq =>
          le_iSup₂ (f := fun pq' (_ : b - ((k : ℤ) + 1) ≤ pq'.1) => Φ.piece pq')
            pq (by omega)))
        rw [(Φ.piece_of_eq (b - ((k : ℤ) + 1)) (n - (b - ((k : ℤ) + 1)))
          (by omega)).symm]
        exact le_iSup₂
          (f := fun pq' (_ : b - ((k : ℤ) + 1) ≤ pq'.1) => Φ.piece pq')
          (b - ((k : ℤ) + 1), n - (b - ((k : ℤ) + 1))) le_rfl
  by_cases hpb : p ≤ b
  · have hk := key (b - p).toNat
    rw [show b - (((b - p).toNat : ℕ) : ℤ) = p from by omega] at hk
    exact hk
  · refine le_trans (Φ.antitone (by omega : b ≤ p)) ?_
    rw [hb]
    exact bot_le

/-- The filtration of the Hodge structure built from an opposed filtration
is the original filtration.-/
theorem filtration_toQHodgeStructure (p : ℤ) :
    Φ.toQHodgeStructure.filtration p = Φ.F p :=
  le_antisymm (Φ.filtration_le_F p) (Φ.F_le_filtration p)

/-- **The filtration-side round trip**: the two constructions are mutually
inverse. Together with `toOpposedFiltration_toQHodgeStructure`, the
decomposition and opposed-filtration presentations of a pure Hodge structure
are equivalent in the strongest sense.-/
theorem toQHodgeStructure_toOpposedFiltration :
    Φ.toQHodgeStructure.toOpposedFiltration = Φ :=
  ext_F (funext fun p => Φ.filtration_toQHodgeStructure p)

end OpposedFiltration

end HodgePilot
