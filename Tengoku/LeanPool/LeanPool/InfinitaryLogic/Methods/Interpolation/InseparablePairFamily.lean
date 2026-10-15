/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Tengoku.LeanPool.LeanPool.InfinitaryLogic.Methods.Henkin.CountableCompletion.GeneratedUniverse
public import Tengoku.LeanPool.LeanPool.InfinitaryLogic.Methods.Interpolation.Inseparability
import Tengoku.LeanPool.LeanPool.InfinitaryLogic.Methods.Interpolation.QuantifierRoundTrip
/-!
# The finite inseparable-pair consistency family and its structural lemmas (issue #8, commit 4a)

This file assembles the **consistency family** whose members will be packaged, in commit 4b,
into a `ConsistencyPropertyEqOn` instance driving the fair Henkin enumeration of the Craig
interpolation argument (`docs/craig-audit.md` §7–§8).

A *family member* over a fixed shared vocabulary `(F, R)`, right-hand side `Δ`, and enumeration
roots `r₁, r₂` is a **finite** set `Γ` of `L[[ℕ]]`-sentences drawn from the generated universe
`GenU r₁ r₂` that is inseparable from `Δ` at some finite allowed support `A` (`InsepAt F R A Γ Δ`).

The bulk of the file proves the *structural closure lemmas* — one per
`ConsistencyPropertyEqOn` field — showing that each syntactic decomposition step (the
propositional `C0`–`C4` rules, the `L_{ω₁ω}` conjunction/disjunction component rules, the atomic
equality/congruence rules, universal instantiation, and the fresh-witness rule for negated
universals) preserves family membership. These are the exact obligations the consistency-property
packaging will discharge.

The two moving parts are:
* the underlying `InsepAt`-level closures (`insepAt_*`), which certify that inseparability
  survives each decomposition — built on the consequence-preservation workhorse
  `insepAt_insert_of_entails` and a handful of propositional/atomic validities; and
* the family-level closures (`insepFamily_*`), which additionally track `GenU`-membership (via the
  `GeneratedUniverse` reachability lemmas) and finiteness (via `Set.Finite.insert`).
-/

@[expose] public section

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-! ## Base-symbol / constant-support union bounds

The separators built in the `InsepAt` closures are combinations (`iSup`, `imp`, `falsum`) of the
component separators; these lemmas bound their base symbols and constant support by the
components'. -/

/--
@isnad1 id=le.1h3v.s6.e89f2e38a32c from=translated src=- shape=d1181574 vocab=1c929533
-/
theorem baseFunctionsIn_iSup_subset {A : Set (Σ n, L.Functions n)}
    (σ : ℕ → L[[ℕ]].Sentenceω) (h : ∀ k, (σ k).baseFunctionsIn ⊆ A) :
    (BoundedFormulaω.iSup σ).baseFunctionsIn ⊆ A := by
  intro s hs
  simp only [BoundedFormulaω.baseFunctionsIn, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq,
    Set.mem_iUnion] at hs
  obtain ⟨k, hk⟩ := hs; exact h k hk

/--
@isnad1 id=le.1h3v.s6.8546ac98de5a from=translated src=- shape=d1181574 vocab=51f8cc38
-/
theorem baseRelationsIn_iSup_subset {A : Set (Σ n, L.Relations n)}
    (σ : ℕ → L[[ℕ]].Sentenceω) (h : ∀ k, (σ k).baseRelationsIn ⊆ A) :
    (BoundedFormulaω.iSup σ).baseRelationsIn ⊆ A := by
  intro s hs
  simp only [BoundedFormulaω.baseRelationsIn, BoundedFormulaω.relationsIn, Set.mem_ofPred_eq,
    Set.mem_iUnion] at hs
  obtain ⟨k, hk⟩ := hs; exact h k hk

/--
@isnad1 id=le.1h3v.s5.4365be4ae711 from=translated src=- shape=9ac639d7 vocab=1f1aeca1
-/
theorem sentenceJConsts_iSup_subset {A : Set ℕ}
    (σ : ℕ → L[[ℕ]].Sentenceω) (h : ∀ k, sentenceJConsts (L' := L) (J := ℕ) (σ k) ⊆ A) :
    sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.iSup σ) ⊆ A := by
  intro j hj
  simp only [sentenceJConsts, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq, Set.mem_iUnion] at hj
  obtain ⟨k, hk⟩ := hj; exact h k hk

/--
@isnad1 id=le.2h4v.s6.64cba39d1534 from=translated src=- shape=4b44de33 vocab=cc6fa700
-/
theorem baseFunctionsIn_imp_subset {A : Set (Σ n, L.Functions n)} {σ₁ σ₂ : L[[ℕ]].Sentenceω}
    (h₁ : σ₁.baseFunctionsIn ⊆ A) (h₂ : σ₂.baseFunctionsIn ⊆ A) :
    (σ₁.imp σ₂).baseFunctionsIn ⊆ A := by
  intro s hs
  simp only [BoundedFormulaω.baseFunctionsIn, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq,
    Set.mem_union] at hs
  rcases hs with hs | hs
  · exact h₁ hs
  · exact h₂ hs

/--
@isnad1 id=le.2h4v.s6.0daff0efbc63 from=translated src=- shape=4b44de33 vocab=9fd600a9
-/
theorem baseRelationsIn_imp_subset {A : Set (Σ n, L.Relations n)} {σ₁ σ₂ : L[[ℕ]].Sentenceω}
    (h₁ : σ₁.baseRelationsIn ⊆ A) (h₂ : σ₂.baseRelationsIn ⊆ A) :
    (σ₁.imp σ₂).baseRelationsIn ⊆ A := by
  intro s hs
  simp only [BoundedFormulaω.baseRelationsIn, BoundedFormulaω.relationsIn, Set.mem_ofPred_eq,
    Set.mem_union] at hs
  rcases hs with hs | hs
  · exact h₁ hs
  · exact h₂ hs

/--
@isnad1 id=le.2h4v.s6.68f9f950947a from=translated src=- shape=3923e4a1 vocab=0268ca88
-/
theorem sentenceJConsts_imp_subset {A : Set ℕ} {σ₁ σ₂ : L[[ℕ]].Sentenceω}
    (h₁ : sentenceJConsts (L' := L) (J := ℕ) σ₁ ⊆ A)
    (h₂ : sentenceJConsts (L' := L) (J := ℕ) σ₂ ⊆ A) :
    sentenceJConsts (L' := L) (J := ℕ) (σ₁.imp σ₂) ⊆ A := by
  intro j hj
  simp only [sentenceJConsts, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq, Set.mem_union] at hj
  rcases hj with hj | hj
  · exact h₁ hj
  · exact h₂ hj

/--
@isnad1 id=eq.0h2v.s5.19673368bc47 from=translated src=- shape=00269e2a vocab=bc55fd02
-/
theorem baseFunctionsIn_not (φ : L[[ℕ]].Sentenceω) :
    φ.not.baseFunctionsIn = φ.baseFunctionsIn := by
  ext s
  simp only [BoundedFormulaω.baseFunctionsIn, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq,
    Set.union_empty]

/--
@isnad1 id=eq.0h2v.s5.c836ac08738c from=translated src=- shape=00269e2a vocab=ec4b07d4
-/
theorem baseRelationsIn_not (φ : L[[ℕ]].Sentenceω) :
    φ.not.baseRelationsIn = φ.baseRelationsIn := by
  ext s
  simp only [BoundedFormulaω.baseRelationsIn, BoundedFormulaω.relationsIn, Set.mem_ofPred_eq,
    Set.union_empty]

/--
@isnad1 id=eq.0h1v.s5.0a6b20b390e0 from=translated src=- shape=7b715f35 vocab=8a69f12b
-/
theorem baseFunctionsIn_falsum :
    (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).baseFunctionsIn = ∅ := by
  ext s
  simp only [BoundedFormulaω.baseFunctionsIn, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false]

/--
@isnad1 id=eq.0h1v.s5.b0af1f556d73 from=translated src=- shape=7b715f35 vocab=6b9196b8
-/
theorem baseRelationsIn_falsum :
    (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).baseRelationsIn = ∅ := by
  ext s
  simp only [BoundedFormulaω.baseRelationsIn, BoundedFormulaω.relationsIn, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false]

/--
@isnad1 id=eq.0h1v.s4.1578b788c4f1 from=translated src=- shape=83ec2b24 vocab=d0902c09
-/
theorem sentenceJConsts_falsum :
    sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω) = ∅ := by
  ext j
  simp only [sentenceJConsts, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false]

/-! ## The consequence-preservation workhorse and semantic validities -/

/-- **Consequence preservation**: adding an entailed sentence to `Γ` cannot break inseparability,
because the separator's `Γ`-entailment survives a cut.
@isnad1 id=insepat.2h7v.s6.a4bd3933119b from=translated src=- shape=ea5f223c vocab=7c9ff8f6
-/
theorem insepAt_insert_of_entails {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    {A : Finset ℕ} {Γ Δ : Set L[[ℕ]].Sentenceω} {φ : L[[ℕ]].Sentenceω}
    (hcons : Theoryω.Entails Γ φ) (h : InsepAt F R A Γ Δ) : InsepAt F R A (insert φ Γ) Δ := by
  rintro ⟨σ, hbf, hbr, hsupp, hΓφσ, hΔσ⟩
  exact h ⟨σ, hbf, hbr, hsupp, Theoryω.Entails.cut hcons hΓφσ, hΔσ⟩

/-- A membership fact plus a pointwise validity yields a `Γ`-entailment.
@isnad1 id=entails.2h4v.s5.66f903c27e06 from=translated src=- shape=790bccf4 vocab=d3e8d44d
-/
theorem entails_of_mem_of_entails {Γ : Set L[[ℕ]].Sentenceω} {σ τ : L[[ℕ]].Sentenceω}
    (hmem : σ ∈ Γ) (hval : Sentenceω.Entails σ τ) : Theoryω.Entails Γ τ := by
  intro M _ _ hmodel
  exact hval M (by intro ρ hρ; rw [Set.mem_singleton_iff] at hρ; exact hρ ▸ hmodel σ hmem)

/--
@isnad1 id=entails.0h3v.s5.fd3bee587480 from=translated src=- shape=03f7884f vocab=6aab322c
-/
theorem negimp_entails_left (φ ψ : L[[ℕ]].Sentenceω) : Sentenceω.Entails (φ.imp ψ).not φ := by
  intro M _ _ hmodel
  have h := hmodel _ (Set.mem_singleton _)
  simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_imp,
    Classical.not_imp] at h ⊢
  exact h.1

/--
@isnad1 id=entails.0h3v.s5.db11f5f60793 from=translated src=- shape=1d836f41 vocab=6aab322c
-/
theorem negimp_entails_right (φ ψ : L[[ℕ]].Sentenceω) : Sentenceω.Entails (φ.imp ψ).not ψ.not := by
  intro M _ _ hmodel
  have h := hmodel _ (Set.mem_singleton _)
  simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_imp,
    Classical.not_imp] at h ⊢
  exact h.2

/--
@isnad1 id=entails.0h2v.s5.95ff4ed9ff8b from=translated src=- shape=cfe48d57 vocab=d3e668be
-/
theorem not_not_entails (φ : L[[ℕ]].Sentenceω) : Sentenceω.Entails φ.not.not φ := by
  intro M _ _ hmodel
  have h := hmodel _ (Set.mem_singleton _)
  simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, not_not] at h
  exact h

/--
@isnad1 id=entails.0h3v.s4.8098e71dae7c from=translated src=- shape=0b1b35f5 vocab=d6f46878
-/
theorem iInf_entails_component (φs : ℕ → L[[ℕ]].Sentenceω) (k : ℕ) :
    Sentenceω.Entails (BoundedFormulaω.iInf φs) (φs k) := by
  intro M _ _ hmodel
  have h := hmodel _ (Set.mem_singleton _)
  simp only [Sentenceω.realize_def, BoundedFormulaω.realize_iInf] at h
  exact h k

/--
@isnad1 id=entails.0h3v.s5.3fd633923767 from=translated src=- shape=ad117fed vocab=3e1113bf
-/
theorem neg_iSup_entails_neg_component (φs : ℕ → L[[ℕ]].Sentenceω) (k : ℕ) :
    Sentenceω.Entails (BoundedFormulaω.iSup φs).not (φs k).not := by
  intro M _ _ hmodel
  have h := hmodel _ (Set.mem_singleton _)
  simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iSup,
    not_exists] at h ⊢
  exact h k

/-! ## Atomic equality and relation-congruence validities

`cval M c` is the ambient interpretation of the constant `c_c`; a constant equality realizes iff
the interpretations coincide. -/

/-- The ambient interpretation of the constant `c_c` (as the realization of `constTermS c`). -/
private noncomputable def cval (M : Type) [S : L[[ℕ]].Structure M] (c : ℕ) : M :=
  (constTermS (L := L) c).realize (Sum.elim Empty.elim Fin.elim0 : Empty ⊕ Fin 0 → M)

private theorem realize_constEq (M : Type) [S : L[[ℕ]].Structure M] (a b : ℕ) :
    Sentenceω.Realize (constEq (L := L) a b) M ↔ cval (L := L) M a = cval (L := L) M b := by
  rw [constEq]; exact BoundedFormulaω.realize_equal (M := M) (constTermS a) (constTermS b)

/--
@isnad1 id=entails.0h3v.s4.228909886e1b from=translated src=- shape=1ec619a8 vocab=370a7839
-/
theorem entails_constEq_refl {Γ : Set L[[ℕ]].Sentenceω} (c : ℕ) :
    Theoryω.Entails Γ (constEq (L := L) c c) := by
  intro M _ _ _
  rw [realize_constEq]

/--
@isnad1 id=entails.1h4v.s5.e4dd004db213 from=translated src=- shape=c28b2809 vocab=41579eff
-/
theorem entails_constEq_symm {Γ : Set L[[ℕ]].Sentenceω} {a b : ℕ}
    (hmem : constEq (L := L) a b ∈ Γ) : Theoryω.Entails Γ (constEq (L := L) b a) := by
  intro M _ _ hmodel
  have h := hmodel _ hmem
  rw [realize_constEq] at h ⊢
  exact h.symm

/--
@isnad1 id=entails.2h5v.s6.5a3491d5e74b from=translated src=- shape=c9d20a35 vocab=41579eff
-/
theorem entails_constEq_trans {Γ : Set L[[ℕ]].Sentenceω} {a b d : ℕ}
    (h1 : constEq (L := L) a b ∈ Γ) (h2 : constEq (L := L) b d ∈ Γ) :
    Theoryω.Entails Γ (constEq (L := L) a d) := by
  intro M _ _ hmodel
  have hab := hmodel _ h1
  have hbd := hmodel _ h2
  rw [realize_constEq] at hab hbd ⊢
  exact hab.trans hbd

/--
@isnad1 id=entails.2h7v.s6.d7f56ec8fb5b from=translated src=- shape=4d182da9 vocab=3bb1e52e
-/
theorem entails_rel_congr {Γ : Set L[[ℕ]].Sentenceω} {l : ℕ} (Rr : L.Relations l) (g : Fin l → ℕ)
    (i : Fin l) (b : ℕ) (h1 : relInst Rr g ∈ Γ) (h2 : constEq (g i) b ∈ Γ) :
    Theoryω.Entails Γ (relInst Rr (Function.update g i b)) := by
  intro M inst _ hmodel
  have hr := hmodel _ h1
  have he := hmodel _ h2
  rw [realize_constEq] at he
  simp only [relInst, Sentenceω.realize_def] at hr ⊢
  -- `BoundedFormulaω.realize_rel` no longer fires: the goal spells the symbol as `Sum.inl Rr`,
  -- typed `L.Relations l ⊕ (constantsOn ℕ).Relations l`, so it is not type-correct at `implicit`
  -- transparency. Supplying the symbol explicitly makes the congruence term-mode.
  refine (Iff.of_eq (congrArg
    (@Structure.RelMap (L[[ℕ]]) M inst l (Sum.inl Rr)) ?_)).mpr hr
  funext j
  dsimp only
  by_cases hji : j = i
  · subst hji
    simp only [Function.update_self]
    exact he.symm
  · rw [Function.update_of_ne hji]

/-! ## Ambient universal instantiation -/

/-- Realizing the constant instance `φ(c)` in an ambient structure is realizing `φ` at the
constant's ambient interpretation. -/
private theorem realize_instConst_ambient_iff (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1)
    (M : Type) [S : L[[ℕ]].Structure M] :
    @Sentenceω.Realize L[[ℕ]] (instConst c φ) M S ↔
      @BoundedFormulaω.Realize L[[ℕ]] M S Empty 1 φ Empty.elim
        (fun _ => ambientConstMap (L := L) M c) := by
  change @BoundedFormulaω.Realize L[[ℕ]] M S Empty 0 (instConst c φ) Empty.elim Fin.elim0 ↔ _
  rw [ambient_realize_iff_wc (S := S) (instConst c φ) Empty.elim Fin.elim0, realize_instConst,
    ambient_realize_iff_wc (S := S) φ Empty.elim (fun _ => ambientConstMap (L := L) M c)]

/--
@isnad1 id=entails.0h3v.s5.eb66b731912f from=translated src=- shape=2c76d471 vocab=df970009
-/
theorem all_entails_instConst (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1) :
    Sentenceω.Entails φ.all (instConst c φ) := by
  intro M S _ hmodel
  have hall : @BoundedFormulaω.Realize L[[ℕ]] M S Empty 0 φ.all Empty.elim Fin.elim0 :=
    hmodel _ (Set.mem_singleton _)
  rw [BoundedFormulaω.realize_all] at hall
  change @Sentenceω.Realize L[[ℕ]] (instConst c φ) M S
  rw [realize_instConst_ambient_iff]
  have hx := hall (ambientConstMap (L := L) M c)
  have hsnoc : (Fin.snoc Fin.elim0 (ambientConstMap (L := L) M c) : Fin 1 → M)
      = (fun _ => ambientConstMap (L := L) M c) := funext fun i => by simp [Fin.snoc, Fin.eq_zero i]
  rwa [hsnoc] at hx

/-! ## `InsepAt`-level closures under the decomposition rules -/

/-- **C4 (disjunction)**: a disjunction in `Γ` splits off a component preserving inseparability.
@isnad1 id=ex.2h7v.s6.b5283db3206e from=translated src=- shape=0067c6ab vocab=f366d381
-/
theorem insepAt_iSup_component {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    {A : Finset ℕ} {Γ Δ : Set L[[ℕ]].Sentenceω}
    (φs : ℕ → L[[ℕ]].Sentenceω) (hmem : BoundedFormulaω.iSup φs ∈ Γ)
    (h : InsepAt F R A Γ Δ) : ∃ k, InsepAt F R A (insert (φs k) Γ) Δ := by
  by_contra hcon
  push Not at hcon
  simp only [InsepAt, not_not] at hcon
  choose σ hbf hbr hsupp hΓσ hΔσ using hcon
  refine h ⟨BoundedFormulaω.iSup σ, baseFunctionsIn_iSup_subset σ hbf,
    baseRelationsIn_iSup_subset σ hbr, sentenceJConsts_iSup_subset σ hsupp, ?_, ?_⟩
  · intro M _ _ hmodel
    have hsup := hmodel _ hmem
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_iSup] at hsup ⊢
    obtain ⟨k, hk⟩ := hsup
    exact ⟨k, hΓσ k M (by
      intro ρ hρ
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · exact hk
      · exact hmodel ρ hρ)⟩
  · intro M _ _ hmodel
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iSup,
      not_exists]
    intro k
    have hk := hΔσ k M hmodel
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hk
    exact hk

/-- **C3' (negated conjunction)**: a negated conjunction in `Γ` splits off a negated component.
@isnad1 id=ex.2h7v.s7.787a33b9d7c8 from=translated src=- shape=01322ae6 vocab=2a075965
-/
theorem insepAt_neg_iInf_component {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    {A : Finset ℕ} {Γ Δ : Set L[[ℕ]].Sentenceω}
    (φs : ℕ → L[[ℕ]].Sentenceω) (hmem : (BoundedFormulaω.iInf φs).not ∈ Γ)
    (h : InsepAt F R A Γ Δ) : ∃ k, InsepAt F R A (insert (φs k).not Γ) Δ := by
  by_contra hcon
  push Not at hcon
  simp only [InsepAt, not_not] at hcon
  choose σ hbf hbr hsupp hΓσ hΔσ using hcon
  refine h ⟨BoundedFormulaω.iSup σ, baseFunctionsIn_iSup_subset σ hbf,
    baseRelationsIn_iSup_subset σ hbr, sentenceJConsts_iSup_subset σ hsupp, ?_, ?_⟩
  · intro M _ _ hmodel
    have hnotinf := hmodel _ hmem
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iInf,
      not_forall] at hnotinf
    obtain ⟨k, hk⟩ := hnotinf
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_iSup]
    exact ⟨k, hΓσ k M (by
      intro ρ hρ
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not]; exact hk
      · exact hmodel ρ hρ)⟩
  · intro M _ _ hmodel
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iSup,
      not_exists]
    intro k
    have hk := hΔσ k M hmodel
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hk
    exact hk

/-- **C1 (implication)**: an implication in `Γ` yields one of the two possible refinements.
@isnad1 id=or.2h8v.s7.124c66ad1717 from=translated src=- shape=c49cc915 vocab=53b96b83
-/
theorem insepAt_imp_dichotomy {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    {A : Finset ℕ} {Γ Δ : Set L[[ℕ]].Sentenceω} {φ ψ : L[[ℕ]].Sentenceω}
    (hmem : φ.imp ψ ∈ Γ) (h : InsepAt F R A Γ Δ) :
    InsepAt F R A (insert φ.not Γ) Δ ∨ InsepAt F R A (insert ψ Γ) Δ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [InsepAt, not_not] at h1 h2
  obtain ⟨σ₁, hbf₁, hbr₁, hsupp₁, hΓσ₁, hΔσ₁⟩ := h1
  obtain ⟨σ₂, hbf₂, hbr₂, hsupp₂, hΓσ₂, hΔσ₂⟩ := h2
  apply h
  refine ⟨(σ₁.not).imp σ₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact baseFunctionsIn_imp_subset (by rw [baseFunctionsIn_not]; exact hbf₁) hbf₂
  · exact baseRelationsIn_imp_subset (by rw [baseRelationsIn_not]; exact hbr₁) hbr₂
  · exact sentenceJConsts_imp_subset (by rw [sentenceJConsts_not]; exact hsupp₁) hsupp₂
  · intro M _ _ hmodel
    have himp := hmodel _ hmem
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_imp] at himp
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_imp, BoundedFormulaω.realize_not]
    intro hnσ₁
    by_cases hφ : BoundedFormulaω.Realize φ (Empty.elim : Empty → M) Fin.elim0
    · exact hΓσ₂ M (by
        intro ρ hρ
        rcases Set.mem_insert_iff.mp hρ with rfl | hρ
        · exact himp hφ
        · exact hmodel ρ hρ)
    · exact absurd (hΓσ₁ M (by
        intro ρ hρ
        rcases Set.mem_insert_iff.mp hρ with rfl | hρ
        · simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not]; exact hφ
        · exact hmodel ρ hρ)) hnσ₁
  · intro M _ _ hmodel
    have h1' := hΔσ₁ M hmodel
    have h2' := hΔσ₂ M hmodel
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_imp]
      at h1' h2' ⊢
    intro hf
    exact h2' (hf h1')

/-- **C0 (falsum)**: `⊥ ∈ Γ` is incompatible with inseparability (`⊥` separates from anything).
@isnad1 id=false.2h6v.s6.eb1043cfc839 from=translated src=- shape=0f824112 vocab=2c948673
-/
theorem insepAt_falsum_absurd {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    {A : Finset ℕ} {Γ Δ : Set L[[ℕ]].Sentenceω}
    (hmem : (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω) ∈ Γ) (h : InsepAt F R A Γ Δ) : False := by
  apply h
  refine ⟨BoundedFormulaω.falsum, ?_, ?_, ?_, ?_, ?_⟩
  · rw [baseFunctionsIn_falsum]; exact Set.empty_subset _
  · rw [baseRelationsIn_falsum]; exact Set.empty_subset _
  · rw [sentenceJConsts_falsum]; exact Set.empty_subset _
  · exact Theoryω.entails_of_mem hmem
  · intro M _ _ _
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_falsum,
      not_false_eq_true]

/-- A sentence and its negation both in `Γ` is incompatible with inseparability.
@isnad1 id=false.3h7v.s6.5132cadd8d1e from=translated src=- shape=b8d4e0b3 vocab=2c7b4d9b
-/
theorem insepAt_contradiction_absurd {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    {A : Finset ℕ} {Γ Δ : Set L[[ℕ]].Sentenceω} {φ : L[[ℕ]].Sentenceω}
    (h1 : φ ∈ Γ) (h2 : φ.not ∈ Γ) (h : InsepAt F R A Γ Δ) : False := by
  apply h
  refine ⟨BoundedFormulaω.falsum, ?_, ?_, ?_, ?_, ?_⟩
  · rw [baseFunctionsIn_falsum]; exact Set.empty_subset _
  · rw [baseRelationsIn_falsum]; exact Set.empty_subset _
  · rw [sentenceJConsts_falsum]; exact Set.empty_subset _
  · intro M _ _ hmodel
    have hφ := hmodel _ h1
    have hnφ := hmodel _ h2
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hnφ
    exact absurd hφ hnφ
  · intro M _ _ _
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_falsum,
      not_false_eq_true]

/-! ## The constant-instance negation identity

The fresh-witness rule produces `instConst c φ.not`; the family field wants `(instConst c φ).not`.
These are literally the same formula (`openBounds` and `subst` distribute over `· .imp ⊥`). -/

/--
@isnad1 id=eq.0h3v.s5.64fd9aa730f1 from=translated src=- shape=ebb114f9 vocab=f363713b
-/
theorem instConst_not (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1) :
    instConst c φ.not = (instConst c φ).not := rfl

/-! ## The finite inseparable-pair consistency family -/

variable {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
  {Δ Γ : Set L[[ℕ]].Sentenceω} {r₁ r₂ : L[[ℕ]].Sentenceω}

/-! ## The family closure lemmas (one per `ConsistencyPropertyEqOn` field) -/

end FirstOrder.Language
