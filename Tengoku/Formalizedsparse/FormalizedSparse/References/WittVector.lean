/-
Copyright (c) 2025 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Yijun Yuan
-/
module

public import Tengoku.Formalizedsparse.FormalizedSparse.References.Miscellaneous
public import Tengoku.Seed.Analysis.Normed.Field.WithAbs
public import Tengoku.Seed.NumberTheory.Padics.Complex
public import Tengoku.Seed.RingTheory.AdicCompletion.Topology
public import Tengoku.Seed.RingTheory.DedekindDomain.AdicValuation
public import Tengoku.Seed.RingTheory.Valuation.Discrete.Basic
public import Tengoku.Seed.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Tengoku.Seed.RingTheory.Valuation.Discrete.RankOne
public import Tengoku.Seed.RingTheory.WittVector.Compare
public import Tengoku.Seed.RingTheory.WittVector.Complete
public import Tengoku.Seed.RingTheory.WittVector.DiscreteValuationRing
public import Tengoku.Seed.RingTheory.WittVector.Teichmuller
public import Tengoku.Seed.Topology.Algebra.Nonarchimedean.AdicTopology
public import Tengoku.Seed.Topology.Algebra.Valued.WithVal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Completed maximal unramified extension of ℚ_[p]

This file contains our implementation of the completed maximal unramified extension of `ℚ_[p]`,
denoted `ℚᵘⁿ_[p]`. Since the ramification theory in mathlib is not yet developed, we use the Witt
vector construction:

- the algebraic closure of `𝔽ₚ` is `𝔽ᵃ_[p]`;
- `ℤᵘⁿ_[p]` is the ring of Witt vectors over `𝔽ᵃ_[p]`, i.e. the ring of integers of the maximal
  unramified extension of `ℚ_[p]`;
- `ℚᵘⁿ_[p]` is the fraction field of `ℤᵘⁿ_[p]`, equipped with the topology induced by the valuation
  corresponding to the unique maximal ideal of `ℤᵘⁿ_[p]`.

## Main definitions

- `FormalizedSparse.Fpbar` (`𝔽ᵃ_[p]`): the algebraic closure of `𝔽ₚ`.
- `FormalizedSparse.OQpUn` (`ℤᵘⁿ_[p]`): the Witt vectors over `𝔽ᵃ_[p]`.
- `FormalizedSparse.QpUn` (`ℚᵘⁿ_[p]`): the fraction field of `ℤᵘⁿ_[p]` with its valuation topology.
- `FormalizedSparse.QpUn.Qp_embd`: the valuation-preserving embedding `ℚ_[p] → ℚᵘⁿ_[p]`.

## Main statements

- `FormalizedSparse.injective_teichmuller`: the Teichmüller lift `𝔽ᵃ_[p] → ℤᵘⁿ_[p]` is injective.
- `FormalizedSparse.QpUn.Qp_embd_keep_val`: the embedding `ℚ_[p] → ℚᵘⁿ_[p]` preserves the valuation.
- The valuation on `ℚᵘⁿ_[p]` is rank-one discrete, making `ℚᵘⁿ_[p]` a complete nontrivially normed
  field. These are standard facts of algebraic number theory, so the proofs are only lightly
  commented.

## Notation

- `𝔽ᵃ_[p]`, `ℤᵘⁿ_[p]`, `ℚᵘⁿ_[p]` for the three objects above.

## Tags

p-adic, Witt vector, unramified extension, valuation
-/

@[expose] public section

namespace FormalizedSparse

open WittVector

/-- The algebraic closure `𝔽ᵃ_[p]` of the finite field `𝔽ₚ`.-/
abbrev Fpbar (p : ℕ) [Fact (Nat.Prime p)] := AlgebraicClosure (ZMod p)
@[inherit_doc] scoped notation "𝔽ᵃ_[" p "]" => Fpbar p

/-- The ring of integers `ℤᵘⁿ_[p]` of the completed maximal unramified extension of `ℚ_[p]`,
realized as the Witt vectors `W(𝔽ᵃ_[p])`.-/
abbrev OQpUn (p : ℕ) [Fact (Nat.Prime p)] := WittVector p (Fpbar p)
@[inherit_doc] scoped notation "ℤᵘⁿ_[" p "]" => OQpUn p

/-- The completed maximal unramified extension `ℚᵘⁿ_[p]` of `ℚ_[p]`, defined as the fraction field
of `ℤᵘⁿ_[p]` equipped with the topology induced by the valuation of its maximal ideal.-/
abbrev QpUn (p : ℕ) [Fact (Nat.Prime p)] :=
  WithVal ((IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).valuation ((FractionRing (ℤᵘⁿ_[p]))))
@[inherit_doc] scoped notation "ℚᵘⁿ_[" p "]" => QpUn p

/-- The Teichmüller lift `𝔽ᵃ_[p] → ℤᵘⁿ_[p]` is injective.
@isnad1 id=injectiv.0h1v.s7.8e3609b22aaa from=translated src=- shape=a5a78327 vocab=bb6aba47
-/
theorem injective_teichmuller (p : ℕ) [Fact (Nat.Prime p)] :
    Function.Injective (teichmuller p : 𝔽ᵃ_[p] → ℤᵘⁿ_[p]) := by
  intro a b hab
  simp only [teichmuller, MonoidHom.coe_mk, OneHom.coe_mk, teichmullerFun, mk'.injEq] at hab
  apply_fun (fun x => x 0) at hab
  simpa

namespace QpUn

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
  Valued (ℚᵘⁿ_[p]) (WithZero (Multiplicative ℤ)) := inferInstance

/-- The valuation `Valued.v` of the image of `r : ℤᵘⁿ_[p]` in `ℚᵘⁿ_[p]` equals the `intValuation`
of `r`. Since `WithVal` is a structure in this mathlib version, `Valued.v` is the `comap` of the
base valuation along `WithVal.equiv`; this lemma packages that bridge once for all proofs below.
@isnad1 id=eq.0h2v.s11.d5d751c1c734 from=translated src=- shape=41f5485b vocab=9baceee8
-/
theorem valued_algebraMap (p : ℕ) [Fact (Nat.Prime p)] (r : ℤᵘⁿ_[p]) :
    Valued.v (algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p]) r) =
      (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).intValuation r := by
  rw [WithVal.algebraMap_right_apply, WithVal.valued_toVal,
    (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).valuation_of_algebraMap]

-- The valuation on `ℚᵘⁿ_[p]` is rank-one discrete (transferred from the adic valuation on
-- `FractionRing ℤᵘⁿ_[p]` via the value-group equality for `WithVal`).
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
    (Valued.v : Valuation ℚᵘⁿ_[p] (WithZero (Multiplicative ℤ))).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    have h : ((IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).valuation
        (FractionRing (ℤᵘⁿ_[p]))).IsRankOneDiscrete := inferInstance
    obtain ⟨γ, hγ, hγ1⟩ := h.exists_generator_lt_one'
    exact ⟨γ, by rw [WithVal.valueGroup_eq]; exact hγ, hγ1⟩

-- The valuation on `ℚᵘⁿ_[p]` has rank one, with associated absolute value `p ^ (-v)`.
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Valuation.RankOne
    (Valued.v : Valuation ℚᵘⁿ_[p] (WithZero (Multiplicative ℤ))) :=
  Valuation.IsRankOneDiscrete.rankOne
    (v := (Valued.v : Valuation ℚᵘⁿ_[p] (WithZero (Multiplicative ℤ))))
    (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt : (1 : NNReal) < (p : NNReal))

-- The normed field structure on `ℚᵘⁿ_[p]` induced by the rank-one valuation.
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : NormedField ℚᵘⁿ_[p] :=
  Valued.toNormedField (ℚᵘⁿ_[p]) (WithZero (Multiplicative ℤ))

-- ℚᵘⁿ_[p] is complete with respect to the valuation topology.
/-- The canonical ring embedding `ℚ_[p] → ℚᵘⁿ_[p]`, induced by the Teichmüller-style map
`ℤ_[p] → ℤᵘⁿ_[p]` on rings of integers and extended to fraction fields.-/
noncomputable def Qp_embd {p : ℕ} [Fact (Nat.Prime p)] : ℚ_[p] →+* ℚᵘⁿ_[p] :=
  @IsFractionRing.map ℤ_[p] ℤᵘⁿ_[p] ℚ_[p] ℚᵘⁿ_[p] _ _ _ _ _ _ _ _ _
    ((WittVector.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).comp
      (WittVector.fromPadicInt p)) (by
  simp only [RingHom.coe_comp]
  refine Function.Injective.comp ?_ ?_
  · exact WittVector.map_injective _ (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective
  · refine Function.injective_iff_hasLeftInverse.mpr ?_
    use (WittVector.toPadicInt p)
    rw [Function.leftInverse_iff_comp]; ext r
    have := toPadicInt_comp_fromPadicInt_ext p r
    simpa
  )

-- The embedding from ℚ_[p] to ℚᵘⁿ_[p] keeps the valuation.

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : NontriviallyNormedField ℚᵘⁿ_[p] :=
  Valued.toNontriviallyNormedField (ℚᵘⁿ_[p]) (WithZero (Multiplicative ℤ))

-- View ℚᵘⁿ_[p] as an algebra over ℚ_[p] via the embedding defined above.
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Algebra ℚ_[p] (ℚᵘⁿ_[p]) := (Qp_embd).toAlgebra

end QpUn

end FormalizedSparse
-- Tengoku: 3 notation(s) of this module made scoped so they do not change other libraries (generated)
