/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Tengoku.LeanPool.LeanPool.CencovPetz.SufficientStatistic
public import Tengoku.LeanPool.LeanPool.CencovPetz.MonotoneMetric
public import Tengoku
import Tengoku.LeanPool.LeanPool.CencovPetz.LeftInverseIsometry

/-!
# `CencovPetz.PermutationInvariance`

Bridge deterministic sufficient statistics and deterministic Markov morphisms, and derive
permutation/equivalence invariance consequences for monotone metric families in the finite
Čencov/Chentsov setting.

## Main results

- `CencovPetz.MarkovMorphism.deterministic_pushforward_eq_simplex_pushforward`:
  deterministic Markov pushforward agrees with the fiberwise-sum pushforward from
  `SufficientStatistic`.
- `CencovPetz.MonotoneMetricFamily.comp_eq_of_equiv`:
  any monotone metric family is invariant under equivalences (permutations) of finite types.
-/

@[expose] public section

namespace LeanPool.CencovPetz
open scoped BigOperators

universe u

variable {α β : Type u} [Fintype α] [Fintype β]

namespace MarkovMorphism

/--
@isnad1 id=eq.1h4v.s5.4d5c55e3d030 from=translated src=- shape=9abf1bea vocab=166da065
-/
lemma deterministic_pushforward_eq_simplex_pushforward [DecidableEq β] (g : α → β)
    (hg : Function.Surjective g) (p : Simplex α) :
    (MarkovMorphism.deterministic (α := α) (β := β) g hg).pushforward p =
      Simplex.pushforward (α := α) (β := β) g hg p := by
  ext b
  simpa [Simplex.pushforward_apply] using
    (MarkovMorphism.deterministic_pushforward_apply (α := α) (β := β) (g := g) (hg := hg) p b)

/--
@isnad1 id=eq.1h4v.s7.bee5b51edb02 from=translated src=- shape=1f201928 vocab=fc3c7b82
-/
lemma deterministic_tangentPushforward_eq_tangentPushforward [DecidableEq β] (g : α → β)
    (hg : Function.Surjective g) (u : tangentSpace (α := α)) :
    (MarkovMorphism.deterministic (α := α) (β := β) g hg).tangentPushforward u =
      _root_.LeanPool.CencovPetz.tangentPushforward (α := α) (β := β) g u := by
  ext b
  simpa [_root_.LeanPool.CencovPetz.tangentPushforward_apply] using
    (MarkovMorphism.deterministic_tangentPushforward_apply
      (α := α) (β := β) (g := g) (hg := hg) u b)

/--
@isnad1 id=eq.0h5v.s6.d56bab770d91 from=translated src=- shape=0ae79fcc vocab=a75fe512
-/
lemma deterministic_pushforward_apply_of_equiv
    (e : α ≃ β) (p : Simplex α) (b : β) :
    ((MarkovMorphism.deterministic (α := α) (β := β)
        (g := (e : α → β)) e.surjective).pushforward
        p).p b =
      p.p (e.symm b) := by
  classical
  have hs : (Finset.univ.filter fun a : α => e a = b) = {e.symm b} := by
    ext a
    simp [e.eq_symm_apply]
  calc
    ((MarkovMorphism.deterministic (α := α) (β := β)
          (g := (e : α → β))
          e.surjective).pushforward p).p b
        = ∑ a with e a = b, p.p a := by
              simpa using
                (MarkovMorphism.deterministic_pushforward_apply
                  (α := α) (β := β) (g := (e : α → β))
                  (hg := e.surjective) p b)
    _ = p.p (e.symm b) := by simp [hs]

/--
@isnad1 id=eq.0h5v.s8.ad4bea12fb4a from=translated src=- shape=a2c95183 vocab=09bae83b
-/
lemma deterministic_tangentPushforward_apply_of_equiv
    (e : α ≃ β) (u : tangentSpace (α := α)) (b : β) :
    ((MarkovMorphism.deterministic (α := α) (β := β)
        (g := (e : α → β))
        e.surjective).tangentPushforward
        u : β → ℝ) b =
      (u : α → ℝ) (e.symm b) := by
  classical
  have hs : (Finset.univ.filter fun a : α => e a = b) = {e.symm b} := by
    ext a
    simp [e.eq_symm_apply]
  calc
    ((MarkovMorphism.deterministic (α := α) (β := β)
          (g := (e : α → β))
          e.surjective).tangentPushforward
          u : β → ℝ) b
        = ∑ a with e a = b, (u : α → ℝ) a := by
              simpa using
                (MarkovMorphism.deterministic_tangentPushforward_apply
                  (α := α) (β := β)
                  (g := (e : α → β))
                  (hg := e.surjective) u b)
    _ = (u : α → ℝ) (e.symm b) := by simp [hs]

/--
@isnad1 id=eq.0h4v.s6.8f71a2a15a4f from=translated src=- shape=639e5c63 vocab=fe5d771f
-/
lemma deterministic_pushforward_comp_symm
    (e : α ≃ β) (p : Simplex α) :
    (MarkovMorphism.deterministic (α := β) (β := α)
        (g := (e.symm : β → α))
        e.symm.surjective).pushforward
      ((MarkovMorphism.deterministic (α := α) (β := β)
          (g := (e : α → β))
          e.surjective).pushforward p)
      = p := by
  classical
  ext a
  -- Evaluate both pushforwards using the explicit
  -- "equivalence" formulas.
  calc
    ((MarkovMorphism.deterministic (α := β) (β := α)
          (g := (e.symm : β → α))
          e.symm.surjective).pushforward
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).pushforward p)).p a
        =
          ((MarkovMorphism.deterministic (α := α) (β := β)
              (g := (e : α → β))
              e.surjective).pushforward p).p
            (e a) := by
              simpa using
                (deterministic_pushforward_apply_of_equiv
                  (α := β) (β := α) (e := e.symm)
                  (p :=
                    (MarkovMorphism.deterministic
                      (α := α) (β := β)
                      (g := (e : α → β))
                      e.surjective).pushforward p)
                  (b := a))
    _ = p.p a := by
          simpa using
            (deterministic_pushforward_apply_of_equiv
              (α := α) (β := β) (e := e)
              (p := p) (b := e a))

/--
@isnad1 id=eq.0h4v.s8.e0e33ff0a2a5 from=translated src=- shape=21c24c51 vocab=e410b350
-/
lemma deterministic_tangentPushforward_comp_symm
    (e : α ≃ β) (u : tangentSpace (α := α)) :
    (MarkovMorphism.deterministic (α := β) (β := α)
        (g := (e.symm : β → α))
        e.symm.surjective).tangentPushforward
      ((MarkovMorphism.deterministic (α := α) (β := β)
          (g := (e : α → β))
          e.surjective).tangentPushforward u)
      = u := by
  classical
  ext a
  -- Evaluate both pushforwards using the explicit
  -- "equivalence" formulas.
  calc
    ((MarkovMorphism.deterministic (α := β) (β := α)
          (g := (e.symm : β → α))
          e.symm.surjective).tangentPushforward
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforward
            u) : α → ℝ) a
        =
          ((MarkovMorphism.deterministic (α := α) (β := β)
              (g := (e : α → β))
              e.surjective).tangentPushforward
              u : β → ℝ)
            (e a) := by
              simpa using
                (deterministic_tangentPushforward_apply_of_equiv
                  (α := β) (β := α) (e := e.symm)
                  (u :=
                    (MarkovMorphism.deterministic
                      (α := α) (β := β)
                      (g := (e : α → β))
                      e.surjective).tangentPushforward u)
                  (b := a))
    _ = (u : α → ℝ) a := by
          simpa using
            (deterministic_tangentPushforward_apply_of_equiv
              (α := α) (β := β) (e := e)
              (u := u) (b := e a))

end MarkovMorphism

namespace MonotoneMetricFamily

/--
@isnad1 id=eq.0h5v.s9.89264789274b from=translated src=- shape=77dd55bd vocab=432148f1
-/
lemma comp_eq_of_equiv
    (G : MonotoneMetricFamily) (e : α ≃ β) (p : Simplex α) :
    (G.g (α := β)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).pushforward p)).comp
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforwardLinear)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforwardLinear)
      = G.g (α := α) p := by
  classical
  let κ : MarkovMorphism α β :=
    MarkovMorphism.deterministic (α := α) (β := β)
      (g := (e : α → β)) e.surjective
  let κ' : MarkovMorphism β α :=
    MarkovMorphism.deterministic (α := β) (β := α)
      (g := (e.symm : β → α)) e.symm.surjective
  refine MonotoneMetricFamily.comp_eq_of_left_inverse
    (G := G) (κ := κ) (κ' := κ') (p := p) ?_ ?_
  · simpa [κ, κ'] using
      MarkovMorphism.deterministic_pushforward_comp_symm
        (α := α) (β := β) (e := e) (p := p)
  · intro u
    simpa [κ, κ'] using
      MarkovMorphism.deterministic_tangentPushforward_comp_symm
        (α := α) (β := β) (e := e) (u := u)

lemma eq_of_equiv
    (G : MonotoneMetricFamily) (e : α ≃ β) (p : Simplex α)
    (u v : tangentSpace (α := α)) :
    G.g (α := β)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).pushforward p)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforward u)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforward v)
      = G.g (α := α) p u v := by
  classical
  let κ : MarkovMorphism α β :=
    MarkovMorphism.deterministic (α := α) (β := β)
      (g := (e : α → β)) e.surjective
  let κ' : MarkovMorphism β α :=
    MarkovMorphism.deterministic (α := β) (β := α)
      (g := (e.symm : β → α)) e.symm.surjective
  refine MonotoneMetricFamily.eq_of_left_inverse
    (G := G) (κ := κ) (κ' := κ') (p := p) ?_ ?_ u v
  · simpa [κ, κ'] using
      MarkovMorphism.deterministic_pushforward_comp_symm
        (α := α) (β := β) (e := e) (p := p)
  · intro u
    simpa [κ, κ'] using
      MarkovMorphism.deterministic_tangentPushforward_comp_symm
        (α := α) (β := β) (e := e) (u := u)

end MonotoneMetricFamily
end LeanPool.CencovPetz
