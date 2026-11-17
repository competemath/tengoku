import Tengoku.AdianRabin.GroupUndecidability.Borisov.Model.HNNModel
import Tengoku.AdianRabin.GroupUndecidability.GroupTheory.HNNLemmas
import Tengoku.AdianRabin.GroupUndecidability.Thue
import Tengoku.Seed.GroupTheory.FreeGroup.Reduce
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Group

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Function

namespace Undecidability
namespace BorisovCStage

noncomputable section

open BorisovHNNModel
open HNNLemmas

/-!
This file isolates Borisov's `c`-stage (his group `Γ₂`) in the actual
iterated-HNN model of `Γ₃`.

Literature: V. V. Borisov, *Simple examples of groups with unsolvable word
problem* (1969), Assertions IV--V and Lemma 4, English translation
pp. 769--772.  The specialization with exponent `α = 4` is checked in
M. Tancer, *Simpler algorithmically unrecognizable 4-manifolds*, Appendix,
pp. 26--27.

The construction needs the two displayed rank-five systems to be free.  The
structure below packages exactly this freeness input.
-/

/-- Indices for `s₁,s₂,A₁,A₂,A₃` and `s₁,s₂,B₁,B₂,B₃`.-/
abbrev RuleBasis := Fin 2 ⊕ Fin 3

def stable3 (beta : Fin 2) : Gamma3 :=
  if beta = 0 then s1_3 else s2_3

def positive3 (w : List (Fin 2)) : Gamma3 :=
  Thue.evalPositive s1_3 s2_3 w

/-- `A_i = d^i F_i e^i`, with Lean's `i` zero-based.-/
def a3 (datum : Thue.StandingDatum) (i : Fin 3) : Gamma3 :=
  d3 ^ (i.val + 1) * positive3 (datum.F i) * e3 ^ (i.val + 1)

/-- `B_i = d^i E_i e^i`, with Lean's `i` zero-based.-/
def b3 (datum : Thue.StandingDatum) (i : Fin 3) : Gamma3 :=
  d3 ^ (i.val + 1) * positive3 (datum.E i) * e3 ^ (i.val + 1)

def uBasis (datum : Thue.StandingDatum) : RuleBasis → Gamma3
  | .inl beta => stable3 beta
  | .inr i => a3 datum i

def vBasis (datum : Thue.StandingDatum) : RuleBasis → Gamma3
  | .inl beta => stable3 beta
  | .inr i => b3 datum i

def uLift (datum : Thue.StandingDatum) : FreeGroup RuleBasis →* Gamma3 :=
  FreeGroup.lift (uBasis datum)

def vLift (datum : Thue.StandingDatum) : FreeGroup RuleBasis →* Gamma3 :=
  FreeGroup.lift (vBasis datum)

/-- Borisov's Assertion IV in the exact form required to build the `c`-HNN
extension.-/
structure RankFiveFree (datum : Thue.StandingDatum) : Prop where
  u_injective : Function.Injective (uLift datum)
  v_injective : Function.Injective (vLift datum)

abbrev U (datum : Thue.StandingDatum) : Subgroup Gamma3 :=
  MonoidHom.range (uLift datum)

abbrev V (datum : Thue.StandingDatum) : Subgroup Gamma3 :=
  MonoidHom.range (vLift datum)

/-- The letterwise correspondence `s_beta ↦ s_beta`, `A_i ↦ B_i`.-/
def cEquiv (datum : Thue.StandingDatum) (hfree : RankFiveFree datum) :
    U datum ≃* V datum :=
  rangeEquiv (uLift datum) (vLift datum)
    hfree.u_injective hfree.v_injective

/--
@isnad1 id=eq.1h2v.s10.ddca2e0b0a39 from=translated src=- shape=b1071949 vocab=62607624
-/
@[simp]
theorem cEquiv_on_basis (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) (q : RuleBasis) :
    ((cEquiv datum hfree
        ⟨uBasis datum q, ⟨FreeGroup.of q, by simp [uLift]⟩⟩ : V datum) : Gamma3) =
      vBasis datum q := by
  let source : U datum :=
    ⟨uBasis datum q, ⟨FreeGroup.of q, by simp [uLift]⟩⟩
  let canonical : U datum :=
    ⟨uLift datum (FreeGroup.of q), ⟨FreeGroup.of q, rfl⟩⟩
  have hsource : source = canonical := by
    apply Subtype.ext
    simp [source, canonical, uLift]
  change ((cEquiv datum hfree source : V datum) : Gamma3) = _
  rw [hsource]
  change vLift datum
      ((equivRangeOfInjective (uLift datum) hfree.u_injective).symm canonical) =
    vBasis datum q
  have hy :
      (equivRangeOfInjective (uLift datum) hfree.u_injective).symm canonical =
        FreeGroup.of q := by
    apply hfree.u_injective
    exact congrArg Subtype.val
      ((equivRangeOfInjective (uLift datum) hfree.u_injective).apply_symm_apply
        canonical)
  rw [hy]
  simp [vLift]

/-- Borisov's `Γ₂`, with Mathlib's stable letter equal to `c⁻¹`.-/
abbrev Gamma2 (datum : Thue.StandingDatum) (hfree : RankFiveFree datum) :=
  HNNExtension Gamma3 (U datum) (V datum) (cEquiv datum hfree)

def of3 (datum : Thue.StandingDatum) (hfree : RankFiveFree datum) :
    Gamma3 →* Gamma2 datum hfree :=
  HNNExtension.of

/-- Borisov's generator `c`; Mathlib's HNN stable letter is `c⁻¹`.-/
def c (datum : Thue.StandingDatum) (hfree : RankFiveFree datum) :
    Gamma2 datum hfree :=
  (HNNExtension.t : Gamma2 datum hfree)⁻¹

/--
@isnad1 id=injectiv.1h1v.s7.148973e5b2e4 from=translated src=- shape=07ef95f6 vocab=046c0367
-/
theorem of3_injective (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) :
    Function.Injective (of3 datum hfree) :=
  HNNExtension.of_injective (cEquiv datum hfree)

/-- The defining `c`-conjugation law on all five displayed basis elements.
@isnad1 id=eq.1h2v.s8.45bd5ae7fc99 from=translated src=- shape=ba3218c9 vocab=2950ad4f
-/
theorem c_conjugates_basis (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) (q : RuleBasis) :
    (c datum hfree)⁻¹ * of3 datum hfree (uBasis datum q) * c datum hfree =
      of3 datum hfree (vBasis datum q) := by
  let uq : U datum :=
    ⟨uBasis datum q, ⟨FreeGroup.of q, by simp [uLift]⟩⟩
  have ht := HNNExtension.t_mul_of (φ := cEquiv datum hfree) uq
  change HNNExtension.t * HNNExtension.of (uBasis datum q) * HNNExtension.t⁻¹ =
    HNNExtension.of (vBasis datum q)
  rw [ht]
  simp [uq, cEquiv_on_basis]

/--
@isnad1 id=commute.1h2v.s7.28094c16f746 from=translated src=- shape=52e0d1a7 vocab=983f6d7e
-/
theorem c_commutes_stable (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) (beta : Fin 2) :
    Commute (of3 datum hfree (stable3 beta)) (c datum hfree) := by
  rw [commute_iff_eq]
  have h := c_conjugates_basis datum hfree (Sum.inl beta)
  change (c datum hfree)⁻¹ * of3 datum hfree (stable3 beta) * c datum hfree =
    of3 datum hfree (stable3 beta) at h
  have hc := congrArg (fun x => c datum hfree * x) h
  simpa [mul_assoc] using hc

/-- The three simulator relations `c⁻¹ A_i c = B_i`.
@isnad1 id=eq.1h2v.s8.bb6aa9f2c8a6 from=translated src=- shape=e226136e vocab=927caba3
-/
theorem c_simulation (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) (i : Fin 3) :
    (c datum hfree)⁻¹ * of3 datum hfree (a3 datum i) * c datum hfree =
      of3 datum hfree (b3 datum i) := by
  simpa [uBasis, vBasis] using
    c_conjugates_basis datum hfree (Sum.inr i)

/-! ## The stable-letter projection and the zero-`c` case of Lemma 4 -/

/-- Kill `d,e` and retain the first HNN stable letter as the first free
generator.-/
def stableProjection1 : Stage1 →* FreeGroup (Fin 2) :=
  HNNExtension.lift (1 : Base →* FreeGroup (Fin 2)) (FreeGroup.of 0) (by
    intro a
    simp)

/--
@isnad1 id=eq.0h1v.s8.6aae84e41828 from=translated src=- shape=727baffe vocab=2e13d770
-/
@[simp]
theorem stableProjection1_of0 (x : Base) :
    stableProjection1 (of0 x) = 1 := by
  simp [stableProjection1, of0]

/--
@isnad1 id=eq.0h0v.s7.851bb5852d27 from=translated src=- shape=8ad73e9a vocab=2fd079d0
-/
@[simp]
theorem stableProjection1_s1 :
    stableProjection1 s1 = FreeGroup.of (0 : Fin 2) := by
  simp [stableProjection1, s1]

/-- Kill `d,e` and remember `s₁,s₂` as a free basis.  This is the projection
used in Borisov's `m = 0` argument.-/
def stableProjection3 : Gamma3 →* FreeGroup (Fin 2) :=
  HNNExtension.lift stableProjection1 (FreeGroup.of 1) (by
    intro a
    let a0 : A0 := inA1.symm a
    have ha : a = inA1 a0 := (inA1.apply_symm_apply a).symm
    rw [ha, phi1_inA1]
    simp [stableProjection1, of0, coe_inA1, coe_inB1])

/--
@isnad1 id=eq.0h0v.s7.67f57ae00667 from=translated src=- shape=9dd44ff7 vocab=6d9cc2e5
-/
@[simp]
theorem stableProjection3_d : stableProjection3 d3 = 1 := by
  simp [stableProjection3, d3, of1]

/--
@isnad1 id=eq.0h0v.s7.3825f050d1f8 from=translated src=- shape=9dd44ff7 vocab=0dc6fbfd
-/
@[simp]
theorem stableProjection3_e : stableProjection3 e3 = 1 := by
  simp [stableProjection3, e3, of1]

/--
@isnad1 id=eq.0h0v.s7.7a1286fadbab from=translated src=- shape=8ad73e9a vocab=b51ee7bf
-/
@[simp]
theorem stableProjection3_s1 :
    stableProjection3 s1_3 = FreeGroup.of (0 : Fin 2) := by
  simp [stableProjection3, s1_3, of1]

/--
@isnad1 id=eq.0h0v.s7.e4df677729e5 from=translated src=- shape=8ad73e9a vocab=9ad69e52
-/
@[simp]
theorem stableProjection3_s2 :
    stableProjection3 s2_3 = FreeGroup.of (1 : Fin 2) := by
  simp [stableProjection3, s2_3]

/-- The positive monoid on two letters, embedded in its free group.-/
def positiveFree (w : List (Fin 2)) : FreeGroup (Fin 2) :=
  FreeGroup.mk (w.map fun i => (i, true))

/--
@isnad1 id=eq.0h1v.s6.80c7ca6c5327 from=translated src=- shape=2bbd6ddc vocab=68fb8ca8
-/
theorem positiveFree_eq_eval (w : List (Fin 2)) :
    positiveFree w =
      Thue.evalPositive (FreeGroup.of 0) (FreeGroup.of 1) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      calc
        positiveFree (i :: w) = FreeGroup.of i * positiveFree w := by
          simp only [positiveFree, List.map_cons]
          change FreeGroup.mk ((i, true) :: w.map fun k => (k, true)) =
            FreeGroup.mk [(i, true)] * FreeGroup.mk (w.map fun k => (k, true))
          rw [FreeGroup.mul_mk]
          rfl
        _ = FreeGroup.of i *
              Thue.evalPositive (FreeGroup.of 0) (FreeGroup.of 1) w := by
          rw [ih]
        _ = Thue.evalPositive (FreeGroup.of 0) (FreeGroup.of 1) (i :: w) := by
          fin_cases i <;> simp [Thue.evalPositive]

/--
@isnad1 id=eq.0h1v.s7.5e35cb11ee18 from=translated src=- shape=399113e2 vocab=4d4734f5
-/
theorem stableProjection3_positive (w : List (Fin 2)) :
    stableProjection3 (positive3 w) = positiveFree w := by
  induction w with
  | nil => exact FreeGroup.one_eq_mk
  | cons i w ih =>
      have hcons : positive3 (i :: w) =
          (if i = 0 then s1_3 else s2_3) * positive3 w := by
        simp [positive3, Thue.evalPositive]
      rw [hcons, map_mul, ih]
      rw [positiveFree_eq_eval, positiveFree_eq_eval]
      fin_cases i <;> simp [Thue.evalPositive]

private theorem positiveLetters_reduced (w : List (Fin 2)) :
    FreeGroup.IsReduced (w.map fun i => (i, true)) := by
  induction w with
  | nil => simp [FreeGroup.IsReduced]
  | cons i w ih =>
      cases w with
      | nil => simp [FreeGroup.IsReduced]
      | cons j w =>
          change List.IsChain (fun a b : Fin 2 × Bool =>
            a.1 = b.1 → a.2 = b.2)
              ((i, true) :: (j, true) :: w.map fun k => (k, true))
          rw [List.isChain_cons]
          exact ⟨by simp, ih⟩

/--
@isnad1 id=injectiv.0h0v.s4.6e8440e47e82 from=translated src=- shape=9c34f928 vocab=16474975
-/
theorem positiveFree_injective : Function.Injective positiveFree := by
  intro u v huv
  have hreduce := FreeGroup.reduce.sound huv
  have hu := (positiveLetters_reduced u).reduce_eq
  have hv := (positiveLetters_reduced v).reduce_eq
  rw [hu, hv] at hreduce
  have hinj : Function.Injective (fun i : Fin 2 => (i, true)) := by
    intro i j h
    exact congrArg Prod.fst h
  exact hinj.list_map hreduce

/-- The base subgroup `<d,e>` of `Γ₃`.-/
def DE3 : Subgroup Gamma3 :=
  Subgroup.closure ({d3, e3} : Set Gamma3)

/--
@isnad1 id=le.0h0v.s7.852304253a45 from=translated src=- shape=7d909ad6 vocab=8f34d8b5
-/
theorem DE3_le_projection_ker :
    DE3 ≤ MonoidHom.ker stableProjection3 := by
  rw [DE3, Subgroup.closure_le]
  intro x hx
  rcases hx with (rfl | hx)
  · simp
  · simpa only [Set.mem_singleton_iff] using hx ▸ stableProjection3_e

/-- Borisov Lemma 4 when the context contains no `c`: projecting to the free
group on `s₁,s₂` forces the two positive words to be literally equal.
@isnad1 id=eq.3h4v.s8.53b545b58677 from=translated src=- shape=fdb227b9 vocab=465b69c7
-/
theorem lemma4_zero_c
    (P Q : List (Fin 2)) (L R : Gamma3)
    (hL : L ∈ DE3) (hR : R ∈ DE3)
    (heq : (positive3 P)⁻¹ * L * positive3 Q * R = 1) :
    P = Q := by
  have hmap := congrArg stableProjection3 heq
  have hL1 : stableProjection3 L = 1 := DE3_le_projection_ker hL
  have hR1 : stableProjection3 R = 1 := DE3_le_projection_ker hR
  simp only [map_mul, map_inv, map_one, stableProjection3_positive,
    hL1, hR1, mul_one] at hmap
  have hpq : positiveFree P = positiveFree Q :=
    inv_mul_eq_one.mp hmap
  exact positiveFree_injective hpq

/-! ## The exact normal-form statement of Borisov's Lemma 4 -/

def dCyclic : Subgroup Gamma3 :=
  Subgroup.closure ({d3} : Set Gamma3)

def eCyclic : Subgroup Gamma3 :=
  Subgroup.closure ({e3} : Set Gamma3)

/--
@isnad1 id=le.0h0v.s6.58a52e39f914 from=translated src=- shape=836e6cbb vocab=d1184359
-/
theorem dCyclic_le_DE3 : dCyclic ≤ DE3 := by
  rw [dCyclic, Subgroup.closure_le, Set.singleton_subset_iff]
  exact Subgroup.subset_closure (by simp)

/--
@isnad1 id=le.0h0v.s6.7f5aefe7d49a from=translated src=- shape=836e6cbb vocab=5e83769e
-/
theorem eCyclic_le_DE3 : eCyclic ≤ DE3 := by
  rw [eCyclic, Subgroup.closure_le, Set.singleton_subset_iff]
  exact Subgroup.subset_closure (by simp)

abbrev CReducedWord (datum : Thue.StandingDatum)
    (_hfree : RankFiveFree datum) :=
  HNNExtension.NormalWord.ReducedWord Gamma3 (U datum) (V datum)

/-- An HNN-reduced word on `{c,d}`.  Its base coefficients are all powers of
`d`; its stable-letter list is the list of occurrences of `c^{±1}`.-/
structure LeftContext (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) where
  word : CReducedWord datum hfree
  head_mem : word.head ∈ dCyclic
  coeff_mem : ∀ p ∈ word.toList, p.2 ∈ dCyclic

/-- An HNN-reduced word on `{c,e}`.-/
structure RightContext (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) where
  word : CReducedWord datum hfree
  head_mem : word.head ∈ eCyclic
  coeff_mem : ∀ p ∈ word.toList, p.2 ∈ eCyclic

def leftValue (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (L : LeftContext datum hfree) : Gamma2 datum hfree :=
  L.word.prod (cEquiv datum hfree)

def rightValue (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (R : RightContext datum hfree) : Gamma2 datum hfree :=
  R.word.prod (cEquiv datum hfree)

def positive2 (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (w : List (Fin 2)) : Gamma2 datum hfree :=
  of3 datum hfree (positive3 w)

/-- The published hypothesis `P⁻¹ L Q R = 1`, with `L` and `R` already in
the irreducible forms used in Borisov's induction.-/
def Lemma4Equation (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) (P Q : List (Fin 2))
    (L : LeftContext datum hfree) (R : RightContext datum hfree) : Prop :=
  (positive2 datum hfree P)⁻¹ * leftValue datum hfree L *
      positive2 datum hfree Q * rightValue datum hfree R = 1

/-- Exact c-stage separation theorem needed by the converse direction.

This is Borisov 1969, Lemma 4, specialized to `N = 2`, `M = 3`, `α = 4`.
The induction measure in the paper is the number of positive occurrences of
`c` in `L.word.toList ++ R.word.toList` (equivalently one half of its length).-/
def BorisovLemma4 (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) : Prop :=
  ∀ (P Q : List (Fin 2))
    (L : LeftContext datum hfree) (R : RightContext datum hfree),
    Lemma4Equation datum hfree P Q L R →
      ThueEq (Thue.systemOf datum.F datum.E) Q P

/-- The `m = 0` branch of the published induction in the iterated HNN model.
@isnad1 id=thueeq.4h5v.s7.9c1cfeffe967 from=translated src=- shape=21430e6c vocab=c501a37a
-/
theorem lemma4_of_context_lists_nil
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (P Q : List (Fin 2))
    (L : LeftContext datum hfree) (R : RightContext datum hfree)
    (hLnil : L.word.toList = []) (hRnil : R.word.toList = [])
    (heq : Lemma4Equation datum hfree P Q L R) :
    ThueEq (Thue.systemOf datum.F datum.E) Q P := by
  have hbase :
      (positive3 P)⁻¹ * L.word.head * positive3 Q * R.word.head = 1 := by
    apply of3_injective datum hfree
    simpa [Lemma4Equation, positive2, leftValue, rightValue,
      HNNExtension.NormalWord.ReducedWord.prod, hLnil, hRnil,
      map_mul, map_inv, of3] using heq
  have hPQ : P = Q :=
    lemma4_zero_c P Q L.word.head R.word.head
      (dCyclic_le_DE3 L.head_mem) (eCyclic_le_DE3 R.head_mem) hbase
  subst P
  exact Relation.ReflTransGen.refl

/-! ## Context subgroups and factorization -/

def CD (datum : Thue.StandingDatum) (hfree : RankFiveFree datum) :
    Subgroup (Gamma2 datum hfree) :=
  Subgroup.closure
    ({c datum hfree, of3 datum hfree d3} : Set (Gamma2 datum hfree))

def CE (datum : Thue.StandingDatum) (hfree : RankFiveFree datum) :
    Subgroup (Gamma2 datum hfree) :=
  Subgroup.closure
    ({c datum hfree, of3 datum hfree e3} : Set (Gamma2 datum hfree))

/--
@isnad1 id=iff.0h5v.s7.bd17e59b7ed4 from=translated src=- shape=30f5063e vocab=9f72dee7
-/
theorem equation_iff_factorization
    {G : Type*} [Group G] (P L Q R : G) :
    P⁻¹ * L * Q * R = 1 ↔ P = L * Q * R := by
  constructor
  · intro h
    apply inv_mul_eq_one.mp
    simpa only [mul_assoc] using h
  · intro h
    rw [h]
    group

/-! ## Isolating the positive-`c` induction step -/

/--
@isnad1 id=thuestep.0h4v.s7.a30b3a752b8c from=translated src=- shape=39e79252 vocab=ffbf5563
-/
theorem thueStep_rule_forward
    (datum : Thue.StandingDatum) (l r : List (Fin 2)) (i : Fin 3) :
    ThueStep (Thue.systemOf datum.F datum.E)
      (l ++ datum.F i ++ r) (l ++ datum.E i ++ r) := by
  refine ⟨l, r, datum.F i, datum.E i, ⟨i, rfl⟩, ?_⟩
  exact Or.inl ⟨rfl, rfl⟩

/--
@isnad1 id=thuestep.0h4v.s7.1cd96447717f from=translated src=- shape=fb8f4d57 vocab=ffbf5563
-/
theorem thueStep_rule_backward
    (datum : Thue.StandingDatum) (l r : List (Fin 2)) (i : Fin 3) :
    ThueStep (Thue.systemOf datum.F datum.E)
      (l ++ datum.E i ++ r) (l ++ datum.F i ++ r) := by
  refine ⟨l, r, datum.F i, datum.E i, ⟨i, rfl⟩, ?_⟩
  exact Or.inr ⟨rfl, rfl⟩

def contextComplexity
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (L : LeftContext datum hfree) (R : RightContext datum hfree) : ℕ :=
  L.word.toList.length + R.word.toList.length

/-- The key deep local statement in Borisov's Lemma 4.

If the context is nonempty, Britton reduction plus Assertions IV--V must
exhibit one semigroup rule in `Q` and new irreducible contexts with strictly
fewer occurrences of `c^{±1}`.  Tancer's Appendix carries out precisely this
case analysis for `α = 4`.-/
def PinchReduction (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) : Prop :=
  ∀ (P Q : List (Fin 2))
    (L : LeftContext datum hfree) (R : RightContext datum hfree),
    Lemma4Equation datum hfree P Q L R →
      contextComplexity datum hfree L R = 0 ∨
        ∃ (Q' : List (Fin 2))
          (L' : LeftContext datum hfree) (R' : RightContext datum hfree),
          ThueEq (Thue.systemOf datum.F datum.E) Q Q' ∧
          Lemma4Equation datum hfree P Q' L' R' ∧
          contextComplexity datum hfree L' R' <
            contextComplexity datum hfree L R

/-- Once the local pinch-reduction statement is available, well-founded
induction gives all of Borisov's Lemma 4.
@isnad1 id=borisovl.2h1v.s3.f57fec2be208 from=translated src=- shape=b28a8773 vocab=c2d85b25
-/
theorem borisovLemma4_of_pinchReduction
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (hpinch : PinchReduction datum hfree) :
    BorisovLemma4 datum hfree := by
  intro P Q L R heq
  generalize hn : contextComplexity datum hfree L R = n
  induction n using Nat.strong_induction_on generalizing Q L R with
  | h n ih =>
      rcases hpinch P Q L R heq with hzero | hstep
      · have hsum : L.word.toList.length + R.word.toList.length = 0 := by
          simpa [contextComplexity] using hzero
        have hlens := Nat.add_eq_zero_iff.mp hsum
        have hLnil : L.word.toList = [] :=
          List.eq_nil_of_length_eq_zero hlens.1
        have hRnil : R.word.toList = [] :=
          List.eq_nil_of_length_eq_zero hlens.2
        exact lemma4_of_context_lists_nil datum hfree P Q L R hLnil hRnil heq
      · rcases hstep with ⟨Q', L', R', hQQ', heq', hlt⟩
        apply hQQ'.trans
        have hlt' : contextComplexity datum hfree L' R' < n := by
          simpa [hn] using hlt
        exact ih (contextComplexity datum hfree L' R') hlt'
          Q' L' R' heq' rfl

/-! ## Exponent balance (Borisov's use of Lemma 3) -/

/-- Exponent sum of Mathlib's stable letter `t = c⁻¹`.-/
def cExponent (datum : Thue.StandingDatum) (hfree : RankFiveFree datum) :
    Gamma2 datum hfree →* Multiplicative ℤ :=
  HNNExtension.lift (1 : Gamma3 →* Multiplicative ℤ)
    (Multiplicative.ofAdd 1) (by intro a; simp)

/--
@isnad1 id=eq.1h1v.s7.5eef327e00e9 from=translated src=- shape=7f3c6d1d vocab=8a21086e
-/
@[simp]
theorem cExponent_c
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum) :
    cExponent datum hfree (c datum hfree) =
      Multiplicative.ofAdd (-1) := by
  simp [c, cExponent]

end

end BorisovCStage
end Undecidability
