import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.Collar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Splitting a generalized loop along a hyperplane cut

If a generalized loop `p : Ω^ N X x` sends the whole slice `{t | t i = c}` (for a cut
level `c ∈ (0,1)`) to the basepoint, then `p` is homotopic rel boundary to the
concatenation, along coordinate `i`, of its two restrictions:

* `Submission.leftGenLoop p i c _ _ hcut`: coordinate `i` reparametrized by
  `t i ↦ c * t i` (the part of `p` with `t i ∈ [0, c]`);
* `Submission.rightGenLoop p i c _ _ hcut`: coordinate `i` reparametrized by
  `t i ↦ c + (1 - c) * t i` (the part with `t i ∈ [c, 1]`).

Main results:

* `Submission.homotopic_transAt_restrictions`:
  `p` is homotopic to `GenLoop.transAt i (leftGenLoop …) (rightGenLoop …)`.
* `Submission.genLoopClass_eq_right_mul_left`: in `HomotopyGroup N X x`,
  `⟦p⟧ = ⟦rightGenLoop …⟧ * ⟦leftGenLoop …⟧`.

## Composition order

Mathlib's `HomotopyGroup.mul_spec` reads `⟦p⟧ * ⟦q⟧ = ⟦transAt i q p⟧`: the *right*
factor of a product is traversed on the first half of coordinate `i`.  Since our
homotopy identifies `p` with `transAt i (left) (right)` (left part on the first half),
the class identity is `⟦p⟧ = ⟦right⟧ * ⟦left⟧` — the left restriction appears as the
RIGHT factor of the product.
-/

noncomputable section

open scoped Topology unitInterval
open Topology.Homotopy Set

namespace Submission

variable {N X : Type*} [TopologicalSpace X] [DecidableEq N] {x : X}

/-! ## The piecewise-linear reparametrization of the interval -/

/-- The piecewise-linear self-map of `I` sending `[0, 1/2]` affinely onto `[0, c]` and
`[1/2, 1]` affinely onto `[c, 1]`.-/
def cutReparam (c : ℝ) : I → I := fun u =>
  if (u : ℝ) ≤ 1 / 2 then Set.projIcc (0 : ℝ) 1 zero_le_one (c * (2 * (u : ℝ)))
  else Set.projIcc (0 : ℝ) 1 zero_le_one (c + (1 - c) * (2 * (u : ℝ) - 1))

theorem continuous_cutReparam (c : ℝ) : Continuous (cutReparam c) := by
  apply Continuous.if_le
  · exact continuous_projIcc.comp' (by fun_prop)
  · exact continuous_projIcc.comp' (by fun_prop)
  · exact continuous_subtype_val
  · exact continuous_const
  · intro u hu
    have h : c * (2 * (u : ℝ)) = c + (1 - c) * (2 * (u : ℝ) - 1) := by rw [hu]; ring
    rw [h]

theorem cutReparam_zero (c : ℝ) : cutReparam c 0 = 0 := by
  simp only [cutReparam, Set.Icc.coe_zero]
  rw [ite_eq_left (by norm_num)]
  exact projIcc_eq_zero (by norm_num)

theorem cutReparam_one (c : ℝ) : cutReparam c 1 = 1 := by
  simp only [cutReparam, Set.Icc.coe_one]
  rw [ite_eq_right (by norm_num)]
  have h : c + (1 - c) * (2 * (1 : ℝ) - 1) = 1 := by ring
  rw [h]
  exact projIcc_eq_one le_rfl

/-! ## The two restrictions of a cut loop -/

variable (p : Ω^ N X x) (i : N) (c : ℝ)

/-- The left restriction of `p` along the cut `t i = c`: coordinate `i` is
reparametrized by `t i ↦ c * t i`, squeezing `[0,1]` onto `[0,c]`.-/
def leftGenLoop (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hcut : ∀ t : I^N, (t i : ℝ) = c → p t = x) : Ω^ N X x :=
  ⟨p.1.comp ⟨fun t => Function.update t i
        (Set.projIcc (0 : ℝ) 1 zero_le_one (c * (t i : ℝ))),
      by exact continuous_id.update i (continuous_projIcc.comp' (by fun_prop))⟩,
    fun t ht => by
      obtain ⟨j, hj⟩ := ht
      show p (Function.update t i
        (Set.projIcc (0 : ℝ) 1 zero_le_one (c * (t i : ℝ)))) = x
      rcases eq_or_ne j i with rfl | hne
      · rcases hj with h0 | h1
        · refine p.2 _ ⟨j, Or.inl ?_⟩
          rw [Function.update_self]
          have h : (t j : ℝ) = 0 := by rw [h0, Set.Icc.coe_zero]
          rw [h, mul_zero]
          exact projIcc_eq_zero le_rfl
        · apply hcut
          rw [Function.update_self]
          have h : (t j : ℝ) = 1 := by rw [h1, Set.Icc.coe_one]
          rw [h, mul_one, Set.coe_projIcc, min_eq_right hc1, max_eq_right hc0]
      · refine p.2 _ ⟨j, ?_⟩
        rwa [Function.update_of_ne hne]⟩

/-- The right restriction of `p` along the cut `t i = c`: coordinate `i` is
reparametrized by `t i ↦ c + (1 - c) * t i`, squeezing `[0,1]` onto `[c,1]`.-/
def rightGenLoop (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hcut : ∀ t : I^N, (t i : ℝ) = c → p t = x) : Ω^ N X x :=
  ⟨p.1.comp ⟨fun t => Function.update t i
        (Set.projIcc (0 : ℝ) 1 zero_le_one (c + (1 - c) * (t i : ℝ))),
      by exact continuous_id.update i (continuous_projIcc.comp' (by fun_prop))⟩,
    fun t ht => by
      obtain ⟨j, hj⟩ := ht
      show p (Function.update t i
        (Set.projIcc (0 : ℝ) 1 zero_le_one (c + (1 - c) * (t i : ℝ)))) = x
      rcases eq_or_ne j i with rfl | hne
      · rcases hj with h0 | h1
        · apply hcut
          rw [Function.update_self]
          have h : (t j : ℝ) = 0 := by rw [h0, Set.Icc.coe_zero]
          rw [h, mul_zero, add_zero, Set.coe_projIcc, min_eq_right hc1, max_eq_right hc0]
        · refine p.2 _ ⟨j, Or.inr ?_⟩
          rw [Function.update_self]
          have h : (t j : ℝ) = 1 := by rw [h1, Set.Icc.coe_one]
          rw [h]
          have h' : c + (1 - c) * (1 : ℝ) = 1 := by ring
          rw [h']
          exact projIcc_eq_one le_rfl
      · refine p.2 _ ⟨j, ?_⟩
        rwa [Function.update_of_ne hne]⟩

@[simp]
theorem leftGenLoop_apply (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hcut : ∀ t : I^N, (t i : ℝ) = c → p t = x) (t : I^N) :
    leftGenLoop p i c hc0 hc1 hcut t
      = p (Function.update t i (Set.projIcc (0 : ℝ) 1 zero_le_one (c * (t i : ℝ)))) :=
  rfl

@[simp]
theorem rightGenLoop_apply (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hcut : ∀ t : I^N, (t i : ℝ) = c → p t = x) (t : I^N) :
    rightGenLoop p i c hc0 hc1 hcut t
      = p (Function.update t i
          (Set.projIcc (0 : ℝ) 1 zero_le_one (c + (1 - c) * (t i : ℝ)))) :=
  rfl

/-- The concatenation of the two restrictions along coordinate `i` is the
reparametrization of `p` by `cutReparam c` in coordinate `i`.-/
theorem transAt_left_right_apply (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hcut : ∀ t : I^N, (t i : ℝ) = c → p t = x) (t : I^N) :
    GenLoop.transAt i (leftGenLoop p i c hc0 hc1 hcut) (rightGenLoop p i c hc0 hc1 hcut) t
      = p (Function.update t i (cutReparam c (t i))) := by
  simp only [GenLoop.transAt, GenLoop.coe_copy, cutReparam]
  split_ifs with h
  · rw [leftGenLoop_apply, Function.update_self, Function.update_idem]
    have ha : ((Set.projIcc (0 : ℝ) 1 zero_le_one (2 * ((t i : I) : ℝ)) : I) : ℝ)
        = 2 * ((t i : I) : ℝ) := by
      rw [Set.coe_projIcc, min_eq_right (by linarith),
        max_eq_right (by nlinarith [unitInterval.nonneg (t i)])]
    rw [ha]
  · rw [rightGenLoop_apply, Function.update_self, Function.update_idem]
    rw [not_le] at h
    have ha : ((Set.projIcc (0 : ℝ) 1 zero_le_one (2 * ((t i : I) : ℝ) - 1) : I) : ℝ)
        = 2 * ((t i : I) : ℝ) - 1 := by
      rw [Set.coe_projIcc, min_eq_right (by nlinarith [unitInterval.le_one (t i)]),
        max_eq_right (by linarith)]
    rw [ha]

/-! ## The homotopy -/

/-- At time `s`, coordinate `i` is reparametrized by the straight-line interpolation
between the identity (`s = 0`) and `cutReparam c` (`s = 1`).-/
def splitHomotopyMap (s : I) (t : I^N) : I^N :=
  Function.update t i (Set.projIcc (0 : ℝ) 1 zero_le_one
    ((1 - (s : ℝ)) * (t i : ℝ) + (s : ℝ) * ((cutReparam c (t i) : I) : ℝ)))

theorem continuous_splitHomotopyMap :
    Continuous fun st : I × I^N => splitHomotopyMap i c st.1 st.2 := by
  refine continuous_snd.update i (continuous_projIcc.comp' ?_)
  have hc : Continuous fun st : I × I^N => ((cutReparam c (st.2 i) : I) : ℝ) :=
    continuous_subtype_val.comp
      ((continuous_cutReparam c).comp ((continuous_apply i).comp continuous_snd))
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))).add
    ((continuous_subtype_val.comp continuous_fst).mul hc)

theorem splitHomotopyMap_zero (t : I^N) : splitHomotopyMap i c 0 t = t := by
  have h : (1 - ((0 : I) : ℝ)) * (t i : ℝ) + ((0 : I) : ℝ) * ((cutReparam c (t i) : I) : ℝ)
      = (t i : ℝ) := by
    rw [Set.Icc.coe_zero]; ring
  simp only [splitHomotopyMap]
  rw [h, Set.projIcc_val, Function.update_eq_self]

theorem splitHomotopyMap_one (t : I^N) :
    splitHomotopyMap i c 1 t = Function.update t i (cutReparam c (t i)) := by
  have h : (1 - ((1 : I) : ℝ)) * (t i : ℝ) + ((1 : I) : ℝ) * ((cutReparam c (t i) : I) : ℝ)
      = ((cutReparam c (t i) : I) : ℝ) := by
    rw [Set.Icc.coe_one]; ring
  simp only [splitHomotopyMap]
  rw [h, Set.projIcc_val]

theorem splitHomotopyMap_mem_boundary (s : I) {t : I^N} (ht : t ∈ Cube.boundary N) :
    splitHomotopyMap i c s t ∈ Cube.boundary N := by
  obtain ⟨j, hj⟩ := ht
  rcases eq_or_ne j i with rfl | hne
  · rcases hj with h0 | h1
    · refine ⟨j, Or.inl ?_⟩
      simp only [splitHomotopyMap]
      rw [Function.update_self, h0, cutReparam_zero]
      have h : (1 - (s : ℝ)) * ((0 : I) : ℝ) + (s : ℝ) * ((0 : I) : ℝ) = 0 := by
        rw [Set.Icc.coe_zero]; ring
      rw [h]
      exact projIcc_eq_zero le_rfl
    · refine ⟨j, Or.inr ?_⟩
      simp only [splitHomotopyMap]
      rw [Function.update_self, h1, cutReparam_one]
      have h : (1 - (s : ℝ)) * ((1 : I) : ℝ) + (s : ℝ) * ((1 : I) : ℝ) = 1 := by
        rw [Set.Icc.coe_one]; ring
      rw [h]
      exact projIcc_eq_one le_rfl
  · refine ⟨j, ?_⟩
    simp only [splitHomotopyMap]
    rwa [Function.update_of_ne hne]

/-- The straight-line reparametrization homotopy, rel the cube boundary, from `p` to
the concatenation of its two restrictions along the cut `t i = c`.-/
def splitHomotopy (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hcut : ∀ t : I^N, (t i : ℝ) = c → p t = x) :
    ContinuousMap.HomotopyRel p.1
      (GenLoop.transAt i (leftGenLoop p i c hc0 hc1 hcut)
        (rightGenLoop p i c hc0 hc1 hcut)).1
      (Cube.boundary N) where
  toFun st := p (splitHomotopyMap i c st.1 st.2)
  continuous_toFun := (map_continuous p.1).comp (continuous_splitHomotopyMap i c)
  map_zero_left t := by
    show p (splitHomotopyMap i c 0 t) = p.1 t
    rw [splitHomotopyMap_zero]
    rfl
  map_one_left t := by
    show p (splitHomotopyMap i c 1 t)
      = (GenLoop.transAt i (leftGenLoop p i c hc0 hc1 hcut)
          (rightGenLoop p i c hc0 hc1 hcut)).1 t
    rw [splitHomotopyMap_one]
    exact (transAt_left_right_apply p i c hc0 hc1 hcut t).symm
  prop' s t ht := by
    show p (splitHomotopyMap i c s t) = p.1 t
    exact (p.2 _ (splitHomotopyMap_mem_boundary i c s ht)).trans (p.2 t ht).symm

/-- **Hyperplane cut**: a generalized loop that collapses the slice `t i = c` to the
basepoint is homotopic rel boundary to the concatenation, along coordinate `i`, of
its left (`t i ∈ [0,c]`) and right (`t i ∈ [c,1]`) restrictions.-/
theorem homotopic_transAt_restrictions (hc0 : 0 < c) (hc1 : c < 1)
    (hcut : ∀ t : I^N, (t i : ℝ) = c → p t = x) :
    GenLoop.Homotopic p
      (GenLoop.transAt i (leftGenLoop p i c hc0.le hc1.le hcut)
        (rightGenLoop p i c hc0.le hc1.le hcut)) :=
  ⟨splitHomotopy p i c hc0.le hc1.le hcut⟩

/-- Class form of the hyperplane cut.  NOTE the order: by `HomotopyGroup.mul_spec`
(`⟦a⟧ * ⟦b⟧ = ⟦transAt i b a⟧`, the right factor runs first), the class of `p` is the
class of the RIGHT restriction times the class of the LEFT restriction.-/
theorem genLoopClass_eq_right_mul_left [Nonempty N] (hc0 : 0 < c) (hc1 : c < 1)
    (hcut : ∀ t : I^N, (t i : ℝ) = c → p t = x) :
    (⟦p⟧ : HomotopyGroup N X x)
      = ((· * ·) : HomotopyGroup N X x → HomotopyGroup N X x → HomotopyGroup N X x)
          ⟦rightGenLoop p i c hc0.le hc1.le hcut⟧
          ⟦leftGenLoop p i c hc0.le hc1.le hcut⟧ := by
  simp only [HomotopyGroup.mul_spec (i := i)]
  exact Quotient.sound (homotopic_transAt_restrictions p i c hc0 hc1 hcut)

end Submission
