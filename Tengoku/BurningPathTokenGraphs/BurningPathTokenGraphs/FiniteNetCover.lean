import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.ContinuousCover
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Converting finite nets into normalized ranked covers

The net points are assigned to the largest available normalized ranks.
-/

namespace BurningPath

/-- Embed `M` indices into the top `M` ranks of a list of length `q`.-/
def topRankEmbedding (q M : ℕ) (hMq : M ≤ q) : Fin M ↪ Fin q where
  toFun i := ⟨q - M + i.val, by omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val hij)

/--
@isnad1 id=eq.1h3v.s5.8afa89571d2e from=translated src=- shape=dfcc76de vocab=bb197572
-/
@[simp]
theorem topRankEmbedding_val (q M : ℕ) (hMq : M ≤ q) (i : Fin M) :
    (topRankEmbedding q M hMq i).val = q - M + i.val :=
  rfl

/--
A legal `δ`-net with `M` points gives a normalized cover of length `q`
whenever the lowest of the top `M` ranks has radius at least `δ`.
@isnad1 id=hasl1nor.6h6v.s7.92c125f8086c from=translated src=- shape=d1d1f61f vocab=39d4338f
-/
theorem hasL1NormalizedRankedCover_of_finiteNet {k M q : ℕ}
    {S : Set (Fin k → ℝ)} {δ : ℝ}
    (hS : S.Nonempty) (hq : 1 ≤ q) (hMq : M ≤ q)
    (net : Fin M → (Fin k → ℝ))
    (hlegal : ∀ i, net i ∈ S)
    (hnet : ∀ x ∈ S, ∃ i, realL1Dist x (net i) ≤ δ)
    (hradius : δ ≤ ((q - M : ℕ) : ℝ) / q) :
    HasL1NormalizedRankedCover S q := by
  classical
  obtain ⟨x, hx⟩ := hS
  obtain ⟨i, _⟩ := hnet x hx
  have hMpos : 0 < M := Fin.pos_iff_nonempty.mpr ⟨i⟩
  let e := topRankEmbedding q M hMq
  let defaultCenter := net ⟨0, hMpos⟩
  let centers : Fin q → (Fin k → ℝ) :=
    Function.extend e net (fun _ ↦ defaultCenter)
  have hcenters (i : Fin M) : centers (e i) = net i :=
    e.injective.extend_apply net (fun _ ↦ defaultCenter) i
  refine ⟨centers, ?_, ?_⟩
  · intro r
    by_cases hr : r ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hr
      rw [hcenters]
      exact hlegal i
    · change Function.extend e net (fun _ ↦ defaultCenter) r ∈ S
      rw [Function.extend_apply' net (fun _ ↦ defaultCenter) r]
      · exact hlegal ⟨0, hMpos⟩
      · simpa only [Set.mem_range] using hr
  · intro y hy
    obtain ⟨j, hj⟩ := hnet y hy
    refine ⟨e j, ?_⟩
    rw [hcenters]
    calc
      realL1Dist y (net j) ≤ δ := hj
      _ ≤ ((q - M : ℕ) : ℝ) / q := hradius
      _ ≤ ((e j).val : ℝ) / q := by
        have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
        apply div_le_div_of_nonneg_right _ hqpos.le
        simp only [e, topRankEmbedding_val]
        exact_mod_cast Nat.le_add_right (q - M) j.val

end BurningPath
