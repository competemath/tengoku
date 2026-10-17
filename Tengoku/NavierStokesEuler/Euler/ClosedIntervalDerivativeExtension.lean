import Tengoku.Seed.Analysis.Calculus.Deriv.Add
import Tengoku.Seed.Analysis.Calculus.Deriv.Mul
import Tengoku.Seed.Topology.Order.OrderClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
An explicit extension converts one-sided derivatives on a nondegenerate
closed time interval into ordinary derivatives there.  It uses affine tails
whose slopes are the actual endpoint derivatives.
-/

noncomputable section

namespace EulerClosedIntervalDerivativeExtension

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def affineExtension (f : ℝ → E) (g₀ gT : E) (T t : ℝ) : E :=
  if t < 0 then f 0 + t • g₀ else if T < t then f T + (t-T) • gT else f t

/--
@isnad1 id=eq.1h6v.s5.faef5b9cbffb from=translated src=- shape=e4216e20 vocab=89cc5bdb
-/
theorem affineExtension_eq {f : ℝ → E} {g₀ gT : E} {T t : ℝ}
    (ht : t ∈ Icc 0 T) : affineExtension f g₀ gT T t = f t := by
  simp only [affineExtension, not_lt.mpr ht.1, not_lt.mpr ht.2, ite_false]

/--
@isnad1 id=eq.2h6v.s7.ae93087b070d from=translated src=- shape=a76f329d vocab=7f700d06
-/
theorem affineExtension_eq_left {f : ℝ → E} {g₀ gT : E} {T t : ℝ}
    (hT : 0 ≤ T) (ht : t ≤ 0) : affineExtension f g₀ gT T t = f 0+t • g₀ := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [affineExtension, not_lt.mpr hT]
  · simp only [affineExtension, ht, ite_true]

/--
@isnad1 id=eq.2h6v.s7.8a99fbcb21f4 from=translated src=- shape=45536163 vocab=840478c6
-/
theorem affineExtension_eq_right {f : ℝ → E} {g₀ gT : E} {T t : ℝ}
    (hT : 0 ≤ T) (ht : T ≤ t) : affineExtension f g₀ gT T t = f T+(t-T) • gT := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [affineExtension, not_lt.mpr hT]
  · simp only [affineExtension, not_lt.mpr (hT.trans ht.le), ht, ite_false, ite_true]

/-- No continuity of the derivative is needed: the matching endpoint slopes
and the one-sided derivative suffice.
@isnad1 id=hasderiv.3h5v.s7.bda66b527a9a from=translated src=- shape=0e6d6d9e vocab=7dbdeb3f
-/
theorem affineExtension_hasDerivAt {f g : ℝ → E} {T t : ℝ}
    (hT : 0 < T) (ht : t ∈ Icc 0 T)
    (hf : HasDerivWithinAt f (g t) (Icc 0 T) t) :
    HasDerivAt (affineExtension f (g 0) (g T) T) (g t) t := by
  have hwithin : HasDerivWithinAt (affineExtension f (g 0) (g T) T) (g t) (Icc 0 T) t :=
    hf.congr_of_mem (fun _ hs => affineExtension_eq hs) ht
  by_cases ht0 : t = 0
  · subst t
    have hleft : HasDerivAt (fun s : ℝ => f 0+s • g 0) (g 0) 0 := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const (g 0)).const_add (f 0)
    have hl := hleft.hasDerivWithinAt.congr_of_mem
      (fun s (hs : s ∈ Iic (0:ℝ)) => affineExtension_eq_left (gT := g T) hT.le hs) self_mem_Iic
    have hr := hwithin.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hT)
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr
  · by_cases htT : t = T
    · subst t
      have hright : HasDerivAt (fun s : ℝ => f T+(s-T) • g T) (g T) T := by
        simpa only [one_smul, id_eq] using (((hasDerivAt_id T).sub_const T).smul_const (g T)).const_add (f T)
      have hr := hright.hasDerivWithinAt.congr_of_mem
        (fun s (hs : s ∈ Ici T) => affineExtension_eq_right (g₀ := g 0) hT.le hs) self_mem_Ici
      have hl := hwithin.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hT)
      simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr
    · exact hwithin.hasDerivAt (Icc_mem_nhds (lt_of_le_of_ne ht.1 (Ne.symm ht0))
        (lt_of_le_of_ne ht.2 htT))

/--
@isnad1 id=ex.2h4v.s7.be0df34fe248 from=translated src=- shape=c5d6aace vocab=cd258ce5
-/
theorem exists_extension {f g : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hf : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (g t) (Icc 0 T) t) :
    ∃ F : ℝ → E, EqOn F f (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, HasDerivAt F (g t) t := by
  refine ⟨affineExtension f (g 0) (g T) T, fun _ ht => affineExtension_eq ht, ?_⟩
  intro t ht
  exact affineExtension_hasDerivAt hT ht (hf t ht)

end EulerClosedIntervalDerivativeExtension
