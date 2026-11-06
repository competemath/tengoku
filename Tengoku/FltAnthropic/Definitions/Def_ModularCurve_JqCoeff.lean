import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open HahnSeries

namespace ModularCurve

section JExpansion

variable (K : Type*) [CommRing K]

def jqModC : LaurentSeries K :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K))

def jqNModC (N : ℕ) [NeZero N] : LaurentSeries K := qExpand K N (jqModC K)

/--
@isnad1 id=eq.0h1v.s4.816f314edb7c from=translated src=- shape=f1d8ce20 vocab=9db5ee4d
-/
@[simp]
theorem jqNModC_one : jqNModC K 1 = jqModC K := qExpand_one_apply _

variable {K} in

/--
@isnad1 id=eq.0h3v.s6.e382a71ab3eb from=translated src=- shape=74f86735 vocab=d4e00de3
-/
theorem map_jqModC {K' : Type*} [CommRing K'] (f : K →+* K') :
    (jqModC K).map f = jqModC K' := by
  have hmul : ∀ x y : LaurentSeries K, (x * y).map f = x.map f * y.map f :=
    fun x y => HahnSeries.map_mul f.toNonUnitalRingHom
  have hsingle : (HahnSeries.single (-1 : ℤ) (1 : K)).map f = HahnSeries.single (-1 : ℤ) 1 := by
    ext g
    rw [HahnSeries.map_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single, apply_ite f,
      map_one, map_zero]
  have hseries : ∀ u : PowerSeries K,
      (HahnSeries.ofPowerSeries ℤ K u).map f = HahnSeries.ofPowerSeries ℤ K' (u.map f) := by
    intro u
    ext k
    rw [HahnSeries.map_coeff]
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_map]
    · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]
  rw [jqModC, jqModC, hmul, hsingle, hseries,
    show (jNum.map (Int.castRingHom K)).map f = jNum.map (Int.castRingHom K') from by
      rw [show PowerSeries.map f (PowerSeries.map (Int.castRingHom K) jNum)
            = PowerSeries.map (f.comp (Int.castRingHom K)) jNum from
          (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom K) f)) jNum).symm,
        RingHom.ext_int (f.comp (Int.castRingHom K)) (Int.castRingHom K')]]

/--
@isnad1 id=eq.0h1v.s6.48e9588a61ea from=translated src=- shape=52047b64 vocab=d6f518e4
-/
theorem jqModC_eq_map_intCast : jqModC K = (jqModC ℤ).map (Int.castRingHom K) :=
  (map_jqModC (Int.castRingHom K)).symm

end JExpansion

section FunctionField

variable (K : Type*) [Field K]

def modularFunctionFieldC (N : ℕ) [NeZero N] :
    IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K {jqModC K, jqNModC K N}

/--
@isnad1 id=mem.0h2v.s7.98903bd24c1f from=translated src=- shape=69c93300 vocab=8fb587d3
-/
theorem jqModC_mem (N : ℕ) [NeZero N] : jqModC K ∈ modularFunctionFieldC K N :=
  IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)

/--
@isnad1 id=mem.0h2v.s7.028f826b7fb7 from=translated src=- shape=408ad163 vocab=02a81829
-/
theorem jqNModC_mem (N : ℕ) [NeZero N] : jqNModC K N ∈ modularFunctionFieldC K N :=
  IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)

/--
@isnad1 id=eq.0h1v.s7.19ee324ea602 from=translated src=- shape=b0330b72 vocab=af3d4dcf
-/
theorem modularFunctionFieldC_one :
    modularFunctionFieldC K 1 = IntermediateField.adjoin K {jqModC K} := by
  unfold modularFunctionFieldC
  rw [jqNModC_one, Set.pair_eq_singleton]

end FunctionField

end ModularCurve

end
