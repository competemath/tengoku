import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PhiGen
import Tengoku.Seed.Algebra.Polynomial.Bivariate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_swapBivar_eq_of_evalSymm.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_swapBivar_eq_of_evalSymm

noncomputable section
open HahnSeries Polynomial IntermediateField

namespace ModularCurve
export _root_.ModularCurve (EvalSymm swapBivar)
open _root_.ModularCurve
namespace SepFibre

section eval
variable {A B : Type*} [CommRing A] [CommRing B]

def ev (Φ : Polynomial (Polynomial ℤ)) (x y : A) : A := Φ.eval₂ (eval₂RingHom (Int.castRingHom A) x) y

/--
@isnad1 id=eq.0h2v.s6.1e81d43d1123 from=translated src=- shape=8e069a70 vocab=fa981774
-/
theorem aeval_toRingHom_eq [Algebra ℤ A] (x : A) :
    (Polynomial.aeval (R := ℤ) x).toRingHom = eval₂RingHom (Int.castRingHom A) x :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

/--
@isnad1 id=eq.0h4v.s6.9f4cc4bcbe49 from=translated src=- shape=f222a8a8 vocab=a74f00ce
-/
theorem ev_eq_evalEval (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev Φ x y = (Φ.map (mapRingHom (Int.castRingHom A))).evalEval x y := by
  rw [ev, ← eval₂_eval₂RingHom_apply]

/--
@isnad1 id=eq.0h6v.s7.92ee50c36b77 from=translated src=- shape=0795c24a vocab=39568fd8
-/
theorem map_ev (φ : A →+* B) (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    φ (ev Φ x y) = ev Φ (φ x) (φ y) := by
  rw [ev_eq_evalEval, ev_eq_evalEval, ← map_mapRingHom_evalEval φ, Polynomial.map_map, mapRingHom_comp,
    RingHom.ext_int (φ.comp (Int.castRingHom A)) (Int.castRingHom B)]

/--
@isnad1 id=eq.0h4v.s7.de757fbef3aa from=translated src=- shape=3949751a vocab=b6a5d460
-/
theorem ev_eq_aevalAeval (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev Φ x y = aevalAeval x y Φ := by
  have h : eval₂RingHom (eval₂RingHom (Int.castRingHom A) x) y = (aevalAeval (R := ℤ) x y).toRingHom := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_) ?_
    · simp
    · simp
  exact RingHom.congr_fun h Φ

/--
@isnad1 id=eq.0h4v.s7.0dd0cebdeb58 from=translated src=- shape=f036317e vocab=3ceb73c5
-/
theorem ev_swap (Φ : Polynomial (Polynomial ℤ)) (x y : A) : ev (Bivariate.swap Φ) x y = ev Φ y x := by
  rw [ev_eq_aevalAeval, ev_eq_aevalAeval, Bivariate.aevalAeval_swap]

/--
@isnad1 id=eq.0h3v.s4.d792bfd49c5b from=translated src=- shape=491d3b47 vocab=3aaa4888
-/
theorem ev_int (Φ : Polynomial (Polynomial ℤ)) (a b : ℤ) : ev Φ a b = Φ.evalEval a b := by
  rw [ev_eq_evalEval]
  congr 1
  have h : mapRingHom (Int.castRingHom ℤ) = RingHom.id (Polynomial ℤ) := by
    rw [RingHom.ext_int (Int.castRingHom ℤ) (RingHom.id ℤ)]; exact mapRingHom_id
  rw [h]; exact Polynomial.map_id

/--
@isnad1 id=eq.0h5v.s6.0217e28d8eac from=translated src=- shape=08ae441f vocab=63835398
-/
theorem ev_sub (Φ Ψ : Polynomial (Polynomial ℤ)) (x y : A) : ev (Φ - Ψ) x y = ev Φ x y - ev Ψ x y := by
  rw [ev_eq_aevalAeval, map_sub, ← ev_eq_aevalAeval, ← ev_eq_aevalAeval]

end eval

/--
@isnad1 id=eq.1h1v.s7.c6a422b5408e from=translated src=- shape=1c36d58c vocab=a0fbc6fb
-/
theorem swap_eq_of_evalSymm {Φ : Polynomial (Polynomial ℤ)} (h : EvalSymm Φ) : Bivariate.swap Φ = Φ := by
  set G : Polynomial (Polynomial ℤ) := Bivariate.swap Φ - Φ with hG

  have hL : ∀ x y : LaurentSeries ℚ, ev G x y = 0 := fun x y => by
    have hxy := h x y
    rw [aeval_toRingHom_eq, aeval_toRingHom_eq] at hxy
    rw [hG, ev_sub, ev_swap, sub_eq_zero]; exact hxy.symm
  let ι : ℤ →+* LaurentSeries ℚ := (algebraMap ℚ (LaurentSeries ℚ)).comp (Int.castRingHom ℚ)
  have hι : Function.Injective ι := (algebraMap ℚ (LaurentSeries ℚ)).injective.comp Int.cast_injective
  have hZ : ∀ a b : ℤ, G.evalEval a b = 0 := fun a b => hι (by rw [← ev_int, map_ev, hL, map_zero])

  have h1 : ∀ b : ℤ, G.eval (Polynomial.C b) = 0 := fun b =>
    Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem (f := fun a : ℤ => a)
      (fun _ _ h => h) fun a => hZ a b)
  have h2 : G = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem
      (f := fun b : ℤ => Polynomial.C b) (fun _ _ h => Polynomial.C_injective h) fun b => h1 b)
  exact sub_eq_zero.mp h2

/--
@isnad1 id=eq.0h1v.s8.1504975a04ee from=translated src=- shape=5120460a vocab=36ab63f7
-/
theorem swapBivar_eq_swap (Φ : Polynomial (Polynomial ℤ)) : swapBivar Φ = Bivariate.swap Φ := by
  have h : swapBivar = (Bivariate.swap (R := ℤ)).toAlgHom.toRingHom :=
    Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (RingHom.ext_int _ _)
      (by simp [Bivariate.swap_X])) (by simp [Bivariate.swap_Y])
  exact RingHom.congr_fun h Φ

/--
@isnad1 id=eq.1h1v.s7.2424bfad4f34 from=translated src=- shape=4d2965bc vocab=25e60cfb
-/
theorem swapBivar_eq_of_evalSymm' {Φ : Polynomial (Polynomial ℤ)} (h : EvalSymm Φ) : swapBivar Φ = Φ := by
  rw [swapBivar_eq_swap, swap_eq_of_evalSymm h]

end SepFibre

end ModularCurve
end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_swapBivar_eq_of_evalSymm.ModularCurve in
/--
@isnad1 id=eq.1h1v.s7.2424bfad4f34 from=translated src=- shape=4d2965bc vocab=25e60cfb
-/
theorem solution {Φ : Polynomial (Polynomial ℤ)} (h : EvalSymm Φ) :
    swapBivar Φ = Φ :=
  SepFibre.swapBivar_eq_of_evalSymm' h
