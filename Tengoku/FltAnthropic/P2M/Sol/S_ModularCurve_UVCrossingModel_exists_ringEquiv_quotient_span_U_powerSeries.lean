import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries.lean`: wrote out 6 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`, 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries

universe u

noncomputable section

namespace ModularCurve
export _root_.ModularCurve (uvCrossingIdeal UVCrossingModel UVCrossingModel.mk UVCrossingModel.U UVCrossingModel.V UVCrossingModel.const)
open _root_.ModularCurve

namespace PortB2

open _root_.ModularCurve.UVCrossingModel
section PowerSeriesMapKernel

variable {R : Type u} [CommRing R]

/--
@isnad1 id=eq.0h2v.s8.9bd56e37c097 from=translated src=- shape=51583f01 vocab=94e5e8fd
-/
theorem ker_powerSeriesMap_quotientMk (r : R) :
    RingHom.ker (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {r}))) =
      Ideal.span {(PowerSeries.C r : PowerSeries R)} := by
  refine le_antisymm (fun φ hφ => ?_) ?_
  · rw [RingHom.mem_ker] at hφ
    have hcoeff : ∀ n : ℕ, r ∣ PowerSeries.coeff n φ := by
      intro n
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, ← PowerSeries.coeff_map,
        hφ, map_zero]
    choose ψ hψ using hcoeff
    rw [Ideal.mem_span_singleton]
    refine ⟨PowerSeries.mk ψ, PowerSeries.ext fun n => ?_⟩
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    exact hψ n
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      PowerSeries.map_C,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self r), map_zero]

end PowerSeriesMapKernel

section KillVariable

variable {W : Type u} [CommRing W]

def uBranchEmb : Unit ↪ Fin 2 :=
  ⟨fun _ => 1, fun a b _ => Subsingleton.elim a b⟩

def vBranchEmb : Unit ↪ Fin 2 :=
  ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩

/--
@isnad1 id=eq.0h1v.s5.86b11100f3c9 from=translated src=- shape=f493abca vocab=6f1ad0e7
-/
@[scoped simp] theorem uBranchEmb_apply (x : Unit) : uBranchEmb x = 1 := rfl

/--
@isnad1 id=eq.0h1v.s5.13291fb6ebe7 from=translated src=- shape=f493abca vocab=477447cc
-/
@[scoped simp] theorem vBranchEmb_apply (x : Unit) : vBranchEmb x = 0 := rfl

/--
@isnad1 id=not.0h0v.s6.433c5acdc1a8 from=translated src=- shape=8298c314 vocab=ddab020f
-/
theorem zero_notMem_range_uBranchEmb : (0 : Fin 2) ∉ Set.range uBranchEmb := by
  rintro ⟨x, hx⟩
  rw [uBranchEmb_apply] at hx
  exact absurd hx (by decide)

/--
@isnad1 id=not.0h0v.s6.a883792ae52d from=translated src=- shape=8298c314 vocab=24d64b3f
-/
theorem one_notMem_range_vBranchEmb : (1 : Fin 2) ∉ Set.range vBranchEmb := by
  rintro ⟨x, hx⟩
  rw [vBranchEmb_apply] at hx
  exact absurd hx (by decide)

/--
@isnad1 id=eq.1h1v.s6.370bef2226b4 from=translated src=- shape=2ac60be8 vocab=3387b671
-/
theorem uBranchEmb_cover : ∀ j : Fin 2, j ≠ 0 → j = uBranchEmb () := by decide

/--
@isnad1 id=eq.1h1v.s6.5a08a850a23c from=translated src=- shape=2ac60be8 vocab=272e5465
-/
theorem vBranchEmb_cover : ∀ j : Fin 2, j ≠ 1 → j = vBranchEmb () := by decide

def killVarHom (e : Unit ↪ Fin 2) : MvPowerSeries (Fin 2) W →+* MvPowerSeries Unit W :=
  (MvPowerSeries.killCompl e).toRingHom

/--
@isnad1 id=eq.0h2v.s7.10373edf2943 from=translated src=- shape=b5e90ef3 vocab=b645799d
-/
theorem killVarHom_X_keep (e : Unit ↪ Fin 2) :
    killVarHom (W := W) e (MvPowerSeries.X (e ())) = PowerSeries.X :=
  MvPowerSeries.killCompl_X ()

/--
@isnad1 id=eq.1h3v.s7.33f8f49a9fbe from=translated src=- shape=b1c21129 vocab=61fe8cba
-/
theorem killVarHom_X_kill (e : Unit ↪ Fin 2) {t : Fin 2} (ht : t ∉ Set.range e) :
    killVarHom (W := W) e (MvPowerSeries.X t) = 0 :=
  MvPowerSeries.killCompl_X_eq_zero ht

/--
@isnad1 id=eq.0h3v.s8.941b5cb40048 from=translated src=- shape=7a2ff489 vocab=97ef9bc6
-/
theorem killVarHom_C (e : Unit ↪ Fin 2) (w : W) :
    killVarHom e (MvPowerSeries.C w) = PowerSeries.C w :=
  MvPowerSeries.killCompl_C w

/--
@isnad1 id=surjecti.0h2v.s7.14e4c15c5203 from=translated src=- shape=8a44225c vocab=a2096b57
-/
theorem killVarHom_surjective (e : Unit ↪ Fin 2) :
    Function.Surjective (killVarHom (W := W) e) := fun q =>
  ⟨MvPowerSeries.rename (⇑e) q, MvPowerSeries.killCompl_rename_app q⟩

/--
@isnad1 id=eq.2h3v.s8.452566e1227f from=translated src=- shape=0f857711 vocab=79274286
-/
theorem ker_killVarHom (e : Unit ↪ Fin 2) (t : Fin 2) (ht : t ∉ Set.range e)
    (hcover : ∀ j : Fin 2, j ≠ t → j = e ()) :
    RingHom.ker (killVarHom (W := W) e) =
      Ideal.span {(MvPowerSeries.X t : MvPowerSeries (Fin 2) W)} := by
  refine le_antisymm (fun φ hφ => ?_) ?_
  · rw [RingHom.mem_ker] at hφ
    have hφ' : MvPowerSeries.killCompl e φ = 0 := hφ
    rw [Ideal.mem_span_singleton, MvPowerSeries.X_dvd_iff]
    intro m hm
    have hne : e () ≠ t := fun h => ht (h ▸ Set.mem_range_self ())
    have hm_eq : m = Finsupp.embDomain e (Finsupp.single () (m (e ()))) := by
      rw [Finsupp.embDomain_single]
      ext j
      rcases eq_or_ne j t with hj | hj
      · rw [hj, hm, Finsupp.single_eq_of_ne' hne]
      · rw [hcover j hj, Finsupp.single_eq_same]
    rw [hm_eq, ← MvPowerSeries.coeff_killCompl, hφ', map_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact killVarHom_X_kill e ht

end KillVariable

section BranchProjection

variable {W : Type u} [CommRing W]

def branchProjection (e : Unit ↪ Fin 2) (π : W) :
    MvPowerSeries (Fin 2) W →+* PowerSeries (W ⧸ Ideal.span {π}) :=
  (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {π}))).comp (killVarHom e)

/--
@isnad1 id=eq.0h3v.s8.f61686a69818 from=translated src=- shape=df37d083 vocab=d5072c1e
-/
theorem branchProjection_X_keep (e : Unit ↪ Fin 2) (π : W) :
    branchProjection e π (MvPowerSeries.X (e ())) = PowerSeries.X :=
  (congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {π})))
    (killVarHom_X_keep e)).trans (PowerSeries.map_X _)

/--
@isnad1 id=eq.1h4v.s9.4043f496503e from=translated src=- shape=fc0b3df8 vocab=eb11019b
-/
theorem branchProjection_X_kill (e : Unit ↪ Fin 2) (π : W) {t : Fin 2}
    (ht : t ∉ Set.range e) :
    branchProjection e π (MvPowerSeries.X t) = 0 :=
  (congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {π})))
    (killVarHom_X_kill e ht)).trans (map_zero _)

/--
@isnad1 id=eq.0h4v.s10.3f0ce455d08a from=translated src=- shape=5a92976b vocab=86234b52
-/
theorem branchProjection_C (e : Unit ↪ Fin 2) (π : W) (w : W) :
    branchProjection e π (MvPowerSeries.C w) =
      PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w) :=
  (congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {π})))
    (killVarHom_C e w)).trans (PowerSeries.map_C _ w)

/--
@isnad1 id=surjecti.0h3v.s8.e384e88ed628 from=translated src=- shape=d8ecdf81 vocab=9d0e248c
-/
theorem branchProjection_surjective (e : Unit ↪ Fin 2) (π : W) :
    Function.Surjective (branchProjection e π) :=
  (PowerSeries.map_surjective _ Ideal.Quotient.mk_surjective).comp (killVarHom_surjective e)

/--
@isnad1 id=eq.2h4v.s9.fb1beb6e234a from=translated src=- shape=5ce0976c vocab=9d8343d1
-/
theorem ker_branchProjection (e : Unit ↪ Fin 2) (t : Fin 2) (ht : t ∉ Set.range e)
    (hcover : ∀ j : Fin 2, j ≠ t → j = e ()) (π : W) :
    RingHom.ker (branchProjection e π) =
      Ideal.span {(MvPowerSeries.X t : MvPowerSeries (Fin 2) W)} ⊔
        Ideal.span {(MvPowerSeries.C π : MvPowerSeries (Fin 2) W)} := by
  have hker : RingHom.ker (branchProjection e π) =
      Ideal.comap (killVarHom e)
        (RingHom.ker (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {π})))) :=
    (RingHom.comap_ker _ _).symm
  have hmap : Ideal.span {(PowerSeries.C π : PowerSeries W)} =
      Ideal.map (killVarHom e)
        (Ideal.span {(MvPowerSeries.C π : MvPowerSeries (Fin 2) W)}) := by
    rw [Ideal.map_span, Set.image_singleton, killVarHom_C]
  rw [hker, ker_powerSeriesMap_quotientMk, hmap,
    Ideal.comap_map_of_surjective _ (killVarHom_surjective e), ← RingHom.ker_eq_comap_bot,
    ker_killVarHom e t ht hcover, sup_comm]

/--
@isnad1 id=eq.1h3v.s9.c8eaadeb351e from=translated src=- shape=0a697240 vocab=2d96139f
-/
theorem uvCrossingIdeal_sup_span_X (t : Fin 2) (π : W)
    (hdvd : (MvPowerSeries.X t : MvPowerSeries (Fin 2) W) ∣
      MvPowerSeries.X 0 * MvPowerSeries.X 1) :
    uvCrossingIdeal W π ⊔ Ideal.span {(MvPowerSeries.X t : MvPowerSeries (Fin 2) W)} =
      Ideal.span {(MvPowerSeries.X t : MvPowerSeries (Fin 2) W)} ⊔
        Ideal.span {(MvPowerSeries.C π : MvPowerSeries (Fin 2) W)} := by
  refine le_antisymm (sup_le ?_ le_sup_left) (sup_le le_sup_right ?_)
  ·
    refine Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
    refine Submodule.sub_mem _ ?_ ?_
    · exact Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr hdvd)
    · exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  ·
    refine Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
    have hCπ : (MvPowerSeries.C π : MvPowerSeries (Fin 2) W) =
        MvPowerSeries.X 0 * MvPowerSeries.X 1 -
          (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C π) := by
      ring
    rw [hCπ]
    refine Submodule.sub_mem _ ?_ ?_
    · exact Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr hdvd)
    · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

end BranchProjection

variable {W : Type u} [CommRing W]

/--
@isnad1 id=eq.0h3v.s9.f9c3af5e94d3 from=translated src=- shape=92b55c7d vocab=54f5cf10
-/
theorem span_mk_X_eq_map (t : Fin 2) (π : W) :
    Ideal.span {UVCrossingModel.mk π (MvPowerSeries.X t)} =
      Ideal.map (Ideal.Quotient.mk (uvCrossingIdeal W π))
        (Ideal.span {(MvPowerSeries.X t : MvPowerSeries (Fin 2) W)}) := by
  rw [Ideal.map_span, Set.image_singleton]
  rfl

def branchQuotientEquiv (e : Unit ↪ Fin 2) (t : Fin 2) (ht : t ∉ Set.range e)
    (hcover : ∀ j : Fin 2, j ≠ t → j = e ())
    (hdvd : (MvPowerSeries.X t : MvPowerSeries (Fin 2) W) ∣
      MvPowerSeries.X 0 * MvPowerSeries.X 1) (π : W) :
    (UVCrossingModel W π ⧸ Ideal.span {UVCrossingModel.mk π (MvPowerSeries.X t)}) ≃+*
      PowerSeries (W ⧸ Ideal.span {π}) :=
  (Ideal.quotEquivOfEq (span_mk_X_eq_map t π)).trans <|
    (DoubleQuot.quotQuotEquivQuotSup (uvCrossingIdeal W π)
      (Ideal.span {(MvPowerSeries.X t : MvPowerSeries (Fin 2) W)})).trans <|
      (Ideal.quotEquivOfEq
        ((uvCrossingIdeal_sup_span_X t π hdvd).trans
          (ker_branchProjection e t ht hcover π).symm)).trans
        (RingHom.quotientKerEquivOfSurjective (branchProjection_surjective e π))

/--
@isnad1 id=eq.3h5v.s13.ad6ff2fd21be from=translated src=- shape=468cb6fa vocab=acb61a69
-/
theorem branchQuotientEquiv_mk (e : Unit ↪ Fin 2) (t : Fin 2) (ht : t ∉ Set.range e)
    (hcover : ∀ j : Fin 2, j ≠ t → j = e ())
    (hdvd : (MvPowerSeries.X t : MvPowerSeries (Fin 2) W) ∣
      MvPowerSeries.X 0 * MvPowerSeries.X 1) (π : W) (f : MvPowerSeries (Fin 2) W) :
    branchQuotientEquiv e t ht hcover hdvd π
        (Ideal.Quotient.mk (Ideal.span {UVCrossingModel.mk π (MvPowerSeries.X t)})
          (UVCrossingModel.mk π f)) =
      branchProjection e π f :=
  rfl

def uBranchEquiv (π : W) :
    (UVCrossingModel W π ⧸ Ideal.span {UVCrossingModel.U π}) ≃+*
      PowerSeries (W ⧸ Ideal.span {π}) :=
  branchQuotientEquiv uBranchEmb 0 zero_notMem_range_uBranchEmb uBranchEmb_cover
    (dvd_mul_right _ _) π

def vBranchEquiv (π : W) :
    (UVCrossingModel W π ⧸ Ideal.span {UVCrossingModel.V π}) ≃+*
      PowerSeries (W ⧸ Ideal.span {π}) :=
  branchQuotientEquiv vBranchEmb 1 one_notMem_range_vBranchEmb vBranchEmb_cover
    (dvd_mul_left _ _) π

/--
@isnad1 id=eq.0h3v.s12.27e5967ebe1f from=translated src=- shape=64fa325c vocab=9f3389c6
-/
theorem uBranchEquiv_mk (π : W) (f : MvPowerSeries (Fin 2) W) :
    uBranchEquiv π (Ideal.Quotient.mk _ (UVCrossingModel.mk π f)) =
      branchProjection uBranchEmb π f :=
  branchQuotientEquiv_mk uBranchEmb 0 zero_notMem_range_uBranchEmb uBranchEmb_cover
    (dvd_mul_right _ _) π f

/--
@isnad1 id=eq.0h2v.s11.75147c4fe032 from=translated src=- shape=2745c6f5 vocab=bebc431c
-/
theorem uBranchEquiv_mk_V (π : W) :
    uBranchEquiv π (Ideal.Quotient.mk _ (UVCrossingModel.V π)) = PowerSeries.X :=
  (uBranchEquiv_mk π (MvPowerSeries.X 1)).trans (branchProjection_X_keep uBranchEmb π)

/--
@isnad1 id=eq.0h2v.s12.56c08160fc1f from=translated src=- shape=8ebee68d vocab=08a7c36e
-/
theorem uBranchEquiv_mk_U (π : W) :
    uBranchEquiv π (Ideal.Quotient.mk _ (UVCrossingModel.U π)) = 0 :=
  (uBranchEquiv_mk π (MvPowerSeries.X 0)).trans
    (branchProjection_X_kill uBranchEmb π zero_notMem_range_uBranchEmb)

/--
@isnad1 id=eq.0h3v.s12.394b3ee453ce from=translated src=- shape=f31ed8d5 vocab=530310d3
-/
theorem uBranchEquiv_mk_const (π : W) (w : W) :
    uBranchEquiv π (Ideal.Quotient.mk _ (UVCrossingModel.const π w)) =
      PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w) :=
  (uBranchEquiv_mk π (MvPowerSeries.C w)).trans (branchProjection_C uBranchEmb π w)

end PortB2
open scoped _root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries.ModularCurve.PortB2

end ModularCurve
open scoped _root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries.ModularCurve.PortB2 _root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries.ModularCurve

end
open scoped _root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries.ModularCurve.PortB2 _root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries.ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries.ModularCurve ModularCurve.UVCrossingModel in
/--
@isnad1 id=ex.0h2v.s13.8450add8bb56 from=translated src=- shape=a19d46fb vocab=4a2f30b6
-/
theorem solution {W : Type*} [CommRing W] (π : W) :
    ∃ e : (UVCrossingModel W π ⧸ Ideal.span {U π}) ≃+* PowerSeries (W ⧸ Ideal.span {π}), e (Ideal.Quotient.mk _ (V π)) = PowerSeries.X ∧ e (Ideal.Quotient.mk _ (U π)) = 0 ∧ ∀ w : W, e (Ideal.Quotient.mk _ (const π w)) = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w) :=
  ⟨ModularCurve.PortB2.uBranchEquiv π, ModularCurve.PortB2.uBranchEquiv_mk_V π, ModularCurve.PortB2.uBranchEquiv_mk_U π, ModularCurve.PortB2.uBranchEquiv_mk_const π⟩
