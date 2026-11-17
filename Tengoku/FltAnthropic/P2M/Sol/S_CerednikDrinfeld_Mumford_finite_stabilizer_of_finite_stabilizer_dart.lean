import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_MumfordPeriod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Mumford_finite_stabilizer_of_finite_stabilizer_dart.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_Mumford_finite_stabilizer_of_finite_stabilizer_dart

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem solution
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (v : W) (hfin : (𝒯.neighborSet v).Finite) (hne : (𝒯.neighborSet v).Nonempty)
    (hD : ∀ d : 𝒯.Dart, d.fst = v → Finite (stabilizer G d)) :
    Finite (stabilizer G v) := by
  classical
  obtain ⟨w₀, hw₀⟩ := hne
  have hadj : 𝒯.Adj v w₀ := hw₀
  let d₀ : 𝒯.Dart := ⟨(v, w₀), hadj⟩
  haveI hfd : Finite (stabilizer G d₀) := hD d₀ rfl
  let H : Subgroup G := stabilizer G v

  let K : Subgroup ↥H := stabilizer (↥H) w₀
  have hKfin : Finite ↥K := by
    refine Finite.of_injective (fun k : ↥K => (⟨((k : ↥H) : G), ?_⟩ : stabilizer G d₀)) ?_
    · show ((k : ↥H) : G) • d₀ = d₀
      have h1 : ((k : ↥H) : G) • v = v := (k : ↥H).2
      have h2 : ((k : ↥H) : G) • w₀ = w₀ := k.2
      exact SimpleGraph.Dart.ext _ _ (Prod.ext h1 h2)
    · intro k₁ k₂ h
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun z : ↥(stabilizer G d₀) => (z : G)) h

  have horb : orbit (↥H) w₀ ⊆ 𝒯.neighborSet v := by
    rintro w ⟨h, rfl⟩
    show 𝒯.Adj v (((h : ↥H) : G) • w₀)
    have hv : ((h : ↥H) : G) • v = v := h.2
    conv_lhs => rw [← hv]
    exact GraphAction.smul_adj _ hadj
  haveI : Finite ↑(orbit (↥H) w₀) := Set.Finite.subset hfin horb
  haveI hQ : Finite (↥H ⧸ K) := Finite.of_equiv _ (orbitEquivQuotientStabilizer (↥H) w₀)
  haveI : Finite ↥K := hKfin
  have : Finite ↥H := Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := K)).symm
  exact this

