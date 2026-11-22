import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomologyEigen
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_isBaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_isBaseChange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=iseigens.5h13v.s15.de09b2b2b0d9 from=translated src=- shape=d03a7827 vocab=ba950fde
-/
theorem HeckeEis.isEigensystemH1_of_isEigensystemH1_of_isBaseChange
    (N : ℕ) {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (S₀ : Set ℕ)
    {V₀ V : Type} [AddCommGroup V₀] [Module K₀ V₀] [AddCommGroup V] [Module K V]
    (ρ₀ : Representation K₀ (CongruenceSubgroup.Gamma0 N) V₀) (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V)
    (a₀ : ℕ → (V₀ →ₗ[K₀] V₀)) (a : ℕ → (V →ₗ[K] V))
    (ha : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
        a ℓ ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a ℓ)
    (j : V₀ →ₛₗ[i] V) (hj : ∀ (g : CongruenceSubgroup.Gamma0 N) (v : V₀), j (ρ₀ g v) = ρ g (j v))
    (hja : ∀ (ℓ : ℕ) (v : V₀), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → j (a₀ ℓ v) = a ℓ (j v))
    (hbc : ∃ (ι : Type) (b₀ : Module.Basis ι K₀ V₀) (b : Module.Basis ι K V), ∀ s : ι, b s = j (b₀ s))
    (lam : ℕ → K₀) (h : HeckeEis.IsEigensystemH1 N ρ₀ a₀ S₀ lam) :
    HeckeEis.IsEigensystemH1 N ρ a S₀ (fun ℓ => i (lam ℓ)) := by exact @_root_.P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_isBaseChange.solution N K₀ K _ _ i S₀ V₀ V _ _ _ _ ρ₀ ρ a₀ a ha j hj hja hbc lam h
