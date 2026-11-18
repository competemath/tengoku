import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicLevel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_image_pow_mem_nhds_one_units_adicCompletion.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_image_pow_mem_nhds_one_units_adicCompletion

set_option autoImplicit false

open NumberField IsDedekindDomain

/--
@isnad1 id=mem.2h4v.s11.1fc6e9b6c550 from=translated src=- shape=5ec9bb78 vocab=71fd709c
-/
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n)
    (V : Set (v.adicCompletion K)ˣ) (hV : V ∈ nhds (1 : (v.adicCompletion K)ˣ)) :
    (fun s : (v.adicCompletion K)ˣ => s ^ n) '' V ∈ nhds (1 : (v.adicCompletion K)ˣ) := by
  letI : NontriviallyNormedField (v.adicCompletion K) :=
    Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have hder : HasStrictDerivAt (fun x : v.adicCompletion K => x ^ n)
      ((n : v.adicCompletion K) * (1 : v.adicCompletion K) ^ (n - 1)) 1 := hasStrictDerivAt_pow n 1
  have hne : ((n : v.adicCompletion K) * (1 : v.adicCompletion K) ^ (n - 1)) ≠ 0 := by
    rw [one_pow, mul_one]; exact Nat.cast_ne_zero.2 hn.ne'
  have hmap : Filter.map (fun x : v.adicCompletion K => x ^ n) (nhds 1) = nhds 1 := by
    have h := hder.map_nhds_eq hne
    rwa [one_pow] at h
  have hemb : Topology.IsOpenEmbedding (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) :=
    Units.isOpenEmbedding_val
  have h1 : (Units.val '' V) ∈ nhds (((1 : (v.adicCompletion K)ˣ) : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
    rw [← hemb.map_nhds_eq]; exact Filter.image_mem_map hV
  rw [Units.val_one] at h1
  have h2 : (fun x : v.adicCompletion K => x ^ n) '' (Units.val '' V) ∈ nhds (1 : v.adicCompletion K) := by
    rw [← hmap]; exact Filter.image_mem_map h1
  have h3 : (fun x : v.adicCompletion K => x ^ n) '' (Units.val '' V) =
      Units.val '' ((fun s : (v.adicCompletion K)ˣ => s ^ n) '' V) := by
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr' fun s => ?_
    simp
  rw [h3] at h2
  rw [hemb.nhds_eq_comap, Units.val_one, Filter.mem_comap]
  exact ⟨_, h2, by rw [hemb.injective.preimage_image]⟩
