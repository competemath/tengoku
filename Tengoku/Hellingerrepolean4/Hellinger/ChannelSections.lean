import Tengoku.Hellingerrepolean4.Hellinger.ParityBlocks
import Tengoku.Hellingerrepolean4.Hellinger.PaperSpecs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms translation_hellinger` (it only prints; the queue checks the axioms of every declaration). -/

/-! Reindexing and actual coordinate sections of the product BSC.
The section comparison is finite conditional Jensen with the original
outside-coordinate kernel. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.ChannelSections

variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

/--
@isnad1 id=eq.0h4v.s5.ea2bd448892b from=translated src=- shape=72282452 vocab=c365be2e
-/
theorem mean_comp_equiv (e : Ω ≃ Λ) (f : Λ → ℝ) : mean (f ∘ e) = mean f := by
  simp only [mean, Function.comp_apply]
  rw [Fintype.card_congr e, e.sum_comp]

/--
@isnad1 id=le.1h3v.s5.d81e0584d3cc from=translated src=- shape=6f600fa3 vocab=3b642aae
-/
theorem mean_mono (f g : Ω → ℝ) (h : ∀ x, f x ≤ g x) : mean f ≤ mean g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => h x)) (by positivity)

/--
@isnad1 id=eq.0h3v.s5.8f664f676ca7 from=translated src=- shape=fbfa7000 vocab=fd454fd3
-/
theorem mean_prod (f : Ω × Λ → ℝ) :
    mean f = mean (fun x => mean (fun y => f (x, y))) := by
  simp only [mean, Fintype.card_prod, Nat.cast_mul, mul_inv, Fintype.sum_prod_type,
    ← Finset.mul_sum]
  ring

/--
@isnad1 id=eq.0h3v.s5.3f55ba8e338b from=translated src=- shape=ffec3d6e vocab=fd454fd3
-/
theorem mean_prod_swap (f : Ω × Λ → ℝ) :
    mean f = mean (fun y => mean (fun x => f (x, y))) := by
  rw [mean_prod]
  simp only [mean, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

def productChannel (K : UniformChannel Ω) (L : UniformChannel Λ) : UniformChannel (Ω × Λ) where
  weight x y := K.weight x.1 y.1 * L.weight x.2 y.2
  nonneg x y := mul_nonneg (K.nonneg _ _) (L.nonneg _ _)
  row_sum x := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, L.row_sum, mul_one, K.row_sum]
  column_sum y := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, L.column_sum, mul_one, K.column_sum]

/--
@isnad1 id=eq.0h7v.s6.02b5b3f042bd from=translated src=- shape=e68d5097 vocab=63e34287
-/
theorem productChannel_apply (K : UniformChannel Ω) (L : UniformChannel Λ)
    (f : Ω × Λ → ℝ) (x : Ω) (y : Λ) :
    (productChannel K L).apply f (x, y) =
      L.apply (fun z => K.apply (fun w => f (w, z)) x) y := by
  simp only [UniformChannel.apply, productChannel, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  ring

/--
@isnad1 id=le.1h5v.s6.3b96282d90f2 from=translated src=- shape=fce0ca12 vocab=f2c6fc53
-/
theorem sections_root_mean_le (K : UniformChannel Ω) (L : UniformChannel Λ)
    (f : Ω × Λ → ℝ) (hf : ∀ p, f p ∈ Set.Icc (-1 : ℝ) 1) :
    mean (fun z => mean (fun y => root (K.apply (fun x => f (x, z)) y))) ≤
      mean (fun p => root ((productChannel K L).apply f p)) := by
  rw [mean_prod]
  have hswap := mean_prod_swap
    (fun p : Ω × Λ => root (K.apply (fun x => f (x, p.2)) p.1))
  rw [mean_prod] at hswap
  rw [← hswap]
  apply mean_mono
  intro y
  simpa only [productChannel_apply] using L.concave_mean_expands
    (fun z => K.apply (fun x => f (x, z)) y) root root_concave
    (fun z => K.apply_mem_Icc _ (fun x => hf (x, z)) y)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def indexedBSC (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : UniformChannel (ι → Bool) :=
  UniformChannel.product (fun _ : ι => bsc ρ hρ)

def cubeEquiv (e : ι ≃ κ) : (ι → Bool) ≃ (κ → Bool) :=
  Equiv.arrowCongr e (Equiv.refl Bool)

/--
@isnad1 id=eq.1h6v.s7.d2a3cddc5370 from=translated src=- shape=65042e9d vocab=721fef79
-/
theorem indexedBSC_weight_reindex (e : ι ≃ κ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (x y : ι → Bool) :
    (indexedBSC κ ρ hρ).weight (cubeEquiv e x) (cubeEquiv e y) =
      (indexedBSC ι ρ hρ).weight x y := by
  exact e.symm.prod_comp (fun i => (bsc ρ hρ).weight (x i) (y i))

/--
@isnad1 id=eq.1h6v.s7.5d22414a4e74 from=translated src=- shape=00466d86 vocab=958e13dd
-/
theorem indexedBSC_apply_reindex (e : ι ≃ κ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (f : (κ → Bool) → ℝ) (x : ι → Bool) :
    (indexedBSC ι ρ hρ).apply (f ∘ cubeEquiv e) x =
      (indexedBSC κ ρ hρ).apply f (cubeEquiv e x) := by
  unfold UniformChannel.apply
  rw [← (cubeEquiv e).sum_comp
    (fun y => (indexedBSC κ ρ hρ).weight (cubeEquiv e x) y * f y)]
  simp only [indexedBSC_weight_reindex, Function.comp_apply]

/--
@isnad1 id=le.3h3v.s7.9cc7ef399195 from=translated src=- shape=64549bd7 vocab=a1643ebf
-/
theorem indexed_antipodal_hellinger [Nonempty ι]
    (f : (ι → Bool) → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (fun i => !(x i)) = -f x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    root ρ ≤ mean (fun y => root ((indexedBSC ι ρ hρ).apply f y)) := by
  let n := Fintype.card ι - 1
  have hn : Fintype.card ι = n + 1 := by
    have := Fintype.card_pos (α := ι)
    omega
  let e : ι ≃ Fin (n + 1) := (Fintype.equivFin ι).trans (finCongr hn)
  let g : (Fin (n + 1) → Bool) → ℝ := f ∘ cubeEquiv e.symm
  have hg : ∀ x, g x = -1 ∨ g x = 1 := fun x => hf _
  have hga : ∀ x, g (antipode (n + 1) x) = -g x := by
    intro x
    exact hanti (cubeEquiv e.symm x)
  have h := ParityBlocks.antipodal_hellinger n g hg hga ρ hρ
  have hcomp : g ∘ cubeEquiv e = f := by
    funext x
    exact congrArg f ((cubeEquiv e).symm_apply_apply x)
  have hpoint (x : ι → Bool) :
      (indexedBSC ι ρ hρ).apply f x =
        (cubeBSC (n + 1) ρ hρ).apply g (cubeEquiv e x) := by
    rw [← hcomp]
    exact indexedBSC_apply_reindex e ρ hρ g x
  simp_rw [hpoint]
  have hm := mean_comp_equiv (cubeEquiv e)
    (fun y => root ((cubeBSC (n + 1) ρ hρ).apply g y))
  exact hm ▸ h

def splitCube (p : ι → Prop) [DecidablePred p] :
    (ι → Bool) ≃ (({i // p i} → Bool) × ({i // ¬p i} → Bool)) :=
  Equiv.piEquivPiSubtypeProd p (fun _ => Bool)

/--
@isnad1 id=eq.1h5v.s9.5b6593683b19 from=translated src=- shape=d13266da vocab=bb805839
-/
theorem indexedBSC_weight_split (p : ι → Prop) [DecidablePred p]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x y : ι → Bool) :
    (productChannel (indexedBSC {i // p i} ρ hρ) (indexedBSC {i // ¬p i} ρ hρ)).weight
      (splitCube p x) (splitCube p y) = (indexedBSC ι ρ hρ).weight x y := by
  exact Fintype.prod_subtype_mul_prod_subtype p (fun i => (bsc ρ hρ).weight (x i) (y i))

/--
@isnad1 id=eq.1h5v.s9.892f5db2b1d1 from=translated src=- shape=d957325c vocab=dbb0a8dd
-/
theorem indexedBSC_apply_split (p : ι → Prop) [DecidablePred p]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (g : (({i // p i} → Bool) × ({i // ¬p i} → Bool)) → ℝ) (x : ι → Bool) :
    (indexedBSC ι ρ hρ).apply (g ∘ splitCube p) x =
      (productChannel (indexedBSC {i // p i} ρ hρ) (indexedBSC {i // ¬p i} ρ hρ)).apply
        g (splitCube p x) := by
  unfold UniformChannel.apply
  rw [← (splitCube p).sum_comp
    (fun y => (productChannel (indexedBSC {i // p i} ρ hρ)
      (indexedBSC {i // ¬p i} ρ hρ)).weight (splitCube p x) y * g y)]
  simp only [indexedBSC_weight_split, Function.comp_apply]

/--
@isnad1 id=le.2h4v.s9.d56b75fb1026 from=translated src=- shape=84181ad1 vocab=71a3312f
-/
theorem indexedBSC_root_sections (p : ι → Prop) [DecidablePred p]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : (ι → Bool) → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    mean (fun z : {i // ¬p i} → Bool => mean (fun y : {i // p i} → Bool =>
      root ((indexedBSC {i // p i} ρ hρ).apply
        (fun w => f ((splitCube p).symm (w, z))) y))) ≤
      mean (fun y => root ((indexedBSC ι ρ hρ).apply f y)) := by
  let g := f ∘ (splitCube p).symm
  have hcomp : g ∘ splitCube p = f := by
    funext x
    exact congrArg f ((splitCube p).symm_apply_apply x)
  have hpoint (x : ι → Bool) :
      (indexedBSC ι ρ hρ).apply f x =
        (productChannel (indexedBSC {i // p i} ρ hρ)
          (indexedBSC {i // ¬p i} ρ hρ)).apply g (splitCube p x) := by
    rw [← hcomp]
    exact indexedBSC_apply_split p ρ hρ g x
  simp_rw [hpoint]
  have hm := mean_comp_equiv (splitCube p)
    (fun y => root ((productChannel (indexedBSC {i // p i} ρ hρ)
      (indexedBSC {i // ¬p i} ρ hρ)).apply g y))
  dsimp only [Function.comp_def] at hm
  rw [hm]
  exact sections_root_mean_le _ _ g (fun x => hf _)

def flipEquiv (n : ℕ) (S : Finset (Fin n)) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := PaperSpecs.flip S
  invFun := PaperSpecs.flip S
  left_inv x := by
    funext i
    by_cases hi : i ∈ S <;> simp [PaperSpecs.flip, hi]
  right_inv x := by
    funext i
    by_cases hi : i ∈ S <;> simp [PaperSpecs.flip, hi]

/--
@isnad1 id=eq.0h4v.s10.57049a87f25a from=translated src=- shape=c904c1a5 vocab=dbfae01b
-/
theorem split_flip_section (n : ℕ) (S : Finset (Fin n))
    (w : {i // i ∈ S} → Bool) (z : {i // i ∉ S} → Bool) :
    (splitCube (fun i => i ∈ S)).symm ((fun i => !(w i)), z) =
      PaperSpecs.flip S ((splitCube (fun i => i ∈ S)).symm (w, z)) := by
  funext i
  by_cases hi : i ∈ S <;>
    simp [splitCube, Equiv.piEquivPiSubtypeProd_symm_apply, PaperSpecs.flip, hi]

/--
@isnad1 id=translat.0h0v.s0.0432ac86949e from=translated src=- shape=45709ebd vocab=0432ac86
-/
theorem translation_hellinger : PaperSpecs.TranslationHellinger := by
  intro n f hf S hS hanti ρ hρ
  let : Fintype {i : Fin n // i ∈ S} := Subtype.fintype (fun i : Fin n => i ∈ S)
  have hmean : mean f = 0 := mean_eq_zero_of_sign_reversing (flipEquiv n S) f hanti
  have hfc : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x
    rcases hf x with hx | hx <;> simp [hx]
  have : Nonempty {i : Fin n // i ∈ S} := by
    obtain ⟨i, hi⟩ := hS
    exact ⟨⟨i, hi⟩⟩
  have hsec (z : {i : Fin n // i ∉ S} → Bool) :
      root ρ ≤ mean (fun y => root ((indexedBSC {i : Fin n // i ∈ S} ρ hρ).apply
        (fun w => f ((splitCube (fun i => i ∈ S)).symm (w, z))) y)) := by
    apply indexed_antipodal_hellinger
    · intro w
      exact hf _
    · intro w
      rw [split_flip_section]
      exact hanti _
  have hroot : root ρ ≤ PaperSpecs.posteriorRootMean f ρ hρ := by
    have havg := mean_mono (fun _ : {i : Fin n // i ∉ S} → Bool => root ρ) _ hsec
    rw [mean_const] at havg
    exact havg.trans (indexedBSC_root_sections (ι := Fin n) (fun i => i ∈ S) ρ hρ f hfc)
  refine ⟨hmean, hroot, ?_⟩
  change objective ((cubeBSC n ρ hρ).apply f) ≤ 1 - root ρ
  rw [objective, UniformChannel.mean_apply, hmean]
  have hz : root 0 = 1 := by norm_num [root]
  rw [hz]
  exact sub_le_sub_left hroot 1

end Hellinger.ChannelSections
