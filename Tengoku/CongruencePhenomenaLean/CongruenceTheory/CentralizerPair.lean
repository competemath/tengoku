import Tengoku
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.ConjPair
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.MixedSupportFactorial
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.Centralizer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The `(n,k)`-generalized counterpart of `Centralizer.lean`: the centralizer-in-`H`
bound for unequal `n,k` and a general prime `p`, needed for the lower bound of
`thm:optimal-divisor`. Same "mixed cycles restrict faithfully" argument as
`Centralizer.lean`, just re-typed on `Fin n ⊕ Fin k` instead of `Fin n ⊕ Fin n`
(`Centralizer.lean` itself is untouched, since `StrongTwoAdic.lean` depends on it).
-/

namespace CongruenceTheory

open Equiv Equiv.Perm Nat

variable {n k : ℕ} (g : Equiv.Perm (Fin n ⊕ Fin k))

open scoped Classical

/-- A point lies in a "mixed" cycle of `g` if its cycle contains both a left
(`A`) point and a right (`B`) point.-/
noncomputable def IsMixedPair (x : Fin n ⊕ Fin k) : Prop :=
  (∃ a : Fin n, g.SameCycle x (Sum.inl a)) ∧ (∃ b : Fin k, g.SameCycle x (Sum.inr b))

/-- The predicate cutting out the left mixed points.-/
noncomputable def MixedAPair (x : Fin n ⊕ Fin k) : Prop := x.isLeft ∧ IsMixedPair g x

/-- The predicate cutting out the right mixed points.-/
noncomputable def MixedBPair (x : Fin n ⊕ Fin k) : Prop := x.isRight ∧ IsMixedPair g x

/--
@isnad1 id=iff.1h5v.s5.0904fd6f89e5 from=translated src=- shape=b9ff266d vocab=d4fbda78
-/
lemma isMixedPair_of_sameCycle {x y : Fin n ⊕ Fin k} (h : g.SameCycle x y) :
    IsMixedPair g x ↔ IsMixedPair g y := by
  unfold IsMixedPair
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, h.symm.trans ha⟩, ⟨b, h.symm.trans hb⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, h.trans ha⟩, ⟨b, h.trans hb⟩⟩

/-- If `h` commutes with `g` and fixes `x`, it fixes every point in `x`'s `g`-cycle.
@isnad1 id=eq.3h6v.s7.8bedb6323c02 from=translated src=- shape=f02fcf8a vocab=1c087d15
-/
lemma fixed_of_commute_of_fixed_pair {h : Equiv.Perm (Fin n ⊕ Fin k)} (hcomm : Commute h g)
    {x y : Fin n ⊕ Fin k} (hxy : g.SameCycle x y) (hx : h x = x) : h y = y := by
  obtain ⟨i, hi⟩ := hxy
  have hc : Commute h (g ^ i) := hcomm.zpow_right i
  calc h y = h ((g ^ i) x) := by rw [hi]
    _ = ((g ^ i) * h) x := by rw [← Equiv.Perm.mul_apply, ← hc]
    _ = (g ^ i) (h x) := rfl
    _ = (g ^ i) x := by rw [hx]
    _ = y := hi

/-- If `h` commutes with `g`, it maps `g`-cycles to `g`-cycles.
@isnad1 id=samecycl.2h6v.s7.6bf07c411492 from=translated src=- shape=75df2bb3 vocab=1c087d15
-/
lemma sameCycle_apply_of_commute_pair {h : Equiv.Perm (Fin n ⊕ Fin k)} (hcomm : Commute h g)
    {x y : Fin n ⊕ Fin k} (hxy : g.SameCycle x y) : g.SameCycle (h x) (h y) := by
  obtain ⟨i, hi⟩ := hxy
  refine ⟨i, ?_⟩
  have hc : h * g ^ i = g ^ i * h := hcomm.zpow_right i
  calc (g ^ i) (h x) = (g ^ i * h) x := rfl
    _ = (h * g ^ i) x := by rw [hc]
    _ = h ((g ^ i) x) := rfl
    _ = h y := by rw [hi]

/-- If `h ∈ H` commutes with `g` and `x` is mixed, so is `h x`.
@isnad1 id=ismixedp.3h5v.s7.d0a2fdda6155 from=translated src=- shape=03f44c56 vocab=287b8275
-/
lemma isMixedPair_apply_of_mem {h : Equiv.Perm (Fin n ⊕ Fin k)} (hH : h ∈ HgrpPair n k)
    (hcomm : Commute h g) {x : Fin n ⊕ Fin k} (hx : IsMixedPair g x) : IsMixedPair g (h x) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hx
  obtain ⟨p, hp⟩ := hH
  refine ⟨⟨p.1 a, ?_⟩, ⟨p.2 b, ?_⟩⟩
  · have hs := sameCycle_apply_of_commute_pair g hcomm ha
    rwa [show h (Sum.inl a) = Sum.inl (p.1 a) by
      rw [← hp, Equiv.Perm.sumCongrHom_apply]; rfl] at hs
  · have hs := sameCycle_apply_of_commute_pair g hcomm hb
    rwa [show h (Sum.inr b) = Sum.inr (p.2 b) by
      rw [← hp, Equiv.Perm.sumCongrHom_apply]; rfl] at hs

/--
@isnad1 id=iff.2h5v.s7.3ff0ac01357d from=translated src=- shape=6d0edf67 vocab=287b8275
-/
lemma isMixedPair_apply_iff {h : Equiv.Perm (Fin n ⊕ Fin k)} (hH : h ∈ HgrpPair n k)
    (hcomm : Commute h g) (x : Fin n ⊕ Fin k) : IsMixedPair g (h x) ↔ IsMixedPair g x := by
  refine ⟨fun hm => ?_, isMixedPair_apply_of_mem g hH hcomm⟩
  have hH' : h⁻¹ ∈ HgrpPair n k := Subgroup.inv_mem _ hH
  have hcomm' : Commute h⁻¹ g := hcomm.inv_left
  have := isMixedPair_apply_of_mem g hH' hcomm' hm
  simpa using this

/-- `h ∈ H` commuting with `g` maps left points to left points.
@isnad1 id=eq.2h4v.s7.9707fab88b7f from=translated src=- shape=0e6028a8 vocab=b99c7489
-/
lemma isLeft_apply_of_mem_pair {h : Equiv.Perm (Fin n ⊕ Fin k)} (hH : h ∈ HgrpPair n k)
    {x : Fin n ⊕ Fin k} (hx : x.isLeft) : (h x).isLeft := by
  obtain ⟨p, hp⟩ := hH
  obtain ⟨a, rfl⟩ := Sum.isLeft_iff.mp hx
  rw [show h (Sum.inl a) = Sum.inl (p.1 a) by
    rw [← hp, Equiv.Perm.sumCongrHom_apply]; rfl]
  exact rfl

/--
@isnad1 id=eq.2h4v.s7.e4618311cbea from=translated src=- shape=0e6028a8 vocab=e8cea956
-/
lemma isRight_apply_of_mem_pair {h : Equiv.Perm (Fin n ⊕ Fin k)} (hH : h ∈ HgrpPair n k)
    {x : Fin n ⊕ Fin k} (hx : x.isRight) : (h x).isRight := by
  obtain ⟨p, hp⟩ := hH
  obtain ⟨b, rfl⟩ := Sum.isRight_iff.mp hx
  rw [show h (Sum.inr b) = Sum.inr (p.2 b) by
    rw [← hp, Equiv.Perm.sumCongrHom_apply]; rfl]
  exact rfl

/-- **Set preservation**: `h ∈ H` commuting with `g` maps `MixedAPair g`-points to
`MixedAPair g`-points.
@isnad1 id=mixedapa.3h5v.s7.13d5fbc6e7b6 from=translated src=- shape=03f44c56 vocab=cf179096
-/
lemma mapsTo_MixedAPair {h : Equiv.Perm (Fin n ⊕ Fin k)} (hH : h ∈ HgrpPair n k)
    (hcomm : Commute h g) {x : Fin n ⊕ Fin k} (hx : MixedAPair g x) : MixedAPair g (h x) :=
  ⟨isLeft_apply_of_mem_pair hH hx.1, isMixedPair_apply_of_mem g hH hcomm hx.2⟩

/--
@isnad1 id=mixedbpa.3h5v.s7.b810f7f129eb from=translated src=- shape=03f44c56 vocab=e3677ae1
-/
lemma mapsTo_MixedBPair {h : Equiv.Perm (Fin n ⊕ Fin k)} (hH : h ∈ HgrpPair n k)
    (hcomm : Commute h g) {x : Fin n ⊕ Fin k} (hx : MixedBPair g x) : MixedBPair g (h x) :=
  ⟨isRight_apply_of_mem_pair hH hx.1, isMixedPair_apply_of_mem g hH hcomm hx.2⟩

/--
@isnad1 id=and.3h5v.s7.211d426de97e from=translated src=- shape=66cf0f5a vocab=3d5f301c
-/
lemma mapsTo_NonMixedAPair {h : Equiv.Perm (Fin n ⊕ Fin k)} (hH : h ∈ HgrpPair n k)
    (hcomm : Commute h g) {x : Fin n ⊕ Fin k} (hx : x.isLeft ∧ ¬ IsMixedPair g x) :
    (h x).isLeft ∧ ¬ IsMixedPair g (h x) :=
  ⟨isLeft_apply_of_mem_pair hH hx.1, fun hm => hx.2 ((isMixedPair_apply_iff g hH hcomm x).mp hm)⟩

/--
@isnad1 id=and.3h5v.s7.d1efc5b43bbc from=translated src=- shape=66cf0f5a vocab=743be791
-/
lemma mapsTo_NonMixedBPair {h : Equiv.Perm (Fin n ⊕ Fin k)} (hH : h ∈ HgrpPair n k)
    (hcomm : Commute h g) {x : Fin n ⊕ Fin k} (hx : x.isRight ∧ ¬ IsMixedPair g x) :
    (h x).isRight ∧ ¬ IsMixedPair g (h x) :=
  ⟨isRight_apply_of_mem_pair hH hx.1, fun hm => hx.2 ((isMixedPair_apply_iff g hH hcomm x).mp hm)⟩

/-- **Faithfulness**: two elements of `C_H(g)` agreeing on the non-mixed points of `A`,
the non-mixed points of `B`, and the mixed points of `A`, are equal.-/
theorem eq_of_agree_pair {h1 h2 : Equiv.Perm (Fin n ⊕ Fin k)} (hH1 : h1 ∈ HgrpPair n k)
    (hH2 : h2 ∈ HgrpPair n k) (hcomm1 : Commute h1 g) (hcomm2 : Commute h2 g)
    (hA : ∀ x, x.isLeft → ¬ IsMixedPair g x → h1 x = h2 x)
    (hB : ∀ x, x.isRight → ¬ IsMixedPair g x → h1 x = h2 x)
    (hMa : ∀ x, MixedAPair g x → h1 x = h2 x) :
    h1 = h2 := by
  have hcomm : Commute (h1⁻¹ * h2) g := Commute.mul_left hcomm1.inv_left hcomm2
  ext x
  by_cases hx : IsMixedPair g x
  · obtain ⟨a, ha⟩ := hx.1
    have hMaa : MixedAPair g (Sum.inl a) := ⟨rfl, (isMixedPair_of_sameCycle g ha).mp hx⟩
    have hfix : (h1⁻¹ * h2) (Sum.inl a) = Sum.inl a := by
      have heq := hMa (Sum.inl a) hMaa
      show h1⁻¹ (h2 (Sum.inl a)) = Sum.inl a
      rw [← heq]
      simp
    have hfixx := fixed_of_commute_of_fixed_pair g hcomm ha.symm hfix
    show h1 x = h2 x
    have h2x' : h1⁻¹ (h2 x) = x := hfixx
    have := congrArg h1 h2x'
    simpa using this.symm
  · cases x with
    | inl a => exact hA (Sum.inl a) rfl hx
    | inr b => exact hB (Sum.inr b) rfl hx

/-- Membership in the stabilizer of `g` (under `H`-conjugation) is exactly commuting with `g`.
@isnad1 id=iff.0h4v.s9.b8e385b56293 from=translated src=- shape=3b89f6b6 vocab=4064a5fd
-/
lemma stab_iff_commute_pair (h : ↥(HgrpPair n k)) :
    h ∈ MulAction.stabilizer ↥(HgrpPair n k) g ↔ Commute (h : Equiv.Perm (Fin n ⊕ Fin k)) g := by
  rw [MulAction.mem_stabilizer_iff, smul_def_pair]
  constructor
  · intro he
    have h2 : (h : Equiv.Perm (Fin n ⊕ Fin k)) * g * (h : Equiv.Perm (Fin n ⊕ Fin k))⁻¹ *
        (h : Equiv.Perm (Fin n ⊕ Fin k)) = g * (h : Equiv.Perm (Fin n ⊕ Fin k)) := by rw [he]
    have h3 : (h : Equiv.Perm (Fin n ⊕ Fin k)) * g = g * (h : Equiv.Perm (Fin n ⊕ Fin k)) := by
      simpa [mul_assoc] using h2
    exact h3
  · intro hc
    show (h : Equiv.Perm (Fin n ⊕ Fin k)) * g * (h : Equiv.Perm (Fin n ⊕ Fin k))⁻¹ = g
    rw [hc]
    simp [mul_assoc]

/-- `a(g)`, the number of mixed points on the `A` side.-/
noncomputable def mixedCardAPair : ℕ := Nat.card {x : Fin n ⊕ Fin k // MixedAPair g x}

/-- `b(g)`, the number of mixed points on the `B` side.-/
noncomputable def mixedCardBPair : ℕ := Nat.card {x : Fin n ⊕ Fin k // MixedBPair g x}

variable {g} in
/-- The restriction of `f` to a `Fintype`-preserved predicate is compatible with `*`.
@isnad1 id=eq.0h7v.s8.077255cdbd36 from=translated src=- shape=2e741add vocab=22949652
-/
lemma subtypePermOfFintype_mul_pair {p : Fin n ⊕ Fin k → Prop} [Finite {x // p x}]
    {f1 f2 : Equiv.Perm (Fin n ⊕ Fin k)} (h1 : ∀ x, p x → p (f1 x)) (h2 : ∀ x, p x → p (f2 x)) :
    Equiv.Perm.subtypePermOfFintype (f1 * f2) (fun x hx => h1 (f2 x) (h2 x hx)) =
      Equiv.Perm.subtypePermOfFintype f1 h1 * Equiv.Perm.subtypePermOfFintype f2 h2 := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/-- The combined restriction map: `C_H(g) → Perm(A∖Ma) × Perm(B∖Mb) × Perm(Ma)`.-/
noncomputable def restrictTriplePair (h : ↥(MulAction.stabilizer ↥(HgrpPair n k) g)) :
    Equiv.Perm {x : Fin n ⊕ Fin k // x.isLeft ∧ ¬ IsMixedPair g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin k // x.isRight ∧ ¬ IsMixedPair g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin k // MixedAPair g x} :=
  ( Equiv.Perm.subtypePermOfFintype (h.1 : Equiv.Perm (Fin n ⊕ Fin k))
      (fun x hx => mapsTo_NonMixedAPair g h.1.2 ((stab_iff_commute_pair g h.1).mp h.2) hx),
    Equiv.Perm.subtypePermOfFintype (h.1 : Equiv.Perm (Fin n ⊕ Fin k))
      (fun x hx => mapsTo_NonMixedBPair g h.1.2 ((stab_iff_commute_pair g h.1).mp h.2) hx),
    Equiv.Perm.subtypePermOfFintype (h.1 : Equiv.Perm (Fin n ⊕ Fin k))
      (fun x hx => mapsTo_MixedAPair g h.1.2 ((stab_iff_commute_pair g h.1).mp h.2) hx) )

/--
@isnad1 id=eq.0h5v.s12.ae4efd4cf7fb from=translated src=- shape=00757e94 vocab=da9af26f
-/
lemma restrictTriplePair_mul (h1 h2 : ↥(MulAction.stabilizer ↥(HgrpPair n k) g)) :
    restrictTriplePair g (h1 * h2) = restrictTriplePair g h1 * restrictTriplePair g h2 := by
  simp only [restrictTriplePair, Prod.mk_mul_mk, Prod.mk.injEq]
  exact ⟨subtypePermOfFintype_mul_pair _ _, subtypePermOfFintype_mul_pair _ _,
    subtypePermOfFintype_mul_pair _ _⟩

/-- **The centralizer restriction homomorphism.**-/
noncomputable def restrictHomPair : ↥(MulAction.stabilizer ↥(HgrpPair n k) g) →*
    Equiv.Perm {x : Fin n ⊕ Fin k // x.isLeft ∧ ¬ IsMixedPair g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin k // x.isRight ∧ ¬ IsMixedPair g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin k // MixedAPair g x} :=
  MonoidHom.mk' (restrictTriplePair g) (restrictTriplePair_mul g)

/--
@isnad1 id=injectiv.0h3v.s13.444e62c1095c from=translated src=- shape=2f3ee562 vocab=63e24078
-/
theorem restrictHomPair_injective : Function.Injective (restrictHomPair (n := n) (k := k) g) := by
  intro h1 h2 heq
  simp only [restrictHomPair, MonoidHom.mk'_apply] at heq
  apply Subtype.ext
  apply Subtype.ext
  apply eq_of_agree_pair g h1.1.2 h2.1.2 ((stab_iff_commute_pair g h1.1).mp h1.2)
    ((stab_iff_commute_pair g h2.1).mp h2.2)
  · intro x hxl hxm
    have h0 := congrArg Prod.fst heq
    have hx := Equiv.ext_iff.mp h0 ⟨x, hxl, hxm⟩
    simpa [restrictTriplePair, Equiv.Perm.subtypePermOfFintype_apply] using hx
  · intro x hxr hxm
    have h0 := congrArg (Prod.fst ∘ Prod.snd) heq
    have hx := Equiv.ext_iff.mp h0 ⟨x, hxr, hxm⟩
    simpa [restrictTriplePair, Equiv.Perm.subtypePermOfFintype_apply] using hx
  · intro x hxm
    have h0 := congrArg (Prod.snd ∘ Prod.snd) heq
    have hx := Equiv.ext_iff.mp h0 ⟨x, hxm⟩
    simpa [restrictTriplePair, Equiv.Perm.subtypePermOfFintype_apply] using hx

/-- The symmetric (`B`-side) version of `eq_of_agree_pair`.-/
theorem eq_of_agree_pair' {h1 h2 : Equiv.Perm (Fin n ⊕ Fin k)} (hcomm1 : Commute h1 g)
    (hcomm2 : Commute h2 g)
    (hA : ∀ x, x.isLeft → ¬ IsMixedPair g x → h1 x = h2 x)
    (hB : ∀ x, x.isRight → ¬ IsMixedPair g x → h1 x = h2 x)
    (hMb : ∀ x, MixedBPair g x → h1 x = h2 x) :
    h1 = h2 := by
  have hcomm : Commute (h1⁻¹ * h2) g := Commute.mul_left hcomm1.inv_left hcomm2
  ext x
  by_cases hx : IsMixedPair g x
  · obtain ⟨b, hb⟩ := hx.2
    have hMbb : MixedBPair g (Sum.inr b) := ⟨rfl, (isMixedPair_of_sameCycle g hb).mp hx⟩
    have hfix : (h1⁻¹ * h2) (Sum.inr b) = Sum.inr b := by
      have heq := hMb (Sum.inr b) hMbb
      show h1⁻¹ (h2 (Sum.inr b)) = Sum.inr b
      rw [← heq]
      simp
    have hfixx := fixed_of_commute_of_fixed_pair g hcomm hb.symm hfix
    show h1 x = h2 x
    have h2x' : h1⁻¹ (h2 x) = x := hfixx
    have := congrArg h1 h2x'
    simpa using this.symm
  · cases x with
    | inl a => exact hA (Sum.inl a) rfl hx
    | inr b => exact hB (Sum.inr b) rfl hx

/-- The restriction map, `B`-side variant: `C_H(g) → Perm(A∖Ma) × Perm(B∖Mb) × Perm(Mb)`.-/
noncomputable def restrictTriplePair' (h : ↥(MulAction.stabilizer ↥(HgrpPair n k) g)) :
    Equiv.Perm {x : Fin n ⊕ Fin k // x.isLeft ∧ ¬ IsMixedPair g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin k // x.isRight ∧ ¬ IsMixedPair g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin k // MixedBPair g x} :=
  ( Equiv.Perm.subtypePermOfFintype (h.1 : Equiv.Perm (Fin n ⊕ Fin k))
      (fun x hx => mapsTo_NonMixedAPair g h.1.2 ((stab_iff_commute_pair g h.1).mp h.2) hx),
    Equiv.Perm.subtypePermOfFintype (h.1 : Equiv.Perm (Fin n ⊕ Fin k))
      (fun x hx => mapsTo_NonMixedBPair g h.1.2 ((stab_iff_commute_pair g h.1).mp h.2) hx),
    Equiv.Perm.subtypePermOfFintype (h.1 : Equiv.Perm (Fin n ⊕ Fin k))
      (fun x hx => mapsTo_MixedBPair g h.1.2 ((stab_iff_commute_pair g h.1).mp h.2) hx) )

/--
@isnad1 id=eq.0h5v.s12.e84a330577ed from=translated src=- shape=00757e94 vocab=deca1361
-/
lemma restrictTriplePair'_mul (h1 h2 : ↥(MulAction.stabilizer ↥(HgrpPair n k) g)) :
    restrictTriplePair' g (h1 * h2) = restrictTriplePair' g h1 * restrictTriplePair' g h2 := by
  simp only [restrictTriplePair', Prod.mk_mul_mk, Prod.mk.injEq]
  exact ⟨subtypePermOfFintype_mul_pair _ _, subtypePermOfFintype_mul_pair _ _,
    subtypePermOfFintype_mul_pair _ _⟩

noncomputable def restrictHomPair' : ↥(MulAction.stabilizer ↥(HgrpPair n k) g) →*
    Equiv.Perm {x : Fin n ⊕ Fin k // x.isLeft ∧ ¬ IsMixedPair g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin k // x.isRight ∧ ¬ IsMixedPair g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin k // MixedBPair g x} :=
  MonoidHom.mk' (restrictTriplePair' g) (restrictTriplePair'_mul g)

/--
@isnad1 id=injectiv.0h3v.s13.83a785afb464 from=translated src=- shape=2f3ee562 vocab=6c1174c0
-/
theorem restrictHomPair'_injective : Function.Injective (restrictHomPair' (n := n) (k := k) g) := by
  intro h1 h2 heq
  simp only [restrictHomPair', MonoidHom.mk'_apply] at heq
  apply Subtype.ext
  apply Subtype.ext
  apply eq_of_agree_pair' g ((stab_iff_commute_pair g h1.1).mp h1.2)
    ((stab_iff_commute_pair g h2.1).mp h2.2)
  · intro x hxl hxm
    have h0 := congrArg Prod.fst heq
    have hx := Equiv.ext_iff.mp h0 ⟨x, hxl, hxm⟩
    simpa [restrictTriplePair', Equiv.Perm.subtypePermOfFintype_apply] using hx
  · intro x hxr hxm
    have h0 := congrArg (Prod.fst ∘ Prod.snd) heq
    have hx := Equiv.ext_iff.mp h0 ⟨x, hxr, hxm⟩
    simpa [restrictTriplePair', Equiv.Perm.subtypePermOfFintype_apply] using hx
  · intro x hxm
    have h0 := congrArg (Prod.snd ∘ Prod.snd) heq
    have hx := Equiv.ext_iff.mp h0 ⟨x, hxm⟩
    simpa [restrictTriplePair', Equiv.Perm.subtypePermOfFintype_apply] using hx

-- `sumLeftSubtypeEquiv`/`sumRightSubtypeEquiv` are reused directly from `Centralizer.lean`,
-- since they're already fully general in `α, β`.

/-- The mixed-support cardinalities.-/
noncomputable def aCardPair : ℕ := Nat.card {a : Fin n // IsMixedPair g (Sum.inl a)}

noncomputable def bCardPair : ℕ := Nat.card {b : Fin k // IsMixedPair g (Sum.inr b)}

/--
@isnad1 id=eq.0h3v.s5.0b038bd67d7f from=translated src=- shape=7516cfe5 vocab=690f5233
-/
lemma card_NonMixedAPair :
    Nat.card {x : Fin n ⊕ Fin k // x.isLeft ∧ ¬ IsMixedPair g x} = n - aCardPair g := by
  rw [Nat.card_congr (sumLeftSubtypeEquiv (fun x => ¬ IsMixedPair g x))]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp [aCardPair, Nat.card_eq_fintype_card, Fintype.card_fin]

/--
@isnad1 id=eq.0h3v.s5.adc313721569 from=translated src=- shape=f3c78b63 vocab=be296aae
-/
lemma card_NonMixedBPair :
    Nat.card {x : Fin n ⊕ Fin k // x.isRight ∧ ¬ IsMixedPair g x} = k - bCardPair g := by
  rw [Nat.card_congr (sumRightSubtypeEquiv (fun x => ¬ IsMixedPair g x))]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp [bCardPair, Nat.card_eq_fintype_card, Fintype.card_fin]

/--
@isnad1 id=eq.0h3v.s5.07978be68609 from=translated src=- shape=010b8127 vocab=afd56480
-/
lemma card_MixedAPair :
    Nat.card {x : Fin n ⊕ Fin k // MixedAPair g x} = aCardPair g := by
  show Nat.card {x : Fin n ⊕ Fin k // x.isLeft ∧ IsMixedPair g x} = aCardPair g
  rw [Nat.card_congr (sumLeftSubtypeEquiv (IsMixedPair g))]
  rfl

/--
@isnad1 id=eq.0h3v.s5.d7fdaecccbc1 from=translated src=- shape=010b8127 vocab=e0ee2e37
-/
lemma card_MixedBPair :
    Nat.card {x : Fin n ⊕ Fin k // MixedBPair g x} = bCardPair g := by
  show Nat.card {x : Fin n ⊕ Fin k // x.isRight ∧ IsMixedPair g x} = bCardPair g
  rw [Nat.card_congr (sumRightSubtypeEquiv (IsMixedPair g))]
  rfl

/--
@isnad1 id=dvd.0h3v.s9.4bedc5afec3d from=translated src=- shape=03a588e3 vocab=232686ca
-/
theorem card_stabilizer_dvd_A_pair :
    Nat.card ↥(MulAction.stabilizer ↥(HgrpPair n k) g) ∣
      (n - aCardPair g)! * (k - bCardPair g)! * (aCardPair g)! := by
  have hdvd := Subgroup.card_dvd_of_injective (restrictHomPair (n := n) (k := k) g)
    (restrictHomPair_injective g)
  rw [Nat.card_prod, Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_perm,
    card_NonMixedAPair, card_NonMixedBPair, card_MixedAPair, ← mul_assoc] at hdvd
  exact hdvd

/--
@isnad1 id=dvd.0h3v.s9.b09d6b70f5ce from=translated src=- shape=33a64b2e vocab=232686ca
-/
theorem card_stabilizer_dvd_B_pair :
    Nat.card ↥(MulAction.stabilizer ↥(HgrpPair n k) g) ∣
      (n - aCardPair g)! * (k - bCardPair g)! * (bCardPair g)! := by
  have hdvd := Subgroup.card_dvd_of_injective (restrictHomPair' (n := n) (k := k) g)
    (restrictHomPair'_injective g)
  rw [Nat.card_prod, Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_perm,
    card_NonMixedAPair, card_NonMixedBPair, card_MixedBPair, ← mul_assoc] at hdvd
  exact hdvd

/--
@isnad1 id=dvd.0h3v.s9.6369cdd88723 from=translated src=- shape=7537cd9b vocab=c3d6924b
-/
theorem card_stabilizer_dvd_min_pair :
    Nat.card ↥(MulAction.stabilizer ↥(HgrpPair n k) g) ∣
      (n - aCardPair g)! * (k - bCardPair g)! * min (aCardPair g)! (bCardPair g)! := by
  have hA := card_stabilizer_dvd_A_pair g
  have hB := card_stabilizer_dvd_B_pair g
  rcases le_total (aCardPair g)! (bCardPair g)! with hle | hle
  · rwa [min_eq_left hle]
  · rwa [min_eq_right hle]

/-- **The centralizer bound, general prime**: `v_p(|C_H(g)|) ≤ v_p((n-a)!) + v_p((k-b)!) +
min(v_p(a!), v_p(b!))`, for any prime `p`.
@isnad1 id=le.1h4v.s9.b0cbc77c5309 from=translated src=- shape=8e5969c9 vocab=aaa56ede
-/
theorem vp_stabilizer_le_pair (p : ℕ) (hp : p.Prime) :
    padicValNat p (Nat.card ↥(MulAction.stabilizer ↥(HgrpPair n k) g)) ≤
      padicValNat p ((n - aCardPair g)!) + padicValNat p ((k - bCardPair g)!) +
        min (padicValNat p ((aCardPair g)!)) (padicValNat p ((bCardPair g)!)) := by
  haveI := Fact.mk hp
  have hdvd := card_stabilizer_dvd_min_pair g
  have hstabpos : Nat.card ↥(MulAction.stabilizer ↥(HgrpPair n k) g) ≠ 0 := Nat.card_ne_zero.mpr
    ⟨⟨1, MulAction.stabilizer ↥(HgrpPair n k) g |>.one_mem⟩, inferInstance⟩
  have hprodpos :
      (n - aCardPair g)! * (k - bCardPair g)! * min (aCardPair g)! (bCardPair g)! ≠ 0 := by
    positivity
  have hle : (Nat.card ↥(MulAction.stabilizer ↥(HgrpPair n k) g)).factorization p ≤
      ((n - aCardPair g)! * (k - bCardPair g)! * min (aCardPair g)! (bCardPair g)!).factorization
        p :=
    Nat.factorization_le_factorization_of_dvd_right hdvd hstabpos hprodpos
  have hval : ((n - aCardPair g)! * (k - bCardPair g)! *
      min (aCardPair g)! (bCardPair g)!).factorization p =
      padicValNat p ((n - aCardPair g)!) + padicValNat p ((k - bCardPair g)!) +
        padicValNat p (min (aCardPair g)! (bCardPair g)!) := by
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
    simp [Nat.factorization_def _ hp]
  have hminv : padicValNat p (min (aCardPair g)! (bCardPair g)!) =
      min (padicValNat p ((aCardPair g)!)) (padicValNat p ((bCardPair g)!)) := by
    rcases le_total (aCardPair g) (bCardPair g) with hle' | hle'
    · rw [min_eq_left (Nat.factorial_le hle')]
      exact (min_eq_left (padicValNat_factorial_mono p hp hle')).symm
    · rw [min_eq_right (Nat.factorial_le hle')]
      exact (min_eq_right (padicValNat_factorial_mono p hp hle')).symm
  rw [hval, hminv] at hle
  simpa [Nat.factorization_def _ hp] using hle

/--
@isnad1 id=ex.1h3v.s7.e46e518c2e2e from=translated src=- shape=59d65df6 vocab=dd74fad8
-/
lemma exists_mixed_pair_pair (hg : g ∉ HgrpPair n k) : ∃ a b, g (Sum.inl a) = Sum.inr b := by
  by_contra hc
  push Not at hc
  apply hg
  apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
  rintro x ⟨a, rfl⟩
  rcases hgx : g (Sum.inl a) with a' | b'
  · exact ⟨a', rfl⟩
  · exact absurd hgx (hc a b')

/--
@isnad1 id=le.1h3v.s6.dc15c979df65 from=translated src=- shape=4cfbd0cb vocab=e61138ee
-/
theorem one_le_aCardPair (hg : g ∉ HgrpPair n k) : 1 ≤ aCardPair g := by
  obtain ⟨a, b, hab⟩ := exists_mixed_pair_pair g hg
  have hmixed : IsMixedPair g (Sum.inl a) := ⟨⟨a, SameCycle.refl g _⟩, ⟨b, ⟨1, by simpa using hab⟩⟩⟩
  haveI : Nonempty {a : Fin n // IsMixedPair g (Sum.inl a)} := ⟨⟨a, hmixed⟩⟩
  exact Nat.card_pos

/--
@isnad1 id=le.1h3v.s6.7a0eb96fdc92 from=translated src=- shape=4cfbd0cb vocab=abe171c5
-/
theorem one_le_bCardPair (hg : g ∉ HgrpPair n k) : 1 ≤ bCardPair g := by
  obtain ⟨a, b, hab⟩ := exists_mixed_pair_pair g hg
  have hmixed : IsMixedPair g (Sum.inl a) := ⟨⟨a, SameCycle.refl g _⟩, ⟨b, ⟨1, by simpa using hab⟩⟩⟩
  have hsc : g.SameCycle (Sum.inl a) (Sum.inr b) := ⟨1, by simpa using hab⟩
  have hmixed' : IsMixedPair g (Sum.inr b) := (isMixedPair_of_sameCycle g hsc).mp hmixed
  haveI : Nonempty {b : Fin k // IsMixedPair g (Sum.inr b)} := ⟨⟨b, hmixed'⟩⟩
  exact Nat.card_pos

/--
@isnad1 id=le.0h3v.s4.e4b59f99159d from=translated src=- shape=a49ffc71 vocab=c68baa76
-/
theorem aCardPair_le (g : Equiv.Perm (Fin n ⊕ Fin k)) : aCardPair g ≤ n := by
  rw [aCardPair]
  have : Nat.card {a : Fin n // IsMixedPair g (Sum.inl a)} ≤ Nat.card (Fin n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  simpa using this

/--
@isnad1 id=le.0h3v.s4.7e58ec71bf74 from=translated src=- shape=3060052a vocab=075679a3
-/
theorem bCardPair_le (g : Equiv.Perm (Fin n ⊕ Fin k)) : bCardPair g ≤ k := by
  rw [bCardPair]
  have : Nat.card {b : Fin k // IsMixedPair g (Sum.inr b)} ≤ Nat.card (Fin k) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  simpa using this

end CongruenceTheory
