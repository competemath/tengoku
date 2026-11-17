import Tengoku.AdianRabin.GroupUndecidability.GroupTheory.CoprodILemmas
import Tengoku.Seed.Algebra.Group.Conj
import Tengoku.Seed.Tactic.Group

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Normal-form infrastructure for the left separated-conjugates map. -/

namespace Undecidability.MillerTancer.LeftNormalForm

open Monoid

/--
@isnad1 id=injectiv.1h3v.s10.7640527efb51 from=translated src=- shape=cdaefd6a vocab=bd5b01cf
-/
theorem FreeGroup.lift_injective_of_coprodI_neWord
    {I : Type} {Q : Type} [Group Q] (a : I → Q)
    (hne : ∀ i j
      (u : CoprodI.NeWord (fun _ : I ↦ FreeGroup Unit) i j),
      CoprodI.lift (fun i ↦ FreeGroup.lift fun _ ↦ a i) u.prod ≠ 1) :
    Function.Injective (FreeGroup.lift a) := by
  have hlift : FreeGroup.lift a =
      (CoprodI.lift fun i ↦ FreeGroup.lift fun _ ↦ a i).comp
        (@freeGroupEquivCoprodI I).toMonoidHom := by
    ext i
    simp
  rw [hlift, MonoidHom.coe_comp]
  exact Function.Injective.comp
    (CoprodI.lift_injective_of_neWord_nontrivial _ hne)
    (@freeGroupEquivCoprodI I).injective

/-- A list-of-nonzero-powers formulation of the normal-form criterion.  This
is the form used by the separated-conjugates calculation: adjacent runs use
different proposed basis elements.
@isnad1 id=injectiv.1h3v.s8.3d9d4e9a25b8 from=translated src=- shape=995f48ff vocab=ef193ef8
-/
theorem FreeGroup.lift_injective_of_reduced_zpow_products
    {I : Type} {Q : Type} [Group Q] (a : I → Q)
    (hprod : ∀ l : List (I × ℤ), l ≠ [] →
      (∀ p ∈ l, p.2 ≠ 0) →
      l.IsChain (fun p q ↦ p.1 ≠ q.1) →
      (l.map fun p ↦ a p.1 ^ p.2).prod ≠ 1) :
    Function.Injective (FreeGroup.lift a) := by
  apply FreeGroup.lift_injective_of_coprodI_neWord a
  intro i j u
  let encode : (Σ _ : I, FreeGroup Unit) → I × ℤ :=
    fun s ↦ (s.1, FreeGroup.freeGroupUnitEquivInt s.2)
  let l := u.toList.map encode
  have hlne : l ≠ [] := by
    simpa [l] using u.toList_ne_nil
  have hlexp : ∀ p ∈ l, p.2 ≠ 0 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨s, hs, rfl⟩
    intro heq
    have hsone : s.2 = 1 :=
      FreeGroup.freeGroupUnitEquivInt.injective (by
        simpa [encode, FreeGroup.freeGroupUnitEquivInt] using heq)
    exact u.toWord.ne_one s hs hsone
  have hlchain : l.IsChain (fun p q ↦ p.1 ≠ q.1) := by
    change (u.toList.map encode).IsChain (fun p q ↦ p.1 ≠ q.1)
    rw [List.isChain_map]
    exact u.toWord.chain_ne.imp (by
      intro p q hpq
      simpa [encode] using hpq)
  have heval :
      (CoprodI.lift fun i ↦ FreeGroup.lift fun _ ↦ a i) u.prod =
        (l.map fun p ↦ a p.1 ^ p.2).prod := by
    simp only [CoprodI.NeWord.prod, CoprodI.Word.prod, map_list_prod,
      List.map_map, l, encode]
    congr 1
    apply List.map_congr_left
    intro s hs
    simp only [Function.comp_apply, CoprodI.lift_of]
    have hreconstruct :
        FreeGroup.of () ^ FreeGroup.freeGroupUnitEquivInt s.2 = s.2 :=
      FreeGroup.freeGroupUnitEquivInt.symm_apply_apply s.2
    calc
      FreeGroup.lift (fun _ ↦ a s.1) s.2 =
          FreeGroup.lift (fun _ ↦ a s.1)
            (FreeGroup.of () ^ FreeGroup.freeGroupUnitEquivInt s.2) := by
              rw [hreconstruct]
      _ = a s.1 ^ FreeGroup.freeGroupUnitEquivInt s.2 := by
        rw [map_zpow, FreeGroup.lift_apply_of]
  rw [heval]
  exact hprod l hlne hlexp hlchain

inductive LeftIndex
  | old
  | alpha
  | beta
  deriving DecidableEq

def LeftFactor (G : Type) : LeftIndex → Type
  | .old => G
  | .alpha => FreeGroup Unit
  | .beta => FreeGroup Unit

variable {G : Type} [Group G]

instance leftFactorGroup : ∀ i, Group (LeftFactor G i) := fun i => by
  cases i <;> simp only [LeftFactor] <;> infer_instance

abbrev LeftProduct (G : Type) [Group G] := CoprodI (LeftFactor G)

def old (g : G) : LeftProduct G := CoprodI.of (i := LeftIndex.old) g

def alpha : LeftProduct G :=
  CoprodI.of (i := LeftIndex.alpha) (FreeGroup.of ())

def beta : LeftProduct G :=
  CoprodI.of (i := LeftIndex.beta) (FreeGroup.of ())

private theorem of_ne_one {i : LeftIndex} {x : LeftFactor G i} (hx : x ≠ 1) :
    CoprodI.of x ≠ (1 : LeftProduct G) := by
  intro h
  apply hx
  apply CoprodI.of_injective i
  simpa using h

/--
@isnad1 id=eq.0h3v.s9.969db6da696d from=translated src=- shape=52a7290f vocab=eb748ae4
-/
@[simp] theorem of_inv {i : LeftIndex} (x : LeftFactor G i) :
    CoprodI.of (M := LeftFactor G) (i := i) x⁻¹ =
      (CoprodI.of (M := LeftFactor G) (i := i) x)⁻¹ :=
  map_inv
    (CoprodI.of (M := LeftFactor G) (i := i) : LeftFactor G i →* LeftProduct G) x

/--
@isnad1 id=eq.0h2v.s5.2d71f8712f9b from=translated src=- shape=ca5e3fdd vocab=c6e3f60a
-/
@[simp] theorem old_inv (g : G) : old (g⁻¹) = (old g)⁻¹ :=
  of_inv (G := G) (i := LeftIndex.old) g

private theorem freeGenerator_ne_one : FreeGroup.of () ≠ (1 : FreeGroup Unit) :=
  by simpa only [zpow_one] using
    FreeGroup.unitGenerator_zpow_ne_one 1 one_ne_zero

/--
@isnad1 id=ne.0h1v.s5.584935428a4a from=translated src=- shape=c4fc3c69 vocab=37881bfb
-/
theorem beta_ne_one : (beta : LeftProduct G) ≠ 1 := by
  apply of_ne_one
  exact freeGenerator_ne_one

def leftFactorToBeta : ∀ i : LeftIndex, LeftFactor G i →* FreeGroup Unit
  | .old => 1
  | .alpha => 1
  | .beta => MonoidHom.id _

def betaProjection : LeftProduct G →* FreeGroup Unit :=
  CoprodI.lift leftFactorToBeta

/--
@isnad1 id=eq.0h2v.s7.a70f04cebba7 from=translated src=- shape=84e87314 vocab=b9773659
-/
@[simp] theorem betaProjection_old (g : G) : betaProjection (old g) = 1 := by
  exact CoprodI.lift_of leftFactorToBeta (i := LeftIndex.old) g

/--
@isnad1 id=eq.0h1v.s6.95602e6f1a51 from=translated src=- shape=d135025f vocab=21d6b2bb
-/
@[simp] theorem betaProjection_beta :
    betaProjection (beta : LeftProduct G) = FreeGroup.of () := by
  exact CoprodI.lift_of leftFactorToBeta (i := LeftIndex.beta) (FreeGroup.of ())

/--
@isnad1 id=ne.1h2v.s6.cf0ace2308ba from=translated src=- shape=64c3d4f8 vocab=749b410c
-/
theorem beta_zpow_ne_one (k : ℤ) (hk : k ≠ 0) :
    (beta : LeftProduct G) ^ k ≠ 1 := by
  intro h
  apply FreeGroup.unitGenerator_zpow_ne_one k hk
  simpa using congrArg betaProjection h

/--
@isnad1 id=ne.0h2v.s6.3fe54cc8573e from=translated src=- shape=e070628b vocab=44112449
-/
theorem old_mul_beta_ne_one (z : G) :
    old z * beta ≠ (1 : LeftProduct G) := by
  intro h
  apply freeGenerator_ne_one
  simpa using congrArg betaProjection h

/--
@isnad1 id=ne.0h2v.s7.9017d841295a from=translated src=- shape=e74c43a7 vocab=44112449
-/
theorem beta_mul_old_mul_beta_ne_one (z : G) :
    beta * (old z * beta) ≠ (1 : LeftProduct G) := by
  intro h
  apply FreeGroup.unitGenerator_zpow_ne_one 2 (by norm_num)
  calc
    (FreeGroup.of () : FreeGroup Unit) ^ (2 : ℤ) =
        FreeGroup.of () * FreeGroup.of () := zpow_two _
    _ = 1 := by simpa using congrArg betaProjection h

/--
@isnad1 id=ne.0h2v.s7.094fb18b66dc from=translated src=- shape=8b75c484 vocab=fe98a7de
-/
theorem inv_old_mul_beta_inv_mul_beta_inv_ne_one (z : G) :
    (old z * beta)⁻¹ * beta⁻¹ ≠ (1 : LeftProduct G) := by
  intro h
  apply FreeGroup.unitGenerator_zpow_ne_one (-2) (by norm_num)
  calc
    (FreeGroup.of () : FreeGroup Unit) ^ (-2 : ℤ) =
        (FreeGroup.of ())⁻¹ * (FreeGroup.of ())⁻¹ := by
          simp [zpow_neg, pow_two]
    _ = 1 := by simpa using congrArg betaProjection h

/-! The inner commutator is cyclically reduced of free-product length four. -/

def commutatorWord (w : G) (hw : w ≠ 1) :
    CoprodI.NeWord (LeftFactor G) LeftIndex.old LeftIndex.beta :=
  .append
    (.singleton (i := LeftIndex.old) w⁻¹ (inv_ne_one.mpr hw)) (by decide)
    (.append
      (.singleton (i := LeftIndex.beta) (FreeGroup.of ())⁻¹
        (inv_ne_one.mpr freeGenerator_ne_one)) (by decide)
      (.append
        (.singleton (i := LeftIndex.old) w hw) (by decide)
        (.singleton (i := LeftIndex.beta) (FreeGroup.of ()) freeGenerator_ne_one)))

/--
@isnad1 id=eq.1h2v.s7.9919b50d056c from=translated src=- shape=979428de vocab=9fe8e93f
-/
@[simp] theorem commutatorWord_prod (w : G) (hw : w ≠ 1) :
    (commutatorWord w hw).prod = (old w)⁻¹ * beta⁻¹ * old w * beta := by
  simp only [commutatorWord, CoprodI.NeWord.append_prod,
    CoprodI.NeWord.prod_singleton (M := LeftFactor G) (i := LeftIndex.old),
    CoprodI.NeWord.prod_singleton (M := LeftFactor G) (i := LeftIndex.beta),
    of_inv (G := G) (i := LeftIndex.old) w,
    of_inv (G := G) (i := LeftIndex.beta) (FreeGroup.of ()), old, beta]
  rw [CoprodI.NeWord.prod_singleton (M := LeftFactor G) (i := LeftIndex.old) w hw,
    CoprodI.NeWord.prod_singleton (M := LeftFactor G) (i := LeftIndex.beta)
      (FreeGroup.of ()) freeGenerator_ne_one]
  simp only [mul_assoc]

/-!
Powers of a cyclically reduced nonempty free-product word are nonempty.
This is the first reusable normal-form lemma needed for `L₃`.
-/

def positivePowerWord {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i) :
    (k : ℕ) → CoprodI.NeWord (LeftFactor G) i j
  | 0 => u
  | k + 1 => .append (positivePowerWord u hij k) hij u

/--
@isnad1 id=eq.1h5v.s7.70c9f9b3792f from=translated src=- shape=e61851e8 vocab=57bcd178
-/
@[simp] theorem positivePowerWord_prod {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i) (k : ℕ) :
    (positivePowerWord u hij k).prod = u.prod ^ (k + 1) := by
  induction k with
  | zero => simp [positivePowerWord]
  | succ k ih =>
      calc
        (positivePowerWord u hij (k + 1)).prod =
            (positivePowerWord u hij k).prod * u.prod := by
              simp only [positivePowerWord, CoprodI.NeWord.append_prod]
        _ = u.prod ^ (k + 1) * u.prod := by rw [ih]
        _ = u.prod ^ (k + 1 + 1) := (pow_succ _ _).symm

/--
@isnad1 id=ne.1h5v.s8.109b9f27b981 from=translated src=- shape=1877f52b vocab=9a877d07
-/
theorem positivePowerWord_prod_ne_one {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i) (k : ℕ) :
    u.prod ^ (k + 1) ≠ 1 := by
  rw [← positivePowerWord_prod u hij]
  intro h
  classical
  have hnormal :
      CoprodI.Word.equiv (M := LeftFactor G) (positivePowerWord u hij k).prod =
        (positivePowerWord u hij k).toWord := by
    change (CoprodI.Word.equiv (M := LeftFactor G))
        ((CoprodI.Word.equiv (M := LeftFactor G)).symm
          (positivePowerWord u hij k).toWord) = _
    exact (CoprodI.Word.equiv (M := LeftFactor G)).apply_symm_apply _
  rw [h] at hnormal
  have hword : (positivePowerWord u hij k).toWord =
      (CoprodI.Word.empty : CoprodI.Word (LeftFactor G)) := by
    simpa [CoprodI.Word.equiv] using hnormal.symm
  exact (CoprodI.NeWord.toList_ne_nil (positivePowerWord u hij k))
    (by simpa [CoprodI.NeWord.toWord] using congrArg CoprodI.Word.toList hword)

/--
@isnad1 id=ne.2h5v.s8.2b41a1341d1f from=translated src=- shape=d022306e vocab=58df8f5f
-/
theorem zpow_ne_one_of_cyclicallyReduced {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i)
    (k : ℤ) (hk : k ≠ 0) : u.prod ^ k ≠ 1 := by
  cases k with
  | ofNat k =>
      cases k with
      | zero => exact (hk rfl).elim
      | succ k =>
          simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
            positivePowerWord_prod_ne_one u hij k
  | negSucc k =>
      simpa only [zpow_negSucc] using
        inv_ne_one.mpr (positivePowerWord_prod_ne_one u hij k)

/--
@isnad1 id=ne.2h3v.s8.a6096af5a3bc from=translated src=- shape=2945e896 vocab=d797aa23
-/
theorem commutator_zpow_ne_one (w : G) (hw : w ≠ 1) (k : ℤ) (hk : k ≠ 0) :
    ((old w)⁻¹ * beta⁻¹ * old w * beta) ^ k ≠ 1 := by
  rw [← commutatorWord_prod w hw]
  exact zpow_ne_one_of_cyclicallyReduced (commutatorWord w hw) (by decide) k hk

/-! A nested two-factor presentation is convenient for the outer alpha
normal-form calculation.  `LeftProduct G` is used as the base factor; its
extra unused free generator is harmless. -/

inductive OuterIndex
  | base
  | alpha
  deriving DecidableEq

def OuterFactor (G : Type) [Group G] : OuterIndex → Type
  | .base => LeftProduct G
  | .alpha => FreeGroup Unit

@[reducible] instance outerFactorGroup : ∀ i, Group (OuterFactor G i) := fun i => by
  cases i <;> simp only [OuterFactor] <;> infer_instance

abbrev MillerLeft (G : Type) [Group G] := CoprodI (OuterFactor G)

def baseOf (x : LeftProduct G) : MillerLeft G :=
  CoprodI.of (i := OuterIndex.base) x

def outerAlpha : MillerLeft G :=
  CoprodI.of (i := OuterIndex.alpha) (FreeGroup.of ())

/--
@isnad1 id=eq.0h2v.s5.d9e6fde284b3 from=translated src=- shape=392a6f92 vocab=cae9ccc4
-/
@[simp] theorem baseOf_inv (x : LeftProduct G) : baseOf x⁻¹ = (baseOf x)⁻¹ :=
  map_inv
    (CoprodI.of (M := OuterFactor G) (i := OuterIndex.base) :
      LeftProduct G →* MillerLeft G) x

/--
@isnad1 id=eq.0h3v.s6.80f5d92cb524 from=translated src=- shape=7b870ba5 vocab=bb38bfe5
-/
@[simp] theorem baseOf_zpow (x : LeftProduct G) (k : ℤ) :
    baseOf (x ^ k) = baseOf x ^ k :=
  map_zpow _ _ _

def outerLeftBasis (w z : G) : Fin 5 → MillerLeft G
  | 0 => baseOf beta
  | 1 => outerAlpha⁻¹ * baseOf beta * outerAlpha
  | 2 => (outerAlpha ^ 2)⁻¹ * (baseOf beta)⁻¹ * outerAlpha *
      baseOf beta * outerAlpha ^ 2
  | 3 => (outerAlpha ^ 3)⁻¹ *
      baseOf ((old w)⁻¹ * beta⁻¹ * old w * beta) * outerAlpha ^ 3
  | 4 => (outerAlpha ^ 2)⁻¹ * baseOf (old z * beta) * outerAlpha ^ 4

def baseSingleton (x : LeftProduct G) (hx : x ≠ 1) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.base OuterIndex.base :=
  .singleton x hx

def alphaSingleton (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha :=
  .singleton ((FreeGroup.of () : FreeGroup Unit) ^ k)
    (FreeGroup.unitGenerator_zpow_ne_one k hk)

/--
@isnad1 id=eq.1h2v.s6.8440ceda85bd from=translated src=- shape=23a42a42 vocab=a1a063bb
-/
@[simp] theorem baseSingleton_prod (x : LeftProduct G) (hx : x ≠ 1) :
    (baseSingleton x hx).prod = baseOf x := by
  exact CoprodI.NeWord.prod_singleton (M := OuterFactor G) (i := OuterIndex.base) x hx

/--
@isnad1 id=eq.1h2v.s6.cb2881a22842 from=translated src=- shape=5d17c20e vocab=d03875f8
-/
@[simp] theorem alphaSingleton_prod (k : ℤ) (hk : k ≠ 0) :
    (alphaSingleton (G := G) k hk).prod = outerAlpha ^ k := by
  change (CoprodI.of (M := OuterFactor G) (i := OuterIndex.alpha))
      ((FreeGroup.of ()) ^ k) =
    ((CoprodI.of (M := OuterFactor G) (i := OuterIndex.alpha))
      (FreeGroup.of ())) ^ k
  exact map_zpow _ _ _

def leftPowerWord1 (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha :=
  .append (alphaSingleton (-1) (by norm_num)) (by decide)
    (.append (baseSingleton (beta ^ k) (beta_zpow_ne_one k hk)) (by decide)
      (alphaSingleton 1 (by norm_num)))

def leftPowerWord2 (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha :=
  .append (alphaSingleton (-2) (by norm_num)) (by decide)
    (.append (baseSingleton beta⁻¹ (inv_ne_one.mpr beta_ne_one)) (by decide)
      (.append (alphaSingleton k hk) (by decide)
        (.append (baseSingleton beta beta_ne_one) (by decide)
          (alphaSingleton 2 (by norm_num)))))

def leftPowerWord3 (w : G) (hw : w ≠ 1) (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha :=
  .append (alphaSingleton (-3) (by norm_num)) (by decide)
    (.append
      (baseSingleton (((old w)⁻¹ * beta⁻¹ * old w * beta) ^ k)
        (commutator_zpow_ne_one w hw k hk)) (by decide)
      (alphaSingleton 3 (by norm_num)))

/--
@isnad1 id=eq.1h4v.s6.af0ad1603a25 from=translated src=- shape=ff270c9b vocab=a56c99c1
-/
@[simp] theorem leftPowerWord1_prod (w z : G) (k : ℤ) (hk : k ≠ 0) :
    (leftPowerWord1 (G := G) k hk).prod = outerLeftBasis w z 1 ^ k := by
  simp [leftPowerWord1, outerLeftBasis, baseOf_zpow]
  symm
  rw [show outerAlpha⁻¹ * baseOf beta * outerAlpha =
      outerAlpha⁻¹ * baseOf beta * (outerAlpha⁻¹)⁻¹ by group]
  rw [conj_zpow]
  group

/--
@isnad1 id=eq.1h4v.s6.4cb95f1e0629 from=translated src=- shape=ff270c9b vocab=c2cfcf13
-/
@[simp] theorem leftPowerWord2_prod (w z : G) (k : ℤ) (hk : k ≠ 0) :
    (leftPowerWord2 (G := G) k hk).prod = outerLeftBasis w z 2 ^ k := by
  simp [leftPowerWord2, outerLeftBasis]
  symm
  rw [show (outerAlpha ^ 2)⁻¹ * (baseOf beta)⁻¹ * outerAlpha *
        baseOf beta * outerAlpha ^ 2 =
      (outerAlpha ^ 2)⁻¹ *
        ((baseOf beta)⁻¹ * outerAlpha * ((baseOf beta)⁻¹)⁻¹) *
        (((outerAlpha ^ 2)⁻¹)⁻¹) by group]
  rw [conj_zpow, conj_zpow]
  group

/--
@isnad1 id=eq.2h4v.s7.b2ce64ba8062 from=translated src=- shape=3ea3bd07 vocab=4f6edb84
-/
@[simp] theorem leftPowerWord3_prod (w z : G) (hw : w ≠ 1)
    (k : ℤ) (hk : k ≠ 0) :
    (leftPowerWord3 w hw k hk).prod = outerLeftBasis w z 3 ^ k := by
  simp [leftPowerWord3, outerLeftBasis, baseOf_zpow]
  symm
  rw [show (outerAlpha ^ 3)⁻¹ *
        baseOf ((old w)⁻¹ * beta⁻¹ * old w * beta) * outerAlpha ^ 3 =
      (outerAlpha ^ 3)⁻¹ *
        baseOf ((old w)⁻¹ * beta⁻¹ * old w * beta) *
        (((outerAlpha ^ 3)⁻¹)⁻¹) by group]
  rw [conj_zpow]
  group

end Undecidability.MillerTancer.LeftNormalForm
