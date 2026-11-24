/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Cohomology
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Conormal
import QPainleve.AlgebraicGeometry.IdealSheaf.Quotient
import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.Product
import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.Restriction

/-!
# Products in the filtration of an exceptional fiber

For a proper exceptional contraction over an affine base, filter the global functions
on the source by vanishing to order at least `n` on the exceptional fiber.
Products of functions of orders at least `m` and `n` generate the layer of order `m + n`.
This is the multiplication step in the formal neighborhood calculation of
[Stacks Project, Lemma 54.16.3](https://stacks.math.columbia.edu/tag/0C2K).
-/

public noncomputable section

open CategoryTheory Functor.LaxMonoidal MonoidalCategory
open TauCeti (isEffectiveCartier_pow)
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

variable {X : Scheme.{u}} {E : X.IdealSheafData} (hE : E.IsExceptionalCurveOfFirstKind)

local notation "P" => pullback E.subschemeι
private abbrev restrictPower (E : X.IdealSheafData) (n : ℕ) :=
  E.subschemeι.pullbackSections (E ^ n).sheaf ⊤

local notation "r(" n ")" => restrictPower E n

private abbrev asFunction (I : X.IdealSheafData) : Γ(I.sheaf, ⊤) →+ Γ(X, ⊤) :=
  ((I.sheafι : I.sheaf ⟶ Scheme.Modules.unit X).app ⊤).hom

include hE in
private theorem surjective_restrict_power
    {Y : Scheme.{u}} [IsAffine Y] [IsLocallyNoetherian Y] {I : Y.IdealSheafData}
    (f : X ⟶ Y) [IsProper f] (hI : I.comap f = E)
    (hU : I.support.compl ≤ f.isoLocus) (n : ℕ) :
    Function.Surjective (r(n)) := by
  let H := isEffectiveCartier_pow hE.isEffectiveCartier n
  have h := hE.subsingleton_cohomology_one_ideal_pow_of_contraction f hI hU (n + 1)
  have he : IsIso ((E ^ n).sheafMul E) :=
    (E ^ n).isIso_sheafMul_of_isEffectiveCartier E hE.isEffectiveCartier
  have hvan : Subsingleton (Cohomology (H.toInvertibleSheaf.obj ⊗ E.sheaf) 1) := by
    rw [H.toInvertibleSheaf_obj]
    let d := (cohomologyFunctor X 1).mapIso
      (asIso ((E ^ n).sheafMul E) ≪≫ eqToIso (congrArg sheaf (pow_succ E n).symm))
    exact @Function.Injective.subsingleton _ _ _ d.addCommGroupIsoToAddEquiv.injective h
  have hs : Function.Surjective
      (E.subschemeι.pullbackSectionsLE H.toInvertibleSheaf.obj ⊤ (E.subschemeι ⁻¹ᵁ ⊤) le_rfl) :=
    E.surjective_pullbackSectionsLE_of_subsingleton_cohomology_one H.toInvertibleSheaf hvan
  have hs' : Function.Surjective (E.subschemeι.pullbackSections H.toInvertibleSheaf.obj ⊤) := by
    intro y
    obtain ⟨x, hx⟩ := hs y
    exact ⟨x, (E.subschemeι.pullbackSectionsLE_self H.toInvertibleSheaf.obj ⊤ x).symm.trans hx⟩
  rw [H.toInvertibleSheaf_obj] at hs'
  exact hs'

include hE in
private theorem mem_next_sections_of_restrict_power_eq_zero (n : ℕ)
    (s : Γ((E ^ n).sheaf, ⊤)) (hs : r(n) s = 0) :
    asFunction (E ^ n) s ∈ (E ^ (n + 1)).sections ⊤ := by
  let H := isEffectiveCartier_pow hE.isEffectiveCartier n
  have hex := E.exact_pullbackSections H.toInvertibleSheaf
  rw [H.toInvertibleSheaf_obj] at hex
  obtain ⟨t, ht⟩ := (hex s).mp hs
  let a := ((E ^ n).sheafMul E).app ⊤ t
  let h : E ^ n * E ≤ E ^ n := mul_le_of_le_one_right' le_top
  have heq : (sheafHomOfLE h).app ⊤ a = s := by
    have hh : (sheafHomOfLE h).app ⊤ a =
        ((E ^ n).sheaf ◁ (E.sheafι : E.sheaf ⟶ 𝟙_ X.Modules) ≫ (ρ_ (E ^ n).sheaf).hom).app ⊤ t :=
      congrArg (fun g ↦ g.app ⊤ t) (sheafMul_sheafHomOfLE_mul (E ^ n) E)
    exact hh.trans ht
  have heq' : asFunction (E ^ n) s = asFunction (E ^ n * E) a := by
    have hh : asFunction (E ^ n) ((sheafHomOfLE h).app ⊤ a) = asFunction (E ^ n * E) a :=
      congrArg (fun g ↦ g.app ⊤ a) (sheafHomOfLE_sheafι h)
    exact (congrArg (asFunction (E ^ n)) heq.symm).trans hh
  rw [pow_succ, heq']
  exact (E ^ n * E).sheafι_app_mem ⊤ a

private def conormalProduct (m n : ℕ) :
    TensorProduct Γ(E.subscheme, ⊤) Γ((P).obj (E ^ m).sheaf, ⊤)
      Γ((P).obj (E ^ n).sheaf, ⊤) →ₗ[Γ(E.subscheme, ⊤)] Γ((P).obj (E ^ (m + n)).sheaf, ⊤) :=
  (μ (sectionsFunctor (⊤ : E.subscheme.Opens)) ((P).obj (E ^ m).sheaf) ((P).obj (E ^ n).sheaf) ≫
    (sectionsFunctor (⊤ : E.subscheme.Opens)).map
      (inv (Functor.OplaxMonoidal.δ P (E ^ m).sheaf (E ^ n).sheaf) ≫
        (P).map ((E ^ m).sheafMul (E ^ n) ≫ eqToHom (congrArg sheaf (pow_add E m n).symm)))).hom

private def multiplyPowerSections {m n : ℕ} (s : Γ((E ^ m).sheaf, ⊤)) (t : Γ((E ^ n).sheaf, ⊤)) :
    Γ((E ^ (m + n)).sheaf, ⊤) :=
  (eqToHom (congrArg sheaf (pow_add E m n).symm)).app ⊤
    ((E ^ m).sectionsMul (E ^ n) ⊤ s t)

private theorem sheafι_multiplyPowerSections {m n : ℕ}
    (s : Γ((E ^ m).sheaf, ⊤)) (t : Γ((E ^ n).sheaf, ⊤)) :
    asFunction (E ^ (m + n)) (multiplyPowerSections s t) =
      asFunction (E ^ m) s * asFunction (E ^ n) t := by
  have he : ∀ {I J : X.IdealSheafData} (h : I = J),
      eqToHom (congrArg sheaf h) ≫ (J.sheafι : J.sheaf ⟶ Scheme.Modules.unit X) = I.sheafι := by
    rintro I _ rfl
    exact Category.id_comp _
  have he' := congrArg (fun g ↦ g.app ⊤ ((E ^ m).sectionsMul (E ^ n) ⊤ s t))
    (he (pow_add E m n).symm)
  exact he'.trans ((E ^ m).sheafι_app_sectionsMul (E ^ n) ⊤ s t)

private theorem conormalProduct_pullbackSections (m n : ℕ)
    (s : Γ((E ^ m).sheaf, ⊤)) (t : Γ((E ^ n).sheaf, ⊤)) :
    conormalProduct (E := E) m n (r(m) s ⊗ₜ r(n) t) = r(m + n) (multiplyPowerSections s t) := by
  let c := eqToHom (congrArg sheaf (pow_add E m n).symm)
  let a := (E ^ m).sheafMul (E ^ n) ≫ c
  let δ := Functor.OplaxMonoidal.δ P (E ^ m).sheaf (E ^ n).sheaf
  let z : Γ((E ^ m).sheaf ⊗ (E ^ n).sheaf, ⊤) :=
    μ (sectionsFunctor (⊤ : X.Opens)) (E ^ m).sheaf (E ^ n).sheaf (s ⊗ₜ t)
  have hδ := E.subschemeι.δ_app_pullbackSections_μ (E ^ m).sheaf ⊤ (E ^ n).sheaf s t
  have hδeq : δ.app ⊤ (E.subschemeι.pullbackSections _ ⊤ z) =
      μ (sectionsFunctor (⊤ : E.subscheme.Opens)) _ _ (r(m) s ⊗ₜ r(n) t) := hδ
  have hδ' : (inv δ).app ⊤
      (μ (sectionsFunctor (⊤ : E.subscheme.Opens)) _ _ (r(m) s ⊗ₜ r(n) t)) =
        E.subschemeι.pullbackSections _ ⊤ z := by
    let y : Γ((P).obj ((E ^ m).sheaf ⊗ (E ^ n).sheaf), ⊤) :=
      E.subschemeι.pullbackSections _ ⊤ z
    have he : (inv δ).app ⊤ (δ.app ⊤ y) = y :=
      congrArg (fun g ↦ g.app ⊤ y) (IsIso.hom_inv_id δ)
    exact (congrArg ((inv δ).app ⊤) hδeq.symm).trans he
  have hz : a.app ⊤ z = multiplyPowerSections s t := by
    dsimp only [a, multiplyPowerSections]
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    dsimp only [z]
    rw [← tmulRight_apply,
      sheafMul_app_tmulRight]
  have hfirst : conormalProduct m n (r(m) s ⊗ₜ r(n) t) =
      ((P).map a).app ⊤ (E.subschemeι.pullbackSections _ ⊤ z) :=
    congrArg (((P).map a).app ⊤) hδ'
  have hsecond : ((P).map a).app ⊤ (E.subschemeι.pullbackSections _ ⊤ z) =
      r(m + n) (a.app ⊤ z) := E.subschemeι.pullbackSections_naturality _ ⊤ a z
  exact hfirst.trans (hsecond.trans (congrArg (r(m + n)) hz))

private theorem exists_restrict_power_eq_of_conormalProduct
    {m n : ℕ} (hm : Function.Surjective (r(m))) (hn : Function.Surjective (r(n)))
    (w : TensorProduct Γ(E.subscheme, ⊤) Γ((P).obj (E ^ m).sheaf, ⊤)
      Γ((P).obj (E ^ n).sheaf, ⊤)) :
    ∃ s : Γ((E ^ (m + n)).sheaf, ⊤),
      asFunction (E ^ (m + n)) s ∈ (E ^ m).sections ⊤ * (E ^ n).sections ⊤ ∧
      r(m + n) s = conormalProduct (E := E) m n w := by
  induction w using TensorProduct.inductionOn with
  | tmul a b =>
      obtain ⟨s, rfl⟩ := hm a
      obtain ⟨t, rfl⟩ := hn b
      refine ⟨multiplyPowerSections s t, ?_, (conormalProduct_pullbackSections m n s t).symm⟩
      rw [sheafι_multiplyPowerSections]
      exact Ideal.mul_mem_mul ((E ^ m).sheafι_app_mem ⊤ s) ((E ^ n).sheafι_app_mem ⊤ t)
  | add a b ha hb =>
      obtain ⟨s, hs, hs'⟩ := ha
      obtain ⟨t, ht, ht'⟩ := hb
      refine ⟨s + t, ?_, ?_⟩
      · rw [map_add]
        exact Ideal.add_mem _ hs ht
      · rw [map_add, map_add, hs', ht']
        rfl

include hE in
/-- Over an affine Noetherian base, products of sections of two powers of the ideal
of a contracted exceptional fiber generate their sum-order layer. The error consists
of sections of the next ideal power. -/
theorem sections_mul_sup_of_exceptional_contraction
    {Y : Scheme.{u}} [IsAffine Y] [IsLocallyNoetherian Y] {I : Y.IdealSheafData}
    (f : X ⟶ Y) [IsProper f] (hI : I.comap f = E)
    (hU : I.support.compl ≤ f.isoLocus) (m n : ℕ) :
    (E ^ m).sections ⊤ * (E ^ n).sections ⊤ ⊔ (E ^ (m + n + 1)).sections ⊤ =
      (E ^ (m + n)).sections ⊤ := by
  refine le_antisymm (sup_le ?_ ?_) ?_
  · rw [pow_add]
    exact Ideal.mul_le.mpr fun s hs t ht ↦ mul_mem_sections_mul hs ht
  · apply sections_mono
    exact pow_le_pow_right_of_le_one' (le_of_le_of_eq le_top (one_eq_top (X := X)).symm)
      (Nat.le_succ _)
  · intro a ha
    let s := (E ^ (m + n)).sectionMk a ha
    have hmul : Function.Surjective (conormalProduct (E := E) m n) :=
      hE.surjective_conormalPowerMultiplication m n
    obtain ⟨w, hw⟩ := hmul (r(m + n) s)
    obtain ⟨t, ht, ht'⟩ := exists_restrict_power_eq_of_conormalProduct
      (hE.surjective_restrict_power f hI hU m) (hE.surjective_restrict_power f hI hU n) w
    have hzero : r(m + n) (s - t) = 0 := by rw [map_sub, ht', hw, sub_self]
    let b := asFunction (E ^ (m + n)) t
    have hab : a - b ∈ (E ^ (m + n + 1)).sections ⊤ := by
      have h := hE.mem_next_sections_of_restrict_power_eq_zero (m + n) (s - t) hzero
      have hs : asFunction (E ^ (m + n)) s = a :=
        (E ^ (m + n)).sheafι_app_sectionMk a ha
      rw [map_sub, hs] at h
      exact h
    exact Submodule.mem_sup.mpr ⟨b, ht, a - b, hab, by abel⟩

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
