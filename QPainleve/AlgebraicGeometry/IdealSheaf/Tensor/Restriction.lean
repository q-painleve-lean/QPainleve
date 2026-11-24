/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.VectorBundle.ProjectionFormula
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.IdealSheaf.TensorSequence
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
import QPainleve.AlgebraicGeometry.IdealSheaf.Quotient
import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.Product
import QPainleve.AlgebraicGeometry.Modules.Pullback.Sections

/-!
# Restriction of a line bundle to a closed subscheme

The quotient of a line bundle by its ideal-sheaf twist is the direct image of the
restricted line bundle. The canonical projection morphism identifies the quotient
arrow with restriction, and identifies the map of quotients with the pullback of
the original map of line bundles.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal
open TauCeti (isEffectiveCartier_pow)
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules (Cohomology cohomologyFunctor)

namespace AlgebraicGeometry.Scheme.IdealSheafData

open Scheme.Modules Scheme.Hom

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData)

local notation "i" => I.subschemeι
local notation "F" => pullback i
local notation "G" => pushforward i

/-- The canonical comparison from the ideal-sheaf quotient to the direct image of the
restricted line bundle. -/
def tensorRestrictionHom (M : InvertibleSheaf X) :
    M.obj ⊗ I.pushforwardSubscheme ⟶ (G).obj ((F).obj M.obj) :=
  (i).tensorPushforwardHom M.obj (𝟙_ I.subscheme.Modules) ≫
    (G).map (ρ_ ((F).obj M.obj)).hom

/-- The canonical comparison on the ideal-sheaf quotient of a line bundle is an isomorphism. -/
theorem isIso_tensorRestrictionHom (M : InvertibleSheaf X) :
    IsIso (I.tensorRestrictionHom M) := by
  have := (i).isIso_tensorPushforwardHom M (𝟙_ I.subscheme.Modules)
  unfold tensorRestrictionHom
  infer_instance

/-- The ideal-sheaf quotient arrow followed by the comparison is the adjunction unit
for restriction to the closed subscheme. -/
@[reassoc]
theorem tensorRestrictionHom_unit (M : InvertibleSheaf X) :
    (ρ_ M.obj).inv ≫ M.obj ◁ I.toPushforwardSubscheme ≫ I.tensorRestrictionHom M =
      (pullbackPushforwardAdjunction i).unit.app M.obj := by
  have hε : I.toPushforwardSubscheme = ε G :=
    I.toPushforwardSubscheme_def.trans (pushforward_ε i).symm
  simp only [hε, tensorRestrictionHom, tensorPushforwardHom_def, Category.assoc]
  let u : M.obj ⟶ (G).obj ((F).obj M.obj) :=
    (pullbackPushforwardAdjunction i).unit.app M.obj
  have h := whisker_exchange_assoc u (ε G)
    (μ G ((F).obj M.obj) (𝟙_ I.subscheme.Modules) ≫ (G).map (ρ_ ((F).obj M.obj)).hom)
  refine (congrArg ((ρ_ M.obj).inv ≫ ·) h).trans ?_
  rw [← Functor.LaxMonoidal.right_unitality G ((F).obj M.obj),
    rightUnitor_naturality u, Iso.inv_hom_id_assoc]

/-- Global sections of a line bundle lift from a closed subscheme if the first
cohomology of the ideal-sheaf twist vanishes. -/
theorem surjective_pullbackSectionsLE_of_subsingleton_cohomology_one (M : InvertibleSheaf X)
    (h : Subsingleton (Cohomology (M.obj ⊗ I.sheaf) 1)) :
    Function.Surjective ((i).pullbackSectionsLE M.obj ⊤ ⊤ (by simp)) := by
  let N := M.obj
  have : M.obj.IsLocallyFree := inferInstanceAs N.IsLocallyFree
  have : M.obj.IsFiniteType := inferInstanceAs N.IsFiniteType
  have hquot := I.surjective_tensorRestriction_of_subsingleton_cohomology_one M.obj h
  have : IsIso (I.tensorRestrictionHom M) := I.isIso_tensorRestrictionHom M
  have hcompare := (ConcreteCategory.bijective_of_isIso ((I.tensorRestrictionHom M).app ⊤)).2
  -- The preimage of the full open is the full open of the closed subscheme.
  let htop : (⊤ : I.subscheme.Opens) ≤ (i) ⁻¹ᵁ (⊤ : X.Opens) := by simp
  have : IsIso (homOfLE htop).op := by
    have := homOfLE_isIso_of_eq htop ((i).preimage_top.symm)
    infer_instance
  have hre : Function.Surjective
      (((F).obj M.obj).presheaf.map (homOfLE htop).op) :=
    (ConcreteCategory.bijective_of_isIso _).2
  intro y
  obtain ⟨v, hv⟩ := hre y
  obtain ⟨x, hx⟩ := hcompare.comp hquot v
  have he := congrArg (fun f ↦ f.app ⊤ x) (I.tensorRestrictionHom_unit M)
  simp only [Scheme.Modules.Hom.comp_app] at he
  have hu : (i).pullbackSections M.obj ⊤ x = v := by
    rw [pullbackSections_apply]
    exact he.symm.trans hx
  refine ⟨x, ?_⟩
  rw [pullbackSectionsLE_apply, hu, hv]

/-- A section of a line bundle vanishes on the closed subscheme exactly when it
comes from the tensor product with the defining ideal. -/
theorem pullbackSections_eq_zero_iff (M : InvertibleSheaf X) (s : Γ(M.obj, ⊤)) :
    (i).pullbackSections M.obj ⊤ s = 0 ↔
      ∃ w, (M.obj ◁ I.sheafι ≫ (ρ_ M.obj).hom).app ⊤ w = s := by
  let μ := (ρ_ M.obj).inv
  let t := M.obj ◁ I.toPushforwardSubscheme
  have : IsIso (I.tensorRestrictionHom M) := I.isIso_tensorRestrictionHom M
  have hzero : t.app ⊤ (μ.app ⊤ s) = 0 ↔ (i).pullbackSections M.obj ⊤ s = 0 := by
    rw [pullbackSections_apply, ← I.tensorRestrictionHom_unit,
      Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      ((I.tensorRestrictionHom M).app ⊤)).1).symm
  rw [← hzero]
  have hex : Function.Exact ⇑((M.obj ◁ I.sheafι).app ⊤) ⇑(t.app ⊤) :=
    TauCeti.AlgebraicGeometry.Scheme.Modules.exact_sections
      (I.shortExact_tensor_toPushforwardSubscheme M.obj)
  rw [hex _]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, by
      simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
      rw [hw]
      exact Iso.inv_hom_id_apply ((sectionsFunctor ⊤).mapIso (ρ_ M.obj)) s⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, by
      simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hw
      rw [← hw]
      exact (Iso.hom_inv_id_apply ((sectionsFunctor ⊤).mapIso (ρ_ M.obj)) _).symm⟩

/-- Under the quotient comparison, the map of quotients is the direct image of the
pullback of the original morphism. -/
@[reassoc]
theorem tensorRestrictionHom_naturality {M N : InvertibleSheaf X} (a : M.obj ⟶ N.obj) :
    a ▷ I.pushforwardSubscheme ≫ I.tensorRestrictionHom N =
      I.tensorRestrictionHom M ≫ (G).map ((F).map a) := by
  simp only [tensorRestrictionHom, Category.assoc]
  refine (tensorPushforwardHom_naturality_left_assoc i a (𝟙_ I.subscheme.Modules) _).trans ?_
  exact congrArg ((i).tensorPushforwardHom M.obj (𝟙_ I.subscheme.Modules) ≫ ·)
    ((Functor.map_comp _ _ _).symm.trans
      ((congrArg (G).map (rightUnitor_naturality ((F).map a))).trans (Functor.map_comp _ _ _)))

/-- A section of the `n`th power of a Cartier ideal restricts to zero on the
divisor exactly when its underlying function belongs to the next power. -/
theorem IsEffectiveCartier.pullbackSections_pow_eq_zero_iff {E : X.IdealSheafData}
    (hE : E.IsEffectiveCartier) (n : ℕ)
    (s : Γ((E ^ n).sheaf, ⊤)) :
    E.subschemeι.pullbackSections (E ^ n).sheaf ⊤ s = 0 ↔
      (E ^ n).sheafι.app ⊤ s ∈ (E ^ (n + 1)).sections ⊤ := by
  rw [pow_succ]
  let N := (isEffectiveCartier_pow hE n).toInvertibleSheaf
  let a := (E ^ n).sheaf ◁ E.sheafι ≫ (ρ_ (E ^ n).sheaf).hom
  let b := sheafHomOfLE (mul_le_of_le_one_right' (a := E ^ n) (b := E) le_top)
  have hab : (E ^ n).sheafMul E ≫ b = a := sheafMul_sheafHomOfLE_mul _ _
  have hk (M : X.Modules) (hM : M = N.obj) (t : Γ(M, ⊤)) :
      E.subschemeι.pullbackSections M ⊤ t = 0 ↔
        ∃ w, (M ◁ E.sheafι ≫ (ρ_ M).hom).app ⊤ w = t := by
    subst M
    exact E.pullbackSections_eq_zero_iff N t
  rw [hk _ (IsEffectiveCartier.toInvertibleSheaf_obj _).symm s]
  constructor
  · rintro ⟨w, rfl⟩
    let z := ((E ^ n).sheafMul E).app ⊤ w
    have hb : a.app ⊤ w = b.app ⊤ z :=
      (ConcreteCategory.congr_hom (congrArg (fun g ↦ g.app ⊤) hab) w).symm
    rw [hb]
    exact (ConcreteCategory.congr_hom (congrArg (fun g ↦ g.app ⊤)
      (sheafHomOfLE_sheafι (mul_le_of_le_one_right' (a := E ^ n) (b := E) le_top))) z).symm ▸
        (E ^ n * E).sheafι_app_mem ⊤ z
  · intro hs
    let z := (E ^ n * E).sectionMk ((E ^ n).sheafι.app ⊤ s) hs
    have hz : b.app ⊤ z = s := by
      apply (E ^ n).sheafι_app_injective ⊤
      have hc := ConcreteCategory.congr_hom (congrArg (fun g ↦ g.app ⊤)
        (sheafHomOfLE_sheafι (mul_le_of_le_one_right' (a := E ^ n) (b := E) le_top))) z
      exact hc.trans (sheafι_app_sectionMk _ _ _)
    have := (E ^ n).isIso_sheafMul_of_isEffectiveCartier E hE
    obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso (((E ^ n).sheafMul E).app ⊤)).2 z
    refine ⟨w, ?_⟩
    have hh := ConcreteCategory.congr_hom (congrArg (fun g ↦ g.app ⊤) hab) w
    exact hh.symm.trans ((congrArg (b.app ⊤) hw).trans hz)

/-- Sections of the `n`th conormal power lift to sections of the ambient Cartier
ideal power when the next ideal power has vanishing first cohomology. -/
theorem IsEffectiveCartier.surjective_pullbackSections_pow_of_subsingleton_cohomology_one
    {E : X.IdealSheafData} (hE : E.IsEffectiveCartier)
    (n : ℕ) (hvan : Subsingleton (Cohomology (E ^ (n + 1)).sheaf 1)) :
    Function.Surjective (E.subschemeι.pullbackSections (E ^ n).sheaf ⊤) := by
  let N := (isEffectiveCartier_pow hE n).toInvertibleSheaf
  have hmul := (E ^ n).isIso_sheafMul_of_isEffectiveCartier E hE
  let e : N.obj ⊗ E.sheaf ≅ (E ^ (n + 1)).sheaf :=
    eqToIso (congrArg (fun M : X.Modules ↦ M ⊗ E.sheaf)
      (IsEffectiveCartier.toInvertibleSheaf_obj _)) ≪≫
    asIso ((E ^ n).sheafMul E) ≪≫ eqToIso (congrArg sheaf (pow_succ E n).symm)
  have hv : Subsingleton (Cohomology (N.obj ⊗ E.sheaf) 1) :=
    @Function.Injective.subsingleton _ _ _
      ((cohomologyFunctor _ 1).mapIso e).addCommGroupIsoToAddEquiv.injective hvan
  have hs : Function.Surjective (E.subschemeι.pullbackSections N.obj ⊤) := by
    intro y
    obtain ⟨x, hx⟩ := E.surjective_pullbackSectionsLE_of_subsingleton_cohomology_one N hv y
    exact ⟨x, by simpa only [Scheme.Hom.pullbackSectionsLE_top] using! hx⟩
  exact IsEffectiveCartier.toInvertibleSheaf_obj _ ▸ hs

end AlgebraicGeometry.Scheme.IdealSheafData
