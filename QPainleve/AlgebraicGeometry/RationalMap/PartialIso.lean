/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Sections

/-!
# The domains of a partial isomorphism over a base

A partial isomorphism identifies the domains of its forward and inverse partial
maps over the base. Sections correspond under this isomorphism, exchanging
the source and target morphisms.
-/

public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.PartialIso

universe u

variable {S X Y : Scheme.{u}}

/-- A partial isomorphism gives a dominant morphism from its source open. -/
instance isDominant_toPartialMap_hom (f : X.PartialIso Y) : IsDominant f.toPartialMap.hom := by
  let := Opens.isDominant_ι f.dense_target
  exact inferInstanceAs (IsDominant (f.iso.hom ≫ f.target.ι))

/-- Restricting the source of a partial isomorphism restricts its forward partial map. -/
@[simp]
theorem toPartialMap_restrictSource (f : X.PartialIso Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hUf : U ≤ f.source) :
    (f.restrictSource U hU hUf).toPartialMap = f.toPartialMap.restrict U hU hUf := by
  refine PartialMap.ext _ _ rfl ?_
  let V := f.source.ι ⁻¹ᵁ U
  have hg : (Opens.isoOfLE hUf).inv ≫ V.ι = X.homOfLE hUf := by
    apply (cancel_mono f.source.ι).mp
    simp only [Category.assoc, V, Opens.isoOfLE_inv_ι, homOfLE_ι]
  -- The restricted source is U on both sides, so compare the open inclusions.
  have h :
      (Opens.isoOfLE hUf).inv ≫ (f.iso.hom.isoImage V).hom ≫
        (f.target.ι.isoImage (f.iso.hom ''ᵁ V)).hom ≫
          (f.target.ι ''ᵁ (f.iso.hom ''ᵁ V)).ι =
      X.homOfLE hUf ≫ f.iso.hom ≫ f.target.ι := by
    simp only [Hom.isoImage_hom_ι, Hom.isoImage_hom_ι_assoc, reassoc_of% hg]
  erw [isoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  exact (Category.assoc _ _ _).trans h

variable {A B : Over S} (f : A.left.PartialIso B.left) [f.toPartialMap.IsOver A.hom B.hom]

/-- Inverting a partial isomorphism over the base preserves base compatibility. -/
instance isOver_symm_toPartialMap : f.symm.toPartialMap.IsOver B.hom A.hom := by
  have hf : f.IsOver A.hom B.hom := f.toPartialMap.over A.hom B.hom
  exact ⟨hf.symm⟩

/-- The isomorphism of the two open domains regarded as schemes over the base. -/
def domainOverIso : f.toPartialMap.domainOver ≅ f.symm.toPartialMap.domainOver :=
  Over.isoMk f.iso (f.toPartialMap.over A.hom B.hom)

@[reassoc (attr := simp)]
theorem domainOverIso_hom_source :
    f.domainOverIso.hom ≫ f.symm.toPartialMap.domainSource = f.toPartialMap.domainTarget := by
  ext : 1
  rw [Over.comp_left, PartialMap.domainSource_left, PartialMap.domainTarget_left]
  rfl

@[reassoc (attr := simp)]
theorem domainOverIso_hom_target :
    f.domainOverIso.hom ≫ f.symm.toPartialMap.domainTarget = f.toPartialMap.domainSource := by
  ext : 1
  rw [Over.comp_left, PartialMap.domainTarget_left, PartialMap.domainSource_left]
  exact f.iso.hom_inv_id_assoc f.source.ι

@[reassoc (attr := simp)]
theorem domainOverIso_inv_source :
    f.domainOverIso.inv ≫ f.toPartialMap.domainSource = f.symm.toPartialMap.domainTarget := by
  rw [← f.domainOverIso_hom_target, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
theorem domainOverIso_inv_target :
    f.domainOverIso.inv ≫ f.toPartialMap.domainTarget = f.symm.toPartialMap.domainSource := by
  rw [← f.domainOverIso_hom_source, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.PartialIso

namespace AlgebraicGeometry.Scheme.PartialMap

universe u

variable {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated]

/-- A partial map representing a birational map is a partial isomorphism after
restricting to the common dense source open of the two representatives. -/
theorem exists_restrict_eq_toPartialMap (f : X.PartialMap Y) (e : X.PartialIso Y)
    (he : e.toRationalMap = f.toRationalMap) :
    ∃ (U : X.Opens) (hU : Dense (U : Set X)) (hUf : U ≤ f.domain) (e' : X.PartialIso Y),
      e'.toPartialMap = f.restrict U hU hUf := by
  let U := f.domain ⊓ e.source
  have hU : Dense (U : Set X) :=
    f.dense_domain.inter_of_isOpen_right e.dense_source e.source.isOpen
  let e' := e.restrictSource U hU inf_le_right
  refine ⟨U, hU, inf_le_left, e', ?_⟩
  have hres : e'.toPartialMap = e.toPartialMap.restrict U hU inf_le_right :=
    e.toPartialMap_restrictSource U hU inf_le_right
  rw [hres]
  have hdom : (e.toPartialMap.restrict U hU inf_le_right).domain =
      (f.restrict U hU inf_le_left).domain := rfl
  refine (equiv_iff_of_domain_eq_of_isSeparated (Limits.terminal.from X)
    (Limits.terminal.from Y) hdom).mp (toRationalMap_eq_iff.mp ?_)
  exact (e.toPartialMap.restrict_toRationalMap U hU inf_le_right).trans
    (he.trans (f.restrict_toRationalMap U hU inf_le_left).symm)

end AlgebraicGeometry.Scheme.PartialMap
