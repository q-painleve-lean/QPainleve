/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition

/-!
# Domains of partial maps over a base

The domain of a partial map over a base has morphisms to the source and the target
over that base. A section of the domain of a composite therefore gives sections
of both domains, with the same intermediate point. The overlap is Mathlib's
`Scheme.PartialMap.comp_domain`.
-/

public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.PartialMap

universe u

variable {S : Scheme.{u}} {X Y Z : Over S} (f : X.left.PartialMap Y.left)

/-- The open domain of a partial map as an object over the common base. -/
abbrev domainOver : Over S := Over.mk (f.domain.ι ≫ X.hom)

/-- The inclusion of the domain into the source over the base. -/
def domainSource : f.domainOver ⟶ X :=
  Over.homMk f.domain.ι

@[simp]
theorem domainSource_left : f.domainSource.left = f.domain.ι := (rfl)

variable [f.IsOver X.hom Y.hom]

/-- The partial map on its domain as a morphism to the target over the base. -/
def domainTarget : f.domainOver ⟶ Y :=
  Over.homMk f.hom (f.over X.hom Y.hom)

@[simp]
theorem domainTarget_left : f.domainTarget.left = f.hom := (rfl)

variable (U : X.left.Opens) (hU : Dense (U : Set X.left)) (hUf : U ≤ f.domain)

/-- The inclusion of a smaller domain into the domain of the original partial map. -/
def restrictDomainHom : (f.restrict U hU hUf).domainOver ⟶ f.domainOver :=
  Over.homMk (X.left.homOfLE hUf) (homOfLE_ι_assoc _ _ _)

omit [f.IsOver X.hom Y.hom] in
@[simp]
theorem restrictDomainHom_left :
    (f.restrictDomainHom U hU hUf).left = X.left.homOfLE hUf := (rfl)

omit [f.IsOver X.hom Y.hom] in
@[reassoc (attr := simp)]
theorem restrictDomainHom_source :
    f.restrictDomainHom U hU hUf ≫ f.domainSource =
      (f.restrict U hU hUf).domainSource := by
  ext : 1
  exact homOfLE_ι _ hUf

@[reassoc (attr := simp)]
theorem restrictDomainHom_target :
    f.restrictDomainHom U hU hUf ≫ f.domainTarget =
      (f.restrict U hU hUf).domainTarget := by
  ext : 1
  rfl

variable [PreirreducibleSpace X.left] [Nonempty Y.left] [IsDominant f.hom]
  (g : Y.left.PartialMap Z.left)

/-- The domain of a composite as an open of the domain of the first partial map. -/
def compDomainLeft : (f.comp g).domainOver ⟶ f.domainOver :=
  Over.homMk (X.left.homOfLE (f.domain.ι_image_le (f.hom ⁻¹ᵁ g.domain)))
    (homOfLE_ι_assoc _ _ _)

omit [f.IsOver X.hom Y.hom] in
@[simp]
theorem compDomainLeft_left :
    (f.compDomainLeft g).left = X.left.homOfLE (f.domain.ι_image_le (f.hom ⁻¹ᵁ g.domain)) :=
  (rfl)

/-- The first partial map sends the composite domain into the domain of the second map. -/
def compDomainRight : (f.comp g).domainOver ⟶ g.domainOver :=
  Over.homMk ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫ f.hom ∣_ g.domain)
    (by
      let U := f.hom ⁻¹ᵁ g.domain
      -- The composite domain is the open image used by the restriction isomorphism.
      change ((f.domain.ι.isoImage U).inv ≫ f.hom ∣_ g.domain) ≫ g.domain.ι ≫ Y.hom =
        (f.domain.ι ''ᵁ U).ι ≫ X.hom
      rw [Category.assoc, morphismRestrict_ι_assoc, f.over X.hom Y.hom]
      exact f.domain.ι.isoImage_inv_ι_assoc _ _)

@[simp]
theorem compDomainRight_left :
    (f.compDomainRight g).left =
      (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫ f.hom ∣_ g.domain :=
  (rfl)

omit [f.IsOver X.hom Y.hom] in
@[reassoc (attr := simp)]
theorem compDomainLeft_source :
    f.compDomainLeft g ≫ f.domainSource = (f.comp g).domainSource := by
  ext : 1
  exact homOfLE_ι _ (f.domain.ι_image_le (f.hom ⁻¹ᵁ g.domain))

@[reassoc]
theorem compDomainLeft_target :
    f.compDomainLeft g ≫ f.domainTarget = f.compDomainRight g ≫ g.domainSource := by
  ext : 1
  let U := f.hom ⁻¹ᵁ g.domain
  -- Use the open image description to identify both maps out of the composite domain.
  change X.left.homOfLE (f.domain.ι_image_le U) ≫ f.hom =
    ((f.domain.ι.isoImage U).inv ≫ f.hom ∣_ g.domain) ≫ g.domain.ι
  rw [Category.assoc, morphismRestrict_ι, Opens.isoImage_ι_inv_ι_assoc]

variable [g.IsOver Y.hom Z.hom]

instance : (f.comp g).IsOver X.hom Z.hom where
  over := by
    have hh : (f.comp g).hom = (f.compDomainRight g).left ≫ g.hom :=
      (Category.assoc _ _ _).symm
    rw [hh, Category.assoc, g.over Y.hom Z.hom]
    exact Over.w (f.compDomainRight g)

@[reassoc (attr := simp)]
theorem compDomainRight_target :
    f.compDomainRight g ≫ g.domainTarget = (f.comp g).domainTarget := by
  ext : 1
  exact Category.assoc _ _ _

instance (A : Over S) : (PartialMap.id A.left).IsOver A.hom A.hom :=
  Hom.isOver_toPartialMap (Category.id_comp _)

@[simp]
theorem domainTarget_id (A : Over S) :
    (PartialMap.id A.left).domainTarget = (PartialMap.id A.left).domainSource := by
  ext : 1
  simp only [domainTarget_left, domainSource_left, Hom.toPartialMap_hom, Scheme.topIso_hom,
    Category.comp_id]
  rfl

end AlgebraicGeometry.Scheme.PartialMap
