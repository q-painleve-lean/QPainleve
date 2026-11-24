/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.RationalMap.ValuationRing
public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
public import QPainleve.AlgebraicGeometry.RationalMap.FunctionField

/-!
# Composition on the common domain of rational maps

A rational map out of an integral scheme can be followed by a second rational map
when the image of the generic point lies in the second map's domain. This lets one
compose with an evaluation on a fixed center fiber even if that evaluation is not
dominant. The construction uses Mathlib's maximal partial maps
(`Scheme.RationalMap.toPartialMap`) and generalizes the common-domain construction
of `Scheme.PartialMap.comp` by taking its density as an explicit hypothesis.
-/

public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

namespace PartialMap

variable {X Y Z : Scheme.{u}}

/-- The open where the first partial map lands in the domain of the second. -/
def compDomain (f : X.PartialMap Y) (g : Y.PartialMap Z) : X.Opens :=
  f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain)

/-- The common domain is the inverse image of the second domain inside the first. -/
theorem compDomain_eq (f : X.PartialMap Y) (g : Y.PartialMap Z) :
    f.compDomain g = f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain) := (rfl)

/-- Membership in the common domain tests both regularity conditions in order. -/
theorem mem_compDomain (f : X.PartialMap Y) (g : Y.PartialMap Z) {x : X} :
    x ∈ f.compDomain g ↔ ∃ hx : x ∈ f.domain, f.hom ⟨x, hx⟩ ∈ g.domain := by
  rw [compDomain, ← SetLike.mem_coe, Hom.coe_image, Set.mem_image]
  exact ⟨fun ⟨y, hy, he⟩ ↦ he ▸ ⟨y.property, f.hom.mem_preimage.mp hy⟩,
    fun ⟨hx, hy⟩ ↦ ⟨⟨x, hx⟩, f.hom.mem_preimage.mpr hy, rfl⟩⟩

/-- Compose two partial maps when their common domain is dense. -/
def compOfDense (f : X.PartialMap Y) (g : Y.PartialMap Z)
    (h : Dense (f.compDomain g : Set X)) : X.PartialMap Z where
  domain := f.compDomain g
  dense_domain := h
  hom := (f.domain.ι.isoImage _).inv ≫ f.hom ∣_ g.domain ≫ g.hom

@[simp]
theorem compOfDense_domain (f : X.PartialMap Y) (g : Y.PartialMap Z)
    (h : Dense (f.compDomain g : Set X)) : (f.compOfDense g h).domain = f.compDomain g := (rfl)

private theorem compOfDense_hom (f : X.PartialMap Y) (g : Y.PartialMap Z)
    (h : Dense (f.compDomain g : Set X)) :
    (f.compOfDense g h).hom =
      (X.isoOfEq ((f.compOfDense_domain g h).trans (f.compDomain_eq g))).hom ≫
        (f.domain.ι.isoImage _).inv ≫ f.hom ∣_ g.domain ≫ g.hom := by
  simp [compOfDense, compDomain]

/-- On a dominant first partial map, composition on a dense common domain is
Mathlib's composition. -/
theorem compOfDense_eq_comp [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    (h : Dense (f.compDomain g : Set X)) : f.compOfDense g h = f.comp g :=
  (rfl)

/-- On any test scheme mapping into the two regular domains, the composite
evaluates to the second map applied to the second lift. -/
theorem compOfDense_hom_eq {T : Scheme.{u}} (f : X.PartialMap Y) (g : Y.PartialMap Z)
    (h : Dense (f.compDomain g : Set X)) (a : T ⟶ f.domain.toScheme)
    (b : T ⟶ g.domain.toScheme) (c : T ⟶ (f.compOfDense g h).domain.toScheme)
    (ha : c ≫ (f.compOfDense g h).domain.ι = a ≫ f.domain.ι)
    (hb : a ≫ f.hom = b ≫ g.domain.ι) :
    c ≫ (f.compOfDense g h).hom = b ≫ g.hom := by
  let j := (X.isoOfEq ((f.compOfDense_domain g h).trans (f.compDomain_eq g))).hom ≫
    (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv
  have hj : c ≫ j ≫ (f.hom ⁻¹ᵁ g.domain).ι = a := by
    apply (cancel_mono f.domain.ι).mp
    simpa [j, Category.assoc] using ha
  have ht : c ≫ j ≫ f.hom ∣_ g.domain = b := by
    apply (cancel_mono g.domain.ι).mp
    simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hj, hb]
  simpa only [compOfDense_hom, j, Category.assoc] using congrArg (· ≫ g.hom) ht

/-- Partial maps over a common base compose over that base. -/
theorem isOver_compOfDense {S : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S}
    (f : X.PartialMap Y) (g : Y.PartialMap Z) [f.IsOver sX sY] [g.IsOver sY sZ]
    (h : Dense (f.compDomain g : Set X)) : (f.compOfDense g h).IsOver sX sZ := by
  constructor
  simp [compOfDense_hom, Category.assoc, g.over sY sZ, f.over sX sY,
    morphismRestrict_ι_assoc]

variable [IrreducibleSpace X]

/-- A lift of the first generic morphism to the second partial domain computes the
generic morphism of the composition. -/
theorem fromFunctionField_compOfDense (f : X.PartialMap Y) (g : Y.PartialMap Z)
    (h : Dense (f.compDomain g : Set X))
    (l : Spec X.functionField ⟶ g.domain.toScheme) (hl : l ≫ g.domain.ι = f.fromFunctionField) :
    (f.compOfDense g h).fromFunctionField = l ≫ g.hom := by
  let r := f.compOfDense g h
  have hη := (genericPoint_specializes _).mem_open r.domain.isOpen
    r.dense_domain.nonempty.choose_spec
  have hη' := (genericPoint_specializes _).mem_open f.domain.isOpen
    f.dense_domain.nonempty.choose_spec
  exact f.compOfDense_hom_eq g h (f.domain.fromSpecStalkOfMem _ hη') l
    (r.domain.fromSpecStalkOfMem _ hη) (by simp [r]) hl.symm

end PartialMap

namespace RationalMap

variable {X Y Z : Scheme.{u}}

local notation "η" => IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X))

section

variable [IsIntegral X] [Y.IsSeparated] [IsReduced Y] [Z.IsSeparated]

/-- The first rational map takes its generic value in the domain of the second exactly
when their maximal representatives have a common dense domain of composition. -/
theorem fromFunctionField_mem_domain_iff (f : X ⤏ Y) (g : Y ⤏ Z) :
    f.fromFunctionField η ∈ g.domain ↔
      Dense (f.toPartialMap.compDomain g.toPartialMap : Set X) := by
  have hp := f.toPartialMap.fromFunctionField_apply_closedPoint
  rw [← fromFunctionField_toRationalMap, toRationalMap_toPartialMap] at hp
  rw [hp, ← g.toPartialMap_domain]
  constructor
  · intro h
    exact (f.toPartialMap.compDomain g.toPartialMap).isOpen.dense
      ⟨genericPoint X, (PartialMap.mem_compDomain ..).mpr ⟨_, h⟩⟩
  · intro h
    have hx := (genericPoint_specializes _).mem_open
      (f.toPartialMap.compDomain g.toPartialMap).isOpen h.nonempty.choose_spec
    obtain ⟨_, hmem⟩ := (PartialMap.mem_compDomain ..).mp hx
    exact hmem

/-- Compose with a rational map defined at the generic value of the first map. -/
def compOfDefined (f : X ⤏ Y) (g : Y ⤏ Z) (h : f.fromFunctionField η ∈ g.domain) : X ⤏ Z :=
  (f.toPartialMap.compOfDense g.toPartialMap
    ((f.fromFunctionField_mem_domain_iff g).mp h)).toRationalMap

/-- Composition at a defined generic value preserves the common base. -/
theorem isOver_compOfDefined {S : Scheme.{u}} [S.IsSeparated]
    {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S}
    (f : X ⤏ Y) (g : Y ⤏ Z) [f.IsOver sX sY] [g.IsOver sY sZ]
    (h : f.fromFunctionField η ∈ g.domain) : (f.compOfDefined g h).IsOver sX sZ := by
  unfold compOfDefined
  have := f.toPartialMap.isOver_compOfDense (sY := sY) g.toPartialMap
    ((f.fromFunctionField_mem_domain_iff g).mp h) (sX := sX) (sZ := sZ)
  infer_instance

/-- The common regular open is contained in the domain of the composite. -/
theorem compDomain_le_domain_compOfDefined (f : X ⤏ Y) (g : Y ⤏ Z)
    (h : f.fromFunctionField η ∈ g.domain) :
    f.toPartialMap.compDomain g.toPartialMap ≤ (f.compOfDefined g h).domain := by
  unfold compOfDefined
  let hd := (f.fromFunctionField_mem_domain_iff g).mp h
  exact (PartialMap.compOfDense_domain _ _ hd).ge.trans (PartialMap.le_domain_toRationalMap _)

/-- Dominant precomposition satisfies the generic domain condition for every rational map. -/
theorem fromFunctionField_mem_domain_of_isDominant [Nonempty Y] (f : X ⤏ Y)
    [f.IsDominant] (g : Y ⤏ Z) : f.fromFunctionField η ∈ g.domain := by
  apply (f.fromFunctionField_mem_domain_iff g).mpr
  have : IsDominant f.toPartialMap.hom :=
    f.toPartialMap.isDominant_toRationalMap_iff.mp (by simpa)
  rw [PartialMap.compDomain_eq, ← PartialMap.comp_domain]
  exact PartialMap.dense_domain _

/-- For a dominant first map the composite agrees with Mathlib's rational composition. -/
theorem compOfDefined_eq_comp [Nonempty Y] (f : X ⤏ Y) [f.IsDominant]
    (g : Y ⤏ Z) (h : f.fromFunctionField η ∈ g.domain) :
    f.compOfDefined g h = f.comp g := by
  have : IsDominant f.toPartialMap.hom :=
    f.toPartialMap.isDominant_toRationalMap_iff.mp (by simpa)
  rw [compOfDefined, PartialMap.compOfDense_eq_comp, ← toRationalMap_comp]
  simp only [toRationalMap_toPartialMap]

/-- Compose at the generic point by lifting to the regular domain of the second map. -/
theorem fromFunctionField_compOfDefined (f : X ⤏ Y) (g : Y ⤏ Z)
    (h : f.fromFunctionField η ∈ g.domain)
    (l : Spec X.functionField ⟶ g.toPartialMap.domain.toScheme)
    (hl : l ≫ g.toPartialMap.domain.ι = f.fromFunctionField) :
    (f.compOfDefined g h).fromFunctionField = l ≫ g.toPartialMap.hom := by
  rw [compOfDefined, fromFunctionField_toRationalMap]
  apply PartialMap.fromFunctionField_compOfDense
  simpa only [← fromFunctionField_toRationalMap, toRationalMap_toPartialMap] using hl

/-- A regular representative on any open containing the generic value computes
the composite, even if the first map factors through a proper closed subscheme. -/
theorem fromFunctionField_compOfDefined_of_rep (f : X ⤏ Y) (p : Y.PartialMap Z)
    (l : Spec X.functionField ⟶ p.domain.toScheme) (hl : l ≫ p.domain.ι = f.fromFunctionField) :
    ∃ h : f.fromFunctionField η ∈ p.toRationalMap.domain,
      (f.compOfDefined p.toRationalMap h).fromFunctionField = l ≫ p.hom := by
  have hη : f.fromFunctionField η ∈ p.domain := by
    rw [← hl]
    exact (l η).property
  refine ⟨p.le_domain_toRationalMap hη, ?_⟩
  let j := Y.homOfLE (p.le_domain_toRationalMap.trans (p.toRationalMap.toPartialMap_domain).ge)
  have hj : j ≫ p.toRationalMap.toPartialMap.domain.ι = p.domain.ι :=
    homOfLE_ι _ _
  have hrep : j ≫ p.toRationalMap.toPartialMap.hom = p.hom :=
    p.toPartialMap_toRationalMap_restrict
  rw [fromFunctionField_compOfDefined f p.toRationalMap _ (l ≫ j)
      (by rw [Category.assoc, hj, hl]), Category.assoc, hrep]

/-- For a regular second map, composition at the generic point is ordinary
postcomposition by that morphism. -/
theorem compOfDefined_toRationalMap (f : X ⤏ Y) (g : Y ⟶ Z) :
    ∃ h : f.fromFunctionField η ∈ g.toRationalMap.domain,
      f.compOfDefined g.toRationalMap h = f.compHom g := by
  let p := g.toPartialMap
  let l : Spec X.functionField ⟶ p.domain.toScheme := f.fromFunctionField ≫ Y.topIso.inv
  have htop : Y.topIso.hom = p.domain.ι := (rfl)
  have hl : l ≫ p.domain.ι = f.fromFunctionField := by
    exact (congrArg (l ≫ ·) htop.symm).trans
      ((Category.assoc f.fromFunctionField Y.topIso.inv Y.topIso.hom).trans
        (by rw [Y.topIso.inv_hom_id, Category.comp_id]))
  obtain ⟨h, he⟩ := f.fromFunctionField_compOfDefined_of_rep p l hl
  refine ⟨h, eq_of_fromFunctionField_eq _ _ ?_⟩
  rw [fromFunctionField_compHom]
  have hcomp : l ≫ p.hom = f.fromFunctionField ≫ g := by
    exact (congrArg (l ≫ ·) (Hom.toPartialMap_hom g)).trans
      ((Category.assoc f.fromFunctionField Y.topIso.inv (Y.topIso.hom ≫ g)).trans
        (congrArg (f.fromFunctionField ≫ ·) (Y.topIso.inv_hom_id_assoc g)))
  exact he.trans hcomp

end

/-- An evaluation composed with the rational identity at a defined generic value is unchanged. -/
@[simp]
theorem compOfDefined_id {A : Scheme.{u}} [IsIntegral X] [IsReduced A] [A.IsSeparated]
    (a : X ⤏ A)
    (ha : a.fromFunctionField (IsLocalRing.closedPoint X.functionField) ∈ (id A).domain) :
    a.compOfDefined (id A) ha = a := by
  obtain ⟨h, he⟩ := a.compOfDefined_toRationalMap (𝟙 A)
  refine he.trans ?_
  obtain ⟨p, rfl⟩ := a.exists_rep
  rw [← compHom_toRationalMap, PartialMap.compHom_id]

section Associativity

variable {W : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  [Y.IsSeparated] [IsReduced Z] [Z.IsSeparated] [W.IsSeparated]

/-- When the first generic value lies in the domain of the second map and its image
lies in the domain of the third, either bracketing gives the same composite. -/
theorem compOfDefined_assoc (f : X ⤏ Y) (g : Y ⤏ Z) (h : Z ⤏ W)
    (hfg : f.fromFunctionField η ∈ g.domain)
    (hfgh : (f.compOfDefined g hfg).fromFunctionField η ∈ h.domain) :
    ∃ (hgh : g.fromFunctionField
        (IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y))) ∈ h.domain)
      (hf : f.fromFunctionField η ∈ (g.compOfDefined h hgh).domain),
      (f.compOfDefined g hfg).compOfDefined h hfgh =
        f.compOfDefined (g.compOfDefined h hgh) hf := by
  obtain ⟨l, hl⟩ := f.exists_lift_fromFunctionField g.toPartialMap.domain
    (by simpa only [toPartialMap_domain] using hfg)
  obtain ⟨m, hm⟩ := (f.compOfDefined g hfg).exists_lift_fromFunctionField h.toPartialMap.domain
    (by simpa only [toPartialMap_domain] using hfgh)
  have hlg : m ≫ h.toPartialMap.domain.ι = l ≫ g.toPartialMap.hom :=
    hm.trans (fromFunctionField_compOfDefined _ _ _ l hl)
  have hx : (l η).val = f.fromFunctionField η :=
    congrArg (fun q : Spec X.functionField ⟶ Y ↦ q η) hl
  have hy : (m η).val = g.toPartialMap.hom (l η) :=
    congrArg (fun q : Spec X.functionField ⟶ Z ↦ q η) hlg
  have hmem : f.fromFunctionField η ∈ g.toPartialMap.compDomain h.toPartialMap := by
    let hv := hx ▸ (l η).property
    have he : (⟨f.fromFunctionField η, hv⟩ : g.toPartialMap.domain) = l η := Subtype.ext hx.symm
    exact (PartialMap.mem_compDomain ..).mpr ⟨hv, he.symm ▸ hy ▸ (m η).property⟩
  have hd := (g.toPartialMap.compDomain h.toPartialMap).isOpen.dense ⟨_, hmem⟩
  have hgh := (g.fromFunctionField_mem_domain_iff h).mpr hd
  let p := g.toPartialMap.compOfDense h.toPartialMap hd
  obtain ⟨a, ha⟩ := f.exists_lift_fromFunctionField p.domain
    (by simpa only [p, PartialMap.compOfDense_domain] using hmem)
  obtain ⟨hf, hef⟩ := fromFunctionField_compOfDefined_of_rep f p a ha
  refine ⟨hgh, hf, eq_of_fromFunctionField_eq _ _ ?_⟩
  exact (fromFunctionField_compOfDefined _ _ _ m hm).trans
    ((g.toPartialMap.compOfDense_hom_eq h.toPartialMap hd l m a
      (ha.trans hl.symm) hlg.symm).symm.trans hef.symm)

/-- Two successive compositions at the generic point can be combined into
ordinary composition of the last two maps if the middle map is dominant. -/
theorem compOfDefined_comp (f : X ⤏ Y) (g : Y ⤏ Z) [g.IsDominant] [Nonempty Z]
    (h : Z ⤏ W) (hfg : f.fromFunctionField η ∈ g.domain)
    (hfgh : (f.compOfDefined g hfg).fromFunctionField η ∈ h.domain) :
    ∃ hk : f.fromFunctionField η ∈ (g.comp h).domain,
      (f.compOfDefined g hfg).compOfDefined h hfgh = f.compOfDefined (g.comp h) hk := by
  obtain ⟨hgh, hc, he⟩ := f.compOfDefined_assoc g h hfg hfgh
  have hg := g.compOfDefined_eq_comp h hgh
  exact ⟨hg ▸ hc, by simpa only [compOfDefined_eq_comp] using he⟩

/-- Pullback along a dominant map preserves the generic domain condition and commutes
with composition at the generic point. -/
theorem comp_compOfDefined
    (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) (h : Z ⤏ W)
    (hgh : g.fromFunctionField (IsLocalRing.closedPoint Y.functionField) ∈ h.domain) :
    ∃ hc : (f.comp g).fromFunctionField η ∈ h.domain,
      (f.comp g).compOfDefined h hc = f.comp (g.compOfDefined h hgh) := by
  let x : Spec X.functionField := η
  let y : Spec Y.functionField := IsLocalRing.closedPoint _
  let : Subsingleton (Spec Y.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Y.functionField))
  have hv : (f.comp g).fromFunctionField x = g.fromFunctionField y := by
    rw [fromFunctionField_comp, Hom.comp_apply]
    exact congrArg g.fromFunctionField (Subsingleton.elim _ _)
  have hd := f.fromFunctionField_mem_domain_of_isDominant g
  have he := f.compOfDefined_eq_comp g hd
  obtain ⟨hg, _, hz⟩ := f.compOfDefined_assoc g h hd (he.symm ▸ hv.symm ▸ hgh)
  refine ⟨hv.symm ▸ hgh, ?_⟩
  simpa only [compOfDefined_eq_comp] using hz

end Associativity

/-- The evaluation squares for two successive dominant transformations compose.
The evaluations themselves may have nondense image. The two initial domain
conditions supply the domain condition for the composite transformation. -/
theorem compOfDefined_comp_eq_of_comp_eq
    {X₀ X₁ X₂ T₀ T₁ T₂ : Scheme.{u}}
    [IsIntegral X₀] [IsIntegral X₁] [Nonempty X₂]
    [IsIntegral T₀] [IsReduced T₁] [Nonempty T₁]
    [T₀.IsSeparated] [T₁.IsSeparated] [T₂.IsSeparated] [X₁.IsSeparated]
    (e₀ : X₀ ⤏ T₀) (e₁ : X₁ ⤏ T₁) (e₂ : X₂ ⤏ T₂)
    (p : X₀ ⟶ X₁) (q : X₁ ⟶ X₂) [IsDominant p] [IsDominant q]
    (f : T₀ ⤏ T₁) (g : T₁ ⤏ T₂) [f.IsDominant]
    (h₀ : e₀.fromFunctionField (IsLocalRing.closedPoint X₀.functionField) ∈ f.domain)
    (h₁ : e₁.fromFunctionField (IsLocalRing.closedPoint X₁.functionField) ∈ g.domain)
    (hp : e₀.compOfDefined f h₀ = p.toRationalMap.comp e₁)
    (hq : e₁.compOfDefined g h₁ = q.toRationalMap.comp e₂) :
    ∃ h : e₀.fromFunctionField (IsLocalRing.closedPoint X₀.functionField) ∈ (f.comp g).domain,
      e₀.compOfDefined (f.comp g) h = (p ≫ q).toRationalMap.comp e₂ := by
  obtain ⟨h₁', he₁⟩ := p.toRationalMap.comp_compOfDefined e₁ g h₁
  have h₀₁ := hp.symm ▸ h₁'
  obtain ⟨h, he⟩ := e₀.compOfDefined_comp f g h₀ h₀₁
  refine ⟨h, he.symm.trans ?_⟩
  have hs : (e₀.compOfDefined f h₀).compOfDefined g h₀₁ =
      (p.toRationalMap.comp e₁).compOfDefined g h₁' := by
    simp only [hp]
  rw [hs, he₁, hq, ← comp_assoc]
  simp only [comp_toRationalMap, Hom.toRationalMap_compHom]

end RationalMap

end AlgebraicGeometry.Scheme
