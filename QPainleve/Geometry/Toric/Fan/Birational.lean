/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.PartialIso
public import QPainleve.Geometry.Toric.Fan.Subdivision.FunctionField

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.AlgebraicGeometry.RationalMap.Restriction

/-!
# Birational changes between toric fans on the same lattice

The common dense torus gives a specified partial isomorphism between the realizations
of two nonempty fans. Its rational map composes by changing the target fan, and for a
subdivision it agrees with the toric projection.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti.Toric.Fan

universe u

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}
  (Φ Ψ : Fan i) [Nonempty Φ.cones] [Nonempty Ψ.cones]

local notation "zeroCone[" A "]" =>
  Subtype.mk ⊥ (Fan.bot_mem A (Subtype.property (Nonempty.some (α := (Fan.cones A)) inferInstance)))
local notation "j[" A "]" => Fan.affineChartι R A zeroCone[A]
local notation "X[" A "]" => Fan.finiteFanScheme R A
local notation "s[" A "]" => Fan.finiteFanSchemeToSpec R A

/-- The partial isomorphism identifying the dense torus in the realizations of two
nonempty fans in the same lattice. -/
def denseTorusPartialIso : X[Φ].PartialIso X[Ψ] where
  source := j[Φ].opensRange
  dense_source := j[Φ].denseRange
  target := j[Ψ].opensRange
  dense_target := j[Ψ].denseRange
  iso := j[Φ].isoOpensRange.symm ≪≫ j[Ψ].isoOpensRange

/-- The source open of the toric change is the dense torus. -/
@[simp]
theorem denseTorusPartialIso_source :
    (Φ.denseTorusPartialIso R Ψ).source = j[Φ].opensRange := (rfl)

/-- The target open of the toric change is the dense torus. -/
@[simp]
theorem denseTorusPartialIso_target :
    (Φ.denseTorusPartialIso R Ψ).target = j[Ψ].opensRange := (rfl)

/-- Reversing the toric change interchanges the two open tori. -/
@[simp]
theorem denseTorusPartialIso_symm :
    (Φ.denseTorusPartialIso R Ψ).symm = Ψ.denseTorusPartialIso R Φ := by
  apply Scheme.PartialIso.ext _ _ rfl rfl
  simp only [Scheme.isoOfEq_rfl, Iso.refl_trans, Iso.trans_refl]

section RationalMap

variable [IsDomain R]

/-- Precomposing the toric birational map with the source torus inclusion gives the
target torus inclusion. -/
@[simp]
theorem affineChartι_bot_comp_denseTorusPartialIso :
    j[Φ].toRationalMap.comp (Φ.denseTorusPartialIso R Ψ).toRationalMap =
      j[Ψ].toRationalMap := by
  let p := (Φ.denseTorusPartialIso R Ψ).toPartialMap
  let e : affineChart R Φ.lattice (⊥ : PointedCone ℝ V) ≅ p.domain.toScheme := j[Φ].isoOpensRange
  let : Nonempty p.domain := Set.nonempty_coe_sort.mpr p.dense_domain.nonempty
  let : IsIntegral p.domain.toScheme := isIntegral_of_isOpenImmersion p.domain.ι
  let : IsDominant p.domain.ι := Opens.isDominant_ι p.dense_domain
  have hj : e.hom ≫ p.domain.ι = j[Φ] := j[Φ].isoOpensRange_hom_ι
  have : IsDominant (e.hom ≫ p.domain.ι) := hj.symm ▸ inferInstanceAs (IsDominant j[Φ])
  have hp : e.hom ≫ p.hom = j[Ψ] := by
    simp [e, p, Scheme.PartialIso.toPartialMap, denseTorusPartialIso]
  calc
    _ = (e.hom ≫ p.domain.ι).toRationalMap.comp p.toRationalMap := by simp only [hj, p]
    _ = e.hom.toRationalMap.comp (p.domain.ι.toRationalMap.comp p.toRationalMap) := by
      rw [← Scheme.RationalMap.comp_assoc]
      simp only [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
    _ = _ := by
      rw [← p.hom_toRationalMap_eq_comp, Scheme.RationalMap.comp_toRationalMap,
        Scheme.Hom.toRationalMap_compHom, hp]

variable {Φ Ψ}

/-- The identity on the common torus determines a rational map between the two fan schemes. -/
theorem eq_denseTorusPartialIso_toRationalMap {f : X[Φ] ⤏ X[Ψ]}
    (hf : j[Φ].toRationalMap.comp f = j[Ψ].toRationalMap) :
    f = (Φ.denseTorusPartialIso R Ψ).toRationalMap :=
  j[Φ].toRationalMap.comp_left_injective
    (hf.trans (Φ.affineChartι_bot_comp_denseTorusPartialIso R Ψ).symm)

/-- A toric subdivision realizes the same-lattice birational change by a morphism. -/
@[simp]
theorem IsSubdivision.toRationalMap_finiteFanSchemeHom (h : Φ.IsSubdivision Ψ) :
    (h.toFanHom.finiteFanSchemeHom R).toRationalMap =
      (Φ.denseTorusPartialIso R Ψ).toRationalMap := by
  apply eq_denseTorusPartialIso_toRationalMap
  rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom,
    h.affineChartι_comp_finiteFanSchemeHom R]

/-- The composite of two toric changes is the toric change between their outer endpoints. -/
@[simp]
theorem denseTorusPartialIso_toRationalMap_comp {Ω : Fan i} [Nonempty Ω.cones] :
    (Φ.denseTorusPartialIso R Ψ).toRationalMap.comp (Ψ.denseTorusPartialIso R Ω).toRationalMap =
      (Φ.denseTorusPartialIso R Ω).toRationalMap := by
  apply eq_denseTorusPartialIso_toRationalMap
  rw [← Scheme.RationalMap.comp_assoc]
  simp only [affineChartι_bot_comp_denseTorusPartialIso]

/-- Changing a fan to itself induces the identity rational map. -/
@[simp]
theorem denseTorusPartialIso_self_toRationalMap :
    (Φ.denseTorusPartialIso R Φ).toRationalMap = Scheme.RationalMap.id X[Φ] := by
  simpa using ((IsSubdivision.refl Φ).toRationalMap_finiteFanSchemeHom R).symm

/-- On a common subdivision, postcomposing either projection with the corresponding
toric change gives the other projection. This holds after any dominant morphism
from a preirreducible source to the common subdivision. -/
theorem IsSubdivision.comp_denseTorusPartialIso {Ω : Fan i} [Nonempty Ω.cones]
    (h : Ω.IsSubdivision Φ) (k : Ω.IsSubdivision Ψ) {Z : Scheme.{u}}
    [PreirreducibleSpace Z] (g : Z ⟶ X[Ω]) [IsDominant g] :
    (g ≫ h.toFanHom.finiteFanSchemeHom R).toRationalMap.comp
        (Φ.denseTorusPartialIso R Ψ).toRationalMap =
      (g ≫ k.toFanHom.finiteFanSchemeHom R).toRationalMap := by
  calc
    _ = g.toRationalMap.comp
        ((h.toFanHom.finiteFanSchemeHom R).toRationalMap.comp
          (Φ.denseTorusPartialIso R Ψ).toRationalMap) := by
      rw [← Scheme.RationalMap.comp_assoc]
      simp only [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
    _ = g.toRationalMap.comp (Ω.denseTorusPartialIso R Ψ).toRationalMap := by
      simp only [h.toRationalMap_finiteFanSchemeHom R, denseTorusPartialIso_toRationalMap_comp]
    _ = _ := by
      rw [← k.toRationalMap_finiteFanSchemeHom R, Scheme.RationalMap.comp_toRationalMap,
        Scheme.Hom.toRationalMap_compHom]

end RationalMap

/-- The toric change is defined over the coefficient ring. -/
theorem denseTorusPartialIso_isOver :
    (Φ.denseTorusPartialIso R Ψ).IsOver s[Φ] s[Ψ] := by
  apply (cancel_epi j[Φ].isoOpensRange.hom).mp
  simp only [denseTorusPartialIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, Category.assoc]
  rw [Φ.affineChartι_finiteFanSchemeToSpec R, Ψ.affineChartι_finiteFanSchemeToSpec R]

/-- The partial map of the toric change is defined over the coefficient ring. -/
instance : (Φ.denseTorusPartialIso R Ψ).toPartialMap.IsOver s[Φ] s[Ψ] :=
  ⟨Φ.denseTorusPartialIso_isOver R Ψ⟩

end TauCeti.Toric.Fan
