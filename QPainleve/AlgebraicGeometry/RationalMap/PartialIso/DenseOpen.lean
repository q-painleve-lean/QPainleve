/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.PartialIso
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.AlgebraicGeometry.RationalMap.FunctionField
import QPainleve.AlgebraicGeometry.RationalMap.Restriction

/-!
# Birational comparison through a common dense open

Two dominant open immersions of a scheme identify the corresponding dense opens in their
targets. For integral schemes this comparison determines their rational maps.
-/

public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.PartialIso

universe u

variable {U X Y Z S : Scheme.{u}}
  (f : U ⟶ X) (g : U ⟶ Y)
  [IsOpenImmersion f] [IsDominant f] [IsOpenImmersion g] [IsDominant g]

/-- Two dominant open immersions from the same scheme identify their images. -/
def ofDenseOpenImmersions : X.PartialIso Y where
  source := f.opensRange
  dense_source := f.denseRange
  target := g.opensRange
  dense_target := g.denseRange
  iso := f.isoOpensRange.symm ≪≫ g.isoOpensRange

/-- The source is the image of the first immersion. -/
@[simp]
theorem ofDenseOpenImmersions_source :
    (ofDenseOpenImmersions f g).source = f.opensRange := (rfl)

/-- The target is the image of the second immersion. -/
@[simp]
theorem ofDenseOpenImmersions_target :
    (ofDenseOpenImmersions f g).target = g.opensRange := (rfl)

/-- Reversing the comparison exchanges the immersions. -/
@[simp]
theorem ofDenseOpenImmersions_symm :
    (ofDenseOpenImmersions f g).symm = ofDenseOpenImmersions g f := by
  apply Scheme.PartialIso.ext _ _ rfl rfl
  simp only [Scheme.isoOfEq_rfl, Iso.refl_trans, Iso.trans_refl]

/-- The comparison preserves the maps to a base when they agree on the common open. -/
theorem ofDenseOpenImmersions_isOver {sX : X ⟶ S} {sY : Y ⟶ S}
    (h : f ≫ sX = g ≫ sY) : (ofDenseOpenImmersions f g).IsOver sX sY := by
  apply (cancel_epi f.isoOpensRange.hom).mp
  simp only [ofDenseOpenImmersions, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, Category.assoc]
  exact h.symm

variable [IsIntegral U] [IsIntegral X]

/-- The comparison restricts to the second immersion on the common open. -/
@[simp]
theorem toRationalMap_comp_ofDenseOpenImmersions :
    f.toRationalMap.comp (ofDenseOpenImmersions f g).toRationalMap = g.toRationalMap := by
  let p := (ofDenseOpenImmersions f g).toPartialMap
  let e : U ≅ p.domain.toScheme := f.isoOpensRange
  let : Nonempty p.domain := Set.nonempty_coe_sort.mpr p.dense_domain.nonempty
  let : IsIntegral p.domain.toScheme := isIntegral_of_isOpenImmersion p.domain.ι
  let : IsDominant p.domain.ι := Opens.isDominant_ι p.dense_domain
  have hj : e.hom ≫ p.domain.ι = f := f.isoOpensRange_hom_ι
  have : IsDominant (e.hom ≫ p.domain.ι) := hj.symm ▸ inferInstanceAs (IsDominant f)
  have hp : e.hom ≫ p.hom = g := by
    simp [e, p, Scheme.PartialIso.toPartialMap, ofDenseOpenImmersions]
  calc
    _ = (e.hom ≫ p.domain.ι).toRationalMap.comp p.toRationalMap := by simp only [hj, p]
    _ = e.hom.toRationalMap.comp (p.domain.ι.toRationalMap.comp p.toRationalMap) := by
      rw [← Scheme.RationalMap.comp_assoc]
      simp only [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
    _ = _ := by
      rw [← p.hom_toRationalMap_eq_comp, Scheme.RationalMap.comp_toRationalMap,
        Scheme.Hom.toRationalMap_compHom, hp]

/-- A rational map from an integral scheme is determined by its restriction to the common open. -/
theorem eq_toRationalMap_of_comp_ofDenseOpenImmersions {φ : X ⤏ Y}
    (hφ : f.toRationalMap.comp φ = g.toRationalMap) :
    φ = (ofDenseOpenImmersions f g).toRationalMap :=
  f.toRationalMap.comp_left_injective (hφ.trans
    (toRationalMap_comp_ofDenseOpenImmersions f g).symm)

/-- Comparing an immersion with itself gives the identity rational map. -/
@[simp]
theorem ofDenseOpenImmersions_toRationalMap_self :
    (ofDenseOpenImmersions f f).toRationalMap = Scheme.RationalMap.id X := by
  symm
  exact eq_toRationalMap_of_comp_ofDenseOpenImmersions f f (Scheme.RationalMap.comp_id _)

variable [IsIntegral Y]
  (h : U ⟶ Z) [IsOpenImmersion h] [IsDominant h]

/-- The comparisons through a common open compose. -/
@[simp]
theorem ofDenseOpenImmersions_toRationalMap_comp :
    (ofDenseOpenImmersions f g).toRationalMap.comp (ofDenseOpenImmersions g h).toRationalMap =
      (ofDenseOpenImmersions f h).toRationalMap := by
  apply eq_toRationalMap_of_comp_ofDenseOpenImmersions
  rw [← Scheme.RationalMap.comp_assoc]
  simp only [toRationalMap_comp_ofDenseOpenImmersions]

end AlgebraicGeometry.Scheme.PartialIso
