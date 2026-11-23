/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Postcomposition of partial and rational maps

Postcomposition with a monomorphism of schemes is injective on both partial maps
and rational maps. Postcomposition can enlarge the domain of definition. On a
reduced source, the kernel of the postcomposing morphism is contained in the
kernel of every representative of the composite.
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

namespace Hom

/-- The rational map of a composite of morphisms is the postcomposition of the
rational map of the first morphism by the second morphism. -/
@[simp]
theorem toRationalMap_compHom (f : X ⟶ Y) (i : Y ⟶ Z) :
    f.toRationalMap.compHom i = (f ≫ i).toRationalMap :=
  (RationalMap.compHom_toRationalMap f.toPartialMap i).symm.trans
    (congrArg PartialMap.toRationalMap (f.toPartialMap_compHom i))

/-- Postcomposition by a monomorphism is injective on partial maps. -/
theorem partialMap_compHom_injective (i : Y ⟶ Z) [Mono i] :
    Function.Injective (fun p : X.PartialMap Y ↦ p.compHom i) := by
  intro p q e
  obtain ⟨h, hh⟩ := (PartialMap.ext_iff _ _).mp e
  have hh' : p.hom ≫ i = (X.isoOfEq h).hom ≫ q.hom ≫ i := hh
  exact PartialMap.ext p q h ((cancel_mono i).mp
    (hh'.trans (Category.assoc _ _ _).symm))

/-- Postcomposition by a monomorphism is injective on rational maps. -/
theorem rationalMap_compHom_injective (i : Y ⟶ Z) [Mono i] :
    Function.Injective (fun f : X ⤏ Y ↦ f.compHom i) := by
  intro f g he
  obtain ⟨p, rfl⟩ := f.exists_rep
  obtain ⟨q, rfl⟩ := g.exists_rep
  dsimp only at he
  rw [← RationalMap.compHom_toRationalMap, ← RationalMap.compHom_toRationalMap] at he
  obtain ⟨W, hW, hWp, hWq, e⟩ := PartialMap.toRationalMap_eq_iff.mp he
  apply PartialMap.toRationalMap_eq_iff.mpr
  refine ⟨W, hW, hWp, hWq, ?_⟩
  apply (cancel_mono i).mp
  have h : X.homOfLE hWp ≫ p.hom ≫ i = X.homOfLE hWq ≫ q.hom ≫ i := e
  exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)

end Hom

namespace RationalMap

/-- Postcomposition by a morphism commutes with precomposition by a dominant rational map. -/
theorem comp_compHom {W : Scheme.{u}} [PreirreducibleSpace W] [Nonempty X]
    (g : W ⤏ X) [g.IsDominant] (f : X ⤏ Y) (i : Y ⟶ Z) :
    g.comp (f.compHom i) = (g.comp f).compHom i := by
  obtain ⟨p, rfl⟩ := f.exists_rep
  rw [← compHom_toRationalMap, comp_def, comp_def, ← compHom_toRationalMap]
  apply congrArg PartialMap.toRationalMap
  have hdom : (g.representative.comp (p.compHom i)).domain =
      ((g.representative.comp p).compHom i).domain := rfl
  have hid : (W.isoOfEq hdom).hom = 𝟙 _ :=
    congrArg Iso.hom (W.isoOfEq_rfl (g.representative.comp (p.compHom i)).domain)
  apply PartialMap.ext _ _ hdom
  have he := Category.id_comp ((g.representative.comp p).compHom i).hom
  rw [hid]
  refine Eq.trans ?_ he.symm
  simp only [PartialMap.comp_hom, PartialMap.compHom_hom]
  -- The two domains use the same preimage, so their restriction maps coincide.
  let a := (g.representative.domain.ι.isoImage (g.representative.hom ⁻¹ᵁ p.domain)).inv
  let b := g.representative.hom ∣_ p.domain
  exact (congrArg (a ≫ ·) (Category.assoc b p.hom i).symm).trans
    (Category.assoc a (b ≫ p.hom) i).symm

variable (f : X ⤏ Y) (i : Y ⟶ Z)

/-- Postcomposition by a morphism is defined at every point where the rational map is defined. -/
theorem domain_le_domain_compHom : f.domain ≤ (f.compHom i).domain := by
  intro x hx
  obtain ⟨q, hxq, hq⟩ := mem_domain.mp hx
  have hr := (compHom_toRationalMap q i).trans (congrArg (·.compHom i) hq)
  exact mem_domain.mpr ⟨q.compHom i, hxq, hr⟩

variable [IsReduced X]

/-- Every representative of the postcomposition annihilates the kernel of the
postcomposing morphism on its entire domain. -/
theorem ker_le_of_toRationalMap_eq_compHom (r : X.PartialMap Z)
    (hr : r.toRationalMap = f.compHom i) : i.ker ≤ r.hom.ker := by
  obtain ⟨p, hp⟩ := f.exists_rep
  have hr' : r.toRationalMap = (p.compHom i).toRationalMap := by
    rw [compHom_toRationalMap, hp]
    exact hr
  obtain ⟨W, hW, hWr, hWp, e⟩ := PartialMap.toRationalMap_eq_iff.mp hr'
  have he : X.homOfLE hWr ≫ r.hom = X.homOfLE hWp ≫ p.hom ≫ i := e
  have : IsDominant (X.homOfLE hWr) := Opens.isDominant_homOfLE hW hWr
  have : IsSchemeTheoreticallyDominant (X.homOfLE hWr) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  calc
    i.ker ≤ ((X.homOfLE hWp ≫ p.hom) ≫ i).ker := Hom.le_ker_comp _ _
    _ = (X.homOfLE hWr ≫ r.hom).ker := congrArg Hom.ker
      ((Category.assoc _ _ _).trans he.symm)
    _ = r.hom.ker := (X.homOfLE hWr).ker_comp_of_isSchemeTheoreticallyDominant _

end RationalMap

end AlgebraicGeometry.Scheme
