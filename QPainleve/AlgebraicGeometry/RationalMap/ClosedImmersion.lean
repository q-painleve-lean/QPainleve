/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.Composition
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Domains of rational maps under closed immersions

Postcomposing a rational map from a reduced scheme with a closed immersion preserves
its domain of definition. More precisely, every partial representative of the
composite factors uniquely through the original target and represents the original
map. Thus an everywhere-defined representative obtained in a projective embedding
gives an everywhere-defined representative into the closed target.

The proof uses the invariance of the scheme-theoretic image under dense open
restriction and Mathlib's universal property `IsClosedImmersion.lift`.
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

namespace RationalMap

variable [IsReduced X] (f : X ⤏ Y) (i : Y ⟶ Z) [IsClosedImmersion i]

/-- A partial representative of the composite with a closed immersion lifts uniquely on
its whole domain to a representative of the original rational map. -/
theorem existsUnique_partialMap_of_toRationalMap_eq_compHom
    (r : X.PartialMap Z) (hr : r.toRationalMap = f.compHom i) :
    ∃! q : X.PartialMap Y, q.compHom i = r ∧ q.toRationalMap = f := by
  have hker := f.ker_le_of_toRationalMap_eq_compHom i r hr
  let q : X.PartialMap Y :=
    ⟨r.domain, r.dense_domain, IsClosedImmersion.lift i r.hom hker⟩
  have hdom : (q.compHom i).domain = r.domain := rfl
  have hid : (X.isoOfEq hdom).hom = 𝟙 r.domain.toScheme :=
    congrArg Iso.hom (X.isoOfEq_rfl r.domain)
  have hq : q.compHom i = r := PartialMap.ext _ _ hdom <|
    (IsClosedImmersion.lift_fac i r.hom hker).trans
      ((Category.id_comp r.hom).symm.trans (congrArg (· ≫ r.hom) hid.symm))
  have hqf : q.toRationalMap = f :=
    i.rationalMap_compHom_injective ((compHom_toRationalMap q i).symm.trans
      ((congrArg PartialMap.toRationalMap hq).trans hr))
  exact ⟨q, ⟨hq, hqf⟩, fun q' hq' ↦ i.partialMap_compHom_injective (hq'.1.trans hq.symm)⟩

/-- Postcomposition with a closed immersion preserves the domain of definition. -/
@[simp]
theorem domain_compHom_of_isClosedImmersion : (f.compHom i).domain = f.domain := by
  apply le_antisymm
  · intro x hx
    obtain ⟨r, hxr, hr⟩ := mem_domain.mp hx
    obtain ⟨q, ⟨hq, hqf⟩, _⟩ := f.existsUnique_partialMap_of_toRationalMap_eq_compHom i r hr
    have hd : q.domain = r.domain := congrArg PartialMap.domain hq
    exact mem_domain.mpr ⟨q, hd.symm ▸ hxr, hqf⟩
  · exact f.domain_le_domain_compHom i

/-- If the composite through a closed immersion is represented by a morphism, the original
rational map is represented by the unique morphism lifting that representative. -/
theorem existsUnique_hom_of_toRationalMap_eq_compHom
    (g : X ⟶ Z) (hg : g.toRationalMap = f.compHom i) :
    ∃! h : X ⟶ Y, h ≫ i = g ∧ h.toRationalMap = f := by
  have hk := f.ker_le_of_toRationalMap_eq_compHom i g.toPartialMap hg
  have hk' : g.toPartialMap.hom.ker = g.ker :=
    (congrArg Hom.ker (Hom.toPartialMap_hom g)).trans (Hom.ker_comp_of_isIso X.topIso.hom g)
  let h := IsClosedImmersion.lift i g (hk.trans_eq hk')
  have hf : h ≫ i = g := IsClosedImmersion.lift_fac _ _ _
  have hmap : h.toRationalMap.compHom i = f.compHom i := by
    rw [Hom.toRationalMap_compHom, hf, hg]
  exact ⟨h, ⟨hf, i.rationalMap_compHom_injective hmap⟩,
    fun h' hh' ↦ (cancel_mono i).mp (hh'.1.trans hf.symm)⟩

end RationalMap

end AlgebraicGeometry.Scheme
