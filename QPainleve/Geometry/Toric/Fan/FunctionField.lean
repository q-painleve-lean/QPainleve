/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import QPainleve.Geometry.Toric.Fan.DenseTorus
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.Geometry.Toric.Algebraic.Fan.Normal

import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Finiteness

/-!
# Rational characters of a toric fan

A nonempty toric fan realizes an integral scheme, and the inclusion of its dense torus
identifies the two function fields. Each lattice character gives a rational function on the
fan scheme whose representatives on the affine cone charts are the corresponding monomials
whenever the character is nonnegative on the cone.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- Affine toric charts of toric cones have Noetherian coordinate rings. -/
theorem IsToricCone.isNoetherianRing_affineCoordinateRing (hσ : IsToricCone i σ)
    (hi : IsIntegralLattice i) :
    IsNoetherianRing (affineCoordinateRing hi σ) := by
  have : Monoid.FG (Multiplicative (dualSemigroup hi σ)) :=
    Monoid.fg_iff_add_fg.mpr (hσ.fg_dualSemigroup hi)
  exact Algebra.FiniteType.isNoetherianRing ℂ _

namespace Fan

variable (Φ : Fan i)

/-- A nonempty toric fan has integral algebraic realization. -/
instance isIntegral_algebraicRealization [Nonempty Φ.cones] :
    IsIntegral Φ.algebraicRealization := by
  apply (isIntegral_iff_irreducibleSpace_and_isReduced _).2
  refine ⟨(irreducibleSpace_def _).2 ?_, inferInstance⟩
  let j := Φ.denseTorusι inferInstance
  have hd : DenseRange j := (isDominant_denseTorusι Φ inferInstance).denseRange
  have hirr := ((IrreducibleSpace.isIrreducible_univ Φ.denseTorus).image j
    j.continuous.continuousOn).closure
  rwa [Set.image_univ, hd.closure_range] at hirr

/-- A toric fan has locally Noetherian algebraic realization. -/
instance isLocallyNoetherian_algebraicRealization : IsLocallyNoetherian Φ.algebraicRealization :=
  (isLocallyNoetherian_iff_openCover Φ.affineToricOpenCover).2 fun σ ↦ by
    let cone : Φ.cones := σ
    have := (Φ.isToricCone cone.property).isNoetherianRing_affineCoordinateRing Φ.lattice
    exact isLocallyNoetherian_Spec.2 this

variable [Nonempty Φ.cones]

/-- A lattice character, viewed as a rational function on the toric scheme via the dense torus. -/
def character : Multiplicative (N →+ ℤ) →* Φ.algebraicRealization.functionField :=
  (inv ((Φ.denseTorusι inferInstance).functionFieldMap)).hom.toMonoidHom.comp
    (((Iso.inv (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice ⊥))) ≫
      Φ.denseTorus.germToFunctionField ⊤).hom.toMonoidHom.comp (MonoidAlgebra.of ℂ _)).comp
        (denseTorusDualEquiv Φ.lattice).symm.toMultiplicative.toMonoidHom)

/-- Pulling a rational character back to the dense torus gives the corresponding monomial. -/
@[simp]
theorem functionFieldMap_character (m : Multiplicative (N →+ ℤ)) :
    (Φ.denseTorusι inferInstance).functionFieldMap (Φ.character m) =
      (Iso.inv (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice ⊥))) ≫
        Φ.denseTorus.germToFunctionField ⊤)
        (MonoidAlgebra.of ℂ _ (ofAdd ((denseTorusDualEquiv Φ.lattice).symm m.toAdd))) := by
  rw [character]
  exact IsIso.inv_hom_id_apply ((Φ.denseTorusι inferInstance).functionFieldMap) _

/-- A regular character on a cone chart is represented there by its coordinate-ring
monomial. -/
theorem functionFieldMap_affineToricChartι_character (σ : Φ.cones)
    (m : dualSemigroup Φ.lattice σ.val) :
    (Φ.affineToricChartι σ).functionFieldMap (Φ.character (ofAdd (m : N →+ ℤ))) =
      ((Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice σ.val))).inv ≫
        (Φ.affineToricChart σ).germToFunctionField ⊤) (MonoidAlgebra.of ℂ _ (ofAdd m)) := by
  let h := (Φ.isToricCone σ.property).salient.bot_isFaceOf
  let f := faceAffineToricSchemeMap Φ.lattice h
  have := isDominant_faceAffineToricSchemeMap Φ.lattice h
  apply f.functionFieldMap.hom.injective
  have hcomp : f ≫ Φ.affineToricChartι σ = Φ.denseTorusι inferInstance :=
    (Φ.denseTorusι_face σ).symm
  have hpull :
      (Φ.affineToricChartι σ).functionFieldMap ≫ f.functionFieldMap =
        (Φ.denseTorusι inferInstance).functionFieldMap := by
    rw [← Scheme.Hom.functionFieldMap_comp]
    apply (Scheme.Hom.eq_functionFieldMap_iff (Φ.denseTorusι inferInstance) _).2
    rw [Scheme.Hom.SpecMap_functionFieldMap_fromSpecStalk, hcomp]
  rw [← ConcreteCategory.comp_apply, hpull, functionFieldMap_character]
  let g := CommRingCat.ofHom (faceAffineCoordinateRingMap Φ.lattice h).toRingHom
  have hg : f = Spec.map g := faceAffineToricSchemeMap_def Φ.lattice h
  have hsections :
      (Φ.affineToricChart σ).germToFunctionField ⊤ ≫ f.functionFieldMap =
        f.appTop ≫ Φ.denseTorus.germToFunctionField ⊤ :=
    f.germToFunctionField_functionFieldMap ⊤
  have htop :
      (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice σ.val))).inv ≫ f.appTop =
        g ≫ (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice ⊥))).inv := by
    rw [hg, ← Scheme.ΓSpecIso_inv_naturality]
  rw [← ConcreteCategory.comp_apply, Category.assoc, hsections, ← Category.assoc, htop,
    Category.assoc, ConcreteCategory.comp_apply]
  simp only [ConcreteCategory.comp_apply, toAdd_ofAdd]
  have hm : g (MonoidAlgebra.of ℂ _ (ofAdd m)) =
      MonoidAlgebra.of ℂ _ (ofAdd ((denseTorusDualEquiv Φ.lattice).symm (m : N →+ ℤ))) := by
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.of_apply, denseTorusDualEquiv_symm_apply]
    exact faceAffineCoordinateRingMap_single Φ.lattice h m 1
  rw [hm]

end Fan

end TauCeti.Toric
