/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Ramification
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import QPainleve.AlgebraicGeometry.Modules.FittingIdeal
import QPainleve.AlgebraicGeometry.VectorBundle.FittingIdeal
import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.Modules.Differentials.Forms
import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFree
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.Scheme.Opens
import TauCeti.RingTheory.FittingIdeal.BaseChange

/-!
# Ramification ideals in affine coordinates and under composition

A ring map presenting an affine chart of a morphism computes the ramification ideal
on that chart. This transports Tau Ceti's calculation on section rings to a
specified affine coordinate ring. For morphisms of smooth schemes of equal relative
dimension, the chain rule for the cotangent map gives the product formula for ramification
ideals.
-/

open CategoryTheory Limits AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry

universe u

/-- On a specified affine chart `Spec B` mapping into an affine open `V` of the target, the
ramification ideal is the zeroth Fitting ideal of the relative differentials of `B` over
`Γ(Y, V)`, transported to the global sections of `Spec B`. -/
public theorem ramificationIdealSheaf_comap_of_isOpenImmersion
    (R : Type u) [CommRing R] {X Y : Scheme.{u}} [X.Over (Spec (.of R))]
    [Y.Over (Spec (.of R))] (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    [(cokernel (cotangentMap R f)).IsFiniteType]
    (V : Y.affineOpens) {B : Type u} [CommRing B] [Algebra Γ(Y, V) B]
    [Module.Finite B Ω[B⁄Γ(Y, V)]]
    (j : Spec (.of B) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V) B)) ≫ V.property.fromSpec) :
    (ramificationIdealSheaf R f).comap j =
      ofIdealTop ((fittingIdeal B Ω[B⁄Γ(Y, V)] 0).map (Scheme.ΓSpecIso (.of B)).inv.hom) := by
  let U : X.affineOpens := ⟨j ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion j⟩
  have ej : ⊤ ≤ j ⁻¹ᵁ U.val := (j.preimage_image_eq _).ge
  have hpre := V.property.fromSpec_preimage_self
  have ev : ⊤ ≤ (j ≫ f) ⁻¹ᵁ V.val := by
    rw [hj, Scheme.Hom.comp_preimage, hpre, Scheme.Hom.preimage_top]
  have e : U.val ≤ f ⁻¹ᵁ V.val := by
    rintro x ⟨y, -, rfl⟩
    exact ev (TopologicalSpace.Opens.mem_top y)
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val e).hom.toAlgebra
  have := Scheme.Modules.finite_sections_of_isAffineOpen (cokernel (cotangentMap R f))
    U.val U.property
  have hf : Module.Finite Γ(X, U) Ω[Γ(X, U)⁄Γ(Y, V)] :=
    Module.Finite.equiv (cotangentCokernelSectionsEquiv R f V U e).symm
  let g := (j.appIso ⊤) ≪≫ Scheme.ΓSpecIso (.of B)
  have hcomp : f.appLE V.val U.val e ≫ g.hom =
      CommRingCat.ofHom (algebraMap Γ(Y, V) B) := by
    have hv : V.property.fromSpec.appLE V.val ⊤ hpre.ge ≫
        (Scheme.ΓSpecIso Γ(Y, V)).hom = 𝟙 _ := by
      rw [V.property.fromSpec_appLE_self, Iso.inv_hom_id]
    have hnat := Scheme.Hom.appLE_ΓSpecIso_hom_naturality V.property.fromSpec
      (CommRingCat.ofHom (algebraMap Γ(Y, V) B)) hj hpre.ge ev
    rw [hv, Category.id_comp] at hnat
    simpa only [g, Iso.trans_hom, ← Category.assoc, j.appIso_hom', ←
      Scheme.Hom.appLE_comp_appLE j f V.val U.val ⊤ e ej] using hnat
  let a : Γ(X, U) ≃ₐ[Γ(Y, V)] B :=
    AlgEquiv.ofRingEquiv (f := g.commRingCatIsoToRingEquiv) fun x ↦
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) x
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [ideal_comap_of_le _ j U ⟨⊤, isAffineOpen_top _⟩ ej,
    ramificationIdealSheaf_ideal_eq_fittingIdeal_kaehlerDifferential R f V U e]
  have ha := fittingIdeal_kaehlerDifferential_eq_map_algEquiv a 0
  have hmap : (a : Γ(X, U) →+* B) = (Scheme.ΓSpecIso (.of B)).hom.hom.comp
      (j.appLE U.val ⊤ ej).hom := by
    rw [← CommRingCat.hom_comp, ← j.appIso_hom']
    rfl
  rw [← Ideal.map_coe a, hmap, ← Ideal.map_map] at ha
  simp only [ofIdealTop_ideal, homOfLE_refl, op_id, (Spec (.of B)).presheaf.map_id,
    Ideal.map_id, CommRingCat.hom_id]
  rw [ha, Ideal.map_map, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
    Ideal.map_id]

/-- The ramification ideal is the unit ideal on an affine chart whose composite
with the morphism is an open immersion. -/
public theorem ramificationIdealSheaf_comap_eq_top_of_isOpenImmersion_comp
    (R : Type u) [CommRing R] {X Y : Scheme.{u}} [X.Over (Spec (.of R))]
    [Y.Over (Spec (.of R))] (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    [(cokernel (cotangentMap R f)).IsFiniteType] {B : Type u} [CommRing B]
    (j : Spec (.of B) ⟶ X) [IsOpenImmersion j] [IsOpenImmersion (j ≫ f)] :
    (ramificationIdealSheaf R f).comap j = ⊤ := by
  let g := j ≫ f
  let V : Y.affineOpens := ⟨g ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion g⟩
  let i := (g.appIso ⊤) ≪≫ Scheme.ΓSpecIso (.of B)
  let : Algebra Γ(Y, V) B := i.hom.hom.toAlgebra
  have hi : Function.Surjective (algebraMap Γ(Y, V) B) :=
    (ConcreteCategory.bijective_of_isIso i.hom).surjective
  have : Algebra.FormallyUnramified Γ(Y, V) B :=
    .of_surjective (Algebra.ofId _ _) hi
  have hV := IsAffineOpen.SpecMap_appLE_fromSpec g V.property (isAffineOpen_top _)
    (g.preimage_image_eq ⊤).ge
  rw [← g.appIso_hom', IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at hV
  have hg : g = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V) B)) ≫ V.property.fromSpec := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Iso.trans_hom,
      Spec.map_comp, Category.assoc, hV]
    simp
  rw [ramificationIdealSheaf_comap_of_isOpenImmersion R f V j hg,
    (fittingIdeal_zero_eq_top_iff).mpr inferInstance, Ideal.map_top]
  exact (equivOfIsAffine (X := Spec (.of B))).symm.toOrderIso.map_top

/-- Equal morphisms to a fixed scheme over the base have the same ramification ideal.
Their source structure maps can be given by different expressions. -/
public theorem ramificationIdealSheaf_congr
    (R : Type u) [CommRing R] {X Y : Scheme.{u}} [oY : Y.Over (Spec (.of R))]
    {f g : X ⟶ Y} (h : f = g)
    {oX oX' : X.Over (Spec (.of R))}
    {hf : @Scheme.Hom.IsOver X Y f (Spec (.of R)) oX oY}
    {hg : @Scheme.Hom.IsOver X Y g (Spec (.of R)) oX' oY}
    {hf' : (cokernel (@cotangentMap R _ X Y oX oY f hf)).IsFiniteType}
    {hg' : (cokernel (@cotangentMap R _ X Y oX' oY g hg)).IsFiniteType} :
    @ramificationIdealSheaf R _ X Y oX oY f hf hf' =
      @ramificationIdealSheaf R _ X Y oX' oY g hg hg' := by
  subst g
  have ho : oX = oX' := by
    cases oX
    cases oX'
    exact congrArg OverClass.ofHom (hf.comp_over.symm.trans hg.comp_over)
  subst oX'
  rfl

/-- An open immersion over the base has unit ramification ideal. -/
@[simp]
public theorem ramificationIdealSheaf_eq_top_of_isOpenImmersion
    (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of R))] [IsOpenImmersion f]
    [(cokernel (cotangentMap R f)).IsFiniteType] :
    ramificationIdealSheaf R f = ⊤ := by
  rw [ramificationIdealSheaf_eq_fittingIdeal_cokernel]
  exact Scheme.Modules.fittingIdeal_zero_eq_top_of_isZero _
    ((Preadditive.epi_iff_isZero_cokernel _).mp inferInstance)

/-- For two composable morphisms between smooth schemes of equal relative dimension, the
ramification ideal of the composite is the product of the first ramification ideal
and the inverse image of the second. -/
public theorem ramificationIdealSheaf_comp
    (R : Type u) [CommRing R] {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [Z.Over (Spec (.of R))]
    (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of R))] [g.IsOver (Spec (.of R))]
    (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of R))]
    [SmoothOfRelativeDimension n (Y ↘ Spec (.of R))]
    [SmoothOfRelativeDimension n (Z ↘ Spec (.of R))] :
    letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    letI := SmoothOfRelativeDimension.smooth n (Y ↘ Spec (.of R))
    ramificationIdealSheaf R (f ≫ g) =
      ramificationIdealSheaf R f * (ramificationIdealSheaf R g).comap f := by
  have := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  have := SmoothOfRelativeDimension.smooth n (Y ↘ Spec (.of R))
  have := SmoothOfRelativeDimension.smooth n (Z ↘ Spec (.of R))
  let E := (FiniteLocallyFreeSheaf.pullback f).obj
    ((FiniteLocallyFreeSheaf.pullback g).obj (FiniteLocallyFreeSheaf.relativeDifferentials R Z))
  let F := (FiniteLocallyFreeSheaf.pullback f).obj
    (FiniteLocallyFreeSheaf.relativeDifferentials R Y)
  let G := FiniteLocallyFreeSheaf.relativeDifferentials R X
  let e : E.obj ≅ (Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pullback g).obj (Z.relativeDifferentials R)) := eqToIso (by
    simp only [E, FiniteLocallyFreeSheaf.pullback_obj_obj,
      FiniteLocallyFreeSheaf.relativeDifferentials_obj])
  let d : F.obj ≅ (Scheme.Modules.pullback f).obj (Y.relativeDifferentials R) := eqToIso (by
    simp only [F, FiniteLocallyFreeSheaf.pullback_obj_obj,
      FiniteLocallyFreeSheaf.relativeDifferentials_obj])
  let c : G.obj ≅ X.relativeDifferentials R :=
    eqToIso (FiniteLocallyFreeSheaf.relativeDifferentials_obj R X)
  let a := e.hom ≫ (Scheme.Modules.pullback f).map (cotangentMap R g) ≫ d.inv
  let b := d.hom ≫ cotangentMap R f ≫ c.inv
  have hF (x : X) : F.rank x = n :=
    (FiniteLocallyFreeSheaf.rank_pullback_apply f _ x).trans
      (FiniteLocallyFreeSheaf.rank_relativeDifferentials_apply R n _)
  have hE (x : X) : E.rank x = n := by
    dsimp only [E]
    rw [FiniteLocallyFreeSheaf.rank_pullback_apply, FiniteLocallyFreeSheaf.rank_pullback_apply]
    exact FiniteLocallyFreeSheaf.rank_relativeDifferentials_apply R n _
  have hG (x : X) : G.rank x = n := FiniteLocallyFreeSheaf.rank_relativeDifferentials_apply R n x
  let ea := cokernel.mapIso a ((Scheme.Modules.pullback f).map (cotangentMap R g))
    e d (by simp [a])
  let eb := cokernel.mapIso b (cotangentMap R f) d c (by simp [b])
  let ecomp := cokernel.mapIso (a ≫ b) (cotangentMap R (f ≫ g))
    (e ≪≫ (Scheme.Modules.pullbackComp f g).app _) c (by
      simp [a, b, cotangentMap_comp])
  simp only [ramificationIdealSheaf_eq_fittingIdeal_cokernel]
  rw [← Scheme.Modules.fittingIdeal_zero_cokernel_comap,
    ← Scheme.Modules.fittingIdeal_congr _ ea 0, ← Scheme.Modules.fittingIdeal_congr _ eb 0,
    ← Scheme.Modules.fittingIdeal_congr _ ecomp 0]
  exact Scheme.Modules.fittingIdeal_zero_cokernel_comp a b
    (fun x ↦ (hE x).trans (hF x).symm) (fun x ↦ (hF x).trans (hG x).symm)

end TauCeti.AlgebraicGeometry
