/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Pullback
public import TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower.Basic
import QPainleve.RingTheory.FittingIdeal.ExteriorPower
import Mathlib.Algebra.Category.ModuleCat.Kernels
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Pullback.Quasicoherent
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic

/-!
# The Fitting ideal of the determinant of a bundle map

For a map of finite locally free sheaves of equal constant rank, the cokernel of the
top exterior power map has the same zeroth Fitting ideal sheaf as the original
cokernel. The comparison uses Tau Ceti's affine exterior power isomorphism and its
Fitting ideal base change formula. It applies over the spectrum of each local ring,
where the bundles become free.

See the Stacks Project, Sections 31.9 (tag 0C3C) and 15.120 (tag 0FJ9).
-/

public section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

local notation "extPower(" X ", " n ")" =>
  (SheafOfModules.exteriorPower (Scheme.sheaf X) n : Scheme.Modules X ⥤ Scheme.Modules X)

local notation "coker(" X ", " f ")" => @cokernel (Scheme.Modules X) _ _ _ _ f _

local notation "fit₀(" M ")" =>
  Scheme.Modules.fittingIdeal M
    (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.val U.property) 0

private theorem fittingIdeal_zero_cokernel_tilde {R : CommRingCat.{u}}
    {M N : ModuleCat.{u} R} [Module.Finite R N] (f : M ⟶ N) :
    fit₀(cokernel (tilde.map f)) =
      Scheme.IdealSheafData.ofIdealTop
        ((TauCeti.fittingIdeal R (N ⧸ LinearMap.range f.hom) 0).map
          (Scheme.ΓSpecIso R).inv.hom) := by
  let Q := ModuleCat.of R (N ⧸ LinearMap.range f.hom)
  let e := ModuleCat.cokernelIsoRangeQuotient f
  let e' : tilde Q ≅ cokernel (tilde.map f) :=
    (tilde.functor R).mapIso e.symm ≪≫ PreservesCokernel.iso (tilde.functor R) f
  have h := fittingIdeal_congr (M := tilde Q)
    (fun U ↦ finite_sections_of_isAffineOpen _ U.val U.property) e' 0
  rw [← h, fittingIdeal_Spec]
  have : Module.Finite R ((𝟭 (ModuleCat R)).obj Q) :=
    inferInstanceAs (Module.Finite R (N ⧸ LinearMap.range f.hom))
  have := Module.Finite.equiv (tilde.toTildeΓNatIso.app Q).toLinearEquiv
  exact congrArg (fun I : Ideal R ↦
    Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso R).inv.hom))
    (TauCeti.fittingIdeal_congr (tilde.toTildeΓNatIso.app Q).toLinearEquiv.symm 0)

variable {X : Scheme.{u}} {E F : FiniteLocallyFreeSheaf X} {n : ℕ}

-- Make the scheme-module instances available for objects of the sheaf exterior power functor.
local instance {M : X.Modules} [M.IsLocallyFree] [M.IsFinitePresentation] :
    (extPower(X, n).obj M).IsFiniteType := by
  let V : FiniteLocallyFreeSheaf X := ⟨M, inferInstance, inferInstance⟩
  exact FiniteLocallyFreeSheaf.exteriorPower_obj_obj n V ▸
    (inferInstance : ((FiniteLocallyFreeSheaf.exteriorPower X n).obj V).obj.IsFiniteType)

local instance {M : X.Modules} [M.IsLocallyFree] [M.IsFinitePresentation] :
    (extPower(X, n).obj M).IsQuasicoherent := by
  let V : FiniteLocallyFreeSheaf X := ⟨M, inferInstance, inferInstance⟩
  exact FiniteLocallyFreeSheaf.exteriorPower_obj_obj n V ▸
    (inferInstance : ((FiniteLocallyFreeSheaf.exteriorPower X n).obj V).obj.IsQuasicoherent)

local instance {M N : X.Modules} [M.IsLocallyFree] [M.IsFinitePresentation]
    [N.IsLocallyFree] [N.IsFinitePresentation] (f : M ⟶ N) :
    (coker(X, extPower(X, n).map f)).IsQuasicoherent :=
  isQuasicoherent_cokernel (X := X) (extPower(X, n).map f)

local instance {M N : X.Modules} [N.IsLocallyFree] [N.IsFinitePresentation] (f : M ⟶ N) :
    (coker(X, extPower(X, n).map f)).IsFiniteType :=
  isFiniteType_cokernel (X := X) (extPower(X, n).map f)

private theorem fittingIdeal_zero_cokernel_exteriorPower_of_isLocalRing
    {R : CommRingCat.{u}} [IsLocalRing R] {E F : FiniteLocallyFreeSheaf (Spec R)}
    (f : E.obj ⟶ F.obj) (hE : E.rank (IsLocalRing.closedPoint R) = n)
    (hF : F.rank (IsLocalRing.closedPoint R) = n) :
    fit₀(cokernel ((extPower((Spec R), n)).map f)) =
      fit₀(cokernel f) := by
  let Γ := moduleSpecΓFunctor (R := R)
  let ε := (tilde.adjunction (R := R)).counit
  let Λ : (Spec R).Modules ⥤ (Spec R).Modules := extPower((Spec R), n)
  let eE := @asIso _ _ _ _ E.obj.fromTildeΓ (isIso_fromTildeΓ_of_isQuasicoherent E.obj)
  let eF := @asIso _ _ _ _ F.obj.fromTildeΓ (isIso_fromTildeΓ_of_isQuasicoherent F.obj)
  let g := Γ.map f
  have hf : tilde.map g ≫ eF.hom = eE.hom ≫ f := by
    exact ε.naturality f
  let e := cokernel.mapIso (tilde.map g) f eE eF hf
  let W := tildeExteriorPowerNatIso (R := R) n
  have hW : tilde.map ((ModuleCat.exteriorPower.functor R n).map g) ≫
      (W.app (Γ.obj F.obj)).hom =
      (W.app (Γ.obj E.obj)).hom ≫ Λ.map (tilde.map g) := W.hom.naturality g
  let eΛ := cokernel.mapIso
    (tilde.map ((ModuleCat.exteriorPower.functor R n).map g)) (Λ.map f)
      (W.app (Γ.obj E.obj) ≪≫ Λ.mapIso eE) (W.app (Γ.obj F.obj) ≪≫ Λ.mapIso eF) (by
        erw [Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom, Category.assoc]
        erw [← Category.assoc (tilde.map _) _ _, hW, Category.assoc,
          ← Λ.map_comp, hf, Λ.map_comp])
  have := (E.finite_projective_moduleSpecΓ).1
  have := (F.finite_projective_moduleSpecΓ).1
  have : Module.Finite R ((ModuleCat.exteriorPower.functor R n).obj (Γ.obj F.obj)) := by
    -- The categorical exterior power is bundled from the finite exterior power module.
    exact (inferInstance : Module.Finite R (⋀[R]^n (Γ.obj F.obj)))
  have he := fittingIdeal_congr
    (fun U ↦ finite_sections_of_isAffineOpen _ U.val U.property) e 0
  have heΛ := fittingIdeal_congr
    (fun U ↦ finite_sections_of_isAffineOpen _ U.val U.property) eΛ 0
  rw [← he, ← heΛ, fittingIdeal_zero_cokernel_tilde, fittingIdeal_zero_cokernel_tilde]
  congr 2
  exact g.hom.fittingIdeal_coker_zero_exteriorPower
    ((E.finrank_moduleSpecΓ _).trans hE) ((F.finrank_moduleSpecΓ _).trans hF)

private theorem fittingIdeal_zero_cokernel_comap {Y : Scheme.{u}} (p : Y ⟶ X)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFiniteType]
    (f : M ⟶ N) :
    fit₀(cokernel ((pullback p).map f)) = (fit₀(cokernel f)).comap p :=
  (fittingIdeal_congr (fun U ↦ finite_sections_of_isAffineOpen _ U.val U.property)
    (PreservesCokernel.iso (pullback p) f).symm 0).trans (fittingIdeal_pullback p _ 0)

/-- The top exterior power of a morphism of finite locally free sheaves of the same
constant rank has the same zeroth cokernel Fitting ideal sheaf as the original morphism. -/
theorem fittingIdeal_zero_cokernel_exteriorPower (f : E.obj ⟶ F.obj)
    (hE : ∀ x, E.rank x = n) (hF : ∀ x, F.rank x = n) :
    fit₀(cokernel ((extPower(X, n)).map f)) =
      fit₀(cokernel f) := by
  suffices h : ∀ (R : Type u) [CommRing R] [IsLocalRing R] (p : Spec (.of R) ⟶ X),
      (fit₀(cokernel ((extPower(X, n)).map f))).comap p =
        (fit₀(cokernel f)).comap p from
    le_antisymm (Scheme.IdealSheafData.le_of_comap_Spec_isLocalRing fun R _ _ p ↦
      (h R p).le) (Scheme.IdealSheafData.le_of_comap_Spec_isLocalRing fun R _ _ p ↦
      (h R p).ge)
  intro R _ _ p
  let E' := (FiniteLocallyFreeSheaf.pullback p).obj E
  let F' := (FiniteLocallyFreeSheaf.pullback p).obj F
  let g : E'.obj ⟶ F'.obj :=
    eqToHom (FiniteLocallyFreeSheaf.pullback_obj_obj p E) ≫ (pullback p).map f ≫
      eqToHom (FiniteLocallyFreeSheaf.pullback_obj_obj p F).symm
  have hg : (pullback p).map f ≫ eqToHom (FiniteLocallyFreeSheaf.pullback_obj_obj p F).symm =
      eqToHom (FiniteLocallyFreeSheaf.pullback_obj_obj p E).symm ≫ g := by simp [g]
  let C := pullbackExteriorPowerComparison p n
  let Λ : (Spec (.of R)).Modules ⥤ (Spec (.of R)).Modules := extPower((Spec (.of R)), n)
  let e := cokernel.mapIso ((pullback p).map ((extPower(X, n)).map f))
    (extPower((Spec (.of R)), n).map g)
    (asIso (C.app E.obj) ≪≫ Λ.mapIso
      (eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj p E).symm))
    (asIso (C.app F.obj) ≪≫ Λ.mapIso
      (eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj p F).symm)) (by
        -- Also transport the category instances from the generic sheaf functor to scheme modules.
        erw [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, eqToIso.hom, Category.assoc,
          asIso_hom, Functor.mapIso_hom, eqToIso.hom]
        have hC : (pullback p).map (extPower(X, n).map f) ≫ C.app F.obj =
            C.app E.obj ≫ Λ.map ((pullback p).map f) := C.naturality f
        erw [← Category.assoc ((pullback p).map _) _ _, hC, Category.assoc,
          ← Λ.map_comp, hg, Λ.map_comp])
  let e' := cokernel.mapIso ((pullback p).map f) g
    (eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj p E).symm)
    (eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj p F).symm) (by simp [g])
  -- The exterior power is computed by the generic sheaf functor on the same modules.
  erw [← fittingIdeal_zero_cokernel_comap p (extPower(X, n).map f),
    ← fittingIdeal_zero_cokernel_comap p f]
  have hlocal := fittingIdeal_zero_cokernel_exteriorPower_of_isLocalRing g
    ((FiniteLocallyFreeSheaf.rank_pullback_apply p E _).trans (hE _))
    ((FiniteLocallyFreeSheaf.rank_pullback_apply p F _).trans (hF _))
  exact (fittingIdeal_congr (fun U ↦ finite_sections_of_isAffineOpen
    (coker((Spec (.of R)), Λ.map g)) U.val U.property) e.symm 0).symm.trans
      (hlocal.trans (fittingIdeal_congr
        (fun U ↦ finite_sections_of_isAffineOpen _ U.val U.property) e'.symm 0))

end

end AlgebraicGeometry.Scheme.Modules
