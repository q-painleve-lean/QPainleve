/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Pullback
public import TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower.Basic
import QPainleve.AlgebraicGeometry.Modules.FittingIdeal
import QPainleve.RingTheory.FittingIdeal.Composition
import QPainleve.RingTheory.FittingIdeal.ExteriorPower
import Mathlib.Algebra.Category.ModuleCat.Kernels
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Pullback.Quasicoherent
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic

/-!
# The Fitting ideal of the determinant of a bundle map

For a map of finite locally free sheaves of equal constant rank, the cokernel of the
top exterior power map has the same zeroth Fitting ideal sheaf as the original
cokernel. The comparison uses Tau Ceti's affine exterior power isomorphism and its
Fitting ideal base change formula. It applies over the spectrum of each local ring,
where the bundles become free. For a composition through bundles of equal rank,
this local calculation also gives the product formula for the zeroth Fitting ideal.

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

private theorem fittingIdeal_zero_cokernel_comp_of_isLocalRing
    {R : CommRingCat.{u}} [IsLocalRing R] {E F G : FiniteLocallyFreeSheaf (Spec R)}
    (f : E.obj ⟶ F.obj) (g : F.obj ⟶ G.obj)
    (hEF : E.rank (IsLocalRing.closedPoint R) = F.rank (IsLocalRing.closedPoint R))
    (hFG : F.rank (IsLocalRing.closedPoint R) = G.rank (IsLocalRing.closedPoint R)) :
    fit₀(cokernel (f ≫ g)) = fit₀(cokernel g) * fit₀(cokernel f) := by
  have := (E.finite_projective_moduleSpecΓ).1
  have := (F.finite_projective_moduleSpecΓ).1
  have := (G.finite_projective_moduleSpecΓ).1
  rw [fittingIdeal_zero_cokernel_Spec, fittingIdeal_zero_cokernel_Spec (f := g),
    fittingIdeal_zero_cokernel_Spec (f := f), ← Scheme.IdealSheafData.ofIdealTop_mul,
    ← Ideal.map_mul, Functor.map_comp, ModuleCat.hom_comp]
  congr 2
  exact LinearMap.fittingIdeal_coker_zero_comp_of_finrank_eq _ _
    ((E.finrank_moduleSpecΓ _).trans (hEF.trans (F.finrank_moduleSpecΓ _).symm))
    ((F.finrank_moduleSpecΓ _).trans (hFG.trans (G.finrank_moduleSpecΓ _).symm))

/-- For a composite of maps between finite locally free sheaves of the same rank at
each point, the zeroth Fitting ideal of the cokernel is the product of the two
zeroth cokernel Fitting ideals. -/
theorem fittingIdeal_zero_cokernel_comp {E F G : FiniteLocallyFreeSheaf X}
    (f : E.obj ⟶ F.obj) (g : F.obj ⟶ G.obj)
    (hEF : ∀ x, E.rank x = F.rank x) (hFG : ∀ x, F.rank x = G.rank x) :
    fit₀(cokernel (f ≫ g)) = fit₀(cokernel g) * fit₀(cokernel f) := by
  suffices h : ∀ (R : Type u) [CommRing R] [IsLocalRing R] (p : Spec (.of R) ⟶ X),
      (fit₀(cokernel (f ≫ g))).comap p = (fit₀(cokernel g) * fit₀(cokernel f)).comap p from
    le_antisymm (Scheme.IdealSheafData.le_of_comap_Spec_isLocalRing fun R _ _ p ↦ (h R p).le)
      (Scheme.IdealSheafData.le_of_comap_Spec_isLocalRing fun R _ _ p ↦ (h R p).ge)
  intro R _ _ p
  let P := FiniteLocallyFreeSheaf.pullback p
  let Q := pullback p
  let e (V : FiniteLocallyFreeSheaf X) : (P.obj V).obj ≅ Q.obj V.obj :=
    eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj p V)
  let f' := (e E).hom ≫ Q.map f ≫ (e F).inv
  let g' := (e F).hom ≫ Q.map g ≫ (e G).inv
  have hrank (V : FiniteLocallyFreeSheaf X) (x : Spec (.of R)) :
      (P.obj V).rank x = V.rank (p x) := FiniteLocallyFreeSheaf.rank_pullback_apply p V x
  have hlocal := fittingIdeal_zero_cokernel_comp_of_isLocalRing f' g'
    ((hrank E _).trans ((hEF _).trans (hrank F _).symm))
    ((hrank F _).trans ((hFG _).trans (hrank G _).symm))
  let ef := cokernel.mapIso f' (Q.map f) (e E) (e F) (by simp [f'])
  let eg := cokernel.mapIso g' (Q.map g) (e F) (e G) (by simp [g'])
  let efg := cokernel.mapIso (f' ≫ g') (Q.map (f ≫ g)) (e E) (e G) (by simp [f', g', Q])
  rw [Scheme.IdealSheafData.comap_mul, ← fittingIdeal_zero_cokernel_comap,
    ← fittingIdeal_zero_cokernel_comap, ← fittingIdeal_zero_cokernel_comap]
  rw [← fittingIdeal_congr _ efg 0, ← fittingIdeal_congr _ ef 0, ← fittingIdeal_congr _ eg 0]
  exact hlocal

end

end AlgebraicGeometry.Scheme.Modules
