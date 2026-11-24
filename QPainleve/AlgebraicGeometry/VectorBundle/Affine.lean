/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.FixedRank
public import TauCeti.AlgebraicGeometry.Modules.Localization

import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Affine frames of vector bundles

Every point has an affine neighbourhood on which a fixed-rank vector bundle
has a basis of sections of the prescribed size.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank

/-- The sections of a vector bundle of fixed rank `r` on a sufficiently small
affine neighbourhood of a point have a basis indexed by `Fin r`. The neighbourhood
can be taken inside any given neighbourhood. -/
theorem exists_isAffineOpen_basis_sections_le {X : Scheme.{u}} {r : ℕ}
    (E : FixedRank X r) {x : X} {W : X.Opens} (hx : x ∈ W) :
    ∃ (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧ U ≤ W ∧
      Nonempty (Module.Basis (ULift.{u} (Fin r)) Γ(X, U)
        ((Scheme.Modules.sectionsFunctor U).obj E.obj.obj)) := by
  obtain ⟨V, hxV, s, hs, hfin⟩ := E.obj.exists_generatingSections x
  have hxVW : x ∈ V ⊓ W := ⟨hxV, hx⟩
  obtain ⟨U, hU, hxU, hUle⟩ := exists_isAffineOpen_mem_and_subset hxVW
  let t := s.restrict (homOfLE (hUle.trans inf_le_left))
  have : IsIso t.π := SheafOfModules.GeneratingSections.isIso_restrict_π s _
  have : Finite t.I := (SheafOfModules.GeneratingSections.restrict_I s _).symm ▸ hfin
  let : Fintype t.I := Fintype.ofFinite _
  have hcard : Fintype.card t.I = r := by
    rw [← Nat.card_eq_fintype_card, ← E.obj.rank_apply_eq_natCard hxU t, E.rank_apply]
  let ι := hU.isoSpec.inv
  have hι : ι ≫ U.ι = hU.fromSpec := hU.isoSpec_inv_ι
  let e := E.obj.obj.restrictIsoFreeOfOverIsoFree U (asIso t.π).symm
  let e' := ((Scheme.Modules.restrictFunctorCongr hι).symm.app E.obj.obj) ≪≫
    (Scheme.Modules.restrictFunctorComp ι U.ι).app E.obj.obj ≪≫
    (Scheme.Modules.restrictFunctor ι).mapIso e ≪≫ Scheme.Modules.restrictFreeIso ι t.I
  let eΓ := ((moduleSpecΓFunctor (R := Γ(X, U))).mapIso e' ≪≫
    moduleSpecΓFunctorFreeIso (R := Γ(X, U)) t.I).toLinearEquiv
  let a := eΓ.symm.trans (E.obj.obj.fromSpecSectionsEquiv hU).symm
  let k := (Fintype.equivFinOfCardEq hcard).trans Equiv.ulift.symm
  exact ⟨U, hU, hxU, hUle.trans inf_le_right, ⟨(Finsupp.basisSingleOne.map a).reindex k⟩⟩

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank
