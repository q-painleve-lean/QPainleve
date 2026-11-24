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

private theorem nonempty_basis_sections_of_generatingSections {X : Scheme.{u}} {r : ℕ}
    (E : FixedRank X r) {x : X} {U V : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U)
    (hUV : U ≤ V) (s : (E.obj.obj.over V).GeneratingSections) [IsIso s.π] [Finite s.I] :
    Nonempty (Module.Basis (ULift.{u} (Fin r)) Γ(X, U)
      ((Scheme.Modules.sectionsFunctor U).obj E.obj.obj)) := by
  let t := s.restrict (homOfLE hUV)
  have : IsIso t.π := SheafOfModules.GeneratingSections.isIso_restrict_π s _
  have : Finite t.I :=
    (SheafOfModules.GeneratingSections.restrict_I s _).symm ▸ (inferInstance : Finite s.I)
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
  exact ⟨(Finsupp.basisSingleOne.map a).reindex k⟩

/-- Finitely many vector bundles admit affine frames on a common neighbourhood
of a point, contained in any prescribed open neighbourhood. -/
theorem exists_isAffineOpen_basis_sections_family_le {X : Scheme.{u}} {ι : Type*} [Finite ι]
    {r : ι → ℕ} (E : (i : ι) → FixedRank X (r i)) {x : X} {W : X.Opens} (hx : x ∈ W) :
    ∃ (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧ U ≤ W ∧
      ∀ i, Nonempty (Module.Basis (ULift.{u} (Fin (r i))) Γ(X, U)
        ((Scheme.Modules.sectionsFunctor U).obj (E i).obj.obj)) := by
  choose V hxV s hs hfin using fun i ↦ (E i).obj.exists_generatingSections x
  have hxVs : x ∈ (⨅ i, V i) := by
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxV
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⨅ i, V i) ⊓ W from ⟨hxVs, hx⟩)
  refine ⟨U, hU, hxU, hUV.trans inf_le_right, fun i ↦ ?_⟩
  have := hs i
  have := hfin i
  exact (E i).nonempty_basis_sections_of_generatingSections hU hxU
    (hUV.trans (inf_le_left.trans (iInf_le V i))) (s i)

/-- The sections of a vector bundle of fixed rank `r` on a sufficiently small
affine neighbourhood of a point have a basis indexed by `Fin r`. The neighbourhood
can be taken inside any given neighbourhood. -/
theorem exists_isAffineOpen_basis_sections_le {X : Scheme.{u}} {r : ℕ}
    (E : FixedRank X r) {x : X} {W : X.Opens} (hx : x ∈ W) :
    ∃ (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧ U ≤ W ∧
      Nonempty (Module.Basis (ULift.{u} (Fin r)) Γ(X, U)
        ((Scheme.Modules.sectionsFunctor U).obj E.obj.obj)) := by
  obtain ⟨U, hU, hxU, hUW, hb⟩ :=
    exists_isAffineOpen_basis_sections_family_le (fun _ : Unit ↦ E) hx
  exact ⟨U, hU, hxU, hUW, hb ()⟩

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank
