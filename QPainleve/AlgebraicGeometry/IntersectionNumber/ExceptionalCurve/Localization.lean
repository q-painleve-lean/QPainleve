/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Comparison
public import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import QPainleve.AlgebraicGeometry.Scheme.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.Flat.StructureSheaf
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Localizing an exceptional contraction

Base change to the spectrum of the local ring at the contracted point preserves
the exceptional curve as the scheme-theoretic closed fiber and the isomorphism
off that fiber. This is the local contraction used in the
[Stacks Project, Lemma 54.16.4](https://stacks.math.columbia.edu/tag/0C2L).
-/

public section

open CategoryTheory Limits
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {p : Y} {E : X.IdealSheafData}

local notation "S" => Spec (Y.presheaf.stalk p)
local notation "s" => Y.fromSpecStalk p
local notation "a" => pullback.fst f s
local notation "g" => pullback.snd f s
local notation "I" => Hom.ker (Spec.map (Y.residue p))

namespace IdealSheafData

variable {f} in
/-- The local form of an exceptional contraction is scheme-theoretically dominant,
induces isomorphisms on sections, and has an exceptional closed fiber
of the first kind. It is an isomorphism off its closed fiber. -/
theorem IsExceptionalCurveOfFirstKind.localize_contraction
    (hE : E.IsExceptionalCurveOfFirstKind) [QuasiCompact f] [QuasiSeparated f]
    (hp : IsClosed ({p} : Set Y)) (hF : (Y.fromSpecResidueField p).ker.comap f = E)
    (hU : ((Y.fromSpecResidueField p).ker.support).compl ≤ f.isoLocus)
    (hf : ∀ V : Y.affineOpens, IsIso (f.app V)) :
    IsSchemeTheoreticallyDominant g ∧
      (∀ V : (S).Opens, IsIso ((g).app V)) ∧
      ((I).comap g).IsExceptionalCurveOfFirstKind ∧ (I).support.compl ≤ (g).isoLocus := by
  have hΓ (V : (S).Opens) : IsIso ((g).app V) := isIso_app_pullback_snd_of_flat f s hf V
  have hdom : IsSchemeTheoreticallyDominant g := by
    have : IsIso (g).appTop := hΓ ⊤
    exact (isSchemeTheoreticallyDominant_iff_appTop_injective g).mpr
      (ConcreteCategory.bijective_of_isIso (g).appTop).1
  have hI := f.comap_ker_residue_pullback_snd_fromSpecStalk hp hF
  have hcurve : (E.comap a).IsExceptionalCurveOfFirstKind := by
    have := Hom.isIso_subschemeMap_comap_pullback_fst_of_support_le f hp hF E le_rfl rfl
    exact hE.comap_of_isIso_subschemeMap a (hE.isEffectiveCartier.comap a)
  have hloc := Hom.preimage_isoLocus_le_of_isPullback (IsPullback.of_hasPullback f s).flip
  refine ⟨hdom, hΓ, hI.symm ▸ hcurve, ?_⟩
  rw [← ker_fromSpecResidueField_comap_fromSpecStalk hp, support_comap]
  exact ((s).preimage_mono hU).trans hloc

end IdealSheafData

end AlgebraicGeometry.Scheme
