/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Blowup

import TauCeti.AlgebraicGeometry.Curves.Node.FiniteEtale
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
import TauCeti.AlgebraicGeometry.Pullback.Carrier

/-!
# Morphisms of nodal conductor squares

A morphism carrying nodes to nodes induces a morphism of their reduced
singular subschemes. A compatible lift to the normalizations then induces
a morphism of the branch schemes.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A conductor branch maps to the same curve point through the normalization
and through the singular subscheme. -/
theorem blowupToBase_branchSchemeToBlowup_apply {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of k))]
    (q : X.branchScheme k) :
    (X.singularLocus k).blowupToBase (X.branchSchemeToBlowup k q) =
      (X.singularLocus k).subschemeι (X.branchSchemeToSingularLocus k q) := by
  rw [← Hom.comp_apply, ← Hom.comp_apply, branchSchemeToSingularLocus_subschemeι]

/-- The image of the branch scheme in the normalization is the inverse image of the
singular locus of the curve. -/
theorem range_branchSchemeToBlowup {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of k))] :
    Set.range (X.branchSchemeToBlowup k) =
      (X.singularLocus k).blowupToBase ⁻¹' ((X.singularLocus k).support : Set X) := by
  rw [← IdealSheafData.range_subschemeι]
  exact Scheme.Pullback.range_snd_of_isPullback (X.isPullback_branchScheme k)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

section NodeMap

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  {f : X ⟶ Y}

local notation "N[" C "]" => IdealSheafData.subscheme (singularLocus k C)
local notation "ι[" C "]" => IdealSheafData.subschemeι (singularLocus k C)

variable [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [SyntomicOfRelativeDimension 1 (Y ↘ Spec (.of k))]

/-- A morphism sending the singular support of a nodal curve into that of another
induces a map of the singular subschemes, since both are étale over the field. -/
def nodalConductorNodeMap (f : X ⟶ Y)
    (hX : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)))
    (hY : AtWorstNodalOfRelativeDimensionOne (Y ↘ Spec (.of k)))
    (h : Set.MapsTo f (X.singularLocus k).support (Y.singularLocus k).support) :
    N[X] ⟶ N[Y] := by
  have := X.etale_singularLocus_subschemeι_comp hX
  have := Y.etale_singularLocus_subschemeι_comp hY
  have : IsReduced N[X] := (ι[X] ≫ (X ↘ Spec (.of k))).isReduced_of_smooth
  have : IsReduced N[Y] := (ι[Y] ≫ (Y ↘ Spec (.of k))).isReduced_of_smooth
  refine IsClosedImmersion.lift ι[Y] (ι[X] ≫ f) ?_
  rw [IdealSheafData.ker_subschemeι, ← (IdealSheafData.isReduced_subscheme_iff_radical_eq
    (Y.singularLocus k)).mp ‹IsReduced N[Y]›, ← IdealSheafData.vanishingIdeal_support]
  apply IdealSheafData.vanishingIdeal_le_ker_of_range_subset
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact h ((X.singularLocus k).range_subschemeι.le ⟨z, rfl⟩)

/-- The map on singular subschemes commutes with the given curve morphism. -/
@[reassoc (attr := simp)]
theorem nodalConductorNodeMap_comp_subschemeι
    (hX : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)))
    (hY : AtWorstNodalOfRelativeDimensionOne (Y ↘ Spec (.of k)))
    (h : Set.MapsTo f (X.singularLocus k).support (Y.singularLocus k).support) :
    f.nodalConductorNodeMap hX hY h ≫ ι[Y] = ι[X] ≫ f :=
  IsClosedImmersion.lift_fac _ _ _

end NodeMap

section BranchMap

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] {f : X ⟶ Y}
  [Flat (X ↘ Spec (.of k))] [LocallyOfFinitePresentation (X ↘ Spec (.of k))]
  [PureRelativeDimension 1 (X ↘ Spec (.of k))]
  [Flat (Y ↘ Spec (.of k))] [LocallyOfFinitePresentation (Y ↘ Spec (.of k))]
  [PureRelativeDimension 1 (Y ↘ Spec (.of k))]

local notation "B[" C "]" => branchScheme k C
local notation "π[" C "]" => branchSchemeToSingularLocus k C
local notation "j[" C "]" => branchSchemeToBlowup k C

variable {fν : (singularLocus k X).blowup ⟶ (singularLocus k Y).blowup}
  {fN : (singularLocus k X).subscheme ⟶ (singularLocus k Y).subscheme}
  (hν : CommSq (singularLocus k X).blowupToBase fν f (singularLocus k Y).blowupToBase)
  (hN : CommSq (singularLocus k X).subschemeι fN f (singularLocus k Y).subschemeι)

/-- The induced map of branch schemes for a morphism with commuting lifts to the
normalizations and singular subschemes. -/
def nodalConductorBranchMap : B[X] ⟶ B[Y] :=
  (Y.isPullback_branchScheme k).lift (π[X] ≫ fN) (j[X] ≫ fν) (by
    simp only [Category.assoc, ← hN.w, ← hν.w, branchSchemeToSingularLocus_subschemeι_assoc])

/-- The branch map lies over the given map on the singular subschemes. -/
@[reassoc (attr := simp)]
theorem nodalConductorBranchMap_comp_toSingularLocus :
    nodalConductorBranchMap hν hN ≫ π[Y] = π[X] ≫ fN :=
  IsPullback.lift_fst _ _ _ _

/-- The branch map lies over the given map on the normalizations. -/
@[reassoc (attr := simp)]
theorem nodalConductorBranchMap_comp_toBlowup :
    nodalConductorBranchMap hν hN ≫ j[Y] = j[X] ≫ fν :=
  IsPullback.lift_snd _ _ _ _

/-- The image of a branch is determined by the image of its point on the normalization. -/
theorem nodalConductorBranchMap_apply_eq_iff (b : B[X]) (b' : B[Y]) :
    nodalConductorBranchMap hν hN b = b' ↔ fν (j[X] b) = j[Y] b' := by
  have : IsClosedImmersion j[Y] :=
    MorphismProperty.of_isPullback (Y.isPullback_branchScheme k) inferInstance
  rw [← (j[Y]).isClosedEmbedding.injective.eq_iff]
  simp only [← Scheme.Hom.comp_apply, nodalConductorBranchMap_comp_toBlowup]

end BranchMap

end AlgebraicGeometry.Scheme.Hom
