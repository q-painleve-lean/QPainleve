/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Isomorphism
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Units
public import QPainleve.AlgebraicGeometry.LineBundle.GluingUnit

import Mathlib.Algebra.BigOperators.Finprod

/-!
# Naturality of nodal gluing scalars

An isomorphism of nodal curves pulls a gluing unit back along the induced isomorphism
of branch schemes. At each node its scalar is preserved or inverted according to the
order in which the two branches map. On a nodal cycle, this gives the transformation
law for the product used to compute the period of a multidegree-zero line bundle.
See [Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Lemma 2.1](https://arxiv.org/pdf/1211.6367#page=6).
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory Scheme.Modules
open TauCeti.AlgebraicGeometry

universe u

namespace CategoryTheory.Iso

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] (e : X ≅ Y) [e.hom.IsOver (Spec (.of k))]

local notation "ν[" C "]" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus k C)
local notation "ι[" C "]" => Scheme.IdealSheafData.subschemeι (Scheme.singularLocus k C)
local notation "B[" C "]" => Scheme.branchScheme k C
local notation "N[" C "]" => Scheme.IdealSheafData.subscheme (Scheme.singularLocus k C)
local notation "nodeIso" => Iso.hom (singularLocusIso (R := k) e)
local notation "branchIso" => Iso.hom (branchSchemeIso (R := k) e)
local notation "conductorSq[" C "]" =>
  IsPullback.toCommSq (IsPullback.flip (Scheme.isPullback_branchScheme k C))

local notation "normalizationSq" =>
  CommSq.mk (Eq.symm (singularLocusBlowupIso_hom_blowupToBase (R := k) e))
local notation "singularLocusSq" =>
  CommSq.mk (Eq.symm (singularLocusIso_hom_subschemeι (R := k) e))

local notation "branchPullback" =>
  Units.map (CommRingCat.Hom.hom (Scheme.Hom.appTop branchIso))

section RelativeCurves

variable [Flat (X ↘ Spec (.of k))] [LocallyOfFinitePresentation (X ↘ Spec (.of k))]
  [PureRelativeDimension 1 (X ↘ Spec (.of k))]
  [Flat (Y ↘ Spec (.of k))] [LocallyOfFinitePresentation (Y ↘ Spec (.of k))]
  [PureRelativeDimension 1 (Y ↘ Spec (.of k))]

/-- An isomorphism of curves pulls a Picard class trivialized by the singular-locus
blowup back to a class trivialized by the corresponding blowup. -/
theorem pullback_mem_ker_pullback_blowupToBase_singularLocus
    (a : (LineBundleClass.pullbackHom (ν[Y])).ker) :
    LineBundleClass.pullback e.hom a.val ∈ (LineBundleClass.pullbackHom (ν[X])).ker := by
  have ha : LineBundleClass.pullback (ν[Y]) a.val = 1 := by
    simpa only [LineBundleClass.pullbackHom_apply] using MonoidHom.mem_ker.mp a.property
  rw [MonoidHom.mem_ker, LineBundleClass.pullbackHom_apply, LineBundleClass.pullback_comp,
    ← e.singularLocusBlowupIso_hom_blowupToBase (R := k), ← LineBundleClass.pullback_comp, ha,
    LineBundleClass.pullback_one]

/-- With the induced trivializations on the blowup and singular subscheme, the gluing unit
pulls back along the induced isomorphism of branch schemes. -/
@[simp]
theorem lineGluingUnit_pullback {M : Y.Modules}
    (t : (pullback (ν[Y])).obj M ≅ 𝟙_ _) (d : (pullback (ι[Y])).obj M ≅ 𝟙_ _) :
    (conductorSq[X]).lineGluingUnit
        ((normalizationSq).pullbackTrivialization t) ((singularLocusSq).pullbackTrivialization d) =
      branchPullback ((conductorSq[Y]).lineGluingUnit t d) :=
  (conductorSq[Y]).lineGluingUnit_pullback (conductorSq[X]) normalizationSq singularLocusSq
    ⟨(e.branchSchemeIso_hom_branchSchemeToBlowup (R := k)).symm⟩
    ⟨(e.branchSchemeIso_hom_branchSchemeToSingularLocus (R := k)).symm⟩ t d

end RelativeCurves

variable [IsSepClosed k] [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [SyntomicOfRelativeDimension 1 (Y ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
  (hX : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)))
  (hY : AtWorstNodalOfRelativeDimensionOne (Y ↘ Spec (.of k)))

/-- The ratio at a node after pullback is the ratio at its image, inverted if the
isomorphism exchanges the two ordered branches there. -/
theorem branchRatioHom_appTop
    (orderX : ∀ z : (X.singularLocus k).subscheme,
      Fin 2 ≃ {q : X.branchScheme k // X.branchSchemeToSingularLocus k q = z})
    (orderY : ∀ z : (Y.singularLocus k).subscheme,
      Fin 2 ≃ {q : Y.branchScheme k // Y.branchSchemeToSingularLocus k q = z})
    (a : Γ(B[Y], ⊤)ˣ) (z : N[X]) (swap : Bool)
    (horder : ∀ i : Fin 2,
      branchIso (orderX z i).val = (orderY (nodeIso z) (if swap then i.rev else i)).val) :
    X.branchRatioHom (k := k) hX orderX (branchPullback a) z =
      if swap then (Y.branchRatioHom (k := k) hY orderY a (nodeIso z))⁻¹ else
        Y.branchRatioHom (k := k) hY orderY a (nodeIso z) := by
  have hvalue (q : B[X]) :
      X.branchSchemeGlobalUnitsEquiv hX (branchPullback a) q =
        Y.branchSchemeGlobalUnitsEquiv hY a (branchIso q) :=
    X.branchSchemeGlobalUnitsEquiv_appTop_of_comp hX hY branchIso (by simp) a q
  simp only [Scheme.branchRatioHom_apply, hvalue, horder]
  cases swap
  · simp only [Bool.false_eq_true, ite_false]
  · have h₀ : (0 : Fin 2).rev = 1 := rfl
    have h₁ : (1 : Fin 2).rev = 0 := rfl
    simp only [ite_true, h₀, h₁, inv_div]

/-- For the product of the gluing ratios of a line bundle, an isomorphism preserving the
branch order at every node leaves the product unchanged. An isomorphism reversing all the
orders inverts the product. In an oriented cycle the branch order distinguishes both
orientations even at a self-node. -/
theorem finprod_branchRatioHom_lineGluingUnit_pullback
    (orderX : ∀ z : (X.singularLocus k).subscheme,
      Fin 2 ≃ {q : X.branchScheme k // X.branchSchemeToSingularLocus k q = z})
    (orderY : ∀ z : (Y.singularLocus k).subscheme,
      Fin 2 ≃ {q : Y.branchScheme k // Y.branchSchemeToSingularLocus k q = z})
    {M : Y.Modules}
    (t : (pullback (ν[Y])).obj M ≅ 𝟙_ _) (d : (pullback (ι[Y])).obj M ≅ 𝟙_ _)
    (swap : Bool) (horder : ∀ (z : N[X]) (i : Fin 2),
      branchIso (orderX z i).val = (orderY (nodeIso z) (if swap then i.rev else i)).val) :
    (∏ᶠ z : N[X], X.branchRatioHom (k := k) hX orderX
        ((conductorSq[X]).lineGluingUnit
          ((normalizationSq).pullbackTrivialization t)
          ((singularLocusSq).pullbackTrivialization d)) z) =
      if swap then (∏ᶠ z : N[Y], Y.branchRatioHom (k := k) hY orderY
        ((conductorSq[Y]).lineGluingUnit t d) z)⁻¹ else
      ∏ᶠ z : N[Y], Y.branchRatioHom (k := k) hY orderY ((conductorSq[Y]).lineGluingUnit t d) z := by
  rw [e.lineGluingUnit_pullback]
  have hbij : Function.Bijective (nodeIso : N[X] → N[Y]) := by
    simpa only [Scheme.coe_homeoOfIso] using
      (Scheme.homeoOfIso (e.singularLocusIso (R := k))).bijective
  refine (finprod_congr fun z ↦
    e.branchRatioHom_appTop hX hY orderX orderY _ z swap (horder z)).trans ?_
  cases swap
  · simpa only [Bool.false_eq_true, ite_false] using finprod_comp _ hbij
  · simp only [ite_true, finprod_inv_distrib]
    exact congrArg Inv.inv (finprod_comp _ hbij)

end CategoryTheory.Iso
