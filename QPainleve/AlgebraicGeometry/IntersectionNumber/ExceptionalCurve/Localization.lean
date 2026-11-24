/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import QPainleve.AlgebraicGeometry.IdealSheaf.Completion
public import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Comparison
public import QPainleve.AlgebraicGeometry.Scheme.Stalk

import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.Morphisms.Flat.StructureSheaf
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Localizing an exceptional contraction

Base change from the target to the spectrum of its local ring at the contracted
point preserves every positive thickening of the exceptional curve. The resulting
proper morphism has the same exceptional curve as its scheme-theoretic closed
fiber. This lets the completion of the local ring be compared with the functions
on the original thickenings, as in the
[Stacks Project, Lemma 54.16.4](https://stacks.math.columbia.edu/tag/0C2L).
-/

public noncomputable section

open CategoryTheory Limits Opposite IsLocalRing TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

open IdealSheafData

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {p : Y} {E : X.IdealSheafData}

local notation "Aₚ" => Y.presheaf.stalk p
local notation "S" => Spec (Y.presheaf.stalk p)
local notation "s" => Y.fromSpecStalk p
local notation "a" => pullback.fst f s
local notation "g" => pullback.snd f s
local notation "I" => Hom.ker (Spec.map (Y.residue p))
local notation "q" n =>
  Spec.map (CommRingCat.ofHom (R := Aₚ) (Ideal.Quotient.mk (maximalIdeal Aₚ ^ (n + 1))))
local notation "powLE" => pow_le_pow_of_le_one bot_le le_top (Nat.le_succ (_ + 1))

namespace Hom

/-- The closed fiber after localizing at a closed point is the inverse image of
the original scheme-theoretic fiber. -/
theorem comap_ker_residue_pullback_snd_fromSpecStalk
    (hp : IsClosed ({p} : Set Y)) (hE : (Y.fromSpecResidueField p).ker.comap f = E) :
    (I).comap g = E.comap a := by
  rw [← ker_fromSpecResidueField_comap_fromSpecStalk hp, ← comap_comp, ← pullback.condition,
    comap_comp, hE]

private theorem isIso_subschemeMap_comap_pullback_fst_of_support_le
    (hp : IsClosed ({p} : Set Y)) (hE : (Y.fromSpecResidueField p).ker.comap f = E)
    (J : X.IdealSheafData) (hJ : J.support ≤ E.support)
    {J' : (pullback f s).IdealSheafData} (hJ' : J' = J.comap a) :
    IsIso (subschemeMap J' J a (hJ' ▸ J.le_map_comap a)) := by
  have h := isPullback_subschemeMap_of_eq hJ' (IsPullback.of_hasPullback f s)
  apply h.isIso_fst_of_fromSpecStalk
  intro x
  have hx : J.subschemeι x ∈ (E.support : Set X) := hJ (by
    rw [← SetLike.mem_coe, ← J.range_subschemeι]
    exact Set.mem_range_self x)
  rw [← hE, support_comap, Closeds.coe_preimage,
    support_ker_fromSpecResidueField_of_isClosed hp, Set.mem_preimage, Set.mem_singleton_iff] at hx
  exact specializes_of_eq ((Hom.comp_apply _ _ _).trans hx)

end Hom

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

namespace Hom

/-- The infinitesimal fiber over the spectrum of the local ring at a closed point
is canonically isomorphic to the corresponding thickening of the original fiber. -/
def localizedFiberThickeningIso
    (hp : IsClosed ({p} : Set Y)) (hE : (Y.fromSpecResidueField p).ker.comap f = E)
    (n : ℕ) : pullback g (q n) ≅ (E ^ (n + 1)).subscheme := by
  have hI := comap_ker_residue_pullback_snd_fromSpecStalk f hp hE
  have hker : RingHom.ker (Y.residue p).hom = maximalIdeal Aₚ := IsLocalRing.ker_residue
  rw [Hom.ker_Spec_map, hker] at hI
  let J := E ^ (n + 1)
  have hJ : E.comap a ^ (n + 1) = J.comap a := (E.comap_pow a _).symm
  have := isIso_subschemeMap_comap_pullback_fst_of_support_le f hp hE J
    (support_pow_succ E n).le hJ
  -- Supply the ring instances of the bundled stalk to the local-ring construction.
  exact @Hom.fiberThickeningIso Aₚ inferInstance inferInstance _ g _ hI n ≪≫
    asIso (subschemeMap _ J a (hJ ▸ J.le_map_comap a))

/-- The localized thickening isomorphism commutes with the projections to the
original source scheme. -/
@[reassoc (attr := simp)]
theorem localizedFiberThickeningIso_hom_subschemeι
    (hp : IsClosed ({p} : Set Y)) (hE : (Y.fromSpecResidueField p).ker.comap f = E)
    (n : ℕ) :
    (localizedFiberThickeningIso f hp hE n).hom ≫ (E ^ (n + 1)).subschemeι =
      pullback.fst g (q n) ≫ a := by
  unfold localizedFiberThickeningIso
  dsimp only [Iso.trans_hom, asIso_hom]
  rw [Category.assoc, subschemeMap_subschemeι, Hom.fiberThickeningIso_hom_subschemeι_assoc]

/-- Restriction between successive infinitesimal fibers agrees with the inclusion
between the corresponding thickenings of the original fiber. -/
theorem localizedFiberThickeningIso_transition
    (hp : IsClosed ({p} : Set Y)) (hE : (Y.fromSpecResidueField p).ker.comap f = E)
    (n : ℕ) :
    @Hom.fiberThickeningι Aₚ inferInstance inferInstance _ g n ≫
        (localizedFiberThickeningIso f hp hE (n + 1)).hom =
      (localizedFiberThickeningIso f hp hE n).hom ≫
        inclusion (powLE : E ^ (n + 2) ≤ E ^ (n + 1)) := by
  apply (cancel_mono (E ^ (n + 2)).subschemeι).mp
  rw [Category.assoc, localizedFiberThickeningIso_hom_subschemeι,
    Hom.fiberThickeningι_fst_assoc, Category.assoc, inclusion_subschemeι,
    localizedFiberThickeningIso_hom_subschemeι]

/-- Localization at the contracted point identifies the inverse system of rings
of functions on the original thickenings with the infinitesimal fiber rings. -/
def localizedFiberThickeningSectionsIso
    (hp : IsClosed ({p} : Set Y)) (hE : (Y.fromSpecResidueField p).ker.comap f = E) :
    E.thickeningSections ≅ @Hom.fiberThickeningSections Aₚ inferInstance inferInstance _ g := by
  let α : E.thickeningSections ⟶ @Hom.fiberThickeningSections Aₚ inferInstance inferInstance _ g :=
    NatTrans.ofOpSequence (fun n ↦ (localizedFiberThickeningIso f hp hE n).hom.appTop)
      (fun n ↦ by
        rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
        exact (Hom.comp_appTop _ _).symm.trans
          ((congrArg Hom.appTop (localizedFiberThickeningIso_transition f hp hE n).symm).trans
            (Hom.comp_appTop _ _)))
  exact NatIso.ofComponents
    (fun n ↦ Scheme.Γ.mapIso (localizedFiberThickeningIso f hp hE n.unop).op)
    (fun {_ _} m ↦ α.naturality m)

/-- At each level, the comparison of section rings is pullback along the
localized thickening isomorphism. -/
@[simp]
theorem localizedFiberThickeningSectionsIso_hom_app
    (hp : IsClosed ({p} : Set Y)) (hE : (Y.fromSpecResidueField p).ker.comap f = E)
    (n : ℕ) :
    (localizedFiberThickeningSectionsIso f hp hE).hom.app (op n) =
      (localizedFiberThickeningIso f hp hE n).hom.appTop :=
  (rfl)

/-- Pullback from the completed local ring at a closed point to the inverse
limit of the section rings of the original fiber thickenings. -/
def completionToThickeningLimitAt
    (hp : IsClosed ({p} : Set Y)) (hE : (Y.fromSpecResidueField p).ker.comap f = E) :
    CommRingCat.of (AdicCompletion (maximalIdeal Aₚ) Aₚ) ⟶ limit E.thickeningSections :=
  @Hom.completionToFiberThickeningLimit Aₚ inferInstance inferInstance _ g ≫
    (HasLimit.isoOfNatIso (localizedFiberThickeningSectionsIso f hp hE)).inv

/-- At each level the completion map is the truncated pullback, transported
back to the section ring of the original thickening. -/
@[reassoc (attr := simp)]
theorem completionToThickeningLimitAt_π
    (hp : IsClosed ({p} : Set Y)) (hE : (Y.fromSpecResidueField p).ker.comap f = E)
    (n : ℕ) :
    completionToThickeningLimitAt f hp hE ≫ limit.π E.thickeningSections (op n) =
      CommRingCat.ofHom (@Hom.completionToFiberThickening Aₚ inferInstance inferInstance _ g n) ≫
        (localizedFiberThickeningSectionsIso f hp hE).inv.app (op n) := by
  let e := localizedFiberThickeningSectionsIso f hp hE
  let c := @Hom.completionToFiberThickeningLimit Aₚ inferInstance inferInstance _ g
  calc
    _ = c ≫ ((HasLimit.isoOfNatIso e).inv ≫ limit.π E.thickeningSections (op n)) :=
      Category.assoc _ _ _
    _ = c ≫ limit.π _ (op n) ≫ e.inv.app (op n) :=
      congrArg (c ≫ ·) (HasLimit.isoOfNatIso_inv_π e (op n))
    _ = _ := @Hom.completionToFiberThickeningLimit_π_assoc Aₚ inferInstance inferInstance _
      g n _ (e.inv.app (op n))

/-- The comparison to functions on the original infinitesimal thickenings is
injective for a proper, scheme-theoretically dominant morphism to a locally
Noetherian scheme. -/
theorem injective_completionToThickeningLimitAt [IsLocallyNoetherian Y] [IsProper f]
    [IsSchemeTheoreticallyDominant f]
    (hp : IsClosed ({p} : Set Y)) (hE : (Y.fromSpecResidueField p).ker.comap f = E) :
    Function.Injective (completionToThickeningLimitAt f hp hE) :=
  (ConcreteCategory.bijective_of_isIso
    (HasLimit.isoOfNatIso (localizedFiberThickeningSectionsIso f hp hE)).inv).1.comp
    (@Hom.injective_completionToFiberThickeningLimit Aₚ inferInstance inferInstance _
      inferInstance g inferInstance inferInstance)

end Hom

end AlgebraicGeometry.Scheme
