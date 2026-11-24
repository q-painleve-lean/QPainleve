/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Nef.Exceptional
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Boundary
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Configuration

/-!
# Contracting a transported internal exceptional configuration

A Picard isometry matching the nef cones, canonical classes and boundary
classes transports a disjoint internal exceptional configuration. The
contraction of the transported curves gives an ordered point-blowup
presentation whose exceptional classes and fibers record the prescribed
classes and whose fibers are omitted from the boundary components.

This is the transport and contraction step in the proof of Theorem 1.8 of
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve
open Scheme.IdealSheafData Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
open TauCeti.AlgebraicGeometry.LineBundleClass
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.Chow

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [Y.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  [hRatX : Scheme.IsRationalOver (X ↘ Spec (.of k))]
  [hRatY : Scheme.IsRationalOver (Y ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "V(" X ")" => (ℝ ⊗[ℤ] Pic(X))
local notation "K(" X ")" => Additive.ofMul (mk (canonicalBundle k X 2))
local notation "B(" X ")" => intersectionBilinForm k X
local notation "classOf(" h ")" => Additive.ofMul ((mk
  (IsEffectiveCartier.toInvertibleSheaf (IsExceptionalCurveOfFirstKind.isEffectiveCartier h)))⁻¹)
local notation "primeClass(" D "," p ")" =>
  Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D p))

variable [TopologicalSpace V(X)] [IsTopologicalAddGroup V(X)] [ContinuousSMul ℝ V(X)] [T2Space V(X)]
  [TopologicalSpace V(Y)] [IsTopologicalAddGroup V(Y)] [ContinuousSMul ℝ V(Y)] [T2Space V(Y)]

/-- Under a Picard isometry preserving canonical classes and real nef cones, a
disjoint internal exceptional configuration transfers to a contraction of the
target surface. Every target prime boundary class must come from a source prime
boundary class. The contracted surface is smooth, projective and rational. Its
closed-point blowup tower has distinct projected centers and the prescribed
ordered exceptional classes. Each exceptional fiber lies off the list of
boundary components. -/
theorem exists_ordered_internal_contraction_of_nefCone_isometry {n : ℕ}
    {D : X.IdealSheafData} {F : Y.IdealSheafData} (E : Fin n → X.IdealSheafData)
    (hE : ∀ j, (E j).IsExceptionalCurveOfFirstKind)
    (hdis : Pairwise fun i j ↦ Disjoint ((E i).support : Set X) (E j).support)
    (hinternal : ∀ j, ¬ (E j).support ≤ D.support) :
    let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral X := hRatX.isIntegral_of_smooth
    let : IsIntegral Y := hRatY.isIntegral_of_smooth
    let : Module.Finite ℤ Pic(X) := X.finite_picard_of_isRationalOver k (rational := hRatX)
    let : Module.Finite ℤ Pic(Y) := Y.finite_picard_of_isRationalOver k (rational := hRatY)
    let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
    let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := (Y ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∀ (e : B(X).IsometryEquiv B(Y)),
      e K(X) = K(Y) →
      (e.baseChange ℝ) '' (nefCone k (X := X) : Set V(X)) = nefCone k (X := Y) →
      (∀ p : F.boundaryPrimes, ∃ q : D.boundaryPrimes, e primeClass(D,q) = primeClass(F,p)) →
      ∃ (Z : Scheme.{u}) (t : Z ⟶ S) (W : Scheme.{u}) (T : BlowupTower Z n W)
        (a : Y ≅ W) (hT : T.IsClosedPointTower Z),
        let : Z.Over S := ⟨t⟩
        let f := a.hom ≫ T.toBase
        IsIntegral Z ∧ Z.IsProjectiveOver k ∧ SmoothOfRelativeDimension 2 t ∧
          Scheme.IsRationalOver t ∧
          f.IsOver S ∧ IsModification f ∧ Function.Injective hT.baseCenter ∧
          f.centre = Set.range hT.baseCenter ∧
          (∀ j, ¬ ((Z.fromSpecResidueField (hT.baseCenter j)).ker.comap T.toBase).support ≤
            (F.comap a.inv).support) ∧
          ∀ j, Additive.ofMul (pullback a.hom (T.exceptionalClass j)) = e classOf(hE j) := by
  intro _ _ _ _ _ _ _ _ _ _ e hK hnef hbd
  obtain ⟨G, hG, hclass, hd⟩ :=
    exists_pairwise_disjoint_exceptionalCurves_of_nefCone_isometry k E hE hdis e hK hnef
  have homit (j : Fin n) : ¬ (G j).support ≤ F.support := by
    intro h
    obtain ⟨p, hp⟩ := (hG j).support_le_iff_exists_boundaryPrime_class_eq.mp h
    obtain ⟨q, hq⟩ := hbd p
    have hEq : e primeClass(D,q) = e classOf(hE j) :=
      hq.trans ((congrArg Additive.ofMul hp).trans (hclass j).symm)
    exact hinternal j ((hE j).support_le_iff_exists_boundaryPrime_class_eq.mpr
      ⟨q, Additive.ofMul.injective (e.injective hEq)⟩)
  obtain ⟨Z, t, W, T, a, hT, hZ, hproj, hsmooth, hover, hmod, hinj, hcent, hFib, ha⟩ :=
    exists_smooth_projective_contraction_of_disjoint_exceptional_curves (k := k) G hG hd
  let : Z.Over S := ⟨t⟩
  let f := a.hom ≫ T.toBase
  let : IsModification f := hmod
  let : f.IsOver S := hover
  have hRatZ : Scheme.IsRationalOver t := by
    obtain ⟨g, hg⟩ := IsModification.birationalOver f
    have hbir : Scheme.BirationalOver (f ≫ t) t :=
      ⟨g, by simpa only [Category.assoc, Category.comp_id] using congrArg (· ≫ t) hg⟩
    have hf : f ≫ t = (Y ↘ S) := comp_over f S
    rw [hf] at hbir
    exact hbir.symm.isRationalOver t (Y ↘ S)
  refine ⟨Z, t, W, T, a, hT, hZ, hproj, hsmooth, hRatZ, hover, hmod, hinj, hcent, ?_, fun j ↦ ?_⟩
  · intro j h
    apply homit j
    rw [← (hFib j).2, comap_comp, support_comap]
    have hF : (F.comap a.inv).support.preimage a.hom.continuous = F.support := by
      rw [← support_comap, ← comap_comp, Iso.hom_inv_id, comap_id]
    rw [← hF, ← SetLike.coe_subset_coe, TopologicalSpace.Closeds.coe_preimage,
      TopologicalSpace.Closeds.coe_preimage]
    exact Set.preimage_mono h
  · rw [ha j, ← hclass j]

end TauCeti.AlgebraicGeometry.Chow
