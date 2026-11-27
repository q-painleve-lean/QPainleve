/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Contraction
public import QPainleve.Geometry.Toric.Fan.Mutation.OrderedBlowup


/-!
# Descent of toric mutation through nodal blowups

The isomorphism of the pivot blowups identifies their strict boundaries. Its lift
through the remaining ordered centers still identifies the full strict boundaries.
Consequently the isomorphism of the ordered models descends through prescribed
nodal blowups of connected nef square-zero pairs.

The elementary transformation is that of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Module.Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : PointedCone.hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : k₀ˣ)

local notation "v" => Ray.primitiveGenerator ρ
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "hΦ₀" => Nonempty.intro (Ray.toCone Φ ρ)
local notation "hΨ₀" => Nonempty.intro (Φ.mutationFanConeEquiv b hv hp hOpp (Subtype.mk _ hp))
local notation "D₀" => Φ.toricBoundaryIdeal k₀ hΦ₀
local notation "D₁" => Fan.toricBoundaryIdeal k₀ (Ψ) hΨ₀
local notation "I₀" => Ray.mutationSourceCenterIdeal b ρ c
local notation "I₁" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "π₀" => Scheme.IdealSheafData.blowupToBase (I₀)
local notation "π₁" => Scheme.IdealSheafData.blowupToBase (I₁)
local notation "eB" => Ray.mutationBlowupIso b ρ hOpp c
local notation "j₀" => Ray.mutationSourceBoundaryι b ρ c
local notation "j₁" => Ray.mutationTargetBoundaryι b ρ hOpp c

section Nodal

variable {n : ℕ} (rays : Fin n → Φ.Ray) (params : Fin n → k₀ˣ)

local notation "r" => Φ.mutationFanRayEquiv b hv hp hOpp
local notation "param′" j:arg =>
  params j * c ^ max (Module.Basis.det b ![Ray.primitiveGenerator (rays j), v]) 0
local notation "A" => alongBoundary (j₀)
  (fun j ↦ Ray.internalCenter k₀ (h₀ := hΦ₀) b (rays j) (params j))
local notation "B" => alongBoundary (j₁)
  (fun j ↦ Ray.internalCenter k₀ (h₀ := hΨ₀) b ((r) (rays j)) (param′ j))
local notation "f₀" => toBase (WithBoundary.toTower (Sigma.snd (A))) ≫ (π₀) ≫
  (Φ.finiteFanSchemeToSpec k₀)
local notation "f₁" => toBase (WithBoundary.toTower (Sigma.snd (B))) ≫ (π₁) ≫
  Fan.finiteFanSchemeToSpec k₀ (Ψ)

variable {X Y X' Y' : Scheme} [IsIntegral X] [IsIntegral X']
  [X.Over (Spec (.of k₀))] [X'.Over (Spec (.of k₀))]
  [X.IsProjectiveOver k₀] [X'.IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))]
  [SmoothOfRelativeDimension 2 (X' ↘ Spec (.of k₀))]
  {D : X.IdealSheafData} {E : X'.IdealSheafData} {m l : ℕ}
  {P : BlowupTower X m Y} {Q : BlowupTower X' l Y'}

local notation "s" => (X ↘ Spec (CommRingCat.of k₀))
local notation "t" => (X' ↘ Spec (CommRingCat.of k₀))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

/-- Mutation at the first pivot center descends to the prescribed nodal contractions
of the ordered models of connected nef square-zero pairs. The comparison on the
ordered models lifts the global pivot isomorphism, and the descended isomorphism
is the unique isomorphism of pairs over the coefficient field making the
contraction square commute. -/
theorem exists_iso_of_nodal_mutation (hΦ : Φ.IsRegular)
    (hsame : ∀ j, (rays j).primitiveGenerator = v → params j ≠ c)
    (hopp : ∀ j, (rays j).primitiveGenerator = -v → params j * c ≠ 1)
    (hP : IsNodalBoundaryTower D s (𝟙 X) P)
    (hQ : IsNodalBoundaryTower E t (𝟙 X') Q)
    (a : Y ≅ (A).1) (a' : Y' ≅ (B).1)
    (ha : a.hom ≫ (f₀) = P.toBase ≫ s)
    (ha' : a'.hom ≫ (f₁) = Q.toBase ≫ t)
    (hb : ((A).2.boundaryι.ker.comap a.hom).support = (D.comap P.toBase).support)
    (hb' : ((B).2.boundaryι.ker.comap a'.hom).support = (E.comap Q.toBase).support)
    (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (hnodalD : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hnodalE : AtWorstNodalOfRelativeDimensionOne (E.subschemeι ≫ t))
    (hconn : _root_.IsConnected (D.support : Set X))
    (hnefD : LineBundleClass.IsNef k₀ s classOf(hD))
    (hnefE : LineBundleClass.IsNef k₀ t classOf(hE))
    (hsqD : Chow.classIntersectionNumber k₀ X classOf(hD) classOf(hD) = 0)
    (hsqE : Chow.classIntersectionNumber k₀ X' classOf(hE) classOf(hE) = 0) :
    ∃ e : (A).1 ≅ (B).1, IsLift (eB) (A).2.toTower (B).2.toTower e ∧
      ∃! g : X ≅ X', P.toBase ≫ g.hom = a.hom ≫ e.hom ≫ a'.inv ≫ Q.toBase ∧
        g.hom ≫ t = s ∧ E.comap g.hom = D := by
  obtain ⟨e, he, -⟩ :=
    exists_iso_mutation_internal_blowup_tower k₀ b ρ hOpp c rays params hsame hopp
  refine ⟨e, he, ?_⟩
  let f := a ≪≫ e ≪≫ a'.symm
  have hover : e.hom ≫ (f₁) = (f₀) := by
    rw [← Category.assoc, he.hom_toBase, Category.assoc,
      ρ.mutationBlowupIso_hom_comp_toBase]
  have hstructure : P.toBase ≫ s = f.hom ≫ Q.toBase ≫ t := by
    simp only [f, Iso.trans_hom, Iso.symm_hom, Category.assoc, ← ha', Iso.inv_hom_id_assoc,
      hover, ha]
  have hboundary := ρ.comap_strictBoundary_mutationBlowupIso_lift k₀ b hOpp c hΦ he
  have hsupport :
      (D.comap P.toBase).support = ((E.comap Q.toBase).comap f.hom).support := by
    rw [support_comap (E.comap Q.toBase), ← hb', ← support_comap, ← comap_comp, ← hb]
    simp only [f, Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id,
      Category.assoc, Category.comp_id, comap_comp, hboundary]
  exact hP.existsUnique_iso_of_nef_square_zero_boundary
    k₀ hQ f hstructure hD hE hnodalD hnodalE hconn hsupport hnefD hnefE hsqD hsqE

end Nodal

end TauCeti.Toric.Fan
