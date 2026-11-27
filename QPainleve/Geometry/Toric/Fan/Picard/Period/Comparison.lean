/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Period.CenterVariation

/-!
# Comparing periods in toric Picard markings

The period of a charge relation is the boundary restriction of a particular
Picard class. Its toric and total exceptional coordinates are independent of
the centers. Consequently a pair isomorphism identifying the full Picard
markings compares the period characters by its sign on the numbered boundaries.

The comparison uses `Fan.exists_picardBoundaryOrthogonalEquivChargeKernel_symm_marking`
and the oriented gluing period of Gross, Hacking and Keel, *Moduli of surfaces with
an anti-canonical cycle*, [§2](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve QPainleve.BlowupTower
open TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open Scheme (NodalCycleNumbering)

namespace TauCeti.Toric.Fan

variable (K : Type) [Field K] [IsAlgClosed K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "dim" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "J[" c "]" => (fun j ↦ Ray.internalCenter K b (s j) (c j))
local notation "hJ[" c "]" => (fun j ↦ Ray.internalCenter_val K b (s j) (c j))
local notation "M[" c "]" =>
  alongBoundary (subschemeι (Fan.toricBoundaryIdeal K Φ inferInstance)) (J[c])
local notation "U[" c "]" => WithBoundary.toTower (Sigma.snd (M[c]))
local notation "m" =>
  (fun j ↦ LinearMap.toAddMonoidHom (Module.Basis.detDualEquiv b (Ray.primitiveGenerator (s j))))
local notation "hm" => (fun j ↦ Module.Basis.detDualEquiv_self b (Ray.primitiveGenerator (s j)))
local notation "hprim" => (fun j ↦ Ray.surjective_detCharacter (s j) b)
local notation "hU[" z "]" =>
  isClosedPointTower_alongBoundary_binomialCenters K dim s m hm hprim z (J[z]) (hJ[z])
local notation "fZ" => (Φ.finiteFanSchemeToSpec K)
local notation "smoothZ" =>
  cast (congrArg (fun d ↦ SmoothOfRelativeDimension d fZ) dim)
    (Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ)

variable [(Φ.finiteFanScheme K).IsProjectiveOver K]
  {c d : Fin n → Kˣ}
  {X Y W W' : Scheme} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
  [X.IsProjectiveOver K] [Y.IsProjectiveOver K] [IsIntegral X] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of K))] [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of K))]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm K X)]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm K Y)]
  {D : X.IdealSheafData} {E : Y.IdealSheafData} {l l' : ℕ}
  {P : BlowupTower X l W} {Q : BlowupTower Y l' W'}
  (hP : IsNodalBoundaryTower D (X ↘ Spec (.of K)) (𝟙 X) P)
  (hQ : IsNodalBoundaryTower E (Y ↘ Spec (.of K)) (𝟙 Y) Q)
  (p : W ≅ (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι
    (fun j ↦ (s j).internalCenter K b (c j))).1)
  (q : W' ≅ (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι
    (fun j ↦ (s j).internalCenter K b (d j))).1)
  (hp : p.inv ≫ P.toBase ≫ (X ↘ Spec (.of K)) =
    (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter K b (c j))).2.toTower.toBase ≫
      ((Φ.finiteFanScheme K) ↘ Spec (.of K)))
  (hq : q.inv ≫ Q.toBase ≫ (Y ↘ Spec (.of K)) =
    (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter K b (d j))).2.toTower.toBase ≫
      ((Φ.finiteFanScheme K) ↘ Spec (.of K)))
  (hDs : ((D.comap P.toBase).comap p.inv).support =
    (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter K b (c j))).2.boundaryι.ker.support)
  (hEs : ((E.comap Q.toBase).comap q.inv).support =
    (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter K b (d j))).2.boundaryι.ker.support)

local notation "a" => (Iso.inv p ≫ BlowupTower.toBase P)
local notation "a'" => (Iso.inv q ≫ BlowupTower.toBase Q)

local notation "kD" => markedBoundaryChargeEquiv K hΦ b s hP p hp hDs
local notation "kE" => markedBoundaryChargeEquiv K hΦ b s hQ q hq hEs
local notation "mark[" z "]" => picardMarking (U[z]) (hU[z]) fZ

variable {f : X ⟶ Y}

variable [PrestableFamily (D.subscheme ↘ Spec (.of K))]
  [PrestableFamily (E.subscheme ↘ Spec (.of K))]
  (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
  (gD : ∀ v : irreducibleComponents (D.subscheme.singularLocus K).blowup,
    (D.subscheme.blowupComponent (K := K) v).toScheme.genus K = 0)
  (gE : ∀ v : irreducibleComponents (E.subscheme.singularLocus K).blowup,
    (E.subscheme.blowupComponent (K := K) v).toScheme.genus K = 0)
  {α β : Type*} {u : α → (D.subscheme ↘ Spec (.of K)).smoothLocus}
  {v : β → (E.subscheme ↘ Spec (.of K)).smoothLocus}
  {r : ℕ} [NeZero r] (A : NodalCycleNumbering u r) (B : NodalCycleNumbering v r)

local notation "periodD" => markedBoundaryPeriod K hΦ b s hP p hp hDs hD gD A
local notation "periodE" => markedBoundaryPeriod K hΦ b s hQ q hq hEs hE gE B

/-- A pair morphism identifying the full toric Picard coordinates compares the marked
periods by the orientation of its boundary isomorphism. The orientation is read from
the actual branches, including for one or two components. -/
theorem markedBoundaryPeriod_eq_of_pullback_marking
    (g : D.subscheme ≅ E.subscheme) [g.hom.IsOver (Spec (.of K))]
    (hcomm : D.subschemeι ≫ f = g.hom ≫ E.subschemeι)
    (hmark : letI : SmoothOfRelativeDimension 2 fZ := smoothZ
      ∀ L : LineBundleClass Y,
        (mark[c]).symm (Additive.ofMul (pullback a (pullback f L))) =
          (mark[d]).symm (Additive.ofMul (pullback a' L))) :
    periodD =
      if DihedralGroup.cycleOrientationSign (g.boundaryCycleAction A B) = -1 then periodE⁻¹
      else periodE := by
  apply MonoidHom.ext
  intro x
  let z := (kE).symm x.toAdd
  let swap := decide (DihedralGroup.cycleOrientationSign (g.boundaryCycleAction A B) = -1)
  obtain ⟨hz, hperiod⟩ := hD.boundaryPeriod_pullback gD A.endpoint_eq hE gE B.endpoint_eq
    f g hcomm swap (by simpa only [swap, decide_eq_true_eq] using
      g.branchOrder_boundaryCycleAction A B) (ofAdd z)
  have heq : (⟨Additive.ofMul (pullback f z.val.toMul), hz⟩ : D.boundaryOrthogonal K) =
      (kD).symm x.toAdd := by
    apply Subtype.ext
    have htarget := coe_markedBoundaryChargeEquiv_symm K hΦ b s hQ q hq hEs x.toAdd
    have hsource := coe_markedBoundaryChargeEquiv_symm K hΦ b s hP p hp hDs x.toAdd
    have hmap := map_picardBoundaryOrthogonalEquivChargeKernel_symm_of_matching_markings K
      hΦ b s hP hQ p q hp hq hDs hEs (pullback f) x.toAdd (hmark _)
    exact (congrArg Additive.ofMul
      ((congrArg (fun L ↦ pullback f L.toMul) htarget).trans hmap)).trans hsource.symm
  have hsource : periodD x = hD.boundaryPeriod gD A.endpoint_eq
      (ofAdd ((kD).symm x.toAdd)) := by
    rw [← ofAdd_toAdd x, markedBoundaryPeriod_apply]
    simp only [toAdd_ofAdd]
  have htarget : periodE x = hE.boundaryPeriod gE B.endpoint_eq (ofAdd z) := by
    rw [← ofAdd_toAdd x, markedBoundaryPeriod_apply]
  simp only [toAdd_ofAdd] at hperiod
  rw [heq, ← hsource, ← htarget] at hperiod
  simp only [swap, decide_eq_true_eq] at hperiod
  split_ifs at hperiod ⊢ <;> simpa only [MonoidHom.inv_apply] using hperiod

end TauCeti.Toric.Fan
