/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Mutation.Contracted

import QPainleve.Geometry.Toric.Fan.StarSubdivision.RayInsertion
import QPainleve.SignedClusterModularGroup.Realization.Refinement

/-!
# Mutation of marked presentations on complete fans

The elementary transformation of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1),
uses a fan containing both pivot directions. A regular subdivision inserts the
opposite ray for the entire marked family. Mutation then gives a new complete
presentation on the same prescribed center domain, with its ordered nodal
contractions and marked Picard pullbacks.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative PointedCone
open Module (Basis)
open QPainleve.BlowupTower QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan
open Scheme Scheme.PartialMap

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) {n : ℕ} (s : Fin (n + 1) → Φ.Ray) (k : Fin (n + 1))
  (hΦ : Φ.IsRegular)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "A" => (Fin (n + 1) → ℤ)
local notation "Centers" => Over.mk (structureMap ℂ A)
local notation "XTor" => scheme ℂ (Fin (n + 1) →₀ ℤ)
local notation "χ(" c ")" => pointsEquiv ℂ A
  (Subtype.mk (CommaMorphism.left (c : Point Centers)) (Over.w (c : Point Centers)))
local notation "centers(" a ")" => fun j : Fin (n + 1) ↦ (a) (ofAdd (Pi.single j 1))
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "Aux[" s "," h "," c "]" => internalBlowupTower (h₀ := h) b s centers(χ(c))

variable {E : SkewExchangeMatrix (Fin (n + 1))} (P : ChargeSeed E N)
  (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = rayChargeMap s)

local notation "w" => Quiver.Hom.toPath (Generator.toStep (Generator.mutate k) E)
local notation "C" => Quiver.Path.centerPartialMap ℂ w P
local notation "F" => Quiver.Path.xRationalMap ℂ w

variable (U : (scheme ℂ (Fin (n + 1) → ℤ)).Opens)
  (hU : Dense (U : Set (scheme ℂ (Fin (n + 1) → ℤ))))
  (hle : U ≤ (Quiver.Path.centerPartialMap ℂ ((Generator.mutate k).toStep E).toPath P).domain)

local notation "C'" => Scheme.PartialMap.restrict C U hU hle
local notation "src(" c ")" => (c) ≫ Scheme.PartialMap.domainSource (X := Centers) (Y := Centers) C'
local notation "dst(" c ")" => (c) ≫ Scheme.PartialMap.domainTarget (X := Centers) (Y := Centers) C'

variable [PrestableFamily (Dtor[Φ,hΦ₀] ↘ S)]
  {m l : ℕ} [NeZero m] [NeZero l]
  {L : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
  {γ : Type*} {a : γ → (Dtor[Φ,hΦ₀] ↘ S).smoothLocus}
  {T : Scheme.NodalCycleNumbering a l} {o : ZMod l}
  {J : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin (n + 1) → ℤ)}
  (M : Point (Over.mk (structureMap ℂ (Fin (n + 1) → ℤ))) →
    MarkedSurface ℂ m H (scheme ℂ (Fin (n + 1) →₀ ℤ)))
  (r : ZMod l ≃ Φ.Ray)

local notation "pullbackPic(" h ")" => LinearMap.prodMap
  (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive
    (LineBundleClass.pullbackHom (FanHom.algebraicMap (Fan.IsSubdivision.toFanHom h)))))
  LinearMap.id

include hform hcharge in
/-- A mutation of a marked toric family over a complete regular fan is realized on
any dense open of the mutation domain. A single regular subdivision supplies the
opposite pivot ray. The terminal center rays and auxiliary Picard inclusion are
obtained by mutating the lifted rays and the pulled-back inclusion. All terminal
fibers over the chosen open carry ordered nodal presentations. The contracted
Picard marking and the action on numbered branches are preserved. -/
theorem exists_mutate_contracted_of_complete (hc : Φ.IsComplete)
    (hr : ∀ j, T.component j = Φ.boundaryNormalizationComponentEquiv hΦ (r j))
    (hpos : ∀ j, b.detDualEquiv (r j).primitiveGenerator (r (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (r j).toCone ≤ σ ∧ (r (j + 1)).toCone ≤ σ)
    (hmodel : ∀ c : CenterPoint (U := Centers) (V := Centers) C',
      ∃ (p : ContractedToricFiber b s hΦ T o J χ(src(c)) (M (src(c))))
        (Y : Scheme) (d : ℕ) (W : BlowupTower (M (src(c))).surface d Y)
        (e : Y ≅ (Aux[s,hΦ₀,src(c)]).1),
      IsNodalBoundaryTower (M (src(c))).pair.hom.left.ker ((M (src(c))).surface ↘ S) (𝟙 _) W ∧
        p.projection = e.inv ≫ W.toBase) :
    ∃ (Ω : Fan i) (h : Ω.IsSubdivision Φ) (hΩ : Ω.IsRegular) (hcΩ : Ω.IsComplete)
        (hopp : hull ℝ {i (-(h.liftRay (s k)).primitiveGenerator)} ∈ Ω.cones),
      let s₀ := h.liftRay ∘ s
      let hv := (s₀ k).primitiveGenerator_ne_zero
      let hp := (s₀ k).hull_primitiveGenerator_mem
      let Ψ := Ω.mutationFan b hv hp hopp
      let hΨ := (Ω.isRegular_mutationFan_iff b hv hp hopp).mpr hΩ
      let hcΨ := (Ω.isComplete_mutationFan_iff b hv hp hopp).mpr hcΩ
      letI : Nonempty Ψ.cones := hcΨ.nonempty_cones
      let t := Ω.mutationFanCenterRays b s₀ k hopp
      let J' := (mutationPicardEquiv b s₀ k hopp hΩ).symm.toLinearMap.comp
        ((pullbackPic(h)).comp J)
      ∃ (hpre : PrestableFamily (Dtor[Ψ,hcΨ.nonempty_cones] ↘ S))
        (l' : ℕ) (hl' : NeZero l'),
        letI := hpre
        letI := hl'
        ∃ (T' : Scheme.NodalCycleNumbering
            (Empty.elim : Empty → (Dtor[Ψ,hcΨ.nonempty_cones] ↘ S).smoothLocus) l')
          (o' : ZMod l') (v : ZMod l' ≃ Ψ.Ray)
          (M' : Point Centers → MarkedSurface ℂ m H XTor)
          (R : GeometricRealization (T₀ := Centers) (T₁ := Centers) M M' C' F),
          (∀ j, T'.component j = Ψ.boundaryNormalizationComponentEquiv hΨ (v j)) ∧
          (∀ j, b.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
            ∃ σ : Ψ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ) ∧
          (Quiver.Path.chargeTarget w P).charge = rayChargeMap t ∧
          R.picard = .refl H ∧ R.boundaryAction = 1 ∧
          ∀ c : CenterPoint (U := Centers) (V := Centers) C',
            ∃ (ev : (M (src(c))).surface ⤏ XTor)
              (hM : M' (dst(c)) = (M (src(c))).withEvaluation ev),
              (R.fiber c).iso ≪≫ eqToIso (congrArg MarkedSurface.pair hM) = Iso.refl _ ∧
              ∃ (p : ContractedToricFiber (h₀ := hcΨ.nonempty_cones)
                    b t hΨ T' o' J' χ(dst(c)) (M' (dst(c))))
                (Y : Scheme) (d : ℕ) (W : BlowupTower (M' (dst(c))).surface d Y)
                (e : Y ≅ (Aux[t,hcΨ.nonempty_cones,dst(c)]).1),
              IsNodalBoundaryTower (M' (dst(c))).pair.hom.left.ker
                ((M' (dst(c))).surface ↘ S) (𝟙 _) W ∧ p.projection = e.inv ≫ W.toBase := by
  have hN := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨Ω, h, hΩ, hcΩ, hopp⟩ := (s k).exists_regular_subdivision_containing_opposite hΦ hc hN
  let : Nonempty Ω.cones := hcΩ.nonempty_cones
  let s₀ := h.liftRay ∘ s
  let hv := (s₀ k).primitiveGenerator_ne_zero
  let hp := (s₀ k).hull_primitiveGenerator_mem
  let Ψ := Ω.mutationFan b hv hp hopp
  let hcΨ : Ψ.IsComplete := (Ω.isComplete_mutationFan_iff b hv hp hopp).mpr hcΩ
  let : Nonempty Ψ.cones := hcΨ.nonempty_cones
  choose p Y d W e hW he using hmodel
  obtain ⟨hpre, l', hl', hnumbering⟩ :=
    ContractedToricFiber.exists_positive_subdivision_family (δ := Empty) h
      (fun c : CenterPoint (U := Centers) (V := Centers) C' ↦ χ(src(c)))
      (fun c ↦ M (src(c))) p hΩ hc (fun c ↦ ⟨Y c, d c, W c, e c, hW c, he c⟩)
      r hr hpos
  let : PrestableFamily (Dtor[Ω,hcΩ.nonempty_cones] ↘ S) := hpre
  let : NeZero l' := hl'
  obtain ⟨T₀, o₀, v₀, hv₀, hpos₀, -, -, hmodels₀⟩ := hnumbering Empty.elim
  have hcharge₀ : P.charge = rayChargeMap s₀ := hcharge.trans (h.rayChargeMap_liftRay s).symm
  obtain ⟨hpre', T', M', R, hv', hpos', hcharge', hpic, hact, hmodels'⟩ :=
    exists_mutate_contracted b s₀ k hopp hΩ P hform hcharge₀ U hU hle M v₀ hcΩ hv₀ hpos₀
      (T := T₀) (o := o₀) (J := (pullbackPic(h)).comp J) (fun c ↦ by
        obtain ⟨q, Y, d, W, e, hW, he, -⟩ := hmodels₀ c
        exact ⟨q, Y, d, W, e, hW, he⟩)
  let v := v₀.trans (Ω.mutationFanRayEquiv b hv hp hopp)
  exact ⟨Ω, h, hΩ, hcΩ, hopp, hpre', l', hl', T', o₀, v, M', R,
    hv', hpos', hcharge', hpic, hact, hmodels'⟩

end QPainleve.SignedClusterModularGroup.GeometricRealization
