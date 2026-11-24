/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.SignedClusterModularGroup.Realization.Agreement
public import QPainleve.SignedClusterModularGroup.Realization.Permutation

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.Picard.Reindex

/-!
# Relabeling contracted toric presentations

A permutation acts on the ordered centers of a contracted toric model. When it
preserves the relative order of repeated centers, the reordering isomorphism
transports the given contraction, carries the exceptional Picard coordinates
along the labels, and renames the independent X evaluation. In a word the
simultaneous noncollision open provides the required separation of centers.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open QPainleve.BlowupTower QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan
open Scheme.IdealSheafData TauCeti.LaurentRing

namespace QPainleve.SignedClusterModularGroup

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L : Type}
  [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "XTor[" r "]" => Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))
local notation "D[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "Pic[" Φ "," r "]" =>
  Additive (LineBundleClass (Fan.algebraicRealization Φ)) × (Fin r → ℤ)
local notation "centers(" c ")" => (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))
local notation "model[" s "," c "]" => internalBlowupTower b s (centers(c))
local notation "renameX(" σ ")" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (rename (R := ℂ) (Equiv.toFun σ))))

variable [hpre : PrestableFamily (D[Φ,h₀] ↘ S)] {γ : Type*} {a : γ → (D[Φ,h₀] ↘ S).smoothLocus}
  {T : Scheme.NodalCycleNumbering a m} {o : ZMod m} {J : L →ₗ[ℤ] Pic[Φ,r]}

variable {c d : Multiplicative (Fin r → ℤ) →* ℂˣ}
  {M : MarkedSurface ℂ n B XTor[r]}
  (p : ContractedToricFiber b s hΦ T o J c M)

variable (σ : Equiv.Perm (Fin r))

local notation "A" => model[s,c]
local notation "A'" => model[s ∘ σ,d]
local notation "π" => toBase (WithBoundary.toTower (Sigma.snd A))
local notation "π'" => toBase (WithBoundary.toTower (Sigma.snd A'))
local notation "J'" => LinearMap.comp (LinearMap.prodMap LinearMap.id
  (LinearEquiv.toLinearMap (LinearEquiv.funCongrLeft ℤ ℤ σ))) J

open Scheme.RationalMap in
private theorem evaluation_eq_reindex (hc : centers(d) = centers(c) ∘ σ)
    (e : (A).1 ≅ (A').1) (he : e.hom ≫ π' = π) :
    (M.compEvaluation (renameX(σ))).evaluation =
      contractedXEvaluation b (s ∘ σ) d hΦ (e.inv ≫ p.projection) := by
  have := isIntegral_internalBlowupTower b s (centers(c)) hΦ
  have hid : (FanHom.id Φ).algebraicMap = 𝟙 Φ.algebraicRealization :=
    FanHom.algebraicMap_id Φ
  have : IsDominant (FanHom.id Φ).algebraicMap := hid.symm ▸ inferInstance
  have htor := (FanHom.id Φ).comp_xEvaluation b b s (s ∘ σ) σ c d (congrFun hc)
    (by intro j; rw [FanHom.id_latticeMap, AddMonoidHom.comp_id]; rfl)
  have hidR (X : Scheme.{0}) : (𝟙 X : X ⟶ X).toRationalMap = Scheme.RationalMap.id X :=
    (id_compHom (𝟙 X)).symm.trans (compHom_id _)
  simp only [FanHom.algebraicMap_id, id_comp] at htor
  dsimp only [MarkedSurface.compEvaluation, MarkedSurface.withEvaluation]
  rw [p.evaluation_eq]
  simpa only [hidR, id_comp] using
    (comp_contractedXEvaluation_of_common_model b s c hΦ p.projection b (s ∘ σ) d hΦ
      (e.inv ≫ p.projection) (𝟙 _) e.hom (𝟙 _) (by simp) (renameX(σ)) (by
        simp only [he, Category.id_comp, htor, comp_compHom])).symm

private theorem marked_pullback_reindex
    (e : (A).1 ≅ (A').1)
    (hm : ∀ x : Pic[Φ,r], LineBundleClass.pullback e.hom
        (internalBlowupPicardMarking b (s ∘ σ) (centers(d)) hΦ
          (x.1, x.2 ∘ σ)).toMul =
        (internalBlowupPicardMarking b s (centers(c)) hΦ x).toMul)
    (x : L) :
    (internalBlowupPicardMarking b (s ∘ σ) (centers(d)) hΦ).symm
        (Additive.ofMul (LineBundleClass.pullback (e.inv ≫ p.projection)
          (M.picardMarking x).toMul)) = J' x := by
  apply (internalBlowupPicardMarking b (s ∘ σ) (centers(d)) hΦ).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  apply (LineBundleClass.pullbackEquiv e).injective
  simp only [LineBundleClass.pullbackEquiv_apply, toMul_ofMul,
    LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
    LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply]
  have hx := congrArg (fun y ↦
    (internalBlowupPicardMarking b s (centers(c)) hΦ y).toMul) (p.marked_pullback x)
  simp only [LinearEquiv.apply_symm_apply, toMul_ofMul] at hx
  simp only [LineBundleClass.pullback_comp, Iso.hom_inv_id_assoc]
  exact hx.trans (hm (J x)).symm

/-- A relabeling of the ordered model transports the contraction of the same marked pair.
It permutes the exceptional coordinates of the Picard inclusion and renames the X
evaluation. Centers may coincide if their relative order is preserved. -/
theorem ContractedToricFiber.exists_reindex (hc : centers(d) = centers(c) ∘ σ)
    (horder : ∀ a b, a < b → σ b < σ a →
      (s (σ a), centers(c) (σ a)) ≠ (s (σ b), centers(c) (σ b))) :
    ∃ (q : ContractedToricFiber b (s ∘ σ) hΦ T o J' d
      (M.compEvaluation (renameX(σ))))
      (e : (A).1 ≅ (A').1), q.projection = e.inv ≫ p.projection ∧
        q.boundaryMap = p.boundaryMap := by
  have h := exists_iso_internalBlowupPicardMarking_reindex b s (centers(c)) hΦ σ horder
  dsimp only at h
  rw [← hc] at h
  obtain ⟨e, he, hb, hm⟩ := h
  have hπ : e.inv ≫ π = π' := by rw [← he, Iso.inv_hom_id_assoc]
  have hβ : (A').2.boundaryι ≫ e.inv = (A).2.boundaryι := by
    rw [← hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hp : (e.inv ≫ p.projection) ≫ M.surface ↘ S =
      π' ≫ Φ.algebraicRealizationStructureMap := by
    rw [Category.assoc, p.projection_over, ← Category.assoc, hπ]
  have hB : p.boundaryMap ≫ M.pair.hom.left = (A').2.boundaryι ≫ e.inv ≫ p.projection := by
    rw [p.boundary_comp, ← Category.assoc, hβ]
  have hk : ((A).2.boundaryι.ker).comap e.inv = (A').2.boundaryι.ker := by
    rw [← hβ, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
  have hs : (M.pair.hom.left.ker.comap (e.inv ≫ p.projection)).support =
      (A').2.boundaryι.ker.support := by
    rw [comap_comp, Scheme.IdealSheafData.support_comap, p.support_comap,
      ← Scheme.IdealSheafData.support_comap, hk]
  exact ⟨{
    projection := e.inv ≫ p.projection
    modification := inferInstanceAs (IsModification (e.inv ≫ p.projection))
    projection_over := hp
    support_comap := hs
    boundaryMap := p.boundaryMap
    boundary_comp := hB
    boundary_over := p.boundary_over
    orientedSubdivision := p.orientedSubdivision
    component_zero := p.component_zero
    marked_pullback := fun x ↦ by
      have h := marked_pullback_reindex p σ e (fun y ↦ by
        simpa only [Prod.mk.eta] using hm y.1 y.2) x
      convert h using 1
      rw [MarkedSurface.compEvaluation_picardMarking]
      rfl
    evaluation_eq := evaluation_eq_reindex p σ hc e he
  }, e, rfl, rfl⟩

namespace GeometricRealization

local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "w[" E "," σ "]" => Quiver.Hom.toPath (Generator.toStep (Generator.permute σ) E)
local notation "χ(" c ")" => pointsEquiv ℂ (Fin r → ℤ)
  (Subtype.mk (CommaMorphism.left (c : Point Centers[r])) (Over.w (c : Point Centers[r])))

variable {E : SkewExchangeMatrix (Fin r)} (P : ChargeSeed E N)

local notation "w" => w[E,σ]
local notation "C" => Quiver.Path.centerPartialMap ℂ w P
local notation "src(" x ")" =>
  x ≫ Scheme.PartialMap.domainSource (X := Centers[r]) (Y := Centers[r]) C
local notation "dst(" x ")" =>
  x ≫ Scheme.PartialMap.domainTarget (X := Centers[r]) (Y := Centers[r]) C

private theorem permute_target_point (x : CenterPoint (U := Centers[r]) (V := Centers[r]) C) :
    dst(x) = src(x) ≫ ((w).centerIsoOver ℂ).hom := by
  ext : 1
  simp only [Over.comp_left, Scheme.PartialMap.domainTarget_left, Quiver.Path.centerPartialMap_hom,
    Scheme.PartialMap.domainSource_left, Quiver.Path.centerIsoOver_hom_left, Category.assoc]

private theorem permute_target_centers (x : CenterPoint (U := Centers[r]) (V := Centers[r]) C) :
    centers(χ(dst(x))) = centers(χ(src(x))) ∘ σ := by
  have h := Quiver.Path.pointsEquiv_symm_comp_centerIso_hom ℂ w χ(src(x))
  have heval (j : Fin r) :
      LinearEquiv.funCongrLeft ℤ ℤ σ.symm (Pi.single j 1) = Pi.single (σ j) 1 := by
    ext l
    simp [LinearEquiv.funCongrLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]
  rw [Quiver.Path.exponentEquiv_toPath, Step.exponentEquiv_permute] at h
  have hd : χ(dst(x)) =
      χ(src(x)).comp
        (LinearEquiv.funCongrLeft ℤ ℤ σ.symm).toAddEquiv.toAddMonoidHom.toMultiplicative := by
    apply (pointsEquiv ℂ (Fin r → ℤ)).symm.injective
    apply Subtype.ext
    simpa only [Equiv.symm_apply_apply, permute_target_point σ P x, Over.comp_left,
      Quiver.Path.centerIsoOver_hom_left] using h
  funext j
  simp only [hd, Function.comp_apply, MonoidHom.comp_apply, AddMonoidHom.coe_toMultiplicative,
    toAdd_ofAdd, AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv]
  exact congrArg (fun v : Fin r → ℤ ↦ χ(src(x)) (ofAdd v)) (heval j)

omit h₀ hpre in
private theorem permute_order_condition (hcharge : P.charge = rayChargeMap s)
    (x : CenterPoint (U := Centers[r]) (V := Centers[r]) C)
    (a b : Fin r) (hab : a < b) :
    (s (σ a), centers(χ(src(x))) (σ a)) ≠ (s (σ b), centers(χ(src(x))) (σ b)) := by
  let x₀ : S := default
  have hx : ((pointsEquiv ℂ (Fin r → ℤ)).symm χ(src(x))).val x₀ ∈ (w).centerOpen ℂ P := by
    have hi : (C).domain.ι (x.left x₀) ∈ (C).domain := (x.left x₀).property
    simpa only [Equiv.symm_apply_apply, Over.comp_left, Scheme.PartialMap.domainSource_left,
      Scheme.Hom.comp_apply, Quiver.Path.centerPartialMap_domain] using hi
  have hn := (Quiver.Path.point_mem_centerOpen_iff w P χ(src(x)) x₀).mp hx
    Quiver.Path.nil w (Quiver.Path.nil_comp _)
  intro h
  have hr : s (σ a) = s (σ b) := congrArg Prod.fst h
  have hc : P.charge (Pi.single (σ a) 1) = P.charge (Pi.single (σ b) 1) := by
    rw [hcharge, rayChargeMap_single, rayChargeMap_single, hr]
  apply hn (σ a) (σ b) (σ.injective.ne hab.ne)
  · simpa only [Quiver.Path.chargeTarget_nil] using hc
  · simpa only [Quiver.Path.exponentEquiv_nil, LinearEquiv.refl_apply] using congrArg Prod.snd h

variable (F : Point Centers[r] → MarkedSurface ℂ n B XTor[r])

local notation "G" => fun y ↦ MarkedSurface.compEvaluation
  (F (y ≫ CategoryTheory.Iso.inv (Quiver.Path.centerIsoOver ℂ w))) (renameX(σ))
local notation "Dₘ(" M ")" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

variable {U : (scheme ℂ (Fin r → ℤ)).Opens}

local notation "C'[" d "," le "]" => Scheme.PartialMap.restrict C U d le
local notation "src'[" d "," le "](" x ")" =>
  x ≫ Scheme.PartialMap.domainSource (X := Centers[r]) (Y := Centers[r]) (C'[d,le])
local notation "dst'[" d "," le "](" x ")" =>
  x ≫ Scheme.PartialMap.domainTarget (X := Centers[r]) (Y := Centers[r]) (C'[d,le])

/-- Start with the prescribed nodal contractions of a marked family at the source centers.
A label permutation realizes the independent X relabeling on any dense open of its
simultaneous center domain, with identity marked Picard pullback and branch action.
At every target center the same nodal tower presents the relabeled marked pair, with the
toric Picard coordinate fixed and all exceptional coordinates relabeled. -/
theorem exists_permute_contracted (hcharge : P.charge = rayChargeMap s)
    (hU : Dense (U : Set (scheme ℂ (Fin r → ℤ)))) (hle : U ≤ (C).domain)
    (hmodel : ∀ x : CenterPoint (U := Centers[r]) (V := Centers[r]) (C'[hU,hle]),
      ∃ p : ContractedToricFiber b s hΦ T o J χ(src'[hU,hle](x)) (F (src'[hU,hle](x))),
      ∃ (Y : Scheme) (l : ℕ) (Q : BlowupTower (F (src'[hU,hle](x))).surface l Y)
        (e : Y ≅ (model[s,χ(src'[hU,hle](x))]).1),
        IsNodalBoundaryTower Dₘ(F (src'[hU,hle](x))) ((F (src'[hU,hle](x))).surface ↘ S) (𝟙 _) Q ∧
        p.projection = e.inv ≫ Q.toBase) :
    ∃ R : GeometricRealization (T₀ := Centers[r]) (T₁ := Centers[r]) F (G) (C'[hU,hle])
        ((w).xRationalMap ℂ),
      R.picard = .refl B ∧ R.boundaryAction = 1 ∧
      ∀ x : CenterPoint (U := Centers[r]) (V := Centers[r]) (C'[hU,hle]),
        ∃ q : ContractedToricFiber b (s ∘ σ) hΦ T o J' χ(dst'[hU,hle](x)) ((G) (dst'[hU,hle](x))),
        ∃ (Y : Scheme) (l : ℕ) (Q : BlowupTower ((G) (dst'[hU,hle](x))).surface l Y)
          (e : Y ≅ (model[s ∘ σ,χ(dst'[hU,hle](x))]).1),
          IsNodalBoundaryTower Dₘ((G) (dst'[hU,hle](x)))
            (((G) (dst'[hU,hle](x))).surface ↘ S) (𝟙 _) Q ∧
          q.projection = e.inv ≫ Q.toBase := by
  let lift (x : CenterPoint (U := Centers[r]) (V := Centers[r]) (C'[hU,hle])) :
      CenterPoint (U := Centers[r]) (V := Centers[r]) C :=
    x ≫ (C).restrictDomainHom (X := Centers[r]) (Y := Centers[r]) U hU hle
  have hs (x) : src(lift x) = src'[hU,hle](x) := by
    simp only [lift, Category.assoc, Scheme.PartialMap.restrictDomainHom_source]
  have ht (x) : dst(lift x) = dst'[hU,hle](x) := by
    simp only [lift, Category.assoc, Scheme.PartialMap.restrictDomainHom_target]
  have hcenter (x : CenterPoint (U := Centers[r]) (V := Centers[r]) (C'[hU,hle])) :
      dst'[hU,hle](x) ≫ ((w).centerIsoOver ℂ).inv = src'[hU,hle](x) := by
    rw [← ht x, ← hs x, permute_target_point σ P (lift x), Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  refine ⟨{ picard := .refl B, boundaryAction := 1, fiber := ?_ }, rfl, rfl, ?_⟩
  · intro x
    rw [hcenter x, Quiver.Path.xRationalMap_permute]
    exact FiberRealization.compEvaluation (F (src'[hU,hle](x))) (renameX(σ))
  intro x
  dsimp only
  rw [hcenter x]
  obtain ⟨p, Y, l, Q, e, hQ, hp⟩ := hmodel x
  have hc : centers(χ(dst'[hU,hle](x))) = centers(χ(src'[hU,hle](x))) ∘ σ := by
    rw [← ht x, ← hs x]
    exact permute_target_centers σ P (lift x)
  obtain ⟨q, f, hq, -⟩ := p.exists_reindex σ hc (fun a b hab _ ↦ by
    rw [← hs x]
    exact permute_order_condition σ P hcharge (lift x) a b hab)
  have he := hq.trans (congrArg (f.inv ≫ ·) hp)
  exact ⟨q, Y, l, Q, e ≪≫ f, hQ, he.trans (Category.assoc _ _ _).symm⟩

end GeometricRealization

end QPainleve.SignedClusterModularGroup
