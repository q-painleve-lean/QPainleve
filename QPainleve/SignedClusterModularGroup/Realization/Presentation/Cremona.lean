/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Cremona
public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.PicardAction

import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Family
import QPainleve.SignedClusterModularGroup.Realization.Surjectivity.PicardAction

/-!
# Cluster modular groups and Cremona isometries

For a marked toric presentation of a primitive nef square-zero anticanonical
cycle without internal `(-2)` curves, Picard pullback maps the opposite signed
cluster modular group onto the Cremona isometry group. The projection is an
equivalence for at least three boundary components. With one or two components,
the signed equivalence also records the branch sign, and the unsigned group
maps isomorphically to the Cremona isometries.

The comparison combines `GeometricRealization.existsUnique_signedPicardEquiv_of_presentation`
with `MarkedSurface.cremonaPicardHom` and the boundary-size comparisons for that map.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData LineBundleClass

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}
  (Q : CompleteToricPresentation i b r L γ)
  {c : Point Centers[r]} {M₀ : MarkedSurface ℂ n B XTor[r]}

local instance instNonemptyCremonaCones : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instNeZeroCremonaBoundaryLength : NeZero Q.length := Q.neZero
local instance instPrestableCremonaBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) := Q.prestable

local notation "Models[" M "," C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b) (s := Q.rays)
    (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin) (ι := Q.inclusion) (P₁ := M)
    (fun z : Point Centers[r] ↦ χ[z]) C

local notation "Γ" => (ClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "Γs" => (SignedClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "incl" => MonoidHom.op (clusterModularGroupInclusion ℂ E)
local notation "Cr" => Chow.cremonaIsometryGroup ℂ M₀.surface
local notation "d" => M₀.boundaryClass M₀.isEffectiveCartier_boundaryIdeal

private theorem exists_unsignedEquiv_of_signedEquivProd
    {G : Type*} [Group G] (e : Γs ≃* G × ℤˣ)
    (hker : ((MonoidHom.snd G ℤˣ).comp e.toMonoidHom).ker.unop =
      (clusterModularGroupInclusion ℂ E).range) :
    ∃ e₀ : Γ ≃* G, ∀ x, e (incl x) = (e₀ x, 1) := by
  have hsign (x : Γ) : (e (incl x)).2 = 1 := by
    have hx : (incl x).unop ∈ (clusterModularGroupInclusion ℂ E).range := ⟨x.unop, rfl⟩
    rw [← hker] at hx
    exact MonoidHom.mem_ker.mp hx
  let f := (MonoidHom.fst G ℤˣ).comp (e.toMonoidHom.comp incl)
  have hinj : Function.Injective f := by
    intro x y hxy
    apply op_injective.comp ((clusterModularGroupInclusion_injective ℂ E).comp unop_injective)
    exact e.injective (Prod.ext hxy ((hsign x).trans (hsign y).symm))
  have hsurj : Function.Surjective f := by
    intro g
    let x := e.symm (g, 1)
    have hx : x.unop ∈ ((MonoidHom.snd G ℤˣ).comp e.toMonoidHom).ker.unop :=
      MonoidHom.mem_ker.mpr (by simp [x])
    rw [hker] at hx
    obtain ⟨y, hy⟩ := hx
    have hincl : incl (op y) = x := unop_injective hy
    exact ⟨op y, by simp [f, hincl, x]⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun x ↦ Prod.ext rfl (hsign x)⟩

/-- Picard pullback identifies the Cremona isometries of a marked reference fiber
without internal `(-2)` curves as a quotient of the opposite signed cluster modular
group. With at least three boundary components this projection is an equivalence.
With one or two components the projection and the branch sign give a product
equivalence, restricting to the Cremona equivalence on the unsigned subgroup. -/
theorem exists_cluster_cremona_equivs_of_nodal_model
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(M₀.isEffectiveCartier_boundaryIdeal)))
    (hnef : (classOf(M₀.isEffectiveCartier_boundaryIdeal)).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(M₀.isEffectiveCartier_boundaryIdeal)
      classOf(M₀.isEffectiveCartier_boundaryIdeal) = 0)
    (hroot : letI : SmoothOfRelativeDimension 2 (M₀.surface ↘ S) := M₀.smooth
      letI : M₀.surface.IsProjectiveOver ℂ := M₀.projective
      letI : IsNoetherian M₀.surface := isNoetherian_of_finiteType (M₀.surface ↘ S)
      letI := (M₀.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      ∀ x : CodimensionOnePoint M₀.surface, Disjoint (closure {(x : M₀.surface)}) D[M₀].support →
        let p := primeDivisorClass x
        Chow.classIntersectionNumber ℂ M₀.surface p p ≠ -2) :
    letI : SmoothOfRelativeDimension 2 (M₀.surface ↘ S) := M₀.smooth
    letI : M₀.surface.IsProjectiveOver ℂ := M₀.projective
    ∃ (M : Point Centers[r] → MarkedSurface ℂ n B XTor[r])
      (hD : ∀ z, D[M z].IsEffectiveCartier)
      (hmark : ∀ z j, (M z).boundaryClass (hD z) j = d j)
      (φ : Γs →* Cr) (η : Γs →* ℤˣ),
      M c = M₀ ∧ (∀ z, Q.HasNodalModel z (M z)) ∧ Function.Surjective φ ∧
      (∀ (w : Word E E),
        let x := op (signedClusterModularGroupMap ℂ E (End.of w))
        η x = (-1 : ℤˣ) ^ w.inversionCount ∧
        ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
          [C.IsOver Centers[r].hom Centers[r].hom]
          (R : GeometricRealization M M C (w.xRationalMap ℂ)), Models[M,C] →
          (φ x).val = M₀.marking.isometryGroupCongr
            (toIsometry B d (R.toSignedBoundaryIsometry d hD hmark))) ∧
      (3 ≤ n → ∃ e : Γs ≃* Cr, e.toMonoidHom = φ) ∧
      (n ≤ 2 → ∃ (e : Γs ≃* Cr × ℤˣ) (e₀ : Γ ≃* Cr),
        (∀ x, e x = (φ x, η x)) ∧ ∀ x, e (incl x) = (e₀ x, 1)) := by
  obtain ⟨M, hD, hM, hfamily⟩ :=
    Q.exists_marked_family_of_nodal_model href M₀.isEffectiveCartier_boundaryIdeal
  subst M₀
  let : SmoothOfRelativeDimension 2 ((M c).surface ↘ S) := (M c).smooth
  let : (M c).surface.IsProjectiveOver ℂ := (M c).projective
  let : IsRationalOver ((M c).surface ↘ S) := (hfamily c).1.isRationalOver
  have hcan := congrArg Inv.inv (href.canonicalClass (M c).isEffectiveCartier_boundaryIdeal)
  let P : ChargeSeed E N :=
    ⟨b.detDualEquiv.toLinearMap, Fan.rayChargeMap Q.rays, b.detDualEquiv_self, hE.symm⟩
  have hmark (z : Point Centers[r]) (j : ZMod n) := congrFun (hfamily z).2 j
  obtain ⟨Θ, ⟨hΘ, hker⟩, -⟩ := existsUnique_signedPicardEquiv_of_presentation
    (Q := Q) (hD := hD) (hmark := hmark) P rfl rfl (fun z _ ↦ (hfamily z).1)
    (hfamily c).1 hprim hnef hsq
  let π := (M c).cremonaPicardHom hcan hnef hsq hroot
  refine ⟨M, hD, hmark, π.comp Θ.toMonoidHom, (sign B _).comp Θ.toMonoidHom,
    rfl, fun z ↦ (hfamily z).1,
    ((M c).cremonaPicardHom_surjective hcan hnef hsq hroot).comp Θ.surjective, ?_, ?_, ?_⟩
  · intro w
    refine ⟨(hΘ w).1, fun R hR ↦ ?_⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, (hΘ w).2 R hR]
    exact (M c).cremonaPicardHom_apply hcan hnef hsq hroot _
  · intro hn
    refine ⟨Θ.trans ((M c).signedBoundaryIsometryEquivCremona hcan hnef hsq hroot hn), ?_⟩
    apply MonoidHom.ext
    intro x
    exact (M c).signedBoundaryIsometryEquivCremona_apply hcan hnef hsq hroot hn (Θ x)
  · intro hn
    let e := Θ.trans ((M c).signedBoundaryIsometryEquivCremonaProd hcan hnef hsq hroot hn)
    have he (x : Γs) : e x = (π (Θ x), sign B _ (Θ x)) :=
      (M c).signedBoundaryIsometryEquivCremonaProd_apply hcan hnef hsq hroot hn (Θ x)
    have hs : (MonoidHom.snd _ ℤˣ).comp e.toMonoidHom =
        (sign B _).comp Θ.toMonoidHom := MonoidHom.ext fun x ↦ congrArg Prod.snd (he x)
    have hk : ((MonoidHom.snd _ ℤˣ).comp e.toMonoidHom).ker.unop =
        (clusterModularGroupInclusion ℂ E).range := hs ▸ hker
    obtain ⟨e₀, he₀⟩ := exists_unsignedEquiv_of_signedEquivProd e hk
    exact ⟨e, e₀, he, he₀⟩

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
