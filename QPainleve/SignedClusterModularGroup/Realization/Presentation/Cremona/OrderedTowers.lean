/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Cremona
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Identification

import QPainleve.Geometry.Toric.Fan.Presentation.Canonical
import QPainleve.SignedClusterModularGroup.Boundary.Cremona

/-!
# Cremona isometries from ordered toric presentations

For an ordered toric presentation of a primitive nef square-zero anticanonical
cycle without internal `(-2)` curves, Picard pullback projects the opposite
signed cluster modular group onto the Cremona isometries of the original
surface. The group identification
`exists_picardGroupEquivs_of_toric_presentation` fixes the original Picard
lattice, and `BoundaryCycle.exists_cremonaProjection_of_numbering`
identifies the image. With one or two boundary components, the signed group
retains the branch sign and the unsigned group identifies with the Cremona group.
-/

public section

open AlgebraicGeometry CategoryTheory Module MulOpposite Quiver
open QPainleve.BlowupTower QPainleve.CharacterTorus QPainleve.Cluster
open QPainleve.SignedBoundaryIsometryGroup
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "δ[" h "]" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "parameters[" c "]" => (fun j ↦ χ[c] (Multiplicative.ofAdd (Pi.single j 1)))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {Φ : Fan i}
  {X W : Scheme} [X.Over S] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [Scheme.IsRationalOver (X ↘ S)]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
  {n r k : ℕ} [NeZero n] {T : BlowupTower X k W}

local instance instIntegralOrderedCremona : IsIntegral X := by
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  exact Scheme.IsRationalOver.isIntegral_of_smooth (f := X ↘ S) inferInstance

local notation "Pic" => Additive (LineBundleClass X)
local notation "L" => (Fin (Module.finrank ℤ Pic) → ℤ)
local notation "B" => Chow.intersectionBilinForm ℂ X
local notation "Cr" => Chow.cremonaIsometryGroup ℂ X
local notation "classes[" A "," hD "]" =>
  (fun j ↦ Additive.ofMul (LineBundleClass.primeDivisorClass
    (D.boundaryPrimeEmbedding (Scheme.NodalCycleNumbering.boundaryPrimeEquiv A hD j))))

local notation "Models[" b₀ "," Q "," M "," C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b₀)
    (s := CompleteToricPresentation.rays Q)
    (hΦ := CompleteToricPresentation.regular Q) (T := CompleteToricPresentation.cycle Q)
    (origin := CompleteToricPresentation.origin Q) (ι := CompleteToricPresentation.inclusion Q)
    (P₁ := M) (fun z : Point Centers[r] ↦ χ[z]) C

local notation "Γ[" E "]" => (ClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "Γs[" E "]" => (SignedClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "incl[" E "]" => MonoidHom.op (clusterModularGroupInclusion ℂ E)

/-- The opposite signed cluster modular group of specified ordered toric and
nodal blowup towers projects onto the Cremona isometries of the original surface
without internal `(-2)` curves.
For at least three boundary components the projection is an equivalence. For
one or two components the projection and the sign form a product equivalence,
with the unsigned group mapping isomorphically to the Cremona factor. On loops
the maps evaluate by the realized Picard pullback and inversion sign. -/
theorem exists_cluster_cremona_equivs_of_toric_presentation
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (s : Fin r → Φ.Ray) (u : Fin r → ℂˣ)
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (e : (Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b s u).1 ≅ W)
    (hbase : e.hom ≫ T.toBase ≫ (X ↘ S) =
      (Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b s u).2.toTower.toBase ≫
        Φ.algebraicRealizationStructureMap)
    (hker : ((D.comap T.toBase).radical).comap e.hom =
      (Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b s u).2.boundaryι.ker)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (hD : D.IsEffectiveCartier)
    (hprim : IsPrimitive (Additive.ofMul δ[hD])) (hnef : δ[hD].IsNef ℂ (X ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ X δ[hD] δ[hD] = 0) :
    letI : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    letI := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (∀ p : CodimensionOnePoint X, Disjoint (closure {(p : X)}) D.support →
      Chow.classIntersectionNumber ℂ X (LineBundleClass.primeDivisorClass p)
        (LineBundleClass.primeDivisorClass p) ≠ -2) →
    ∃ (H : LinearMap.BilinForm ℤ L) (μ : H.IsometryEquiv B)
      (b' : Basis (Fin 2) ℤ N) (Q : CompleteToricPresentation i b' r L Empty),
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    ∃ (c : Point Centers[r]) (f : X ⤏ XTor[r]) (E : SkewExchangeMatrix (Fin r))
      (M : Point Centers[r] → MarkedSurface ℂ n H XTor[r])
      (φ : Γs[E] →* Cr) (η : Γs[E] →* ℤˣ),
      ((b' = b ∧ parameters[c] = u) ∨
        (b' = b.reindex (Equiv.swap 0 1) ∧ parameters[c] = u⁻¹)) ∧
      (∃ hfan : Q.fan = Φ, hfan ▸ Q.rays = s) ∧
      E.matrix = chargeExchangeMatrix b'.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays) ∧
      M c = MarkedSurface.ofBoundary D A μ f ∧ (∀ z, Q.HasNodalModel z (M z)) ∧
      Function.Surjective φ ∧
      (∀ (w : Word E E),
        let x := op (signedClusterModularGroupMap ℂ E (End.of w))
        η x = (-1 : ℤˣ) ^ w.inversionCount ∧
        ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
          [C.IsOver Centers[r].hom Centers[r].hom]
          (R : GeometricRealization M M C (w.xRationalMap ℂ)), Models[b',Q,M,C] →
          ((φ x).val, η x) =
            (μ.isometryGroupCongr (H.isometryGroupEquivIsometryEquiv.symm R.picard),
              R.orientation)) ∧
      η.ker.unop = (clusterModularGroupInclusion ℂ E).range ∧
      (3 ≤ n → ∃ g : Γs[E] ≃* Cr, g.toMonoidHom = φ) ∧
      (n ≤ 2 → ∃ (g : Γs[E] ≃* Cr × ℤˣ) (g₀ : Γ[E] ≃* Cr),
        (∀ x, g x = (φ x, η x)) ∧ ∀ x, g (incl[E] x) = (g₀ x, 1)) := by
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  intro hroot
  have hP : D.HasToricPresentation (X ↘ S) b i :=
    (hasToricPresentation_iff ..).mpr ⟨Φ, hΦ, hc, r, s, u, k, W, T, hT, e, hbase, hker⟩
  have hK := hP.canonicalClass hD (by
    rw [← over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne)
  obtain ⟨π, hπ, hsurj, hinj, hsmall⟩ :=
    BoundaryCycle.exists_cremonaProjection_of_numbering ℂ A hD hK hnef hsq hroot
  obtain ⟨P, hframe, hrays⟩ :=
    exists_picardGroupEquivs_of_toric_presentation hΦ hc s u hT e hbase hker A hD hprim hnef hsq
  let d := classes[A,hD]
  let Θ := P.signedEquiv
  let φ := π.comp Θ.toMonoidHom
  let η := (sign B d).comp Θ.toMonoidHom
  refine ⟨P.form, P.marking, P.basis, P.presentation, P.center, P.evaluation, P.exchangeMatrix,
    P.family, φ, η, hframe, hrays, P.matrix_eq, P.family_center, P.hasNodalModel,
    hsurj.comp Θ.surjective, ?_, P.sign_ker_unop, ?_, ?_⟩
  · intro w
    refine ⟨?_, fun R hR ↦ ?_⟩
    · simpa only [η, Θ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        SignedBoundaryIsometryGroup.sign_apply] using P.sign_signedEquiv_apply_word w
    · simpa only [φ, η, Θ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hπ, toIsometry_apply,
        SignedBoundaryIsometryGroup.sign_apply, Prod.eta] using P.signedEquiv_apply_word w R hR
  · intro hn
    exact ⟨MulEquiv.ofBijective φ ⟨(hinj hn).comp Θ.injective, hsurj.comp Θ.surjective⟩, rfl⟩
  · intro hn
    obtain ⟨g₀, hg₀⟩ := hsmall hn
    let p := mulEquivProdOfLeTwo B d hn
    let g := Θ.trans (p.trans (g₀.prodCongr (MulEquiv.refl ℤˣ)))
    have hg (x : Γs[P.exchangeMatrix]) : g x = (φ x, η x) := by
      have hx : ((p (Θ x)).1.val, (p (Θ x)).2) = (Θ x).val :=
        coe_mulEquivProdOfLeTwo_apply B d hn (Θ x)
      simp only [g, MulEquiv.trans_apply, MulEquiv.prodCongr_apply, MulEquiv.refl_apply]
      refine Prod.ext ((hg₀ _).trans (Subtype.ext ?_)) ?_
      · simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hπ, toIsometry_apply,
          coe_rotationInclusion]
        exact congrArg Prod.fst hx
      · simpa only [η, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          SignedBoundaryIsometryGroup.sign_apply] using congrArg Prod.snd hx
    refine ⟨g, P.unsignedEquiv.trans g₀, hg, fun x ↦ ?_⟩
    rw [hg]
    have hx := (P.rotationInclusion_unsignedEquiv_apply x).symm
    refine Prod.ext ((congrArg π hx).trans (hg₀ _).symm) ?_
    exact (congrArg (sign B d) hx).trans (by
      simp only [SignedBoundaryIsometryGroup.sign_apply, coe_rotationInclusion])

end QPainleve.SignedClusterModularGroup
