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
import QPainleve.SignedClusterModularGroup.BoundaryCycle
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Cremona isometries from ordered toric presentations

For an ordered toric presentation of a primitive nef square-zero anticanonical
cycle without internal `(-2)` curves, Picard pullback projects the opposite
signed cluster modular group onto the Cremona isometries of the original
surface. The group identification
`exists_picardGroupEquivs_of_toric_presentation` fixes the original Picard
lattice, and `BoundaryCycle.range_toIsometry_eq_cremonaIsometryGroup_of_cycle_gram`
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

private theorem exists_cremonaProjection {d : ZMod n → Pic}
    (hrange : (toIsometry B d).range = Cr)
    (hinj : 3 ≤ n → Function.Injective d) :
    ∃ π : signedBoundaryIsometryGroup B d →* Cr,
      (∀ x, (π x).val = toIsometry B d x) ∧ Function.Surjective π ∧
      (3 ≤ n → Function.Injective π) ∧
      (n ≤ 2 → ∃ e : boundaryRotationGroup B d ≃* Cr,
        ∀ x, e x = π (rotationInclusion B d x)) := by
  let f := toIsometry B d
  let π := (MulEquiv.subgroupCongr hrange).toMonoidHom.comp f.rangeRestrict
  have hπ (x : signedBoundaryIsometryGroup B d) : (π x).val = f x := by
    simp only [π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.subgroupCongr_apply, MonoidHom.coe_rangeRestrict]
  have hsurj : Function.Surjective π :=
    (MulEquiv.subgroupCongr hrange).surjective.comp f.rangeRestrict_surjective
  refine ⟨π, hπ, hsurj, fun hn x y h ↦ ?_, fun hn ↦ ?_⟩
  · apply toIsometry_injective B d hn (hinj hn)
    simpa only [hπ] using congrArg Subtype.val h
  · have hrot : boundaryRotationGroup B d = Cr := by
      rw [← hrange]
      ext g
      constructor
      · intro hg
        exact ⟨rotationInclusion B d ⟨g, hg⟩, by
          simp only [toIsometry_apply, coe_rotationInclusion]⟩
      · rintro ⟨x, rfl⟩
        let y := mulEquivProdOfLeTwo B d hn x
        have hy : y.1.val = x.val.1 :=
          congrArg Prod.fst (coe_mulEquivProdOfLeTwo_apply B d hn x)
        rw [toIsometry_apply, ← hy]
        exact y.1.property
    refine ⟨MulEquiv.subgroupCongr hrot, fun x ↦ Subtype.ext ?_⟩
    rw [MulEquiv.subgroupCongr_apply, hπ, toIsometry_apply, coe_rotationInclusion]

private theorem exists_cremonaProjection_of_numbering
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (hD : D.IsEffectiveCartier)
    (hK : LineBundleClass.mk hD.toInvertibleSheaf =
      LineBundleClass.mk (canonicalBundle ℂ X 2))
    (hnef : δ[hD].IsNef ℂ (X ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ X δ[hD] δ[hD] = 0) :
    letI : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    letI := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let d := classes[A,hD]
    (∀ p : CodimensionOnePoint X, Disjoint (closure {(p : X)}) D.support →
      Chow.classIntersectionNumber ℂ X (LineBundleClass.primeDivisorClass p)
        (LineBundleClass.primeDivisorClass p) ≠ -2) →
    ∃ π : signedBoundaryIsometryGroup B d →* Cr,
      (∀ x, (π x).val = toIsometry B d x) ∧ Function.Surjective π ∧
      (3 ≤ n → Function.Injective π) ∧
      (n ≤ 2 → ∃ e : boundaryRotationGroup B d ≃* Cr,
        ∀ x, e x = π (rotationInclusion B d x)) := by
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  dsimp only
  intro hroot
  let p := (A.boundaryPrimeEquiv hD).toEmbedding.trans D.boundaryPrimeEmbedding
  have hp (q : CodimensionOnePoint X) : (q : X) ∈ D.support ↔ q ∈ Set.range p := by
    have hprimes : Set.range p = Set.range D.boundaryPrimeEmbedding :=
      (A.boundaryPrimeEquiv hD).surjective.range_comp _
    rw [hprimes, range_boundaryPrimeEmbedding]
    rfl
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subscheme ↘ S) :=
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  let : IsReduced D.subscheme := hN.isReduced
  have hgram := BoundaryCycle.intersectionBilinForm_eq_of_nodal_cycle hD hN hnef hsq p
    ⟨A.ambientNode, A.ambientNode_injective⟩ hp
    (fun _ _ hij ↦ by
      simpa only [p, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
        coe_boundaryPrimeEmbedding, Function.Embedding.coeFn_mk] using
        A.closure_boundaryPrime_inter_of_ne hD hij)
  have hrange := BoundaryCycle.range_toIsometry_eq_cremonaIsometryGroup_of_cycle_gram
    ℂ hD p hp hK (hK ▸ hnef) (hK ▸ hsq) hgram hroot
  exact exists_cremonaProjection hrange
    (fun hn ↦ BoundaryCycle.injective_of_cycle_gram B _ hgram (by omega))

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
    exists_cremonaProjection_of_numbering A hD hK hnef hsq hroot
  obtain ⟨H, μ, b', Q, c, f, E, M, _, Θ, Θrot, hframe, hrays, hE, hM, hmodels, _,
    hwords, hkerSign, hrot⟩ :=
    exists_picardGroupEquivs_of_toric_presentation hΦ hc s u hT e hbase hker A hD hprim hnef hsq
  let d := classes[A,hD]
  let φ := π.comp Θ.toMonoidHom
  let η := (sign B d).comp Θ.toMonoidHom
  refine ⟨H, μ, b', Q, c, f, E, M, φ, η, hframe, hrays, hE, hM, hmodels,
    hsurj.comp Θ.surjective, ?_, hkerSign, ?_, ?_⟩
  · intro w
    refine ⟨(hwords w).1, fun R hR ↦ ?_⟩
    simpa only [φ, η, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hπ, toIsometry_apply,
      SignedBoundaryIsometryGroup.sign_apply, Prod.eta] using (hwords w).2 R hR
  · intro hn
    exact ⟨MulEquiv.ofBijective φ ⟨(hinj hn).comp Θ.injective, hsurj.comp Θ.surjective⟩, rfl⟩
  · intro hn
    obtain ⟨g₀, hg₀⟩ := hsmall hn
    let p := mulEquivProdOfLeTwo B d hn
    let g := Θ.trans (p.trans (g₀.prodCongr (MulEquiv.refl ℤˣ)))
    have hg (x : Γs[E]) : g x = (φ x, η x) := by
      have hx : ((p (Θ x)).1.val, (p (Θ x)).2) = (Θ x).val :=
        coe_mulEquivProdOfLeTwo_apply B d hn (Θ x)
      simp only [g, MulEquiv.trans_apply, MulEquiv.prodCongr_apply, MulEquiv.refl_apply]
      refine Prod.ext ((hg₀ _).trans (Subtype.ext ?_)) ?_
      · simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hπ, toIsometry_apply,
          coe_rotationInclusion]
        exact congrArg Prod.fst hx
      · simpa only [η, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          SignedBoundaryIsometryGroup.sign_apply] using congrArg Prod.snd hx
    refine ⟨g, Θrot.trans g₀, hg, fun x ↦ ?_⟩
    rw [hg]
    refine Prod.ext ((congrArg π (hrot x).symm).trans (hg₀ _).symm) ?_
    exact (congrArg (sign B d) (hrot x).symm).trans (by
      simp only [SignedBoundaryIsometryGroup.sign_apply, coe_rotationInclusion])

end QPainleve.SignedClusterModularGroup
