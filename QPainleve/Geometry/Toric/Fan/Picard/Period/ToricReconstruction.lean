/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.CommonPresentation
public import QPainleve.Geometry.Toric.Fan.Picard.Period.SignedReconstruction

import QPainleve.Geometry.Toric.Fan.Boundary.CycleAction
import QPainleve.Geometry.Toric.Fan.Boundary.NumberedPrime
import QPainleve.Geometry.Toric.Fan.Equiv

/-!
# Reconstruction from signed periods in different toric presentations

Matching the ordered exceptional classes and strict boundary classes identifies the
fans of two ordered presentations. The resulting lift gives common Picard coordinates
for period reconstruction and transports the ordered branches of the toric boundary.
The descended isomorphism realizes the given Picard pullback and the signed boundary
action on the original surfaces.

This is the reconstruction after the exceptional contractions in the proof of
[Gross, Hacking and Keel, Theorem 1.8](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open Scheme (NodalCycleNumbering)

namespace TauCeti.Toric.Fan

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  [h₀ : Nonempty Φ.cones] [h₁ : Nonempty Ψ.cones]
  (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
  (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
  {r : ℕ} (s : Fin r → Φ.Ray) (s' : Fin r → Ψ.Ray)
  (c d : Multiplicative (Fin r → ℤ) →* k₀ˣ)

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Btor[" coeff "," f "]" => Scheme.IdealSheafData.subscheme
  (Fan.toricBoundaryIdeal coeff f inferInstance)
local notation "center" a:arg => (fun j : Fin r ↦ a (ofAdd (Pi.single j 1)))
local notation "M" a:arg => internalBlowupTower k₀ b s (center a)
local notation "M'" => internalBlowupTower k₀ b' s' (center d)
local notation "π" a:arg => toBase (WithBoundary.toTower (Sigma.snd (M a)))
local notation "π'" => toBase (WithBoundary.toTower (Sigma.snd M'))
local notation "ι" a:arg => WithBoundary.boundaryι (Sigma.snd (M a))
local notation "ι'" => WithBoundary.boundaryι (Sigma.snd M')
local notation "mark" a:arg => internalBlowupPicardMarking k₀ b s (center a) hΦ
local notation "prime[" a "]" => internalBlowupBoundaryPrimeEquiv k₀ hΦ b s (center a)
local notation "base" f:arg => Fan.finiteFanSchemeToSpec k₀ f
local notation "rankTwo(" a ")" => Eq.trans (Module.finrank_eq_card_basis a) (Fintype.card_fin 2)
local notation "strict[" h ", " a ", " t ", " z "]" =>
  strictRayBoundaryClass k₀ h rankTwo(a) (WithBoundary.toTower (Sigma.snd
    (internalBlowupTower k₀ a t z))) (isClosedPointTower_internalBlowupTower k₀ a t z)
local notation "B(" coeff "," X ")" => Chow.intersectionBilinForm coeff X

variable [PrestableFamily (Btor[k₀,Φ] ↘ Spec (.of k₀))] [PrestableFamily (Btor[k₀,Ψ] ↘ Spec
  (.of k₀))]
  {m : ℕ} [NeZero m] {γ δ : Type*}
  {a : γ → (Btor[k₀,Φ] ↘ Spec (.of k₀)).smoothLocus} {a' : δ →
    (Btor[k₀,Ψ] ↘ Spec (.of k₀)).smoothLocus}
  (C : NodalCycleNumbering a m) (C' : NodalCycleNumbering a' m)
  {u : ZMod m ≃ Φ.Ray} {v : ZMod m ≃ Ψ.Ray}
  (hv : ∀ j, b'.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
    ∃ σ : Ψ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)
  (hC : ∀ j, C.component j = Φ.boundaryNormalizationComponentEquiv k₀ hΦ (u j))
  (hC' : ∀ j, C'.component j = Ψ.boundaryNormalizationComponentEquiv k₀ hΨ (v j))

variable {X Y W Z : Scheme} [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₀))]
  [IsIntegral X] [IsIntegral Y] [X.IsProjectiveOver k₀] [Y.IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))] [SmoothOfRelativeDimension 2 (Y ↘ Spec
    (.of k₀))]
  [(Φ.finiteFanScheme k₀).IsProjectiveOver k₀] [(Ψ.finiteFanScheme k₀).IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme k₀) ↘ Spec (.of k₀))]
  [LinearMap.IsPerfPair B(k₀,X)] [LinearMap.IsPerfPair B(k₀,Y)]
  [LinearMap.IsPerfPair
    (B(k₀,(Φ.finiteFanScheme k₀)).prod (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ
      (Fin r → ℤ))))]
  {D : X.IdealSheafData} {E : Y.IdealSheafData}
  {l l' : ℕ} {T : BlowupTower X l W} {U : BlowupTower Y l' Z}
  (e : W ≅ (internalBlowupTower k₀ b s (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))).1)
  (e' : Z ≅ (internalBlowupTower k₀ b' s' (fun j : Fin r ↦ d (ofAdd (Pi.single j 1)))).1)

local notation "p" => (Iso.inv e ≫ toBase T)
local notation "q" => (Iso.inv e' ≫ toBase U)

variable [PrestableFamily (D.subscheme ↘ Spec (.of k₀))] [PrestableFamily (E.subscheme ↘ Spec
  (.of k₀))]
  {n : ℕ} [NeZero n] {α β : Type*}
  {a₀ : α → (D.subscheme ↘ Spec (.of k₀)).smoothLocus} {a₁ : β →
    (E.subscheme ↘ Spec (.of k₀)).smoothLocus}
  (A : NodalCycleNumbering a₀ n) (A' : NodalCycleNumbering a₁ n)

include hv hC hC' in
/-- Reconstruct a pair isomorphism with a prescribed Picard pullback and signed
action on the numbered branches. The nodal refinements may have different ordered
toric models. A compatible isometry of the auxiliary Picard groups matches the
strict ray classes and total internal exceptional classes. A corresponding pair of
surviving rays specifies the image of component zero. -/
theorem exists_iso_of_signed_boundary_period_of_toric_presentations
    (hc : Φ.IsComplete) (hc' : Ψ.IsComplete)
    (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
    (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
      (Φ.toricBoundaryIdeal k₀ h₀).subschemeι ((Btor[k₀,Φ]).dualGraphEdgeEquiv (K := k₀) a
        (C.edge j)).val =
        (Φ.distinguishedSection (R := k₀) σ) (IsLocalRing.closedPoint k₀))
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (hU : IsNodalBoundaryTower E (Y ↘ S) (𝟙 Y) U)
    (hp : p ≫ (X ↘ S) = π c ≫ base Φ) (hq : q ≫ (Y ↘ S) = π' ≫ base Ψ)
    (hD : (D.comap p).support = (ι c).ker.support)
    (hE : (E.comap q).support = (ι').ker.support)
    (G : B(k₀,Y).IsometryEquiv B(k₀,X))
    (Gaux :
      letI : (M c).1.Over S := ⟨π c ≫ ((Φ.finiteFanScheme k₀) ↘ S)⟩
      letI : (M').1.Over S := ⟨π' ≫ ((Ψ.finiteFanScheme k₀) ↘ S)⟩
      letI : (M c).1.IsProjectiveOver k₀ := (M c).2.toTower.isProjectiveOver k₀
      letI : (M').1.IsProjectiveOver k₀ := (M').2.toTower.isProjectiveOver k₀
      letI := isIntegral_internalBlowupTower k₀ b s (center c) hΦ
      letI := isIntegral_internalBlowupTower k₀ b' s' (center d) hΨ
      letI : SmoothOfRelativeDimension 2 ((M c).1 ↘ S) :=
        smoothOfRelativeDimension_internalBlowupTower k₀ b s (center c) hΦ
      letI : SmoothOfRelativeDimension 2 ((M').1 ↘ S) :=
        smoothOfRelativeDimension_internalBlowupTower k₀ b' s' (center d) hΨ
      B(k₀,(M').1).IsometryEquiv B(k₀,(M c).1))
    (hPic : ∀ L : LineBundleClass Y,
      Gaux (Additive.ofMul (pullback q L)) =
        Additive.ofMul (pullback p (G (Additive.ofMul L)).toMul))
    (hExc : ∀ j, Gaux (Additive.ofMul ((M').2.toTower.exceptionalClass j)) =
      Additive.ofMul ((M c).2.toTower.exceptionalClass j))
    (hStrict : ∀ j, Gaux (strict[hΨ, b', s', center d] (v j)) =
      strict[hΦ, b, s, center c] (u j))
    {f : Btor[k₀,Φ] ⟶ D.subscheme} {g : Btor[k₀,Ψ] ⟶ E.subscheme} [f.IsOver S] [g.IsOver S]
    (hf : f ≫ D.subschemeι = ι c ≫ p) (hg : g ≫ E.subschemeι = ι' ≫ q)
    (hfs : f.IsOrientedCycleSubdivision C A) (act : DihedralGroup n)
    (hgs : g.IsOrientedCycleSubdivision C'
      (if DihedralGroup.cycleOrientationSign act = -1 then A'.reverse else A'))
    (hCartierD : D.IsEffectiveCartier) (hCartierE : E.IsEffectiveCartier)
    (gD : ∀ w : irreducibleComponents (D.subscheme.singularLocus k₀).blowup,
      (D.subscheme.blowupComponent (K := k₀) w).toScheme.genus k₀ = 0)
    (gE : ∀ w : irreducibleComponents (E.subscheme.singularLocus k₀).blowup,
      (E.subscheme.blowupComponent (K := k₀) w).toScheme.genus k₀ = 0)
    (hOrth : ∀ x : E.boundaryOrthogonal k₀, G x.val ∈ D.boundaryOrthogonal k₀)
    (hperiod : ∀ x : E.boundaryOrthogonal k₀,
      hCartierE.boundaryPeriod gE A'.endpoint_eq (ofAdd x) =
        hCartierD.boundaryPeriod gD A.endpoint_eq (ofAdd ⟨G x.val, hOrth x⟩) ^
          (DihedralGroup.cycleOrientationSign act : ℤ))
    (j : ZMod m)
    (hj : f (C.componentGenericPoint j) = A.componentGenericPoint 0)
    (hj' : g (C'.componentGenericPoint j) =
      A'.componentGenericPoint (DihedralGroup.cycleVertexPerm act 0)) :
    Nonempty (SignedTorelliPairIso (D := D) (E := E) A A'
      (fun L ↦ (G (Additive.ofMul L)).toMul) act) := by
  have hu j := And.intro (hdet j) ((hnodes j).imp fun _ h ↦ And.intro h.1 h.2.1)
  obtain ⟨F, ⟨hF, -, t, ht, htB, hmark⟩, -⟩ :=
    exists_common_toric_presentation_of_picard_isometry k₀ b b' s s' (center c) (center d)
      hΦ hΨ hc hc' u v hu hv Gaux hExc hStrict
  let e'' := e' ≪≫ t.symm
  let q' := e''.inv ≫ U.toBase
  let boundaryIso := F.boundaryIso k₀ h₀ h₁
  let g' := boundaryIso.hom ≫ g
  have heq : q' = t.hom ≫ q := by simp only [e'', q', Iso.trans_inv, Iso.symm_inv, Category.assoc]
  have hq' : q' ≫ (Y ↘ S) = π d ≫ base Φ := by
    rw [heq, Category.assoc, hq, ht.hom_toBase_assoc, FanEquiv.finiteFanSchemeIso_hom,
      FanHom.finiteFanSchemeHom_comp_finiteFanSchemeToSpec]
  have hE' : (E.comap q').support = (ι d).ker.support := by
    have htker : (ι').ker.comap t.hom = (ι d).ker := by
      rw [← Scheme.Hom.ker_comp_of_isIso boundaryIso.hom, ← htB,
        Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
    rw [heq, comap_comp, support_comap, hE, ← support_comap, htker]
  have hg' : g' ≫ E.subschemeι = ι d ≫ q' := by
    dsimp only [g', boundaryIso]
    rw [heq, Category.assoc, hg, ← reassoc_of% htB]
  have hdetF := F.detDualEquiv_of_matching_adjacent_rays b b' hΦ (hF 0) (hF (0 + 1))
    (hdet 0) (hv 0).1 (hu 0).2
  have hsign := F.cycleOrientationSign_boundaryIso k₀ hΦ hΨ C C' hC hC' b b'
    hdet (fun j ↦ (hv j).1) false hdetF
  have hsub := boundaryIso.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one C C' hsign
  -- Read the same numbered component on both sides of the toric boundary isomorphism.
  have hjF := v.injective ((F.boundaryIso_cycleVertexPerm k₀ hΦ hΨ C C' hC hC' j).trans (hF j))
  have hjg : g' (C.componentGenericPoint j) =
      A'.componentGenericPoint (DihedralGroup.cycleVertexPerm act 0) := by
    dsimp only [g']
    rw [Scheme.Hom.comp_apply, boundaryIso.apply_componentGenericPoint C C', hjF, hj']
  have primeAt (z : Multiplicative (Fin r → ℤ) →* k₀ˣ) :
      (prime[z] (u j)).val = (ι z) (C.componentGenericPoint j) := by
    rw [internalBlowupBoundaryPrime_val, C.componentGenericPoint_def, hC]
  have hj₀ : p (prime[c] (u j)).val = D.subschemeι (A.componentGenericPoint 0) := by
    rw [primeAt, ← Scheme.Hom.comp_apply, ← hf, Scheme.Hom.comp_apply, hj]
  have hj₁ : q' (prime[d] (u j)).val =
      E.subschemeι (A'.componentGenericPoint (DihedralGroup.cycleVertexPerm act 0)) := by
    rw [primeAt, ← Scheme.Hom.comp_apply, ← hg', Scheme.Hom.comp_apply, hjg]
  let picardMap := fun L : LineBundleClass Y ↦ (G (Additive.ofMul L)).toMul
  have hL := Additive.toMul.surjective.comp (G.surjective.comp Additive.ofMul.surjective)
  have hmark' (L' : LineBundleClass Y) :
      (mark c).symm (Additive.ofMul (pullback p (picardMap L'))) =
        (mark d).symm (Additive.ofMul (pullback q' L')) := by
    rw [heq, ← pullback_comp t.hom q]
    exact (congrArg (mark c).symm (hPic L').symm).trans (hmark (pullback q L'))
  exact exists_iso_of_signed_boundary_period_of_matching_picard_markings k₀ hΦ b s c d e e'' A A' C
    hc u (fun j ↦ by simpa only [NodalCycleNumbering.component_apply] using hC j)
    hdet hnodes hT hU hp hq' hD hE' picardMap hL hmark'
    hf hg' hfs act (hsub.comp hgs) hCartierD hCartierE gD gE hOrth hperiod (u j) hj₀ hj₁

end TauCeti.Toric.Fan
