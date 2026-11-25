/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Numbering
public import QPainleve.Geometry.Toric.Fan.Picard.Period.ToricReconstruction

import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.Geometry.Toric.Fan.Picard.Orthogonal
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import TauCeti.Algebra.Group.FreeAbelianCharacter

/-!
# Signed period reconstruction from internal contractions

After transporting an exceptional configuration, the two auxiliary surfaces are
given as contractions to toric pairs. Their numbered boundaries and labeled
exceptional classes determine the compatible toric presentations used in signed
period reconstruction.

This is the reconstruction after the exceptional contractions in the proof of
[Gross, Hacking and Keel, Theorem 1.8](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve QPainleve.BlowupTower
open TauCeti TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData TopologicalSpace
open Scheme (NodalCycleNumbering)

namespace TauCeti.Toric.Fan

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "B(" X ")" => Chow.intersectionBilinForm ℂ X
local notation "s(" X ")" => (X ↘ S)
local notation "R(" D ", " T ")" => radical (comap D (toBase T))
local notation "f(" D ", " T ")" =>
  subschemeMap (R(D, T)) D (toBase T) (le_map_iff_comap_le.mpr (le_radical _))
local notation "I[" Φ ", " hc "]" => Fan.boundaryIdeal Φ (IsComplete.nonempty_cones hc)
local notation "prime[" D ", " A ", " h ", " j "]" =>
  Additive.ofMul
    (primeDivisorClass (boundaryPrimeEmbedding D (NodalCycleNumbering.boundaryPrimeEquiv A h j)))
local notation "ex[" T ", " d ", " j "]" =>
  Additive.ofMul (pullback (Iso.hom d) (exceptionalClass T j))

private theorem exists_centerCharacter {r : ℕ} (c : Fin r → ℂˣ) :
    ∃ χ : Multiplicative (Fin r → ℤ) →* ℂˣ,
      (fun j ↦ χ (ofAdd (Pi.single j 1))) = c := by
  let e := (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin r)).symm.toAddEquiv.toMultiplicative
  refine ⟨(freeAbelianCharEquiv.symm c).comp e.toMonoidHom, funext fun j ↦ ?_⟩
  simp [e]

private theorem contraction_boundary_support {X W M : Scheme} {D : X.IdealSheafData}
    {l : ℕ} {T : BlowupTower X l W} (e : M ≅ W) (I : M.IdealSheafData)
    (h : (R(D, T)).comap e.hom = I) :
    (D.comap (e.hom ≫ T.toBase)).support = I.support := by
  simp only [← h, comap_comp, support_comap, support_radical]

section Boundary

variable {X W C M : Scheme} [X.Over S] [W.Over S] [C.Over S]
  {D : X.IdealSheafData} {l : ℕ} {T : BlowupTower X l W}
  {n m : ℕ} [NeZero n] [NeZero m]
  [PrestableFamily s(D.subscheme)] [PrestableFamily s((R(D, T)).subscheme)] [PrestableFamily s(C)]
  {α β γ : Type*} {a : α → s(D.subscheme).smoothLocus}
  {b : β → s((R(D, T)).subscheme).smoothLocus} {c : γ → s(C).smoothLocus}
  {A : NodalCycleNumbering a n} {B : NodalCycleNumbering b m} {C' : NodalCycleNumbering c m}

/-- The boundary map from a recovered model to the original surface factors through
the boundary of the auxiliary surface. -/
private theorem contraction_boundary_map (e : M ≅ W)
    (v : C ≅ (R(D, T)).subscheme) [v.hom.IsOver S]
    (ι : C ⟶ M) (hv : v.hom ≫ (R(D, T)).subschemeι = ι ≫ e.hom)
    (hover : T.toBase ≫ s(X) = s(W)) (hact : v.boundaryCycleAction C' B = 1)
    (hsub : (f(D, T)).IsOrientedCycleSubdivision B A) :
    let g := v.hom ≫ f(D, T)
    g.IsOver S ∧ g ≫ D.subschemeι = ι ≫ e.hom ≫ T.toBase ∧
    g.IsOrientedCycleSubdivision C' A ∧
    ∀ j, g (C'.componentGenericPoint j) = f(D, T) (B.componentGenericPoint j) := by
  have hf : (f(D, T)).IsOver S := ⟨by
    rw [D.over_eq_subschemeι_comp, ← Category.assoc, subschemeMap_subschemeι,
      Category.assoc, hover, (R(D, T)).over_eq_subschemeι_comp]⟩
  let := hf
  refine ⟨inferInstance, ?_, ?_, fun j ↦ ?_⟩
  · rw [Category.assoc, subschemeMap_subschemeι, reassoc_of% hv]
  · exact (v.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one C' B (by simp [hact])).comp
      hsub
  · simp only [Scheme.Hom.comp_apply, v.apply_componentGenericPoint C' B, hact, map_one,
      Equiv.Perm.one_apply]

end Boundary

/-- Pullback along the recovered model comparison transports the auxiliary Picard form. -/
private theorem exists_internalModel_picardPullback
    {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ]
    {W : Scheme} [W.Over S] [IsIntegral W] [W.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 s(W)]
    (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) {r : ℕ} (rays : Fin r → Φ.Ray)
    (c : Fin r → ℂˣ) (e : (internalBlowupTower b rays c).1 ≅ W)
    (he : e.hom ≫ s(W) =
      (internalBlowupTower b rays c).2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap) :
    let M := internalBlowupTower b rays c
    let : M.1.Over S := ⟨M.2.toTower.toBase ≫ s(Φ.algebraicRealization)⟩
    let : M.1.IsProjectiveOver ℂ := M.2.toTower.isProjectiveOver ℂ
    let : IsIntegral M.1 := isIntegral_internalBlowupTower b rays c hΦ
    let : SmoothOfRelativeDimension 2 s(M.1) :=
      smoothOfRelativeDimension_internalBlowupTower b rays c hΦ
    ∃ G : B(W).IsometryEquiv B(M.1), ∀ x : Pic(W),
      G x = Additive.ofMul (pullback e.hom x.toMul) := by
  intro M _ _ _ _
  let : e.hom.IsOver S := ⟨he⟩
  exact ⟨Chow.picardPullbackIsometry ℂ e, Chow.picardPullbackIsometry_apply ℂ e⟩

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (hΨ : Ψ.IsRegular) (hc' : Ψ.IsComplete)
  (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
  {X Y W Z P Q U U' : Scheme}
  [X.Over S] [Y.Over S] [W.Over S] [Z.Over S] [P.Over S] [Q.Over S]
  [IsIntegral X] [IsIntegral Y] [IsIntegral W] [IsIntegral Z]
  [X.IsProjectiveOver ℂ] [Y.IsProjectiveOver ℂ] [W.IsProjectiveOver ℂ] [Z.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 s(X)] [SmoothOfRelativeDimension 2 s(Y)]
  [SmoothOfRelativeDimension 2 s(W)] [SmoothOfRelativeDimension 2 s(Z)]
  [LinearMap.IsPerfPair B(X)]
  {D : X.IdealSheafData} {E : Y.IdealSheafData}
  {E₀ : P.IdealSheafData} {E₁ : Q.IdealSheafData}
  [LocallyOfFinitePresentation (E₀.subschemeι ≫ s(P))]
  [LocallyOfFinitePresentation (E₁.subschemeι ≫ s(Q))]
  {l l' r : ℕ} {T : BlowupTower X l W} {T' : BlowupTower Y l' Z}
  {L : BlowupTower P r U} {L' : BlowupTower Q r U'}
  [PrestableFamily s(D.subscheme)] [PrestableFamily s(E.subscheme)]
  [PrestableFamily s((R(D, T)).subscheme)] [PrestableFamily s((R(E, T')).subscheme)]
  {n m : ℕ} [NeZero n] [NeZero m] {α β γ δ : Type*}
  {a : α → s(D.subscheme).smoothLocus} {a' : β → s(E.subscheme).smoothLocus}
  {p : γ → s((R(D, T)).subscheme).smoothLocus} {p' : δ → s((R(E, T')).subscheme).smoothLocus}
  (A : NodalCycleNumbering a n) (A' : NodalCycleNumbering a' n)
  (C : NodalCycleNumbering p m) (C' : NodalCycleNumbering p' m)

include hΦ hc hΨ hc' b b' in
/-- Reconstruct a pair isomorphism from signed period compatibility and matching
exceptional contractions to toric pairs, with distinct smooth boundary centers on each base.
The auxiliary Picard isometry matches the ordered total exceptional classes and the numbered
boundary classes. A common surviving component fixes the image of component zero. The
oriented subdivisions specify the action on the branches, including for one- and two-component
cycles. -/
theorem exists_iso_of_signed_boundary_period_of_toric_contractions
    (hT : IsNodalBoundaryTower D s(X) (𝟙 X) T)
    (hT' : IsNodalBoundaryTower E s(Y) (𝟙 Y) T')
    (hW : T.toBase ≫ s(X) = s(W)) (hZ : T'.toBase ≫ s(Y) = s(Z))
    (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (hR : (R(D, T)).IsEffectiveCartier) (hR' : (R(E, T')).IsEffectiveCartier)
    (hL : L.IsClosedPointTower P) (hL' : L'.IsClosedPointTower Q)
    (d : W ≅ U) (d' : Z ≅ U') (u : P ≅ Φ.algebraicRealization) (u' : Q ≅ Ψ.algebraicRealization)
    (hu : u.hom ≫ Φ.algebraicRealizationStructureMap = s(P))
    (hu' : u'.hom ≫ Ψ.algebraicRealizationStructureMap = s(Q))
    (huB : I[Φ, hc].comap u.hom = E₀) (huB' : I[Ψ, hc'].comap u'.hom = E₁)
    (hd : (d.hom ≫ L.toBase).IsOver S) (hd' : (d'.hom ≫ L'.toBase).IsOver S)
    (v : (R(D, T)).subscheme ≅ E₀.subscheme) (v' : (R(E, T')).subscheme ≅ E₁.subscheme)
    (hv : v.hom ≫ E₀.subschemeι = (R(D, T)).subschemeι ≫ d.hom ≫ L.toBase)
    (hv' : v'.hom ≫ E₁.subschemeι = (R(E, T')).subschemeι ≫ d'.hom ≫ L'.toBase)
    (hdistinct : Function.Injective hL.baseCenter) (hdistinct' : Function.Injective hL'.baseCenter)
    (hcenters : ∀ j, ∃ q : E₀.subscheme, E₀.subschemeι q = hL.baseCenter j ∧
      q ∈ (E₀.subschemeι ≫ s(P)).smoothLocus)
    (hcenters' : ∀ j, ∃ q : E₁.subscheme, E₁.subschemeι q = hL'.baseCenter j ∧
      q ∈ (E₁.subschemeι ≫ s(Q)).smoothLocus)
    (G : B(Y).IsometryEquiv B(X)) (Gaux : B(Z).IsometryEquiv B(W))
    (hPic : ∀ a : LineBundleClass Y,
      Gaux (Additive.ofMul (pullback T'.toBase a)) =
        Additive.ofMul (pullback T.toBase (G (Additive.ofMul a)).toMul))
    (hexc : ∀ j, Gaux (ex[L', d', j]) = ex[L, d, j])
    (hstrict : let := LocallyOfFiniteType.isLocallyNoetherian s(W)
      let := s(W).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      let := LocallyOfFiniteType.isLocallyNoetherian s(Z)
      let := s(Z).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      ∀ j, Gaux (prime[R(E, T'), C', hR', j]) = prime[R(D, T), C, hR, j])
    (act : DihedralGroup n)
    (hsub : (f(D, T)).IsOrientedCycleSubdivision C A)
    (hsub' : (f(E, T')).IsOrientedCycleSubdivision C'
      (if DihedralGroup.cycleOrientationSign act = -1 then A'.reverse else A'))
    (gD : ∀ w : irreducibleComponents (D.subscheme.singularLocus ℂ).blowup,
      (D.subscheme.blowupComponent (K := ℂ) w).toScheme.genus ℂ = 0)
    (gE : ∀ w : irreducibleComponents (E.subscheme.singularLocus ℂ).blowup,
      (E.subscheme.blowupComponent (K := ℂ) w).toScheme.genus ℂ = 0)
    (hOrth : ∀ x : E.boundaryOrthogonal ℂ, G x.val ∈ D.boundaryOrthogonal ℂ)
    (hperiod : ∀ x : E.boundaryOrthogonal ℂ,
      hE.boundaryPeriod gE A'.endpoint_eq (ofAdd x) =
        hD.boundaryPeriod gD A.endpoint_eq (ofAdd ⟨G x.val, hOrth x⟩) ^
          (DihedralGroup.cycleOrientationSign act : ℤ))
    (j : ZMod m)
    (hj : f(D, T) (C.componentGenericPoint j) = A.componentGenericPoint 0)
    (hj' : f(E, T') (C'.componentGenericPoint j) =
      A'.componentGenericPoint (DihedralGroup.cycleVertexPerm act 0)) :
    Nonempty (SignedTorelliPairIso (D := D) (E := E) A A'
      (fun L ↦ (G (Additive.ofMul L)).toMul) act) := by
  let : LinearMap.IsPerfPair B(Y) :=
    LinearMap.IsPerfPair.congr (B(X)) G.toLinearEquiv G.toLinearEquiv (B(Y))
      (LinearMap.ext₂ fun x y ↦ G.symm.map_app y x)
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Nonempty Ψ.cones := hc'.nonempty_cones
  let := LocallyOfFiniteType.isLocallyNoetherian s(W)
  let := LocallyOfFiniteType.isLocallyNoetherian s(Z)
  let := s(W).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := s(Z).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  -- Use the common auxiliary numbering to orient each recovered fan.
  obtain ⟨hp, b₀, r₀, c, e, eB, hover, C₀, -, hpos, hnodes, -, he, heB, hbound, hact,
    hExc, hStrict⟩ :=
    exists_numbered_toric_model_of_boundary_contraction b hΦ hc C hR hL d u hu huB hd v hv
      hdistinct hcenters
  obtain ⟨hp', b₁, r₁, c', e', eB', hover', C₁, -, hpos', hnodes', -, he', heB', hbound',
    hact', hExc', hStrict'⟩ :=
    exists_numbered_toric_model_of_boundary_contraction b' hΨ hc' C' hR' hL' d' u' hu' huB' hd'
      v' hv' hdistinct' hcenters'
  let := hp
  let := hp'
  let := hover
  let := hover'
  obtain ⟨χ, rfl⟩ := exists_centerCharacter c
  obtain ⟨χ', rfl⟩ := exists_centerCharacter c'
  let M := internalBlowupTower b₀ r₀ (fun j ↦ χ (ofAdd (Pi.single j 1)))
  let M' := internalBlowupTower b₁ r₁ (fun j ↦ χ' (ofAdd (Pi.single j 1)))
  let : Φ.algebraicRealization.IsProjectiveOver ℂ :=
    Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b₀
  let : Ψ.algebraicRealization.IsProjectiveOver ℂ :=
    Ψ.isProjectiveOver_algebraicRealization_of_isComplete hΨ hc' b₁
  let : SmoothOfRelativeDimension 2 s(Φ.algebraicRealization) := by
    rw [algebraicRealization_over]
    exact ((Module.finrank_eq_card_basis b₀).trans (Fintype.card_fin 2)) ▸
      Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  obtain ⟨G₀, hG₀⟩ := exists_internalModel_picardPullback hΦ b₀ r₀ _ e he
  obtain ⟨G₁, hG₁⟩ := exists_internalModel_picardPullback hΨ b₁ r₁ _ e' he'
  let Gmodel := G₁.symm.trans (Gaux.trans G₀)
  have hG (x : Pic(Z)) : Gmodel (Additive.ofMul (pullback e'.hom x.toMul)) =
      Additive.ofMul (pullback e.hom (Gaux x).toMul) := by
    -- Conjugation by pullback cancels the target comparison before applying the marking.
    change G₀ (Gaux (G₁.symm (Additive.ofMul (pullback e'.hom x.toMul)))) = _
    have hinv : G₁.symm (G₁ x) = x := G₁.toLinearEquiv.symm_apply_apply x
    rw [← hG₁ x, hinv, hG₀]
  -- Compose the boundary identifications with the nodal projections.
  obtain ⟨hf, hfcomp, hfsub, hfgen⟩ := contraction_boundary_map e eB _ heB hW hact hsub
  obtain ⟨hg, hgcomp, hgsub, hggen⟩ := contraction_boundary_map e' eB' _ heB' hZ hact' hsub'
  let := hf
  let := hg
  have hmark (a : LineBundleClass Y) :
      Gmodel (Additive.ofMul (pullback (e'.hom ≫ T'.toBase) a)) =
        Additive.ofMul (pullback (e.hom ≫ T.toBase) (G (Additive.ofMul a)).toMul) := by
    rw [← pullback_comp, ← pullback_comp]
    exact (hG (Additive.ofMul (pullback T'.toBase a))).trans (by rw [hPic]; rfl)
  have hExc'G k := (congrArg Gmodel (congrArg Additive.ofMul (hExc' k).symm)).trans
    ((hG (ex[L', d', k])).trans (by rw [hexc, toMul_ofMul, hExc k]))
  have hStrict'G k := (congrArg Gmodel (hStrict' k).symm).trans
    ((hG (prime[R(E, T'), C', hR', k])).trans (by rw [hstrict, toMul_ofMul, hStrict k]))
  have hp₀ : e.hom ≫ T.toBase ≫ s(X) = M.2.toTower.toBase ≫ s(Φ.algebraicRealization) := by
    rw [hW, he, algebraicRealization_over]
  have hp₁ : e'.hom ≫ T'.toBase ≫ s(Y) = M'.2.toTower.toBase ≫ s(Ψ.algebraicRealization) := by
    rw [hZ, he', algebraicRealization_over]
  -- The original and toric models give two point-blowup markings of the same surface.
  let c₀ : Fin r → ℂˣ := fun j ↦ χ (ofAdd (Pi.single j 1))
  have hperf (a : W ≅ (internalBlowupTower b₀ r₀ c₀).1)
      (ha : a.inv ≫ T.toBase ≫ s(X) =
        (internalBlowupTower b₀ r₀ c₀).2.toTower.toBase ≫ s(Φ.algebraicRealization)) :
      LinearMap.IsPerfPair (B(Φ.algebraicRealization).prod
        (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))) := by
    -- The scheme comparison and its projection equation both depend on the tower.
    revert ha a
    rw [internalBlowupTower_eq_alongBoundary]
    intro a ha
    exact isPerfPair_internal_markedForm hΦ
      ((Module.finrank_eq_card_basis b₀).trans (Fintype.card_fin 2)) r₀
      (fun j ↦ (b₀.detDualEquiv (r₀ j).primitiveGenerator).toAddMonoidHom)
      (fun j ↦ b₀.detDualEquiv_self _) (fun j ↦ (r₀ j).surjective_detCharacter b₀) c₀
      (fun j ↦ (r₀ j).internalCenter b₀ (c₀ j)) (fun j ↦ (r₀ j).internalCenter_val b₀ (c₀ j))
      hT a ha
  let := hperf e.symm (by simpa only [Iso.symm_inv] using hp₀)
  exact exists_iso_of_signed_boundary_period_of_toric_presentations hΦ hΨ b₀ b₁ r₀ r₁ χ χ' C₀ C₁
    (fun k ↦ ⟨hpos' k, by obtain ⟨σ, h₁, h₂, -⟩ := hnodes' k; exact ⟨σ.val, h₁, h₂⟩⟩)
    (fun k ↦ (Φ.boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering hΦ C₀ k).symm)
    (fun k ↦ (Ψ.boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering hΨ C₁ k).symm)
    e.symm e'.symm A A' hc hc' hpos
    (fun k ↦ by obtain ⟨σ, h₁, h₂, hn⟩ := hnodes k; exact ⟨σ.val, h₁, h₂, hn⟩) hT hT'
    (by simpa only [Iso.symm_inv, Category.assoc, algebraicRealization_over] using hp₀)
    (by simpa only [Iso.symm_inv, Category.assoc, algebraicRealization_over] using hp₁)
    (contraction_boundary_support e _ hbound)
    (contraction_boundary_support e' _ hbound') G Gmodel hmark hExc'G hStrict'G
    hfcomp hgcomp hfsub act hgsub hD hE gD gE hOrth hperiod j ((hfgen j).trans hj)
    ((hggen j).trans hj')

end TauCeti.Toric.Fan
