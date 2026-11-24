/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Picard.Hirzebruch
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.OppositeSection

import QPainleve.AlgebraicGeometry.Blowup.Point.Fiber
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.Fan.Picard.Homaloidal
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Decrease

/-!
# The quadric Sarkisov block with a corner and a smooth center

In the frame of the exchanged ruling, the first link at the toric corner gives
a Hirzebruch-one surface. The smooth center on the opposite section lifts
uniquely to the common toric blowup. It remains the first center over its image
in the transported tower. The link at this point and the final ruling exchange
give the degree-decreasing resolution over a quadric.

This is the corner case of the two-point block in Lutz's appendix to
[*Homological mirror symmetry for log Calabi–Yau surfaces*][HKL],
Proposition 8.11, Cases B and C.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ F : Fan i}

local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "f[" Δ "]" => Fan.algebraicRealizationStructureMap Δ
local notation "I[" σ "]" => Scheme.Hom.ker (Fan.distinguishedPointHom _ σ)
local notation "π[" H "]" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom H)
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "pt" => IsLocalRing.closedPoint ℂ
local notation "dim(" b ")" =>
  Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "p[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ dim(b)
    (Module.Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c

private theorem exists_binomialCenter_lift_of_shared_ray
    (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ)
    (ρ : Φ.Ray) (ρ' : Ψ.Ray) (hρ : ρ.primitiveGenerator = ρ'.primitiveGenerator)
    (b d : Basis (Fin 2) ℤ N) (c : ℂˣ) :
    ∃ (c' : ℂˣ) (z : X[F]),
      π[s] z = p[b,ρ,c] pt ∧ π[t] z = p[d,ρ',c'] pt ∧
      p[b,ρ,c] pt ∈ (π[s]).isoLocus ∧ p[d,ρ',c'] pt ∈ (π[t]).isoLocus := by
  have hl : s.liftRay ρ = t.liftRay ρ' := Fan.Ray.primitiveGenerator_injective (by
    rw [s.primitiveGenerator_liftRay, t.primitiveGenerator_liftRay, hρ])
  obtain ⟨c', hc'⟩ := ρ'.exists_binomialCenter_eq_of_basis d b c
  let z := p[b,s.liftRay ρ,c] pt
  have hs := s.binomialCenter_liftRay_comp_algebraicMap ρ b c
  have ht := t.binomialCenter_liftRay_comp_algebraicMap ρ' b c
  dsimp only at hs ht
  have hsrc : π[s] z = p[b,ρ,c] pt := congrArg (fun a : S ⟶ X[Φ] ↦ a pt) hs
  have htgt : π[t] z = p[d,ρ',c'] pt := by
    rw [hc']
    exact congrArg (fun a : S ⟶ X[Ψ] ↦ a pt) (hl ▸ ht)
  refine ⟨c', z, hsrc, htgt, ?_, ?_⟩
  · exact s.range_binomialCenter_subset_isoLocus ρ dim(b) (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c (Set.mem_range_self pt)
  · exact t.range_binomialCenter_subset_isoLocus ρ' dim(d) (d.detDualEquiv_self _)
      (ρ'.surjective_detCharacter d) c' (Set.mem_range_self pt)

private theorem notMem_isoLocus_distinguishedPoint_of_blowup
    (b : Basis (Fin 2) ℤ N) (hΨ : Ψ.IsRegular) (τ : Ψ.cones)
    (f : X[F] ⟶ X[Ψ]) (w : X[F] ≅ (I[τ]).blowup)
    (hw : w.hom ≫ (I[τ]).blowupToBase = f) :
    Ψ.distinguishedPointHom τ pt ∉ f.isoLocus := by
  let : Nonempty Ψ.cones := ⟨τ⟩
  let : SmoothOfRelativeDimension 2 f[Ψ] :=
    dim(b) ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
  have : Smooth f[Ψ] := SmoothOfRelativeDimension.smooth 2 _
  have hclosed := Ψ.isClosed_singleton_distinguishedPoint τ
  have : IsRegularLocalRing (X[Ψ].presheaf.stalk (Ψ.distinguishedPointHom τ pt)) :=
    isRegularLocalRing_stalk_of_smooth f[Ψ] _
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f[Ψ] 2).mp
    inferInstance).2 _ hclosed
  have hcentre : f.centre = {Ψ.distinguishedPointHom τ pt} := by
    rw [← hw, Scheme.Hom.centre_def, Scheme.Hom.isoLocus_comp_of_isIso, ← Scheme.Hom.centre_def,
      (Ψ.distinguishedPointHom τ).ker_eq_ker_fromSpecResidueField,
      Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
    exact centre_blowupToBase_closed_point hclosed hdim
  have hmem : Ψ.distinguishedPointHom τ pt ∈ f.centre := by
    rw [hcentre]
    exact Set.mem_singleton _
  simpa only [Scheme.Hom.centre_def, Set.mem_compl_iff, SetLike.mem_coe] using hmem

section CornerLink

variable {n : ℕ} {Y : Scheme} {σ : Φ.cones} {τ : Ψ.cones}
  {T : BlowupTower (I[σ]).blowup (n + 1) Y}
  (hT : IsClosedPointTower (I[σ]).blowup T)
  (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ)
  (v : X[F] ≅ (I[σ]).blowup) (w : X[F] ≅ (I[τ]).blowup)
  (hv : v.hom ≫ (I[σ]).blowupToBase = π[s])
  (hw : w.hom ≫ (I[τ]).blowupToBase = π[t])

local notation "R" => BlowupTower.transport T (v.symm ≪≫ w)
local notation "hW" =>
  IsClosedPointTower.snoc (IsClosedPointTower.nil (X := X[Ψ])) _
    (Fan.isClosed_singleton_distinguishedPoint Ψ τ)
    (Scheme.Hom.ker_eq_ker_fromSpecResidueField (Fan.distinguishedPointHom Ψ τ))

include hv hw in
private theorem first_center_of_toric_link
    (b : Basis (Fin 2) ℤ N) (hΨ : Ψ.IsRegular)
    {z : X[F]} (hs : π[s] z ∈ (π[s]).isoLocus) (ht : π[t] z ∈ (π[t]).isoLocus)
    (l : Fin (n + 1)) (hl : (I[σ]).blowupToBase (hT.baseCenter l) = π[s] z)
    (hfirst : ∀ k < l, (I[σ]).blowupToBase (hT.baseCenter k) ≠ π[s] z) :
    let hR := (R).isLift.isClosedPointTower hT
    let hU := (hW).append hR
    hU.baseCenter (l.natAdd 1) = π[t] z ∧
      ∀ k < l.natAdd 1, hU.baseCenter k ≠ π[t] z := by
  intro hR hU
  have hsrc (k : Fin (n + 1)) :=
    congrArg (fun f : X[F] ⟶ X[Φ] ↦ f (v.inv (hT.baseCenter k))) hv
  simp only [Scheme.Hom.comp_apply, Scheme.inv_hom_apply] at hsrc
  have htgt (k : Fin (n + 1)) :
      hU.baseCenter (k.natAdd 1) = π[t] (v.inv (hT.baseCenter k)) := by
    rw [baseCenter_append_natAdd (hW) hR, ← (R).isLift.hom_baseCenter hT hR,
      toBase_snoc, toBase_nil, Category.comp_id]
    simpa only [Iso.trans_hom, Iso.symm_hom, Scheme.Hom.comp_apply] using
      (congrArg (fun f : X[F] ⟶ X[Ψ] ↦ f (v.inv (hT.baseCenter k))) hw)
  have hproj := (hsrc l).symm.trans hl
  have hpt : v.inv (hT.baseCenter l) = z := (π[s]).injOn_preimage_isoLocus
    (by simpa only [Set.mem_preimage, hproj, SetLike.mem_coe] using hs) hs hproj
  refine ⟨(htgt l).trans (congrArg π[t] hpt), ?_⟩
  refine Fin.addCases ?_ ?_
  · intro k _ he
    have hclosed := Ψ.isClosed_singleton_distinguishedPoint τ
    rw [baseCenter_append_castAdd (hW) hR, Subsingleton.elim k (Fin.last 0),
      baseCenter_snoc_last, toBase_nil,
      lastCenter_eq _ _ hclosed (Ψ.distinguishedPointHom τ).ker_eq_ker_fromSpecResidueField] at he
    apply notMem_isoLocus_distinguishedPoint_of_blowup b hΨ τ π[t] w hw
    simpa [← he] using ht
  · intro k hk he
    have e := (htgt k).symm.trans he
    have e' := (π[t]).injOn_preimage_isoLocus
      (by simpa only [Set.mem_preimage, e, SetLike.mem_coe] using ht) ht e
    exact hfirst k (by simpa only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left] using hk)
      ((hsrc k).trans (congrArg π[s] e'))

end CornerLink

section Quadric

variable (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hcΦ : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
  (σ : Φ.cones) (hσ : σ.val = hull ℝ (Set.range (i ∘ b)))
  {n : ℕ} {Y : Scheme} {T : BlowupTower X[Φ] (n + 2) Y} (hT : IsClosedPointTower X[Φ] T)

local notation "C[" b "," e "," h "," r "," hr "]" => Fan.hirzebruchPicardBasis b e h r hr
local notation "C₀" => C[b,0,hΦ,r,hr]

include hσ in
private theorem exists_hirzebruchOne_resolution_of_corner_with_smooth_center
    (j l : Fin (n + 2))
    (hj : hT.baseCenter j = Φ.distinguishedPointHom σ pt)
    (hfirst : ∀ k < j, hT.baseCenter k ≠ Φ.distinguishedPointHom σ pt)
    (c : ℂˣ) (hl : hT.baseCenter l = p[b,r 2,c] pt)
    (hlfirst : ∀ k < l, hT.baseCenter k ≠ p[b,r 2,c] pt)
    (L : LineBundleClass Y) :
    let : Nonempty Φ.cones := hcΦ.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      dim(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let x := (T.picardMarking hT f[Φ]).symm (Additive.ofMul L)
    ∃ (Ψ F : Fan i) (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete) (_ : F.IsRegular)
      (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ) (τ : Ψ.cones)
      (v : X[F] ≅ (I[σ]).blowup) (w : X[F] ≅ (I[τ]).blowup)
      (d : Basis (Fin 2) ℤ N) (r' : Fin 4 ≃ Ψ.Ray)
      (hr' : (fun k ↦ (r' k).primitiveGenerator) = ![d 0, d 1, -d 0, (1 : ℤ) • d 0 - d 1])
      (q : Y ⟶ X[F]) (Z : Scheme) (U : BlowupTower X[Ψ] (1 + (n + 1)) Z)
      (hU : IsClosedPointTower X[Ψ] U) (e : Y ≅ Z) (c' : ℂˣ) (l' : Fin (n + 1)),
      v.hom ≫ (I[σ]).blowupToBase = π[s] ∧ w.hom ≫ (I[τ]).blowupToBase = π[t] ∧
      q ≫ π[s] = T.toBase ∧ q ≫ π[t] = e.hom ≫ U.toBase ∧
      j.succAbove l' = l ∧
      let k := l'.natAdd 1
      hU.baseCenter k = p[d,r' 2,c'] pt ∧ (∀ m < k, hU.baseCenter m ≠ p[d,r' 2,c'] pt) ∧
      let : Nonempty Ψ.cones := hcΨ.nonempty_cones
      let : SmoothOfRelativeDimension 2 f[Ψ] :=
        dim(d) ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
      let y := (U.picardMarking hU f[Ψ]).symm (Additive.ofMul (pullback e.inv L))
      C[d,1,hΨ,r',hr'].repr y.1 0 = (C₀).repr x.1 0 + (C₀).repr x.1 1 + x.2 j ∧
      C[d,1,hΨ,r',hr'].repr y.1 1 = (C₀).repr x.1 1 ∧
      y.2 = Fin.addCases (fun _ : Fin 1 ↦ -(C₀).repr x.1 1 - x.2 j) (x.2 ∘ j.succAbove) := by
  intro _ _ x
  let : Nonempty Φ.cones := hcΦ.nonempty_cones
  let : SmoothOfRelativeDimension 2 f[Φ] :=
    dim(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have hrays : Set.range (Fan.Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1} := by
    rw [← r.surjective.range_comp, Function.comp_def, hr]
    ext x
    simp [or_comm, or_assoc]
  obtain ⟨Ψ, F, hΨ, hF, hcΨ, hcF, d, τ, s, t, v, w, r₀, r', hr₀, hr', hd₀, _, _, hv, hw, hC⟩ :=
    Φ.exists_hirzebruch_toric_elementary_transform_picard_coordinates b 0 hΦ hcΦ hrays σ hσ
  have hr₀' : r₀ = r := Equiv.ext fun k ↦ Fan.Ray.primitiveGenerator_injective
    ((congrFun hr₀ k).trans (congrFun hr k).symm)
  subst r₀
  have hray : (r 2).primitiveGenerator = (r' 2).primitiveGenerator := by
    simp [congrFun hr 2, congrFun hr' 2, hd₀]
  obtain ⟨c', z, hsrc, htgt, hs, ht⟩ := exists_binomialCenter_lift_of_shared_ray s t _ _ hray b d c
  -- The corner blowup supplies the common base for reordering and transporting the tail.
  have hmove := hT.exists_move_closed_point_blowup_to_front j
    (Φ.isClosed_singleton_distinguishedPoint σ) hj hfirst
  rw [← (Φ.distinguishedPointHom σ).ker_eq_ker_fromSpecResidueField] at hmove
  obtain ⟨W, A, e, hA, he, hE, hcenters, htail⟩ := hmove
  have hjl : l ≠ j := by
    intro hjl
    exact notMem_isoLocus_distinguishedPoint_of_blowup b hΦ σ π[s] v hv (by rwa [← hj, ← hjl, hl])
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hjl
  let R := A.transport (v.symm ≪≫ w)
  let U := (BlowupTower.nil.snoc (I[τ])).append R.tower
  let hR := R.isLift.isClosedPointTower hA
  let hτ : IsClosedPointTower X[Ψ] (BlowupTower.nil.snoc (I[τ])) :=
    .snoc .nil _ (Ψ.isClosed_singleton_distinguishedPoint τ)
      (Ψ.distinguishedPointHom τ).ker_eq_ker_fromSpecResidueField
  let hU := hτ.append hR
  obtain ⟨hcenter, hfirst'⟩ := first_center_of_toric_link hA s t v w hv hw d hΨ
    (hsrc.symm ▸ hs) (htgt.symm ▸ ht) k (by rw [hcenters, hk, hl, hsrc]) (by
      intro m hm
      rw [hcenters, hsrc]
      exact hlfirst _ (hk ▸ (Fin.strictMono_succAbove j) hm))
  let q := e.hom ≫ A.toBase ≫ v.inv
  have hq : q ≫ π[s] = T.toBase := by simp only [q, Category.assoc, ← hv, Iso.inv_hom_id_assoc, he]
  have hq' : q ≫ π[t] = (e ≪≫ R.iso).hom ≫ U.toBase := by
    simp only [q, U, Iso.trans_hom, toBase_append, toBase_snoc, toBase_nil,
      Category.comp_id, Category.assoc, R.isLift.hom_toBase_assoc, Iso.symm_hom, ← hw]
  refine ⟨Ψ, F, hΨ, hcΨ, hF, s, t, τ, v, w, d, r', hr', q, _, U, hU, e ≪≫ R.iso, c', k, hv, hw,
    hq, hq', hk, hcenter.trans htgt, fun m hm ↦ htgt ▸ hfirst' m hm, ?_⟩
  intro _ _ y
  let : Nonempty Ψ.cones := hcΨ.nonempty_cones
  let : SmoothOfRelativeDimension 2 f[Ψ] :=
    dim(d) ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
  let a := (C₀).repr x.1 0
  let β := (C₀).repr x.1 1
  let x' : Fin (1 + (n + 1)) → ℤ :=
    Fin.addCases (fun _ : Fin 1 ↦ -β - x.2 j) (x.2 ∘ j.succAbove)
  let C' := C[d,1,hΨ,r',hr']
  have hL : (T.picardHom x).toMul = L := by
    rw [← T.picardMarking_apply hT f[Φ], LinearEquiv.apply_symm_apply, toMul_ofMul]
  have hx : x.1 = a • C₀ 0 + β • C₀ 1 := by
    simpa only [a, β, Fin.sum_univ_two] using ((C₀).sum_repr x.1).symm
  have hmark := T.pullback_picardHom_move_to_front j e he hE htail x.1 x.2
  -- Pull the marking back first along the reordering and then across the common blowup.
  have hclass := congrArg (pullback w.inv) (hC a β (x.2 j))
  simp only [pullback_comp, Iso.inv_hom_id, pullback_id] at hclass
  have hy : y = ((a + β + x.2 j) • C' 0 + β • C' 1, x') := by
    apply (LinearEquiv.symm_apply_eq _).mpr
    apply Additive.toMul.injective
    rw [U.picardMarking_apply hU f[Ψ], toMul_ofMul, Iso.trans_inv, ← pullback_comp, ← hL,
      hmark, picardHom_append, picardHom_append]
    have hRmark := R.isLift.symm.pullback_picardHom
    simp only [Iso.symm_hom] at hRmark
    rw [hRmark]
    simp only [x', Fin.addCases_left, Fin.addCases_right, Iso.trans_inv, Iso.symm_inv,
      hx]
    rw [hclass]
    rfl
  rw [hy]
  have hrepr :
      C'.repr ((a + β + x.2 j) • C' 0 + β • C' 1) 0 = a + β + x.2 j ∧
      C'.repr ((a + β + x.2 j) • C' 0 + β • C' 1) 1 = β := by simp
  exact ⟨hrepr.1, hrepr.2, rfl⟩

local notation "hv[" r "]" => Fan.Ray.primitiveGenerator_ne_zero (r (2 : Fin 4))
local notation "hp[" r "]" => Fan.Ray.hull_primitiveGenerator_mem (r (2 : Fin 4))
local notation "opp[" d "," r "," hr "]" =>
  Fan.hull_neg_primitiveGenerator_mem_of_hirzebruch_section_two d 1 r hr
local notation "ret[" Ψ "," d "," r "," hr "]" =>
  Fan.mutationFan Ψ d hv[r] hp[r] opp[d,r,hr]
local notation "reg[" Ψ "," d "," r "," hr "," hΨ "]" =>
  Iff.mpr (Fan.isRegular_mutationFan_iff Ψ d hv[r] hp[r] opp[d,r,hr]) hΨ
local notation "complete[" Ψ "," d "," r "," hr "," hcΨ "]" =>
  Iff.mpr (Fan.isComplete_mutationFan_iff Ψ d hv[r] hp[r] opp[d,r,hr]) hcΨ
local notation "rays[" Ψ "," d "," r "," hr "]" =>
  Equiv.trans r (Fan.mutationFanRayEquiv Ψ d hv[r] hp[r] opp[d,r,hr])
local notation "μ[" Ψ "," d "," r "," hr "," c "]" =>
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap Ψ d (c : ℂ) hv[r] hp[r] opp[d,r,hr])

variable [X[Φ].IsProjectiveOver ℂ]

include hσ in
/-- On a quadric written in the frame of the exchanged ruling, suppose that the two
orders greater than half the original fiber degree are at a corner of the chosen
section and at a smooth point of the opposite section. The toric link at the
corner, mutation at the transported smooth point, and ruling exchange give
regular projections on the specified resolution, transported by isomorphisms.

For original fiber and section coefficients β and a in this frame, and base
orders m and m' at the two points, the final coefficients are a and β + a - m - m'.
The second final coefficient is positive and the Sarkisov bidegree decreases.
The exceptional coordinates record the reverse pivots and the order inherited
from the original tower, including at infinitely near centers. -/
theorem exists_quadric_resolution_of_corner_and_smooth_high_centers
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f[Φ])
    (hbir : Scheme.BirationalOver g (𝟙 P))
    (j l : Fin (n + 2))
    (hj : hT.baseCenter j = Φ.distinguishedPointHom σ pt)
    (hjfirst : ∀ k < j, hT.baseCenter k ≠ Φ.distinguishedPointHom σ pt)
    (c : ℂˣ) (hl : hT.baseCenter l = p[b,r 2,c] pt)
    (hlfirst : ∀ k < l, hT.baseCenter k ≠ p[b,r 2,c] pt) :
    let : Nonempty Φ.cones := hcΦ.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      dim(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let x := (T.picardMarking hT f[Φ]).symm (Additive.ofMul (pullback g H))
    let β := (C₀).repr x.1 0
    let a := (C₀).repr x.1 1
    let m := fun k ↦ -x.2 k
    β < 2 * m j → m j ≤ β → β < 2 * m l → m l ≤ β →
    (∀ k, k ≠ j → k ≠ l → 0 ≤ m k ∧ 2 * m k ≤ β) →
    ∃ (Ψ F : Fan i) (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete) (_ : F.IsRegular)
      (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ) (τ : Ψ.cones)
      (v : X[F] ≅ (I[σ]).blowup) (w : X[F] ≅ (I[τ]).blowup)
      (d : Basis (Fin 2) ℤ N) (r' : Fin 4 ≃ Ψ.Ray)
      (hr' : (fun k ↦ (r' k).primitiveGenerator) = ![d 0, d 1, -d 0, (1 : ℤ) • d 0 - d 1])
      (q : Y ⟶ X[F]) (Z : Scheme) (U : BlowupTower X[Ψ] (1 + (n + 1)) Z)
      (hU : IsClosedPointTower X[Ψ] U) (e : Y ≅ Z) (c' : ℂˣ) (l' : Fin (n + 1)),
      v.hom ≫ (I[σ]).blowupToBase = π[s] ∧ w.hom ≫ (I[τ]).blowupToBase = π[t] ∧
      q ≫ π[s] = T.toBase ∧ q ≫ π[t] = e.hom ≫ U.toBase ∧
      j.succAbove l' = l ∧
      let k := l'.natAdd 1
      hU.baseCenter k = p[d,r' 2,c'] pt ∧ (∀ m < k, hU.baseCenter m ≠ p[d,r' 2,c'] pt) ∧
      let Θ := ret[Ψ,d,r',hr']
      let hΘ := reg[Ψ,d,r',hr',hΨ]
      let hcΘ := complete[Ψ,d,r',hr',hcΨ]
      let s' := rays[Ψ,d,r',hr']
      let : Nonempty Ψ.cones := hcΨ.nonempty_cones
      let : Nonempty Θ.cones := hcΘ.nonempty_cones
      let : SmoothOfRelativeDimension 2 f[Ψ] :=
        dim(d) ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
      let : SmoothOfRelativeDimension 2 f[Θ] :=
        dim(d) ▸ Θ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΘ
      let : IsIntegral Z := hU.isIntegral f[Ψ]
      let : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two f[Ψ]
      ∃ (b' : Basis (Fin 2) ℤ N)
        (hs' : (fun k ↦ (s' k).primitiveGenerator) = ![b' 0, b' 1, -b' 0, (0 : ℤ) • b' 0 - b' 1])
        (W₀ : Scheme) (V₀ : BlowupTower X[Θ] (1 + (1 + n)) W₀)
        (k₀ : Z ≅ W₀) (W : Scheme) (V : BlowupTower X[Θ] (1 + (1 + n)) W)
        (hV : IsClosedPointTower X[Θ] V) (k₁ : Z ≅ W),
        let τq := (Fan.quadricRulingExchange b' hΘ hcΘ s' hs').toFanHom.algebraicMap
        U.toBase.toRationalMap.comp μ[Ψ,d,r',hr',c'] = (k₀.hom ≫ V₀.toBase).toRationalMap ∧
        (k₀.hom ≫ V₀.toBase) ≫ τq = k₁.hom ≫ V.toBase ∧
        let g' := k₁.inv ≫ e.inv ≫ g
        g' ≫ (P ↘ S) = V.toBase ≫ f[Θ] ∧ Scheme.BirationalOver g' (𝟙 P) ∧
        let z := (V.picardMarking hV f[Θ]).symm (Additive.ofMul (pullback g' H))
        (C[b',0,hΘ,s',hs']).repr z.1 0 = a ∧
        (C[b',0,hΘ,s',hs']).repr z.1 1 = β + a - m j - m l ∧
        z.2 = Fin.addCases (fun _ : Fin 1 ↦ -a - x.2 l)
          ((Fin.addCases (fun _ : Fin 1 ↦ -a - x.2 j) (x.2 ∘ j.succAbove) :
            Fin (1 + (n + 1)) → ℤ) ∘ k.succAbove) ∧
        0 < (C[b',0,hΘ,s',hs']).repr z.1 1 ∧
        hirzebruchSarkisovBidegree ((C[b',0,hΘ,s',hs']).repr z.1 1).toNat (∑ k, -z.2 k).toNat <
          hirzebruchSarkisovBidegree β.toNat (∑ k, m k).toNat := by
  intro hcones hdim x β a m hjbig hjle hlbig hlle hsmall
  let := hcones
  let := hdim
  obtain ⟨Ψ, F, hΨ, hcΨ, hF, s, t, τ, v, w, d, r', hr', q, Z, U, hU, e, c', l', hv, hw,
      hq, hq', hidx, hk, hkfirst, ha, hβ, horders⟩ :=
    exists_hirzebruchOne_resolution_of_corner_with_smooth_center b hΦ hcΦ r hr σ hσ hT
      j l hj hjfirst c hl hlfirst (pullback g H)
  let k := l'.natAdd 1
  -- The homaloidal identities compare the initial degree with the final ruling coefficient.
  have ⟨hsq, hsum⟩ := hT.homaloidal_intersection_identities_of_hirzebruch b 0 hΦ hcΦ r hr g hg hbir
  have hsq' : ∑ k, m k ^ 2 = 2 * β * a - 1 := by
    simpa only [m, x, β, a, neg_sq, Nat.cast_zero, zero_mul, sub_zero,
      Fan.algebraicRealization_over] using hsq
  have hsum' : ∑ k, m k = 2 * β + 2 * a - 3 := by
    simpa only [m, x, β, a, Nat.cast_zero, sub_zero, Fan.algebraicRealization_over] using hsum
  have hlt := quadric_sarkisov_degree_decrease_of_pair (a := a) (b := β) (m := m)
    (by omega) (hidx ▸ Fin.ne_succAbove j l')
    (hsq'.trans (by ring))
    (hsum'.trans (by ring))
    hjbig.le hjle hlbig.le hlle hsmall
  refine ⟨Ψ, F, hΨ, hcΨ, hF, s, t, τ, v, w, d, r', hr', q, Z, U, hU, e, c', l', hv, hw,
    hq, hq', hidx, hk, hkfirst, ?_⟩
  intro Θ hΘ hcΘ s' hconesΨ hconesΘ hdimΨ hdimΘ hZ hUmod
  let := hconesΨ
  let := hconesΘ
  let := hdimΨ
  let := hdimΘ
  let := hZ
  let := hUmod
  -- The return mutation and the ruling exchange act on the isomorphic resolving tower.
  obtain ⟨b', hs', W₀, V₀, hV₀, k₀, hμ, _, hover, hcoord⟩ :=
    hU.exists_quadric_resolution_of_hirzebruchOne_mutation d hΨ hcΨ r' hr' c' k hk hkfirst
  let τq := (Fan.quadricRulingExchange b' hΘ hcΘ s' hs').toFanHom.algebraicMap
  let R := V₀.transport (asIso τq)
  let k₁ := k₀ ≪≫ R.iso
  have hproj : (k₀.hom ≫ V₀.toBase) ≫ τq = k₁.hom ≫ R.tower.toBase := by
    rw [Category.assoc, Iso.trans_hom, Category.assoc, R.isLift.hom_toBase, asIso_hom]
  have h₀ : e.hom ≫ U.toBase ≫ f[Ψ] = T.toBase ≫ f[Φ] := by
    rw [← Category.assoc, ← hq', Category.assoc,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap,
      ← FanHom.algebraicMap_comp_algebraicRealizationStructureMap (Fan.IsSubdivision.toFanHom s),
      ← Category.assoc, hq]
  refine ⟨b', hs', W₀, V₀, k₀, R.top, R.tower, R.isLift.isClosedPointTower hV₀, k₁, hμ, hproj, ?_⟩
  have hover' : k₁.hom ≫ R.tower.toBase ≫ f[Θ] = U.toBase ≫ f[Ψ] := by
    simpa only [k₁, R, τq, Fan.algebraicRealization_over] using hover
  have hg' : (k₁.inv ≫ e.inv ≫ g) ≫ (P ↘ S) = R.tower.toBase ≫ f[Θ] := by
    simp only [Category.assoc, hg, ← h₀, Iso.inv_hom_id_assoc, ← hover']
  have hbir' : Scheme.BirationalOver (k₁.inv ≫ e.inv ≫ g) (𝟙 P) := by
    refine Scheme.BirationalOver.trans (sY := g) ⟨.ofIso (e ≪≫ k₁).symm, ?_⟩ hbir
    simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso]
  refine ⟨hg', hbir', ?_⟩
  let z := (R.tower.picardMarking (R.isLift.isClosedPointTower hV₀) f[Θ]).symm
    (Additive.ofMul (pullback (k₁.inv ≫ e.inv ≫ g) H))
  have hm : ((U.picardMarking hU f[Ψ]).symm
      (Additive.ofMul (pullback e.inv (pullback g H)))).2 k = x.2 l := by
    simp only [horders, k, Fin.addCases_right, Function.comp_apply, hidx, x]
  obtain ⟨hz₀, hz₁, hzfirst, hztail⟩ := hcoord (pullback e.inv (pullback g H))
  have hz₀' : (C[b',0,hΘ,s',hs']).repr z.1 0 = a := by
    simpa only [z, k₁, τq, R, ← pullback_comp, Category.assoc, Fan.algebraicRealization_over,
      hβ] using hz₀
  have hz₁' : (C[b',0,hΘ,s',hs']).repr z.1 1 = β + a - m j - m l := by
    simpa only [z, k₁, τq, R, ← pullback_comp, Category.assoc, Fan.algebraicRealization_over,
      ha, hm, m, sub_neg_eq_add, add_comm a β] using hz₁
  refine ⟨hz₀', hz₁', ?_, hz₁' ▸ hlt.1, ?_⟩
  · funext i
    refine Fin.addCases (fun f ↦ ?_) (fun f ↦ ?_) i
    · rw [Subsingleton.elim f (0 : Fin 1), Fin.addCases_left]
      have hrev : z.2 (Fin.castAdd (1 + n) (0 : Fin 1)) = -a - x.2 l := by
        convert hzfirst using 1
        · simp only [z, k₁, τq, R, Θ, s', ← pullback_comp, Fan.algebraicRealization_over]
          rfl
        · simp only [Fan.algebraicRealization_over, hβ, hm, a, x]
      exact hrev
    · simpa only [z, k₁, τq, R, Θ, hΘ, hcΘ, s', ← pullback_comp, Category.assoc,
        Fan.algebraicRealization_over, Fin.addCases_right, Function.comp_apply, horders, k, a, x]
        using hztail f
  · rw [Prod.Lex.lt_iff, ofLex_hirzebruchSarkisovBidegree, ofLex_hirzebruchSarkisovBidegree]
    exact Or.inl (by rw [hz₁']; omega)

end Quadric

end QPainleve.BlowupTower.IsClosedPointTower
