/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.OppositeSection

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.Fan.Logarithmic.Subdivision
import QPainleve.Geometry.Toric.Fan.Mutation.Tower
import QPainleve.Geometry.Toric.Fan.Picard.Homaloidal
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower
import QPainleve.SignedClusterModularGroup.SarkisovDegree.ToricLink
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# The quadric Sarkisov block with a corner and a smooth center

In the frame of the exchanged ruling, the first link at the toric corner gives
a Hirzebruch-one surface. The smooth center on the opposite section lifts
uniquely to the common toric blowup. It remains the first center over its image
in the transported tower. The link at this point and the final ruling exchange
give the new resolution over a quadric and compute its Picard coordinates.
The original logarithmic pole ideal works for each regular projection in this
block, and its inverse image works on the final transported point tower.

This is the corner case of the two-point block in Lutz's appendix to
[*Homological mirror symmetry for log Calabi–Yau surfaces*][HKL],
Proposition 8.11, Cases B and C.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

local notation "X[" coeff "," Δ "]" => Fan.finiteFanScheme coeff Δ
local notation "f[" Δ "]" => Fan.finiteFanSchemeToSpec k₀ Δ
local notation "I[" σ "]" => Scheme.Hom.ker (Fan.distinguishedSection (R := k₀) _ σ)
local notation "π[" H "]" => FanHom.finiteFanSchemeHom k₀ (Fan.IsSubdivision.toFanHom H)
local notation "D[" Δ "," hc "]" => Fan.toricBoundaryIdeal k₀ Δ (Fan.IsComplete.nonempty_cones hc)
local notation "R[" f "]" => ramificationIdealSheaf k₀ f
local notation "S" => Spec (CommRingCat.of k₀)
local notation "P" => Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k₀ (Fin 3 → k₀) 1)
local notation "pt" => IsLocalRing.closedPoint k₀
local notation "dim(" b ")" =>
  Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "p[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ k₀ dim(b)
    (Module.Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c

section Quadric

variable (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hcΦ : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
  (σ : Φ.cones) (hσ : σ.val = hull ℝ (Set.range (i ∘ b)))
  {n : ℕ} {Y : Scheme} {T : BlowupTower X[k₀,Φ] (n + 2) Y} (hT : IsClosedPointTower X[k₀,Φ] T)

local notation "C[" b "," e "," h "," r "," hr "]" => Fan.hirzebruchPicardBasis k₀ b e h r hr
local notation "C₀" => C[b,0,hΦ,r,hr]

include hσ in
private theorem exists_hirzebruchOne_resolution_of_corner_with_smooth_center
    (j l : Fin (n + 2))
    (hj : hT.baseCenter j = (Φ.distinguishedSection (R := k₀) σ) pt)
    (hfirst : ∀ k < j, hT.baseCenter k ≠ (Φ.distinguishedSection (R := k₀) σ) pt)
    (c : k₀ˣ) (hl : hT.baseCenter l = p[b,r 2,c] pt)
    (hlfirst : ∀ k < l, hT.baseCenter k ≠ p[b,r 2,c] pt)
    (L : LineBundleClass Y) :
    let : Nonempty Φ.cones := hcΦ.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      dim(b) ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let x := (T.picardMarking hT f[Φ]).symm (Additive.ofMul L)
    ∃ (Ψ F : Fan i) (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete) (_ : F.IsRegular)
      (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ) (τ : Ψ.cones)
      (v : X[k₀,F] ≅ (I[σ]).blowup) (w : X[k₀,F] ≅ (I[τ]).blowup)
      (d : Basis (Fin 2) ℤ N) (r' : Fin 4 ≃ Ψ.Ray)
      (hr' : (fun k ↦ (r' k).primitiveGenerator) = ![d 0, d 1, -d 0, (1 : ℤ) • d 0 - d 1])
      (q : Y ⟶ X[k₀,F]) (Z : Scheme) (U : BlowupTower X[k₀,Ψ] (1 + (n + 1)) Z)
      (hU : IsClosedPointTower X[k₀,Ψ] U) (e : Y ≅ Z) (c' : k₀ˣ) (l' : Fin (n + 1)),
      v.hom ≫ (I[σ]).blowupToBase = π[s] ∧ w.hom ≫ (I[τ]).blowupToBase = π[t] ∧
      q ≫ π[s] = T.toBase ∧ q ≫ π[t] = e.hom ≫ U.toBase ∧
      j.succAbove l' = l ∧
      let k := l'.natAdd 1
      hU.baseCenter k = p[d,r' 2,c'] pt ∧ (∀ m < k, hU.baseCenter m ≠ p[d,r' 2,c'] pt) ∧
      let : Nonempty Ψ.cones := hcΨ.nonempty_cones
      let : SmoothOfRelativeDimension 2 f[Ψ] :=
        dim(d) ▸ Ψ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΨ
      let y := (U.picardMarking hU f[Ψ]).symm (Additive.ofMul (pullback e.inv L))
      C[d,1,hΨ,r',hr'].repr y.1 0 = (C₀).repr x.1 0 + (C₀).repr x.1 1 + x.2 j ∧
      C[d,1,hΨ,r',hr'].repr y.1 1 = (C₀).repr x.1 1 ∧
      y.2 = Fin.addCases (fun _ : Fin 1 ↦ -(C₀).repr x.1 1 - x.2 j) (x.2 ∘ j.succAbove) := by
  intro _ _ x
  let : Nonempty Φ.cones := hcΦ.nonempty_cones
  let : SmoothOfRelativeDimension 2 f[Φ] :=
    dim(b) ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
  have hrays : Set.range (Fan.Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1} := by
    rw [← r.surjective.range_comp, Function.comp_def, hr]
    ext x
    simp [or_comm, or_assoc]
  have hmove := hT.exists_move_closed_point_blowup_to_front j
    (Φ.isClosed_singleton_distinguishedSection k₀ σ) hj hfirst
  rw [← ((Φ.distinguishedSection (R := k₀) σ)).ker_eq_ker_fromSpecResidueField] at hmove
  obtain ⟨W, A, e, hA, he, hE, hcenters, htail⟩ := hmove
  obtain ⟨Ψ, F, hΨ, hF, hcΨ, _, d, τ, s, t, v, w, r₀, r', hr₀, hr', Z, B, e', hU,
    hd₀, _, _, hv, hw, -, -, -, hproj, hcorner, hretained, hC⟩ :=
    hA.exists_hirzebruch_toric_link_resolution k₀ b 0 hΦ hcΦ hrays σ hσ
  have hr₀' : r₀ = r := Equiv.ext fun k ↦ Fan.Ray.primitiveGenerator_injective
    ((congrFun hr₀ k).trans (congrFun hr k).symm)
  subst r₀
  have hray : (r 2).primitiveGenerator = (r' 2).primitiveGenerator := by
    simp [congrFun hr 2, congrFun hr' 2, hd₀]
  obtain ⟨c', z, hsrc, htgt, hs, ht⟩ := s.exists_binomialCenter_lift_of_shared_ray k₀ t _ _
    hray b d c
  have hjl : l ≠ j := by
    intro hjl
    exact Φ.notMem_isoLocus_distinguishedSection_of_blowup k₀ hΦ dim(b) σ π[s] v hv
      (by rwa [← hj, ← hjl, hl])
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hjl
  let U := (BlowupTower.nil.snoc (I[τ])).append B
  have hcorner' : hU.baseCenter (Fin.castAdd (n + 1) (0 : Fin 1)) ∉ (π[t]).isoLocus := by
    rw [hcorner]
    exact Ψ.notMem_isoLocus_distinguishedSection_of_blowup k₀ hΨ dim(d) τ π[t] w hw
  obtain ⟨hcenter, hfirst'⟩ := hA.first_center_of_toric_link k₀ hU s t v hv hcorner' hretained
    (hsrc.symm ▸ hs) (htgt.symm ▸ ht) k (by rw [hcenters, hk, hl, hsrc])
  have hfirst'' : ∀ m < k, (I[σ]).blowupToBase (hA.baseCenter m) ≠ π[s] z := by
    intro m hm
    rw [hcenters, hsrc]
    exact hlfirst _ (hk ▸ (Fin.strictMono_succAbove j) hm)
  let q := e.hom ≫ A.toBase ≫ v.inv
  have hq : q ≫ π[s] = T.toBase := by simp only [q, Category.assoc, ← hv, Iso.inv_hom_id_assoc, he]
  have hq' : q ≫ π[t] = (e ≪≫ e').hom ≫ U.toBase := by
    simp only [q, Iso.trans_hom, Category.assoc, hproj, U]
  refine ⟨Ψ, F, hΨ, hcΨ, hF, s, t, τ, v, w, d, r', hr', q, Z, U, hU, e ≪≫ e', c', k, hv, hw,
    hq, hq', hk, hcenter.trans htgt, fun m hm ↦ htgt ▸ hfirst' hfirst'' m hm, ?_⟩
  intro _ _ y
  let : Nonempty Ψ.cones := hcΨ.nonempty_cones
  let : SmoothOfRelativeDimension 2 f[Ψ] :=
    dim(d) ▸ Ψ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΨ
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
  have hclass := congrArg (pullback e'.inv) (hC a β (x.2 j) (x.2 ∘ j.succAbove)).1
  rw [pullback_comp, Iso.inv_hom_id, pullback_id] at hclass
  have hy : y = ((a + β + x.2 j) • C' 0 + β • C' 1, x') := by
    apply (LinearEquiv.symm_apply_eq _).mpr
    apply Additive.toMul.injective
    rw [U.picardMarking_apply hU f[Ψ], toMul_ofMul, Iso.trans_inv, ← pullback_comp, ← hL, hmark]
    simpa only [x', Fin.append, ← hx] using! hclass.symm
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
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap k₀ Ψ d (c : k₀) hv[r] hp[r] opp[d,r,hr])

include hσ in
/-- On a quadric written in the frame of the exchanged ruling, take the first
centers at a corner of the chosen section and at a smooth point of the opposite
section. The toric link at the corner, mutation at the transported smooth point,
and ruling exchange give regular projections on the specified resolution,
transported by isomorphisms.

For original fiber and section coefficients β and a in this frame, and base
orders m and m' at the two points, the final coefficients are a and β + a - m - m'.
The second final coefficient is the positive fiber degree at the endpoint.
The pole factorization is preserved along the common toric blowup, its contraction,
the mutation and the final ruling exchange. On the final point tower the pole ideal
is pulled back along the inverse of the composite resolving isomorphism.
The exceptional coordinates record the reverse pivots and the order inherited
from the original tower, including at infinitely near centers. -/
theorem exists_quadric_resolution_of_corner_and_smooth_centers
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f[Φ])
    (hbir : Scheme.BirationalOver g (𝟙 P))
    (j l : Fin (n + 2))
    (hj : hT.baseCenter j = (Φ.distinguishedSection (R := k₀) σ) pt)
    (hjfirst : ∀ k < j, hT.baseCenter k ≠ (Φ.distinguishedSection (R := k₀) σ) pt)
    (c : k₀ˣ) (hl : hT.baseCenter l = p[b,r 2,c] pt)
    (hlfirst : ∀ k < l, hT.baseCenter k ≠ p[b,r 2,c] pt) :
    let : Nonempty Φ.cones := hcΦ.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      dim(b) ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let x := (T.picardMarking hT f[Φ]).symm (Additive.ofMul (pullback g H))
    let β := (C₀).repr x.1 0
    let a := (C₀).repr x.1 1
    let m := fun k ↦ -x.2 k
    ∃ (Ψ F : Fan i) (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete) (_ : F.IsRegular)
      (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ) (τ : Ψ.cones)
      (v : X[k₀,F] ≅ (I[σ]).blowup) (w : X[k₀,F] ≅ (I[τ]).blowup)
      (d : Basis (Fin 2) ℤ N) (r' : Fin 4 ≃ Ψ.Ray)
      (hr' : (fun k ↦ (r' k).primitiveGenerator) = ![d 0, d 1, -d 0, (1 : ℤ) • d 0 - d 1])
      (q : Y ⟶ X[k₀,F]) (Z : Scheme) (U : BlowupTower X[k₀,Ψ] (1 + (n + 1)) Z)
      (hU : IsClosedPointTower X[k₀,Ψ] U) (e : Y ≅ Z) (c' : k₀ˣ) (l' : Fin (n + 1)),
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
        dim(d) ▸ Ψ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΨ
      let : SmoothOfRelativeDimension 2 f[Θ] :=
        dim(d) ▸ Θ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΘ
      let : IsIntegral Z := hU.isIntegral f[Ψ]
      let : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two f[Ψ]
      ∃ (b' : Basis (Fin 2) ℤ N)
        (hs' : (fun k ↦ (s' k).primitiveGenerator) = ![b' 0, b' 1, -b' 0, (0 : ℤ) • b' 0 - b' 1])
        (W₀ : Scheme) (V₀ : BlowupTower X[k₀,Θ] (1 + (1 + n)) W₀)
        (u₀ : Z ≅ W₀) (W : Scheme) (V : BlowupTower X[k₀,Θ] (1 + (1 + n)) W)
        (hV : IsClosedPointTower X[k₀,Θ] V) (k₁ : Z ≅ W),
        let τq := ((Fan.quadricRulingExchange b' hΘ hcΘ s' hs').toFanHom.finiteFanSchemeHom k₀)
        U.toBase.toRationalMap.comp μ[Ψ,d,r',hr',c'] = (u₀.hom ≫ V₀.toBase).toRationalMap ∧
        (u₀.hom ≫ V₀.toBase) ≫ τq = k₁.hom ≫ V.toBase ∧
        let g' := k₁.inv ≫ e.inv ≫ g
        g' ≫ (P ↘ S) = V.toBase ≫ f[Θ] ∧ Scheme.BirationalOver g' (𝟙 P) ∧
        let z := (V.picardMarking hV f[Θ]).symm (Additive.ofMul (pullback g' H))
        (C[b',0,hΘ,s',hs']).repr z.1 0 = a ∧
        (C[b',0,hΘ,s',hs']).repr z.1 1 = β + a - m j - m l ∧
        z.2 = Fin.addCases (fun _ : Fin 1 ↦ -a - x.2 l)
          ((Fin.addCases (fun _ : Fin 1 ↦ -a - x.2 j) (x.2 ∘ j.succAbove) :
            Fin (1 + (n + 1)) → ℤ) ∘ k.succAbove) ∧
        0 < (C[b',0,hΘ,s',hs']).repr z.1 1 ∧
        letI : SmoothOfRelativeDimension 2 (X[k₀,Φ] ↘ S) := by
          simpa only [Fan.finiteFanScheme_over k₀] using
            (dim(b) ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ :
              SmoothOfRelativeDimension 2 f[Φ])
        letI : SmoothOfRelativeDimension 2 (X[k₀,Θ] ↘ S) := by
          simpa only [Fan.finiteFanScheme_over k₀] using
            (dim(d) ▸ Θ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΘ :
              SmoothOfRelativeDimension 2 f[Θ])
        letI : Y.Over S := ⟨T.toBase ≫ (X[k₀,Φ] ↘ S)⟩
        letI : Smooth (Y ↘ S) := (hT.smoothOfRelativeDimension (X[k₀,Φ] ↘ S)).smooth
        letI : T.toBase.IsOver S := ⟨rfl⟩
        ∃ (_ : q.IsOver S) (_ : (e.hom ≫ U.toBase).IsOver S)
          (_ : (e.hom ≫ u₀.hom ≫ V₀.toBase).IsOver S)
          (_ : (e.hom ≫ k₁.hom ≫ V.toBase).IsOver S),
          ∀ D : Y.IdealSheafData, D[Φ,hcΦ].comap T.toBase = D * R[T.toBase] →
            D[F,s.isComplete_iff.mpr hcΦ].comap q = D * R[q] ∧
            D[Ψ,hcΨ].comap (e.hom ≫ U.toBase) = D * R[e.hom ≫ U.toBase] ∧
            D[Θ,hcΘ].comap (e.hom ≫ u₀.hom ≫ V₀.toBase) =
              D * R[e.hom ≫ u₀.hom ≫ V₀.toBase] ∧
            D[Θ,hcΘ].comap (e.hom ≫ k₁.hom ≫ V.toBase) =
              D * R[e.hom ≫ k₁.hom ≫ V.toBase] ∧
            D[Θ,hcΘ].comap V.toBase =
              D.comap (e ≪≫ k₁).inv * hV.ramificationIdealSheafToBase k₀ := by
  intro hcones hdim x β a m
  let := hcones
  let := hdim
  -- Resolve the first link and find the lifted smooth pivot in the ordered tower.
  obtain ⟨Ψ, F, hΨ, hcΨ, hF, s, t, τ, v, w, d, r', hr', q, Z, U, hU, e, c', l', hv, hw,
      hq, hq', hidx, hk, hkfirst, ha, hβ, horders⟩ :=
    exists_hirzebruchOne_resolution_of_corner_with_smooth_center k₀ b hΦ hcΦ r hr σ hσ hT
      j l hj hjfirst c hl hlfirst (pullback g H)
  let k := l'.natAdd 1
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
  obtain ⟨b', hs', W₀, V₀, hV₀, u₀, hμ, _, hover, hcoord⟩ :=
    hU.exists_quadric_resolution_of_hirzebruchOne_mutation k₀ d hΨ hcΨ r' hr' c' k hk hkfirst
  let τq := ((Fan.quadricRulingExchange b' hΘ hcΘ s' hs').toFanHom.finiteFanSchemeHom k₀)
  let R := V₀.transport (asIso τq)
  let k₁ := u₀ ≪≫ R.iso
  have hproj : (u₀.hom ≫ V₀.toBase) ≫ τq = k₁.hom ≫ R.tower.toBase := by
    rw [Category.assoc, Iso.trans_hom, Category.assoc, R.isLift.hom_toBase, asIso_hom]
  have h₀ : e.hom ≫ U.toBase ≫ f[Ψ] = T.toBase ≫ f[Φ] := by
    rw [← Category.assoc, ← hq', Category.assoc,
      FanHom.finiteFanSchemeHom_comp_finiteFanSchemeToSpec,
      ← FanHom.finiteFanSchemeHom_comp_finiteFanSchemeToSpec k₀ (Fan.IsSubdivision.toFanHom s),
      ← Category.assoc, hq]
  refine ⟨b', hs', W₀, V₀, u₀, R.top, R.tower, R.isLift.isClosedPointTower hV₀, k₁, hμ, hproj, ?_⟩
  have hover' : k₁.hom ≫ R.tower.toBase ≫ f[Θ] = U.toBase ≫ f[Ψ] := by
    simpa only [k₁, R, τq, Fan.finiteFanScheme_over k₀] using hover
  have hg' : (k₁.inv ≫ e.inv ≫ g) ≫ (P ↘ S) = R.tower.toBase ≫ f[Θ] := by
    simp only [Category.assoc, hg, ← h₀, Iso.inv_hom_id_assoc, ← hover']
  have hbir' : Scheme.BirationalOver (k₁.inv ≫ e.inv ≫ g) (𝟙 P) := by
    refine Scheme.BirationalOver.trans (sY := g) ⟨.ofIso (e ≪≫ k₁).symm, ?_⟩ hbir
    simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso]
  refine ⟨hg', hbir', ?_⟩
  -- Compute the two ruling coefficients and the reverse-pivot orders in the final marking.
  let z := (R.tower.picardMarking (R.isLift.isClosedPointTower hV₀) f[Θ]).symm
    (Additive.ofMul (pullback (k₁.inv ≫ e.inv ≫ g) H))
  have hm : ((U.picardMarking hU f[Ψ]).symm
      (Additive.ofMul (pullback e.inv (pullback g H)))).2 k = x.2 l := by
    simp only [horders, k, Fin.addCases_right, Function.comp_apply, hidx, x]
  obtain ⟨hz₀, hz₁, hzfirst, hztail⟩ := hcoord (pullback e.inv (pullback g H))
  have hz₀' : (C[b',0,hΘ,s',hs']).repr z.1 0 = a := by
    simpa only [z, k₁, τq, R, ← pullback_comp, Category.assoc, Fan.finiteFanScheme_over k₀,
      hβ] using hz₀
  have hz₁' : (C[b',0,hΘ,s',hs']).repr z.1 1 = β + a - m j - m l := by
    simpa only [z, k₁, τq, R, ← pullback_comp, Category.assoc, Fan.finiteFanScheme_over k₀,
      ha, hm, m, sub_neg_eq_add, add_comm a β] using hz₁
  let : X[k₀,Θ].IsProjectiveOver k₀ := Θ.isProjectiveOver_quadric k₀ b' hΘ hcΘ s' hs'
  have hpos : 0 < (C[b',0,hΘ,s',hs']).repr z.1 1 :=
    ((R.isLift.isClosedPointTower hV₀).hirzebruch_resolution_degree_bounds k₀
      b' 0 hΘ hcΘ s' hs' (k₁.inv ≫ e.inv ≫ g)
      (by simpa only [Fan.finiteFanScheme_over k₀] using hg') hbir').1
  refine ⟨hz₀', hz₁', ?_, hpos, ?_⟩
  · funext i
    refine Fin.addCases (fun f ↦ ?_) (fun f ↦ ?_) i
    · rw [Subsingleton.elim f (0 : Fin 1), Fin.addCases_left]
      have hrev : z.2 (Fin.castAdd (1 + n) (0 : Fin 1)) = -a - x.2 l := by
        convert hzfirst using 1
        · simp only [z, k₁, τq, R, Θ, s', ← pullback_comp, Fan.finiteFanScheme_over k₀]
          rfl
        · simp only [Fan.finiteFanScheme_over k₀, hβ, hm, a, x]
      exact hrev
    · simpa only [z, k₁, τq, R, Θ, hΘ, hcΘ, s', ← pullback_comp, Category.assoc,
        Fan.finiteFanScheme_over k₀, Fin.addCases_right, Function.comp_apply, horders, k, a, x]
        using hztail f
  · -- Compare the pole ideals on the original resolution before moving to the final tower.
    let : SmoothOfRelativeDimension 2 (X[k₀,Φ] ↘ S) := by
      simpa only [Fan.finiteFanScheme_over k₀] using hdim
    let : SmoothOfRelativeDimension 2 (X[k₀,Ψ] ↘ S) := by
      simpa only [Fan.finiteFanScheme_over k₀] using hdimΨ
    let : SmoothOfRelativeDimension 2 (X[k₀,Θ] ↘ S) := by
      simpa only [Fan.finiteFanScheme_over k₀] using hdimΘ
    let : Smooth (X[k₀,Θ] ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : Y.Over S := ⟨T.toBase ≫ (X[k₀,Φ] ↘ S)⟩
    let : T.toBase.IsOver S := ⟨rfl⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension (X[k₀,Φ] ↘ S)
    let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : Z.Over S := ⟨U.toBase ≫ (X[k₀,Ψ] ↘ S)⟩
    let : SmoothOfRelativeDimension 2 (Z ↘ S) := hU.smoothOfRelativeDimension (X[k₀,Ψ] ↘ S)
    let : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : q.IsOver S := ⟨by rw [← comp_over π[s] S, ← Category.assoc, hq]; rfl⟩
    have hy : (Y ↘ S) = T.toBase ≫ (X[k₀,Φ] ↘ S) := rfl
    let : (e.hom ≫ U.toBase).IsOver S := ⟨by
      rw [hy, Category.assoc]
      simpa only [Fan.finiteFanScheme_over k₀] using h₀⟩
    have hfinal : (e.hom ≫ k₁.hom ≫ R.tower.toBase).IsOver S := ⟨by
      rw [hy]
      simpa only [Category.assoc, Fan.finiteFanScheme_over k₀] using
        (congrArg (e.hom ≫ ·) hover').trans h₀⟩
    have hstep : (e.hom ≫ u₀.hom ≫ V₀.toBase) ≫ τq = e.hom ≫ k₁.hom ≫ R.tower.toBase := by
      simpa only [Category.assoc] using congrArg (e.hom ≫ ·) hproj
    have hmutation : (e.hom ≫ u₀.hom ≫ V₀.toBase).IsOver S := ⟨by
      rw [← comp_over τq S, ← Category.assoc, hstep, comp_over]⟩
    refine ⟨‹_›, ‹_›, hmutation, hfinal, fun D hpole ↦ ?_⟩
    let : IsIntegral Y := hT.isIntegral (X[k₀,Φ] ↘ S)
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two
      (X[k₀,Φ] ↘ S)
    have : IsDominant (q ≫ π[s]) := hq ▸ inferInstanceAs (IsDominant T.toBase)
    obtain ⟨_, _, A, a, hA, ha, -, -⟩ :=
      s.exists_toric_subdivision_blowup_tower k₀ hΦ hF hcΦ.nonempty_cones dim(b)
    have : IsModification A.toBase :=
      hA.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X[k₀,Φ] ↘ S)
    have : IsModification π[s] := ha ▸ inferInstanceAs (IsModification (a.hom ≫ A.toBase))
    have : IsDominant q := IsModification.isDominant_of_comp q π[s]
    have hbase : D[Φ,hcΦ].comap (q ≫ π[s]) = D * R[q ≫ π[s]] :=
      (congrArg (D[Φ,hcΦ].comap ·) hq).trans
        (hpole.trans (congrArg (D * ·) (ramificationIdealSheaf_congr k₀ hq).symm))
    have hFpole :=
      (s.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf_comp_iff k₀ hΦ hF hcΦ dim(b) q
        D).mp hbase
    have hΨpole :=
      (t.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf_comp_iff k₀ hΨ hF hcΨ dim(b) q
        D).mpr hFpole
    have hbefore : D[Ψ,hcΨ].comap (e.hom ≫ U.toBase) = D * R[e.hom ≫ U.toBase] :=
      (congrArg (D[Ψ,hcΨ].comap ·) hq'.symm).trans
        (hΨpole.trans (congrArg (D * ·) (ramificationIdealSheaf_congr k₀ hq')))
    have hramU := hU.comap_ramificationIdealSheafToBase k₀ e (f := e.hom ≫ U.toBase) rfl
    have hU' : D[Ψ,hcΨ].comap U.toBase = D.comap e.inv * hU.ramificationIdealSheafToBase k₀ := by
      have h := hbefore
      rw [← hramU] at h
      simpa only [comap_mul, ← comap_comp, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Scheme.IdealSheafData.comap_id] using congrArg (·.comap e.inv) h
    obtain ⟨hOver, hiff⟩ := (r' 2).mutation_resolution_poleIdeal_iff k₀ d opp[d,r',hr'] c'
      hU hΨ hcΨ (u₀.hom ≫ V₀.toBase) (D.comap e.inv) hμ
    let : (u₀.hom ≫ V₀.toBase).IsOver S := hOver
    have hz : (Z ↘ S) = U.toBase ≫ (X[k₀,Ψ] ↘ S) := rfl
    have : e.hom.IsOver S := ⟨by
      rw [hz, hy]
      simpa only [Fan.finiteFanScheme_over k₀] using h₀⟩
    let p := u₀.hom ≫ V₀.toBase
    have hmut : D[Θ,hcΘ].comap (e.hom ≫ p) = D * R[e.hom ≫ p] := by
      apply comap_eq_mul_ramificationIdealSheaf_comp k₀ e.hom p 2 (hiff.mp hU')
      simp only [← comap_comp, Iso.hom_inv_id, Scheme.IdealSheafData.comap_id,
        ramificationIdealSheaf_eq_top_of_isOpenImmersion, mul_top]
    have hexchange : D[Θ,hcΘ].comap τq = D[Θ,hcΘ] * R[τq] := by
      rw [ramificationIdealSheaf_eq_top_of_isOpenImmersion, mul_top]
      exact FanEquiv.comap_toricBoundaryIdeal_finiteFanSchemeHom k₀
        (Fan.quadricRulingExchange b' hΘ hcΘ s' hs') _ _
    have hafter := comap_eq_mul_ramificationIdealSheaf_comp k₀ _ τq 2 hexchange hmut
    have hlast : D[Θ,hcΘ].comap (e.hom ≫ k₁.hom ≫ R.tower.toBase) =
        D * R[e.hom ≫ k₁.hom ≫ R.tower.toBase] :=
      (congrArg (D[Θ,hcΘ].comap ·) hstep.symm).trans
        (hafter.trans (congrArg (D * ·) (ramificationIdealSheaf_congr k₀ hstep)))
    refine ⟨hFpole, hbefore, hmut, hlast, ?_⟩
    let a := e ≪≫ k₁
    have ha : a.hom ≫ R.tower.toBase = e.hom ≫ k₁.hom ≫ R.tower.toBase := by
      simp only [a, Iso.trans_hom, Category.assoc]
    rw [← (R.isLift.isClosedPointTower hV₀).comap_ramificationIdealSheafToBase k₀ a ha,
      ← ha] at hlast
    simpa only [comap_mul, ← comap_comp, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Scheme.IdealSheafData.comap_id] using congrArg (·.comap a.inv) hlast

end Quadric

end QPainleve.BlowupTower.IsClosedPointTower
