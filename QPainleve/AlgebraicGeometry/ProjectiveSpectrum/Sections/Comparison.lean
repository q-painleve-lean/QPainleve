/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.RationalMap

/-!
# Comparing rational projective presentations

A map of line bundles that carries each coordinate section to its counterpart
preserves the rational projective map. It preserves the normalized coordinates
on the common nonvanishing open, where the corresponding ratios are defined.
-/

public section

open CategoryTheory Opposite TopologicalSpace
open HomogeneousLocalization TauCeti.MvPolynomial

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {M N : X.Modules}
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X N]
  {R ι : Type u} [CommRing R] (f : X ⟶ Spec (.of R))
  (s : ι → Γ(M, ⊤)) (t : ι → Γ(N, ⊤))
  (φ : M ⟶ N) (hφ : ∀ j, φ.app ⊤ (s j) = t j)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R
local notation "U[" i "]" => M.nonvanishingLocus (s i)
local notation "V[" i "]" => N.nonvanishingLocus (t i)
local notation "j[" i "]" => Proj.awayι 𝒜 (MvPolynomial.X i)
  (Iff.mpr (MvPolynomial.mem_homogeneousSubmodule _ _) (MvPolynomial.isHomogeneous_X R i)) one_pos
local notation "res[" A ", " W "]" => CategoryTheory.Functor.map (Scheme.Modules.presheaf A)
  (Quiver.Hom.op (homOfLE (le_top : W ≤ ⊤)))

include hφ in
private theorem germ_sectionRatio_projective_eq (i j : ι) {x : X}
    (hxU : x ∈ U[i]) (hxV : x ∈ V[i]) :
    X.presheaf.germ (U[i]) x hxU
      (M.sectionRatio (res[M, U[i]] (s j)) (res[M, U[i]] (s i))
        (by rw [M.nonvanishingLocus_map, inf_idem])) =
    X.presheaf.germ (V[i]) x hxV
      (N.sectionRatio (res[N, V[i]] (t j)) (res[N, V[i]] (t i))
        (by rw [N.nonvanishingLocus_map, inf_idem])) := by
  let W := U[i] ⊓ V[i]
  let p : W ⟶ U[i] := homOfLE inf_le_left
  let q : W ⟶ V[i] := homOfLE inf_le_right
  have hx : x ∈ W := ⟨hxU, hxV⟩
  have hM : W ≤ M.nonvanishingLocus (res[M, W] (s i)) := by
    rw [M.nonvanishingLocus_map]
    exact le_inf le_rfl p.le
  have hN : W ≤ N.nonvanishingLocus (res[N, W] (t i)) := by
    rw [N.nonvanishingLocus_map]
    exact le_inf le_rfl q.le
  have hmap (k : ι) : φ.app W (res[M, W] (s k)) = res[N, W] (t k) := by
    have he := φ.mapPresheaf.naturality_apply (homOfLE (le_top : W ≤ ⊤)).op (s k)
    simpa only [mapPresheaf_app, unop_op, hφ] using he
  have hratio : M.sectionRatio (res[M, W] (s j)) (res[M, W] (s i)) hM =
      N.sectionRatio (res[N, W] (t j)) (res[N, W] (t i)) hN := by
    symm
    apply (N.sectionRatio_eq_iff hN).mpr
    rw [← hmap i, ← Hom.app_smul, M.sectionRatio_smul, hmap j]
  have hrestrictM (k : ι) :
      M.presheaf.map p.op (res[M, U[i]] (s k)) = res[M, W] (s k) := by
    rw [← Functor.map_comp_apply, ← op_comp]
    exact congrArg (fun g : W ⟶ ⊤ ↦ M.presheaf.map g.op (s k)) (Subsingleton.elim _ _)
  have hrestrictN (k : ι) :
      N.presheaf.map q.op (res[N, V[i]] (t k)) = res[N, W] (t k) := by
    rw [← Functor.map_comp_apply, ← op_comp]
    exact congrArg (fun g : W ⟶ ⊤ ↦ N.presheaf.map g.op (t k)) (Subsingleton.elim _ _)
  let a := M.sectionRatio (res[M, U[i]] (s j)) (res[M, U[i]] (s i))
    (by rw [M.nonvanishingLocus_map, inf_idem])
  let b := N.sectionRatio (res[N, V[i]] (t j)) (res[N, V[i]] (t i))
    (by rw [N.nonvanishingLocus_map, inf_idem])
  have ha : X.presheaf.map p.op a = M.sectionRatio (res[M, W] (s j)) (res[M, W] (s i)) hM := by
    simpa only [hrestrictM] using
      M.map_sectionRatio p (res[M, U[i]] (s j)) (res[M, U[i]] (s i))
        (by rw [M.nonvanishingLocus_map, inf_idem])
  have hb : X.presheaf.map q.op b = N.sectionRatio (res[N, W] (t j)) (res[N, W] (t i)) hN := by
    simpa only [hrestrictN] using
      N.map_sectionRatio q (res[N, V[i]] (t j)) (res[N, V[i]] (t i))
        (by rw [N.nonvanishingLocus_map, inf_idem])
  have h := congrArg (X.presheaf.germ W x hx) (ha.trans (hratio.trans hb.symm))
  simpa only [TopCat.Presheaf.germ_res_apply] using h

include hφ in
/-- When a map of line bundles takes one indexed family of sections to the other, the two
projective presentations give the same rational map on a common dense coordinate chart. -/
theorem toRationalMap_partialMapToProjectiveSpace_eq_of_hom [IsIntegral X]
    (i : ι) (hs : Dense (U[i] : Set X)) (ht : Dense (V[i] : Set X)) :
    (M.partialMapToProjectiveSpace f s i hs).toRationalMap =
      (N.partialMapToProjectiveSpace f t i ht).toRationalMap := by
  have hxU : genericPoint X ∈ U[i] :=
    (genericPoint_specializes _).mem_open (U[i]).isOpen hs.nonempty.choose_spec
  have hxV : genericPoint X ∈ V[i] :=
    (genericPoint_specializes _).mem_open (V[i]).isOpen ht.nonempty.choose_spec
  let p := (U[i]).fromSpecStalkOfMem _ hxU ≫ M.toProjectiveSpaceChart f s i
  let q := (V[i]).fromSpecStalkOfMem _ hxV ≫ N.toProjectiveSpaceChart f t i
  have hp : p ≫ j[i] ≫ Proj.toSpecCoeff 𝒜 = X.fromSpecStalk (genericPoint X) ≫ f := by
    simp only [p, Category.assoc, Proj.awayι_toSpecCoeff,
      toProjectiveSpaceChart_toSpecCoeff, Opens.fromSpecStalkOfMem_ι_assoc]
  have hq : q ≫ j[i] ≫ Proj.toSpecCoeff 𝒜 = X.fromSpecStalk (genericPoint X) ≫ f := by
    simp only [q, Category.assoc, Proj.awayι_toSpecCoeff,
      toProjectiveSpaceChart_toSpecCoeff, Opens.fromSpecStalkOfMem_ι_assoc]
  have h : p = q := Proj.eq_of_awayXRatio i p q (hp.trans hq.symm) fun j ↦
    (genericProjectiveChart_preimage_awayXRatio (R := R) (f := f) i j hxU).trans
      ((germ_sectionRatio_projective_eq s t φ hφ i j hxU hxV).trans
        (genericProjectiveChart_preimage_awayXRatio (R := R) (f := f) i j hxV).symm)
  apply RationalMap.eq_of_fromFunctionField_eq
  rw [RationalMap.fromFunctionField_toRationalMap, RationalMap.fromFunctionField_toRationalMap]
  rw [fromFunctionField_partialMapToProjectiveSpace f s i hs hxU,
    fromFunctionField_partialMapToProjectiveSpace f t i ht hxV, ← Category.assoc,
    ← Category.assoc]
  exact congrArg (· ≫ j[i]) h

end AlgebraicGeometry.Scheme.Modules
