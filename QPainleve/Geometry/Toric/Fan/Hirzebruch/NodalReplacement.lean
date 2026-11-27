/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Numbering
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Locus
public import QPainleve.Geometry.Toric.Fan.Hirzebruch.Bisection

import QPainleve.AlgebraicGeometry.Blowup.Disjoint
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Complexity
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Complexity
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Interchange
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Subdivision
import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Integral
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Smooth
import QPainleve.Geometry.Toric.Fan.StarSubdivision.ClosedPoint
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Replacing the internal center of a Hirzebruch-one bisection

Contracting the negative section of a Hirzebruch-one pair with an anticanonical
bisection gives a smooth boundary center on the plane. Blowing up a node of that
plane boundary gives another Hirzebruch-one surface. The two centers are disjoint,
so the replacement is resolved by one nodal blowup of the original surface and
one internal blowup of the new surface. The new boundary has lower complexity.

This is the index-one bisection case in
[Gross, Hacking and Keel, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory Limits Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Plane" => Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k₀)
local notation "I[" x "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ x)
local notation "J[" x "]" => vanishingIdeal
  (TopologicalSpace.Closeds.mk (closure ({x} : Set Plane)) isClosed_closure)
local notation "π[" x "]" => blowupToBase (I[x])
local notation "T[" x "]" => BlowupTower.nil.snoc (I[x])
local notation "R[" D "," x "]" => radical (comap D (π[x]))
local notation "RN[" D "," x "]" => radical (comap D (BlowupTower.toBase (T[x])))
local notation "St[" I "," D "]" => Scheme.Hom.ker (blowupMap I (subschemeι D))

local instance : SmoothOfRelativeDimension 2 (Plane ↘ S) :=
  Proj.smoothOfRelativeDimension_toSpecCoeff k₀ 2

open TauCeti.SymmetricAlgebra in
private theorem complexity_drop_of_bisection_replacement
    {X : Scheme} {D : X.IdealSheafData} {A : (Plane).IdealSheafData} {p q : Plane}
    (a : X ≅ (I[p]).blowup) (u : D.subscheme ≅ A.subscheme)
    (hu : u.hom ≫ A.subschemeι = D.subschemeι ≫ a.hom ≫ π[p])
    (hp : IsClosed ({p} : Set Plane)) (hA : A.IsEffectiveCartier) (hD : D.IsEffectiveCartier)
    (hT : IsNodalBoundaryTower A (Plane ↘ S) (𝟙 Plane) T[q]) :
    (R[A,q]).boundaryComplexity + 1 = D.boundaryComplexity := by
  let : IsIntegral Plane := Proj.isIntegral_polynomialProj
  let : IsNoetherian Plane := isNoetherian_of_finiteType (Plane ↘ S)
  let : Module.Finite ℤ (Additive (LineBundleClass Plane)) :=
    Module.Finite.equiv ((LineBundleClass.pullbackEquiv
      (Pi.basisFun k₀ (Fin 3)).polynomialProjIso).toAdditive.toIntLinearEquiv)
  let hP : IsClosedPointTower Plane T[p] := .snoc .nil p hp rfl
  let B := D.comap a.inv
  obtain ⟨v, hv⟩ := D.exists_iso_of_comap_eq_ker a.symm B.subschemeι B.ker_subschemeι.symm
  have hproj : (v ≪≫ u).hom ≫ A.subschemeι = B.subschemeι ≫ T[p].toBase := by
    rw [Iso.trans_hom, Category.assoc, hu, reassoc_of% hv, Iso.symm_hom,
      Iso.inv_hom_id_assoc, toBase_snoc, toBase_nil, Category.comp_id]
  have hdrop := hP.boundaryComplexity_eq_add_length_of_subschemeIso k₀ hA (hD.comap a.inv)
    (v ≪≫ u) hproj
  have hdrop' : D.boundaryComplexity = A.boundaryComplexity + 1 := by
    simpa only [Nat.zero_add, Nat.cast_one] using
      ((boundaryComplexity_comap_iso a.symm D).symm.trans hdrop)
  have hkeep := hT.boundaryComplexity_comap hA
  simpa only [toBase_snoc, toBase_nil, Category.comp_id, boundaryComplexity_radical] using
    (congrArg (· + 1) hkeep).trans hdrop'.symm

omit [IsAlgClosed k₀] in
private theorem bisection_replacement_square
    {X : Scheme} [X.Over S] {D : X.IdealSheafData} {A : (Plane).IdealSheafData}
    [IsReduced A.subscheme] {p q : Plane} {x : X} (a : X ≅ (I[p]).blowup)
    (ha : a.hom ≫ π[p] ≫ Plane ↘ S = X ↘ S)
    (u : D.subscheme ≅ A.subscheme)
    (hu : u.hom ≫ A.subschemeι = D.subschemeι ≫ a.hom ≫ π[p])
    (hJ : ((I[p]).comap A.subschemeι).IsEffectiveCartier)
    (hp : IsClosed ({p} : Set Plane)) (hx : IsClosed ({x} : Set X))
    (hpD : p ∈ A.smoothBoundaryPoints (Plane ↘ S))
    (hxD : D.IsNodeOfReducedBoundary (X ↘ S) x) (hxq : (a.hom ≫ π[p]) x = q)
    (hne : q ≠ p) :
    ∃ (y : (I[q]).blowup) (e : (I[x]).blowup ≅ (I[y]).blowup),
      IsClosed ({y} : Set (I[q]).blowup) ∧ π[q] y = p ∧
      y ∈ (R[A,q]).smoothBoundaryPoints (π[q] ≫ Plane ↘ S) ∧
      IsPullback (π[x]) (e.hom ≫ π[y]) (a.hom ≫ π[p]) (π[q]) ∧
      (St[I[y],R[A,q]]).comap e.hom = R[D,x] := by
  have hD : St[I[p],A] = D.comap a.inv := by
    have h := (I[p]).eq_blowupLift hJ (g := u.inv ≫ D.subschemeι ≫ a.hom) (by
      simp only [Category.assoc, ← hu, Iso.inv_hom_id_assoc])
    have hker : ((I[p]).blowupLift A.subschemeι hJ).ker = St[I[p],A] := by
      rw [ker_blowupLift, ker_blowupMap]
    rw [← hker, ← h, Scheme.Hom.ker_comp_of_isIso]
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, ker_subschemeι] using
      ((D.subschemeι ≫ a.hom).comap_ker_comp_of_isClosedImmersion a.inv).symm
  let z := a.hom x
  have hz : IsClosed ({z} : Set (I[p]).blowup) := by
    simpa only [z, Set.image_singleton] using a.hom.isClosedMap _ hx
  have hzq : π[p] z = q := (Scheme.Hom.comp_apply a.hom (π[p]) x).symm.trans hxq
  have hbase : a.inv ≫ X ↘ S = π[p] ≫ Plane ↘ S := by
    rw [← ha, Iso.inv_hom_id_assoc]
  have hzD : St[I[p],A].IsNodeOfReducedBoundary (π[p] ≫ Plane ↘ S) z := by
    rw [hD, ← hbase]
    apply (D.isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion _ a.inv z).mpr
    have hback : a.inv z = x := by
      dsimp only [z]
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    rwa [hback]
  clear hxq
  subst q
  obtain ⟨y, v, hq, -, hJ', hy, hyp, hI', hyD, -, hv₂, hvD, -, -⟩ :=
    A.exists_iso_internal_nodal_blowup_interchange (Plane ↘ S) hp hz hne hpD hzD
  have hIₓ : (I[z]).comap a.hom = I[x] := a.hom.comap_ker_fromSpecResidueField_apply x
  let w := blowupIso a ((congrArg (·.comap a.hom) hJ').trans hIₓ).symm
  have hw : w.hom ≫ ((I[π[p] z]).comap π[p]).blowupToBase = π[x] ≫ a.hom :=
    blowupIso_hom_blowupToBase _ _
  -- Rewrite the pulled-back center to the actual closed point on the new surface.
  generalize htmp : (I[p]).comap π[π[p] z] = K at v hv₂ hvD hI'
  clear htmp
  subst K
  let e := w ≪≫ v
  have he : e.hom ≫ π[y] = w.hom ≫ (I[π[p] z]).blowupMap π[p] := by
    simp only [e, Iso.trans_hom, Category.assoc, hv₂]
  have hd : Disjoint ((I[π[p] z]).support : Set Plane) (I[p]).support := by
    rw [Scheme.support_ker_fromSpecResidueField_of_isClosed hq,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hp, Set.disjoint_singleton]
    simpa using hne
  have hpb := (I[π[p] z]).isPullback_blowupMap_of_disjoint (I[p]) hd
  refine ⟨y, e, hy, hyp, hyD, ?_, ?_⟩
  · exact hpb.of_iso' w a (Iso.refl _) (Iso.refl _) hw
      (by simpa only [Iso.refl_hom, Category.comp_id] using he.symm) (by simp) (by simp)
  · rw [Iso.trans_hom, comap_comp]
    rw [hvD, ← radical_comap_of_isOpenImmersion, ← comap_comp, hw, comap_comp, hD]
    rw [← comap_comp D a.hom a.inv, Iso.hom_inv_id, comap_id]

private theorem numbered_node_image_of_bisection_contraction
    {X : Scheme} [X.Over S] {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
    {n : ℕ} [NeZero n] {α : Type*} {m : α → (D.subscheme ↘ S).smoothLocus}
    (B : Scheme.NodalCycleNumbering m n) (j : ZMod n)
    {A : (Plane).IdealSheafData} (f : X ⟶ Plane) (hf : f ≫ Plane ↘ S = X ↘ S)
    (u : D.subscheme ≅ A.subscheme) (hu : u.hom ≫ A.subschemeι = D.subschemeι ≫ f) :
    ∃ hA : PrestableFamily (A.subscheme ↘ S),
      letI := hA
      ∃ C : Scheme.NodalCycleNumbering
        (Empty.elim : Empty → (A.subscheme ↘ S).smoothLocus) n,
        C.ambientNode j = f (B.ambientNode j) := by
  have hbase : u.hom ≫ A.subscheme ↘ S = D.subscheme ↘ S := by
    rw [A.over_eq_subschemeι_comp, ← Category.assoc, hu, Category.assoc, hf,
      D.over_eq_subschemeι_comp]
  let : u.hom.IsOver S := ⟨hbase⟩
  let hA : PrestableFamily (A.subscheme ↘ S) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily) u.hom _).mp
      (hbase.symm ▸ ‹PrestableFamily (D.subscheme ↘ S)›)
  let C := u.mapNodalCycleNumbering B (q := (Empty.elim : Empty → _))
  refine ⟨hA, C, ?_⟩
  have hsing := u.singularLocusIso_hom_subschemeι_assoc (R := k₀) A.subschemeι
  rw [hu] at hsing
  simpa only [C, Scheme.NodalCycleNumbering.ambientNode_def, Scheme.Hom.comp_apply,
    CategoryTheory.Iso.node_mapNodalCycleNumbering] using
    (congrArg (fun g : (D.subscheme.singularLocus k₀).subscheme ⟶ Plane ↦ g (B.node j)) hsing)

open AlgebraicGeometry.Proj in
private theorem exists_numbered_hirzebruch_model_of_bisection_plane
    {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V} (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    {A : (Plane).IdealSheafData} [PrestableFamily (A.subscheme ↘ S)]
    {n : ℕ} [NeZero n] {m : Empty → (A.subscheme ↘ S).smoothLocus}
    (B : Scheme.NodalCycleNumbering m n) (j : ZMod n) (hA : A.IsEffectiveCartier)
    (hcan : LineBundleClass.mk hA.toInvertibleSheaf =
      LineBundleClass.mk (canonicalBundle k₀ Plane 2)) :
    let q := B.ambientNode j
    ∃ (Ψ : Fan i) (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete) (d : Basis (Fin 2) ℤ N)
      (r' : Fin 4 ≃ Ψ.Ray) (f : (Ψ.finiteFanScheme k₀) ≅ (I[q]).blowup),
      let X' := (Ψ.finiteFanScheme k₀)
      letI : Nonempty Ψ.cones := hcΨ.nonempty_cones
      letI : SmoothOfRelativeDimension 2 (X' ↘ S) := by
        rw [finiteFanScheme_over]
        exact ((finrank_eq_card_basis d).trans (Fintype.card_fin 2)) ▸
          Ψ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΨ
      let E := (RN[A,q]).comap f.hom
      (fun l ↦ (r' l).primitiveGenerator) = ![d 0, d 1, -d 0, d 0 - d 1] ∧
      f.hom ≫ π[q] ≫ Plane ↘ S = X' ↘ S ∧
      ∃ (hE : E.IsEffectiveCartier) (hPre : PrestableFamily (E.subscheme ↘ S)),
        letI := hPre
        LineBundleClass.mk hE.toInvertibleSheaf = LineBundleClass.mk (canonicalBundle k₀ X' 2) ∧
        Nonempty (Scheme.NodalCycleNumbering (Empty.elim : Empty → (E.subscheme ↘ S).smoothLocus)
          (n + 1)) := by
  intro q
  have hT : IsNodalBoundaryTower A (Plane ↘ S) (𝟙 Plane) T[q] :=
    isNodalBoundaryTower_numbered_node B j
  have hToBase : T[q].toBase = π[q] := by rw [toBase_snoc, toBase_nil, Category.comp_id]
  let a := projectivePlaneIso k₀ b hi
  let : Nonempty (projectiveSpace b hi).cones := (isComplete_projectiveSpace b hi).nonempty_cones
  let : a.hom.IsOver S := ⟨by
    rw [over_polynomial (R := k₀) (σ := Fin 3), projectivePlaneIso_hom_toSpecCoeff,
      finiteFanScheme_over]⟩
  have hnodal : AtWorstNodalOfRelativeDimensionOne (A.subschemeι ≫ Plane ↘ S) := by
    rw [← A.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  obtain ⟨Ψ, hΨ, hcΨ, d, _, f, hr', -, hπ, -, -, hE, hK, -⟩ :=
    exists_hirzebruch_one_model_of_plane_nodal_blowup k₀ b hi a hA hnodal q
      (B.isClosed_ambientNode j) (B.isNodeOfReducedBoundary_ambientNode j rfl) hcan
  obtain ⟨r', hr'⟩ := exists_rayEquiv_of_hirzebruch_ray_generators d 1 (by simpa using hr')
  let E := (RN[A,q]).comap f.hom
  have hEeq : (A.comap (f.hom ≫ π[q])).radical = E := by
    rw [comap_comp, radical_comap_of_isOpenImmersion, ← hToBase]
  let : Nonempty Ψ.cones := hcΨ.nonempty_cones
  let : (I[q]).blowup.Over S := ⟨T[q].toBase ≫ Plane ↘ S⟩
  have hπ' : f.hom ≫ π[q] ≫ Plane ↘ S = (Ψ.finiteFanScheme k₀) ↘ S := by
    rw [← Category.assoc]
    let : (f.hom ≫ π[q]).IsOver S := hπ
    exact comp_over (f.hom ≫ π[q]) S
  obtain ⟨v, hv⟩ := (RN[A,q]).exists_iso_of_comap_eq_ker f E.subschemeι E.ker_subschemeι.symm
  have hfOver : f.hom ≫ (I[q]).blowup ↘ S = (Ψ.finiteFanScheme k₀) ↘ S :=
    (congrArg (fun g ↦ f.hom ≫ g ≫ Plane ↘ S) hToBase).trans hπ'
  have hbase : v.hom ≫ (RN[A,q]).subscheme ↘ S = E.subscheme ↘ S := by
    simp only [over_eq_subschemeι_comp, reassoc_of% hv, hfOver]
  let : v.hom.IsOver S := ⟨hbase⟩
  let : IsIntegral Plane := Proj.isIntegral_polynomialProj
  let : IsNoetherian Plane := isNoetherian_of_finiteType (Plane ↘ S)
  let : PrestableFamily ((RN[A,q]).subscheme ↘ S) := hT.prestableFamily_radical_comap_toBase hA
  let hPre : PrestableFamily (E.subscheme ↘ S) :=
    hbase ▸ (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily) v.hom _).mpr
      inferInstance
  obtain ⟨C, -, -⟩ := hT.exists_isOrientedCycleSubdivision_nodalBoundaryTower hA B
    (p' := (Empty.elim : Empty → _))
  let : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
  have hE' : E.IsEffectiveCartier := hEeq ▸ hE
  refine ⟨Ψ, hΨ, hcΨ, d, r', f, by simpa using hr', hπ', hE', hPre, ?_, ?_⟩
  · simpa only [hEeq] using hK
  · let : v.symm.hom.IsOver S := inferInstanceAs (v.inv.IsOver S)
    have C' : Scheme.NodalCycleNumbering (Empty.elim :
        Empty → ((RN[A,q]).subscheme ↘ S).smoothLocus) (n + 1) := by
      simpa only [Nat.zero_add] using C
    exact ⟨v.symm.mapNodalCycleNumbering C'⟩

omit [IsAlgClosed k₀] in
private theorem bisection_replacement_square_on_fan
    {X Y W : Scheme} [Y.Over S] {D : X.IdealSheafData} {A : W.IdealSheafData}
    {x : X} {z : W} {g : X ⟶ Plane} {p : W ⟶ Plane}
    (f : Y ≅ W) (e : (I[x]).blowup ≅ (I[z]).blowup)
    (hf : f.hom ≫ p ≫ Plane ↘ S = Y ↘ S) (hz : IsClosed ({z} : Set W))
    (hs : z ∈ A.smoothBoundaryPoints (p ≫ Plane ↘ S))
    (hpb : IsPullback (π[x]) (e.hom ≫ π[z]) g p)
    (hD : St[I[z],A].comap e.hom = R[D,x]) :
    ∃ (y : Y) (d : (I[x]).blowup ≅ (I[y]).blowup),
      IsClosed ({y} : Set Y) ∧ f.hom y = z ∧
      y ∈ (A.comap f.hom).smoothBoundaryPoints (Y ↘ S) ∧
      IsPullback (π[x]) (d.hom ≫ π[y]) g (f.hom ≫ p) ∧
      St[I[y],A.comap f.hom].comap d.hom = R[D,x] := by
  let y := f.inv z
  have hy : IsClosed ({y} : Set Y) := by
    simpa only [y, Set.image_singleton] using f.inv.isClosedMap _ hz
  have hyz : f.hom y = z := by
    dsimp only [y]
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have hcenter : (I[z]).comap f.hom = I[y] := by
    rw [← hyz, f.hom.comap_ker_fromSpecResidueField_apply]
  let w := blowupIso f hcenter.symm
  let d := e ≪≫ w.symm
  have hw : w.inv ≫ π[y] ≫ f.hom = π[z] := by
    rw [← blowupIso_hom_blowupToBase f hcenter.symm, Iso.inv_hom_id_assoc]
  refine ⟨y, d, hy, hyz, ?_, ?_, ?_⟩
  · rw [← hf]
    have htop : (⊤ : W.Opens) ≤ f.hom.isoLocus := f.hom.le_isoLocus_iff.mpr inferInstance
    apply (A.mem_smoothBoundaryPoints_comap_iff_of_mem_isoLocus _ f.hom
      (htop (TopologicalSpace.Opens.mem_top _))).mpr
    rwa [hyz]
  · refine hpb.of_iso' (Iso.refl _) (Iso.refl _) f (Iso.refl _) (by simp) ?_ (by simp) (by simp)
    simp only [d, Iso.refl_hom, Iso.trans_hom, Iso.symm_hom, Category.id_comp, Category.assoc, hw]
  · have hwD : St[I[z],A].comap w.hom = St[I[y],A.comap f.hom] :=
      comap_ker_blowupMap_subschemeι_blowupIso (I[z]) A f hcenter
    rw [Iso.trans_hom, Iso.symm_hom, ← hwD, ← comap_comp,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, hD]

omit [IsAlgClosed k₀] in
private theorem bisection_plane_center_smooth_and_ne_node
    {A : (Plane).IdealSheafData} [IsReduced A.subscheme]
    {p q : Plane} {z : A.subscheme} (hz : A.subschemeι z = p)
    (hsm : ((A.subschemeι ≫ Plane ↘ S).stalkMap z).hom.FormallySmooth)
    (hq : A.IsNodeOfReducedBoundary (Plane ↘ S) q) :
    p ∈ A.smoothBoundaryPoints (Plane ↘ S) ∧ q ≠ p := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rw [mem_smoothBoundaryPoints_iff, A.isReduced_subscheme_iff_radical_eq.mp inferInstance]
    exact ⟨z, hz, hsm⟩
  · obtain ⟨z', hz', hn⟩ := (A.isNodeOfReducedBoundary_iff_of_isReduced _ _).mp
      (h ▸ hq : A.IsNodeOfReducedBoundary (Plane ↘ S) p)
    have hzz' := A.subschemeι.injective (hz.trans hz'.symm)
    exact hn.not_formallySmooth_stalkMap (hzz' ▸ hsm)

/-- Replace the smooth plane center of a Hirzebruch-one anticanonical bisection by
a chosen numbered node of its boundary. The new Hirzebruch-one pair has one more
numbered component and complexity one less. The blowups of the original and new
surfaces form a Cartesian square over the plane. The reduced total boundary on
the original side is the strict transform on the new side, whose blowup center
is a smooth boundary point. -/
theorem exists_hirzebruch_one_nodal_replacement_of_bisection
    {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (r : Fin 4 ≃ Φ.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (1 : ℤ) • b 0 - b 1])
    [SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme k₀) ↘ S)]
    {D : (Φ.finiteFanScheme k₀).IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
    (hD : D.IsEffectiveCartier)
    (hK : LineBundleClass.mk hD.toInvertibleSheaf =
      LineBundleClass.mk (canonicalBundle k₀ (Φ.finiteFanScheme k₀) 2))
    (t : D.boundaryPrimes)
    (ht : (Φ.hirzebruchPicardBasis k₀ b 1 hΦ r hr).repr
      (Additive.ofMul (@primeDivisorClass _ _ _
        (Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R :=
          k₀) hΦ) (D.boundaryPrimeEmbedding t))) 1
      = 2)
    {n : ℕ} [NeZero n] {α : Type*} {m : α → (D.subscheme ↘ S).smoothLocus}
    (B : Scheme.NodalCycleNumbering m n) (j : ZMod n) :
    let X := (Φ.finiteFanScheme k₀)
    let x := B.ambientNode j
    ∃ (p q : Plane) (a : X ≅ (I[p]).blowup)
      (Ψ : Fan i) (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete) (d : Basis (Fin 2) ℤ N)
      (r' : Fin 4 ≃ Ψ.Ray) (f : (Ψ.finiteFanScheme k₀) ≅ (I[q]).blowup)
      (y : (Ψ.finiteFanScheme k₀)) (e : (I[x]).blowup ≅ (I[y]).blowup),
      let X' := (Ψ.finiteFanScheme k₀)
      let A := D.map (a.hom ≫ π[p])
      let E := (RN[A,q]).comap f.hom
      letI : Nonempty Ψ.cones := hcΨ.nonempty_cones
      letI : SmoothOfRelativeDimension 2 (X' ↘ S) := by
        rw [finiteFanScheme_over]
        exact ((finrank_eq_card_basis d).trans (Fintype.card_fin 2)) ▸
          Ψ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΨ
      IsClosed ({p} : Set Plane) ∧ IsClosed ({q} : Set Plane) ∧
      (a.hom ≫ π[p]) x = q ∧ p ≠ q ∧
      a.hom ≫ π[p] ≫ Plane ↘ S = X ↘ S ∧ f.hom ≫ π[q] ≫ Plane ↘ S = X' ↘ S ∧
      (fun l ↦ (r' l).primitiveGenerator) = ![d 0, d 1, -d 0, d 0 - d 1] ∧
      IsClosed ({y} : Set X') ∧ (f.hom ≫ π[q]) y = p ∧
      y ∈ E.smoothBoundaryPoints (X' ↘ S) ∧
      IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T[x] ∧
      IsPullback (π[x]) (e.hom ≫ π[y]) (a.hom ≫ π[p]) (f.hom ≫ π[q]) ∧
      (St[I[y],E]).comap e.hom = R[D,x] ∧
      E.boundaryComplexity + 1 = D.boundaryComplexity ∧
      ∃ (hE : E.IsEffectiveCartier) (hPre : PrestableFamily (E.subscheme ↘ S)),
        letI := hPre
        LineBundleClass.mk hE.toInvertibleSheaf = LineBundleClass.mk (canonicalBundle k₀ X' 2) ∧
        Nonempty (Scheme.NodalCycleNumbering (Empty.elim : Empty → (E.subscheme ↘ S).smoothLocus)
          (n + 1)) := by
  intro X x
  let : X.IsProjectiveOver k₀ := Φ.isProjectiveOver_finiteFanScheme_of_isComplete k₀ hΦ hc b
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have hcontraction :=
    exists_plane_internalBlowdown_of_hirzebruch_one_anticanonical_bisection
      k₀ b 1 hΦ hc r hr hD hK rfl ht hN
  obtain ⟨p, a, hp, ha, -, hA, hcan, hAN, -, -, hJ, hs, u, hu⟩ := hcontraction
  generalize hIp : J[p] = J at a ha hA hcan hAN hJ hs u hu
  have hJp : J = I[p] := hIp.symm.trans (Scheme.ker_fromSpecResidueField_eq_vanishingIdeal p).symm
  clear hIp
  subst J
  let A := D.map (a.hom ≫ π[p])
  obtain ⟨hPreA, C, hnode⟩ := numbered_node_image_of_bisection_contraction k₀ B j _ ha u hu
  let := hPreA
  let q := C.ambientNode j
  have hq := C.isClosed_ambientNode j
  have hqNode := C.isNodeOfReducedBoundary_ambientNode j rfl
  let : IsReduced A.subscheme := hAN.isReduced
  obtain ⟨z, hz, hzs⟩ := hs
  obtain ⟨hpD, hneq⟩ :=
    bisection_plane_center_smooth_and_ne_node k₀ hz (Scheme.Hom.mem_smoothLocus.mp hzs) hqNode
  obtain ⟨y, e, hy, hyp, hyD, hpb, hcomp⟩ := bisection_replacement_square k₀ a ha u hu hJ hp
    (B.isClosed_ambientNode j) hpD (B.isNodeOfReducedBoundary_ambientNode j rfl) hnode.symm hneq
  obtain ⟨Ψ, hΨ, hcΨ, d, r', f, hr', hf, hE, hPreE, hEK, hnum⟩ :=
    exists_numbered_hirzebruch_model_of_bisection_plane k₀ b Φ.lattice C j hA hcan
  have hdrop := complexity_drop_of_bisection_replacement k₀ a u hu hp hA hD
    (isNodalBoundaryTower_numbered_node C j)
  let : Nonempty Ψ.cones := hcΨ.nonempty_cones
  obtain ⟨y', e', hy', hyy, hyD', hpb', hcomp'⟩ :=
    bisection_replacement_square_on_fan k₀ f e hf hy hyD hpb hcomp
  have hToBase : T[q].toBase = π[q] := by rw [toBase_snoc, toBase_nil, Category.comp_id]
  rw [← hToBase] at hyD' hcomp'
  refine ⟨p, q, a, Ψ, hΨ, hcΨ, d, r', f, y', e', hp, hq, hnode.symm, hneq.symm, ha, hf, hr',
    hy', ?_, hyD', isNodalBoundaryTower_numbered_node B j, hpb', hcomp', ?_,
    hE, hPreE, hEK, hnum⟩
  · rwa [Scheme.Hom.comp_apply, hyy]
  · simpa only [boundaryComplexity_comap_iso f, hToBase] using hdrop

end TauCeti.Toric.Fan
