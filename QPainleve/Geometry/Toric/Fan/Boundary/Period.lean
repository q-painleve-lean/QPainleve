/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Period.DivisorRatio
public import QPainleve.Geometry.Toric.Fan.Boundary.BranchCoordinates
public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter

import QPainleve.AlgebraicGeometry.CartierDivisor.Pullback
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Modules.Clopen
import QPainleve.AlgebraicGeometry.Modules.Pullback.Unit
import QPainleve.Geometry.Toric.Fan.Boundary.DualGraph

/-!
# Period of a binomial center ratio

The quotient of two center ideal line bundles on the same boundary ray has
multidegree zero. Its period is the ratio of the center parameters with the sign
determined by the order of the two branches on that ray. This is the individual
center contribution to the marked period in [Gross, Hacking and Keel, Proposition 2.9][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData Scheme.Modules

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] (hΦ : Φ.IsRegular)
  (ρ : Φ.Ray) (hdim : Module.finrank ℤ N = 2) {m : N →+ ℤ}
  (hm : m ρ.primitiveGenerator = 0) (hprim : Function.Surjective m)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "C" => Scheme.IdealSheafData.subscheme (Φ.boundaryIdeal inferInstance)
local notation "I₀" => Scheme.singularLocus ℂ C
local notation "ν" => Scheme.IdealSheafData.blowupToBase I₀

variable [PrestableFamily ((Φ.boundaryIdeal inferInstance).subscheme ↘ Spec (.of ℂ))]

local notation "U[" τ "]" =>
  Scheme.blowupComponent (K := ℂ) C (Φ.boundaryNormalizationComponentEquiv hΦ τ)
local notation "P" =>
  ρ.boundaryNormalizationComponentIso hΦ ≪≫ ρ.boundaryIsoProjectiveLine hΦ hdim hm hprim
local notation "E" => Proj.symmetricAlgebraTwistingBundle ℂ (Fin 2 → ℂ) 1
local notation "L" => Functor.obj (InvertibleSheaf.pullback (Iso.hom P)) E
local notation "s[" a "]" =>
  Scheme.Hom.pullbackSections (Iso.hom P) (ObjectProperty.FullSubcategory.obj E) ⊤
    (projectiveLine.binomialSection ℂ (↑(a : ℂˣ)⁻¹ : ℂ))
local notation "p[" b "]" => projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) b 0 ≫ Iso.inv P
local notation "J[" a "]" => Scheme.Hom.ker (ρ.binomialCenterOnBoundary hdim hm hprim a)
local notation "cartier[" a "]" => ρ.isEffectiveCartier_ker_binomialCenterOnBoundary hdim hm hprim a
local notation "avoids[" a "]" => ρ.comap_ker_binomialCenterOnBoundary_singularLocus hdim hm hprim a

private abbrev pullbackCenterInclusion {T : Scheme} (f : T ⟶ (I₀).blowup) (a : ℂˣ) :
    (pullback f).obj ((pullback ν).obj (J[a]).sheaf) ⟶ 𝟙_ T.Modules :=
  (pullback f).map ((pullback ν).map (J[a]).sheafι ≫ (pullbackObjUnitIso ν).hom) ≫
    (pullbackObjUnitIso f).hom

local notation "inc[" f "," a "]" => pullbackCenterInclusion ρ hdim hm hprim f a

attribute [local instance] Ray.isProper_boundaryComponent_of_prestableFamily

private theorem rayCenter_comap_isEffectiveCartier (a : ℂˣ) (τ : Φ.Ray) :
    ((J[a]).comap ((U[τ]).ι ≫ ν)).IsEffectiveCartier := by
  rw [comap_comp]
  refine ((cartier[a]).comap_of_support_subset_isoLocus ν ?_).comap (U[τ]).ι
  refine (fun x hx ↦ ?_)
  apply (ν).le_isoLocus_iff.mpr (I₀).isIso_blowupToBase_restrict_compl_support
  intro hn
  obtain ⟨y, rfl⟩ := (I₀).range_subschemeι.ge hn
  have hy : y ∈ ((J[a]).comap (I₀).subschemeι).support := by
    rw [support_comap]
    exact hx
  simp only [avoids[a], support_top, ← SetLike.mem_coe, Closeds.coe_bot,
    Set.mem_empty_iff_false] at hy

private theorem exists_rayCenter_evalIso (a : ℂˣ) :
    ∃ u : (InvertibleSheaf.dual L).obj ≅ (pullback (U[ρ]).ι).obj ((pullback ν).obj (J[a]).sheaf),
      u.hom ≫ inc[(U[ρ]).ι, a] = (L).dualSectionEquiv.symm s[a] := by
  have h := ρ.comap_ker_binomialCenterOnBoundary_normalizationComponent hΦ hdim hm hprim a
  have hC := rayCenter_comap_isEffectiveCartier hΦ ρ hdim hm hprim a ρ
  have hs : s[a] ≠ 0 := by
    intro hz
    have hzero := ((L).zeroIdeal_eq_bot_iff s[a]).mpr hz
    obtain ⟨x⟩ : Nonempty (U[ρ]).toScheme := inferInstance
    exact (hC.stalkIdeal_ne_bot x) (by rw [h.trans hzero, stalkIdeal_bot])
  obtain ⟨u, hu⟩ := (L).exists_iso_pullbackSheaf_of_zeroIdeal ((U[ρ]).ι ≫ ν) (cartier[a]) hs h.symm
  let A := pullbackComp (U[ρ]).ι ν
  refine ⟨u ≪≫ (A.app _).symm, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (u.hom ≫ ·) (pullbackComp_inv_app_map_toUnit (U[ρ]).ι ν (J[a]).sheafι)).trans hu)

private theorem exists_rayCenterRatio_on_ray (c d : ℂˣ) :
    ∃ u : (pullback (U[ρ]).ι).obj ((pullback ν).obj (J[c]).sheaf) ≅
        (pullback (U[ρ]).ι).obj ((pullback ν).obj (J[d]).sheaf),
      ∀ a : Fin 2,
        (pullback p[a]).map u.hom ≫
            (pullback p[a]).map inc[(U[ρ]).ι,d] ≫ (pullbackObjUnitIso p[a]).hom =
          (pullback p[a]).map inc[(U[ρ]).ι,c] ≫ (pullbackObjUnitIso p[a]).hom ≫
            globalSectionsSmul (𝟙_ (S).Modules)
              ((Scheme.ΓSpecIso (.of ℂ)).inv (if a = 0 then 1 else ((c / d : ℂˣ) : ℂ))) := by
  obtain ⟨u, hu⟩ := exists_rayCenter_evalIso hΦ ρ hdim hm hprim c
  obtain ⟨v, hv⟩ := exists_rayCenter_evalIso hΦ ρ hdim hm hprim d
  refine ⟨u.symm ≪≫ v, fun a ↦ ?_⟩
  apply (cancel_epi ((pullback p[a]).map u.hom)).mp
  have huv : u.hom ≫ (u.symm ≪≫ v).hom = v.hom := u.hom_inv_id_assoc v.hom
  rw [← Functor.map_comp_assoc, huv, ← Functor.map_comp_assoc, hv]
  rw [← Functor.map_comp_assoc, hu]
  exact (L).pullback_map_dualSectionEquiv_symm_eq_smul _ _
    (ρ.pullbackSections_binomialCenter_eq_smul_at_normalizationEndpoint hΦ hdim hm hprim a d c)

private theorem exists_rayCenterRatio_off_ray (τ : Φ.Ray) (hτ : ρ ≠ τ) (c d : ℂˣ) :
    ∃ u : (pullback (U[τ]).ι).obj ((pullback ν).obj (J[c]).sheaf) ≅
        (pullback (U[τ]).ι).obj ((pullback ν).obj (J[d]).sheaf),
      u.hom ≫ inc[(U[τ]).ι,d] = inc[(U[τ]).ι,c] := by
  let f := (U[τ]).ι ≫ ν
  have htop (a : ℂˣ) : (J[a]).comap f = ⊤ :=
    ρ.comap_ker_binomialCenterOnBoundary_normalizationComponent_eq_top_of_ne
      hΦ hdim hm hprim τ hτ a
  let F (a : ℂˣ) := ((pullbackComp (U[τ]).ι ν).app (J[a]).sheaf) ≪≫
    (cartier[a]).pullbackTrivializationOfComapEqTop f (htop a)
  have hF (a : ℂˣ) : (F a).hom = inc[(U[τ]).ι, a] := by
    simp only [F, Iso.trans_hom, Iso.app_hom,
      IsEffectiveCartier.pullbackTrivializationOfComapEqTop_hom]
    rw [← pullbackComp_inv_app_map_toUnit (U[τ]).ι ν (J[a]).sheafι]
    simp only [Iso.hom_inv_id_app_assoc]
  refine ⟨F c ≪≫ (F d).symm, ?_⟩
  rw [← hF, ← hF, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

local notation "B" => Scheme.branchScheme ℂ C
local notation "j" => Scheme.branchSchemeToBlowup ℂ C
local notation "nodal" => PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := C ↘ S)
local notation "q[" z "]" => Scheme.branchRationalPoint C nodal z ≫ j
local notation "scalar[" v "]" =>
  globalSectionsSmul (𝟙_ (Scheme.Modules S))
    (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of ℂ)) ((v : ℂˣ) : ℂ))
local notation "A[" c "," d "]" =>
  (Functor.obj (pullback ν) (sheaf J[c]) ≅ Functor.obj (pullback ν) (sheaf J[d]))
local notation "localIso[" τ "," c "," d "]" =>
  (Functor.obj (pullback (Scheme.Opens.ι U[τ])) (Functor.obj (pullback ν) (sheaf J[c])) ≅
    Functor.obj (pullback (Scheme.Opens.ι U[τ])) (Functor.obj (pullback ν) (sheaf J[d])))
local notation "factor[" a "," c "," d "]" => ite (a = (0 : Fin 2)) 1 (c / d)

private theorem rayCenterRatio_branch_value {c d : ℂˣ} (A : A[c,d])
    {T : Scheme} (l : T ⟶ (I₀).blowup) (f : S ⟶ T) (z : B) (hz : q[z] = f ≫ l)
    (v : ℂˣ)
    (hv : (pullback f).map ((pullback l).map A.hom) ≫
          (pullback f).map inc[l,d] ≫ (pullbackObjUnitIso f).hom =
        (pullback f).map inc[l,c] ≫ (pullbackObjUnitIso f).hom ≫ scalar[v]) :
    (C).branchSchemeGlobalUnitsEquiv nodal
      (Scheme.nodalCartierRatioUnit (k := ℂ) (cartier[c]) (cartier[d])
        (avoids[c]) (avoids[d]) A) z = v := by
  apply (Scheme.nodalCartierRatioUnit_branch_eq_iff_toBlowup
    (cartier[c]) (cartier[d]) (avoids[c]) (avoids[d]) A z v).mpr
  dsimp only
  rw [hz]
  let cmp := pullbackComp f l
  have hn := cmp.inv.naturality_assoc A.hom
    ((pullback f).map inc[l,d] ≫ (pullbackObjUnitIso f).hom)
  simp only [Functor.comp_map] at hn
  rw [← pullbackComp_inv_app_map_toUnit f l
    ((pullback ν).map (J[d]).sheafι ≫ (pullbackObjUnitIso ν).hom), hn,
    ← pullbackComp_inv_app_map_toUnit f l
      ((pullback ν).map (J[c]).sheafι ≫ (pullbackObjUnitIso ν).hom)]
  simpa only [Category.assoc] using
    congrArg (cmp.inv.app ((pullback ν).obj (J[c]).sheaf) ≫ ·) hv

private theorem rayCenterRatio_branch_off_ray {c d : ℂˣ} (A : A[c,d])
    (τ : Φ.Ray) (z : B) (hz : j z ∈ U[τ])
    (hA : (pullback (U[τ]).ι).map A.hom ≫ inc[(U[τ]).ι,d] = inc[(U[τ]).ι,c]) :
    (C).branchSchemeGlobalUnitsEquiv nodal
      (Scheme.nodalCartierRatioUnit (k := ℂ) (cartier[c]) (cartier[d])
        (avoids[c]) (avoids[d]) A) z = 1 := by
  have hrange : Set.range q[z] ⊆ Set.range (U[τ]).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.branchRationalPoint_apply, (U[τ]).range_ι]
    exact hz
  let f := IsOpenImmersion.lift (U[τ]).ι q[z] hrange
  apply rayCenterRatio_branch_value ρ hdim hm hprim A (U[τ]).ι f z
    (IsOpenImmersion.lift_fac _ _ _).symm
  rw [← Functor.map_comp_assoc, hA]
  simp only [Units.val_one, map_one, globalSectionsSmul_one, Category.comp_id]

private theorem exists_rayCenterRatio_normalizationIso (c d : ℂˣ) :
    ∃ A : A[c,d],
      (∀ (a : Fin 2) (z : B), q[z] = p[a] ≫ (U[ρ]).ι →
        (C).branchSchemeGlobalUnitsEquiv nodal
          (Scheme.nodalCartierRatioUnit (k := ℂ) (cartier[c]) (cartier[d])
            (avoids[c]) (avoids[d]) A) z = factor[a,c,d]) ∧
      ∀ (τ : Φ.Ray) (_ : ρ ≠ τ) (z : B), j z ∈ U[τ] →
        (C).branchSchemeGlobalUnitsEquiv nodal
          (Scheme.nodalCartierRatioUnit (k := ℂ) (cartier[c]) (cartier[d])
            (avoids[c]) (avoids[d]) A) z = 1 := by
  classical
  obtain ⟨u, hu⟩ := exists_rayCenterRatio_on_ray hΦ ρ hdim hm hprim c d
  choose v hv using fun τ hτ ↦ exists_rayCenterRatio_off_ray hΦ ρ hdim hm hprim τ hτ c d
  let a (τ : Φ.Ray) : localIso[τ,c,d] := if h : ρ = τ then h ▸ u else v τ h
  have ha : a ρ = u := dite_eq_left rfl
  have hb (τ : Φ.Ray) (hτ : ρ ≠ τ) : a τ = v τ hτ := dite_eq_right hτ
  have hcov : ⨆ τ, U[τ] = ⊤ :=
    (Φ.boundaryNormalizationComponentEquiv hΦ).iSup_comp.trans ((C).iSup_blowupComponent)
  have hdisj : Pairwise fun τ σ : Φ.Ray ↦ Disjoint U[τ] U[σ] :=
    fun _ _ h ↦ (C).pairwise_disjoint_blowupComponent
      ((Φ.boundaryNormalizationComponentEquiv hΦ).injective.ne h)
  obtain ⟨A, hA⟩ := Scheme.Modules.exists_iso_of_pairwise_disjoint_openCover
    (fun τ : Φ.Ray ↦ U[τ]) hcov hdisj a
  refine ⟨A, ?_, ?_⟩
  · intro t z hz
    apply rayCenterRatio_branch_value ρ hdim hm hprim A (U[ρ]).ι p[t] z hz
    rw [hA, ha]
    simpa only [apply_ite, Units.val_one] using hu t
  · intro τ hτ z hz
    apply rayCenterRatio_branch_off_ray hΦ ρ hdim hm hprim A τ z hz
    rw [hA, hb τ hτ]
    exact hv τ hτ

variable {ι : Type*}
  {ps : ι → ((Φ.boundaryIdeal inferInstance).subscheme ↘ Spec (.of ℂ)).smoothLocus}
  {n : ℕ} [NeZero n]
  {e : ZMod n ≃ ((Φ.boundaryIdeal inferInstance).subscheme.dualGraph ps).Edge}
  {o : ((Φ.boundaryIdeal inferInstance).subscheme.dualGraph ps).Edge → Equiv.Perm (Fin 2)}
  {w : ZMod n ≃ ((Φ.boundaryIdeal inferInstance).subscheme.dualGraph ps).Vertex}
  (r : ZMod n ≃ Φ.Ray)
local notation "flag[" t "," b "]" => Scheme.dualGraphBranchEquiv C ps (e t, o (e t) b)
local notation "t₀" => r.symm ρ

variable (hw : ∀ t b, ((Φ.boundaryIdeal inferInstance).subscheme.dualGraph ps).endpoint
    (e t) (o (e t) b) = w ((TauCeti.DualGraph.cycle n).endpoint t b))
  (hcomp : ∀ t, (Φ.boundaryIdeal inferInstance).subscheme.dualGraphVertexEquiv ps (w t) =
    Φ.boundaryNormalizationComponentEquiv hΦ (r t))

include hw hcomp in
private theorem toric_boundary_branch_mem_numbered_component (t : ZMod n) (b : Fin 2) :
    j flag[t,b] ∈ U[r ((TauCeti.DualGraph.cycle n).endpoint t b)] := by
  rw [Scheme.branchSchemeToBlowup_dualGraphBranchEquiv,
    ← SetLike.mem_coe, (C).coe_blowupComponent]
  apply ((C).dualGraphVertexEquiv_endpoint_eq_iff ps (e t) (o (e t) b) _).mp
  rw [hw, hcomp]

include hw hcomp in
/-- The ratio of the center ideal classes is multidegree zero. In a cyclic numbering,
if the outgoing branch on the center ray is the zero of the projective coordinate,
the period is `d / c`. If the outgoing branch is its pole, the period is `c / d`. -/
theorem Ray.exists_binomialCenterRatio_nodalPicardCycleMulEquiv (c d : ℂˣ) (b : Fin 2)
    (hout : q[flag[t₀,0]] = p[b] ≫ (U[ρ]).ι)
    (hin : q[flag[t₀ - 1,1]] = p[b.rev] ≫ (U[ρ]).ι) :
    ∃ x : (LineBundleClass.pullbackHom ν).ker,
      x.val = LineBundleClass.mk (cartier[c]).toInvertibleSheaf /
        LineBundleClass.mk (cartier[d]).toInvertibleSheaf ∧
      Scheme.nodalPicardCycleMulEquiv hw x = if b = 0 then c / d else d / c := by
  classical
  obtain ⟨A, hA, hoff⟩ := exists_rayCenterRatio_normalizationIso hΦ ρ hdim hm hprim c d
  let x := Scheme.nodalCartierRatioClass (k := ℂ) (cartier[c]) (cartier[d]) A
  refine ⟨x, Scheme.nodalCartierRatioClass_val .., ?_⟩
  rw [Scheme.nodalPicardCycleMulEquiv_nodalCartierRatioClass hw (cartier[c]) (cartier[d])
    (avoids[c]) (avoids[d]) A, Scheme.nodalConductorCycleProduct_apply]
  let v := (C).branchSchemeGlobalUnitsEquiv nodal
    (Scheme.nodalCartierRatioUnit (k := ℂ) (cartier[c]) (cartier[d])
      (avoids[c]) (avoids[d]) A)
  have hleft (t : ZMod n) : v flag[t,0] = if t = t₀ then factor[b,c,d] else 1 := by
    by_cases h : t = t₀
    · rw [ite_eq_left h, h]
      exact hA _ _ hout
    · rw [ite_eq_right h]
      apply hoff (r t) (fun ht ↦ h (r.injective (ht.symm.trans (r.apply_symm_apply ρ).symm)))
      simpa only [TauCeti.DualGraph.cycle, ite_true] using
        toric_boundary_branch_mem_numbered_component hΦ r hw hcomp t 0
  have hright (t : ZMod n) : v flag[t,1] = if t = t₀ - 1 then factor[b.rev,c,d] else 1 := by
    by_cases h : t = t₀ - 1
    · rw [ite_eq_left h, h]
      exact hA _ _ hin
    · rw [ite_eq_right h]
      apply hoff (r (t + 1)) (fun ht ↦ h (by
        have hh := r.injective (ht.symm.trans (r.apply_symm_apply ρ).symm)
        exact eq_sub_of_add_eq hh))
      simpa only [TauCeti.DualGraph.cycle, (one_ne_zero : (1 : Fin 2) ≠ 0), ite_false] using
        toric_boundary_branch_mem_numbered_component hΦ r hw hcomp t 1
  -- Fold the branch evaluation to use the two indicator formulas.
  change (∏ t, v flag[t,1] / v flag[t,0]) = _
  simp only [hleft, hright, Finset.prod_div_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  fin_cases b <;> simp [div_div_eq_mul_div]

local notation "point" => IsLocalRing.closedPoint ℂ
local notation "D" => Φ.boundaryIdeal inferInstance

omit [NeZero n] in
private theorem toric_boundary_branch_at_node (t : ZMod n) (a : Fin 2)
    {σ : Φ.cones} (hσ : (D).subschemeι ((C).dualGraphEdgeEquiv ps (e t)).val =
      Φ.distinguishedPointHom σ point) :
    (D).subschemeι (ν (j flag[t,a])) = Φ.distinguishedPointHom σ point := by
  rw [Scheme.branchSchemeToBlowup_dualGraphBranchEquiv, Scheme.blowupToBase_branchPointEquiv]
  exact hσ

include hw hcomp in
private theorem toric_boundary_branch_eq_endpoint (t : ZMod n) (a side : Fin 2) (τ : Φ.Ray)
    {σ : Φ.cones} (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ)
    (hside : r ((TauCeti.DualGraph.cycle n).endpoint t side) = ρ)
    (ha : 0 < (if a = 1 then 1 else -1 : ℤ) * m τ.primitiveGenerator)
    (hσ : (D).subschemeι ((C).dualGraphEdgeEquiv ps (e t)).val =
      Φ.distinguishedPointHom σ point) :
    q[flag[t,side]] = p[a] ≫ (U[ρ]).ι := by
  apply ρ.branchRationalPoint_comp_toBlowup_eq_normalizationEndpoint hΦ hdim hm hprim
    hρ τ hτ a ha
  · rw [(U[ρ]).range_ι, ← hside]
    exact SetLike.mem_coe.mpr
      (toric_boundary_branch_mem_numbered_component hΦ r hw hcomp t side)
  · exact toric_boundary_branch_at_node t side hσ

variable (b : Module.Basis (Fin 2) ℤ N)

local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "χ[" τ "]" => LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator τ))

include hw hcomp in
/-- In a positively numbered toric boundary, the quotient of the center ideal classes
has multidegree zero and period `d / c`. The numbered nodes are the fixed points of
the cones between successive rays. -/
theorem exists_internalCenterRatio_nodalPicardCycleMulEquiv
    (hdet : ∀ t, b.detDualEquiv (r t).primitiveGenerator (r (t + 1)).primitiveGenerator = 1)
    (hnodes : ∀ t, ∃ σ : Φ.cones, (r t).toCone ≤ σ ∧ (r (t + 1)).toCone ≤ σ ∧
      (D).subschemeι ((C).dualGraphEdgeEquiv ps (e t)).val = Φ.distinguishedPointHom σ point)
    (ρ : Φ.Ray) (c d : ℂˣ) :
    ∃ x : (LineBundleClass.pullbackHom ν).ker,
      x.val = LineBundleClass.mk (ρ.internalCenter b c).property.toInvertibleSheaf /
        LineBundleClass.mk (ρ.internalCenter b d).property.toInvertibleSheaf ∧
      Scheme.nodalPicardCycleMulEquiv hw x = d / c := by
  let k := r.symm ρ
  have hk : r k = ρ := r.apply_symm_apply _
  have hp : k - 1 + 1 = k := sub_add_cancel _ _
  have hpos : 0 < χ[ρ] (r (k + 1)).primitiveGenerator := by
    have h := hdet k
    rw [hk] at h
    simpa only [LinearMap.toAddMonoidHom_coe, h] using (zero_lt_one : (0 : ℤ) < 1)
  have hneg : χ[ρ] (r (k - 1)).primitiveGenerator = -1 := by
    have h := hdet (k - 1)
    rw [hp, hk, b.detDualEquiv_swap] at h
    simpa only [LinearMap.toAddMonoidHom_coe, neg_neg] using congrArg Neg.neg h
  obtain ⟨σ, hσ, hσ', hz⟩ := hnodes k
  obtain ⟨τ, hτ, hτ', hz'⟩ := hnodes (k - 1)
  have hout := toric_boundary_branch_eq_endpoint hΦ ρ rankTwo
    (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) r hw hcomp k 1 0
    (r (k + 1)) (hk ▸ hσ) hσ' (by simpa only [TauCeti.DualGraph.cycle, ite_true] using hk)
    (by simpa using hpos) hz
  have hin := toric_boundary_branch_eq_endpoint hΦ ρ rankTwo
    (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) r hw hcomp (k - 1) 0 1
    (r (k - 1)) (by simpa only [hp, hk] using hτ') hτ
    (by simpa only [TauCeti.DualGraph.cycle, (one_ne_zero : (1 : Fin 2) ≠ 0), ite_false, hp]
      using hk) (by simp [hneg]) hz'
  obtain ⟨x, hx, hval⟩ := ρ.exists_binomialCenterRatio_nodalPicardCycleMulEquiv hΦ rankTwo
    (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) r hw hcomp c d 1 hout hin
  refine ⟨x, ?_, by simpa using hval⟩
  rw [hx]
  exact congrArg₂ (· / ·)
    (LineBundleClass.mk_toInvertibleSheaf_congr _ _ (ρ.internalCenter_val b c).symm)
    (LineBundleClass.mk_toInvertibleSheaf_congr _ _ (ρ.internalCenter_val b d).symm)

include hw hcomp in
/-- A weighted product of center-ideal quotients belongs to the normalization kernel.
Its period in the positive determinant orientation is the product of the inverse
center ratios to the same integer powers. -/
theorem exists_prod_internalCenterRatio_nodalPicardCycleMulEquiv
    (hdet : ∀ t, b.detDualEquiv (r t).primitiveGenerator (r (t + 1)).primitiveGenerator = 1)
    (hnodes : ∀ t, ∃ σ : Φ.cones, (r t).toCone ≤ σ ∧ (r (t + 1)).toCone ≤ σ ∧
      (D).subschemeι ((C).dualGraphEdgeEquiv ps (e t)).val = Φ.distinguishedPointHom σ point)
    {κ : Type*} [Fintype κ] (s : κ → Φ.Ray) (c d : κ → ℂˣ) (x : κ → ℤ) :
    let I (u : κ → ℂˣ) (label : κ) :=
      LineBundleClass.mk ((s label).internalCenter b (u label)).property.toInvertibleSheaf
    ∃ ratios : (LineBundleClass.pullbackHom ν).ker,
      ratios.val = (∏ label, I c label ^ x label) / (∏ label, I d label ^ x label) ∧
      Scheme.nodalPicardCycleMulEquiv hw ratios = ∏ label, (d label / c label) ^ x label := by
  dsimp only
  choose ratios hL hperiod using fun label : κ ↦
    exists_internalCenterRatio_nodalPicardCycleMulEquiv hΦ r hw hcomp b hdet hnodes
      (s label) (c label) (d label)
  refine ⟨∏ label, ratios label ^ x label, ?_, ?_⟩
  · calc
      (↑(∏ label, ratios label ^ x label) : LineBundleClass C) =
          ∏ label, (↑(ratios label ^ x label) : LineBundleClass C) :=
        map_prod (LineBundleClass.pullbackHom ν).ker.subtype _ _
      _ = _ := by simp only [Subgroup.coe_zpow, hL, div_zpow, Finset.prod_div_distrib]
  · simp only [map_prod, map_zpow, hperiod]

include hΦ in
/-- A positive cyclic numbering of the rays gives a single orientation of the toric
boundary in which each ratio of binomial center ideal classes has period `d / c`.
The formula uses the determinant coordinate of the chosen ordered basis. -/
theorem exists_toric_boundary_period_of_cyclicRayNumbering (hc : Φ.IsComplete)
    (ps : ι → (C ↘ S).smoothLocus) (r : ZMod n ≃ Φ.Ray)
    (hr : ∀ t, b.detDualEquiv (r t).primitiveGenerator (r (t + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (r t).toCone ≤ σ ∧ (r (t + 1)).toCone ≤ σ) :
    ∃ (e : ZMod n ≃ ((C).dualGraph ps).Edge) (o : ((C).dualGraph ps).Edge → Equiv.Perm (Fin 2))
      (w : ZMod n ≃ ((C).dualGraph ps).Vertex)
      (hw : ∀ t a, ((C).dualGraph ps).endpoint (e t) (o (e t) a) =
        w ((TauCeti.DualGraph.cycle n).endpoint t a)),
      (∀ t, (C).dualGraphVertexEquiv ps (w t) = Φ.boundaryNormalizationComponentEquiv hΦ (r t)) ∧
      ∀ (ρ : Φ.Ray) (c d : ℂˣ), ∃ x : (LineBundleClass.pullbackHom ν).ker,
        x.val = LineBundleClass.mk (ρ.internalCenter b c).property.toInvertibleSheaf /
          LineBundleClass.mk (ρ.internalCenter b d).property.toInvertibleSheaf ∧
        Scheme.nodalPicardCycleMulEquiv hw x = d / c := by
  obtain ⟨e, o, v, hv, hcomp, hnodes⟩ := Φ.exists_toric_boundary_dualGraph_cycle hΦ hc ps b r hr
  refine ⟨e, o, v, hv, hcomp, fun ρ c d ↦
    exists_internalCenterRatio_nodalPicardCycleMulEquiv hΦ r hv hcomp b
      (fun t ↦ (hr t).1) (fun t ↦ ?_) ρ c d⟩
  obtain ⟨σ, hσ, hσ', hpoint⟩ := hnodes t
  exact ⟨σ.val, hσ, hσ', hpoint⟩

end TauCeti.Toric.Fan
