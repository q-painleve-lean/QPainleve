/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import QPainleve.Geometry.Toric.Fan.Equiv
public import TauCeti.Geometry.Toric.Algebraic.BaseChange.Fan
public import TauCeti.Geometry.Toric.Algebraic.Fan.Equiv

/-!
# Morphisms of toric schemes over a ring

A map of fans induces a morphism of the corresponding toric schemes over the coefficient ring.
On an affine chart it is the spectrum of the algebra map induced by precomposition of characters.
-/

public section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra
open scoped AlgebraMonoidAlgebra

namespace TauCeti.Toric

universe u

variable (R : Type u) [CommRing R]
  {N N' N'' : Type u} {V V' V'' : Type*}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V'']
  [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}
  {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'} {υ : PointedCone ℝ V''}

/-- A lattice map compatible with a map of cones induces a morphism of affine toric charts. -/
noncomputable def affineChartMap (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) : affineChart R hi σ ⟶ affineChart R hi' τ :=
  Spec.map (CommRingCat.ofHom (mapDomainAlgHom R R (dualSemigroupMap hi hi' f g hfg hστ)).toRingHom)

/-- The chart morphism is the spectrum of the algebra map on monomials. -/
theorem affineChartMap_def (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) :
    affineChartMap R hi hi' f g hfg hστ =
      Spec.map (CommRingCat.ofHom
        (mapDomainAlgHom R R (dualSemigroupMap hi hi' f g hfg hστ)).toRingHom) :=
  (rfl)

/-- Composition of compatible lattice maps induces composition of chart morphisms. -/
@[reassoc]
theorem affineChartMap_comp (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (hi'' : IsIntegralLattice i'') (f : N →+ N') (f' : N' →+ N'')
    (g : V →ₗ[ℝ] V') (g' : V' →ₗ[ℝ] V'')
    (hfg : ∀ n, g (i n) = i' (f n)) (hf'g' : ∀ n, g' (i' n) = i'' (f' n))
    (hστ : Set.MapsTo g σ τ) (hτυ : Set.MapsTo g' τ υ) :
    affineChartMap R hi hi' f g hfg hστ ≫ affineChartMap R hi' hi'' f' g' hf'g' hτυ =
      affineChartMap R hi hi'' (f'.comp f) (g'.comp g)
        (fun n ↦ by simp [hfg, hf'g']) (hτυ.comp hστ) := by
  rw [affineChartMap_def, affineChartMap_def, affineChartMap_def, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, dualSemigroupMap_comp hi hi' hi'' f f' g g' hfg hf'g' hστ hτυ,
    mapDomainAlgHom_comp]
  rfl

/-- The identity lattice map and a face inclusion induce the face chart morphism. -/
theorem faceAffineChartMap_eq_affineChartMap (hi : IsIntegralLattice i)
    {σ τ : PointedCone ℝ V} (h : σ.IsFaceOf τ) :
    faceAffineChartMap R hi h =
      affineChartMap R hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
        (by intro _ hx; exact h.le hx) := by
  have hmaps : Set.MapsTo (LinearMap.id : V →ₗ[ℝ] V) (σ : Set V) (τ : Set V) := by
    intro _ hx
    exact h.le hx
  have heq : AddSubmonoid.inclusion (dualSemigroup_anti hi h.le) =
      dualSemigroupMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) hmaps := by
    ext m : 1
    exact Subtype.ext (coe_dualSemigroupMap_id hi hmaps m).symm
  rw [faceAffineChartMap_def, affineChartMap_def, ← heq]
  apply congrArg (fun φ : affineChartRing R hi τ →ₐ[R] affineChartRing R hi σ ↦
    Spec.map (CommRingCat.ofHom φ.toRingHom))
  apply AlgHom.toLinearMap_injective
  ext m : 2
  simp

/-- The identity lattice map on a cone gives the identity of its chart. -/
@[simp]
theorem affineChartMap_id (hi : IsIntegralLattice i) :
    affineChartMap R hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
      (by simpa only [LinearMap.id_coe] using Set.mapsTo_id (σ : Set V)) =
      𝟙 (affineChart R hi σ) := by
  rw [← faceAffineChartMap_eq_affineChartMap R hi (PointedCone.IsFaceOf.refl σ),
    faceAffineChartMap_id]

/-- A chart morphism respects the structure maps to the spectrum of the coefficient ring. -/
@[reassoc (attr := simp)]
theorem affineChartMap_comp_specAlgebraMap (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) :
    affineChartMap R hi hi' f g hfg hστ ≫ Spec.algebraMap R (affineChartRing R hi' τ) =
      Spec.algebraMap R (affineChartRing R hi σ) := by
  rw [affineChartMap_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ))
    (mapDomainAlgHom R R (dualSemigroupMap hi hi' f g hfg hστ)).comp_algebraMap

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Changing coefficients commutes with a morphism of affine toric charts. -/
@[reassoc]
theorem affineChartMap_comp_coefficientMap (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) :
    affineChartMap S hi hi' f g hfg hστ ≫
        Spec.algebraMap (affineChartRing R hi' τ) (affineChartRing S hi' τ) =
      Spec.algebraMap (affineChartRing R hi σ) (affineChartRing S hi σ) ≫
        affineChartMap R hi hi' f g hfg hστ := by
  rw [affineChartMap_def, affineChartMap_def, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ))
    (mapRingHom_comp_mapDomainRingHom (algebraMap R S)
      (dualSemigroupMap hi hi' f g hfg hστ)).symm

namespace Fan

variable (Φ : Fan i)

/-- The structure morphism of the toric scheme makes it a scheme over the coefficient ring. -/
noncomputable instance finiteFanSchemeOver : (Φ.finiteFanScheme R).Over (Spec (.of R)) :=
  OverClass.ofHom (Φ.finiteFanSchemeToSpec R)

/-- The structure over the coefficient ring uses the descended structure morphism. -/
@[simp]
theorem finiteFanScheme_over :
    Φ.finiteFanScheme R ↘ Spec (.of R) = Φ.finiteFanSchemeToSpec R :=
  (rfl)

/-- Affine chart inclusions respect their structures over the spectrum of the coefficient ring. -/
instance isOver_affineChartι (σ : Φ.cones) : (Φ.affineChartι R σ).IsOver (Spec (.of R)) where
  comp_over := by
    rw [finiteFanScheme_over, affineChartι_finiteFanSchemeToSpec]
    rfl

end Fan

namespace FanHom

variable {Φ : Fan i} {Ψ : Fan i'} {Ω : Fan i''}

/-- The chart map into the least target cone, followed by the target chart inclusion. -/
private noncomputable def chartToScheme (f : FanHom Φ Ψ) (σ : Φ.cones) :
    affineChart R Φ.lattice σ ⟶ Ψ.finiteFanScheme R :=
  affineChartMap R Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice
    (show Set.MapsTo f.realMap (σ.val : Set V) (f.leastCone σ.property : Set V') from
      fun x hx ↦ f.map_le_leastCone σ.property ⟨x, hx, rfl⟩) ≫
    Ψ.affineChartι R ⟨f.leastCone σ.property, f.leastCone_mem σ.property⟩

private theorem faceAffineChartMap_comp_chartToScheme (f : FanHom Φ Ψ)
    {τ σ : Φ.cones} (h : τ ≤ σ) :
    faceAffineChartMap R Φ.lattice (Φ.isFaceOf_of_le σ.property τ.property h) ≫
      f.chartToScheme R σ = f.chartToScheme R τ := by
  have hface := f.leastCone_isFaceOf σ.property (Φ.isFaceOf_of_le σ.property τ.property h)
  rw [chartToScheme, chartToScheme]
  conv_rhs =>
    rw [← Fan.faceAffineChartMap_comp_affineChartι R
      (τ := ⟨f.leastCone τ.property, f.leastCone_mem τ.property⟩)
      (σ := ⟨f.leastCone σ.property, f.leastCone_mem σ.property⟩) hface]
  simp only [← Category.assoc, faceAffineChartMap_eq_affineChartMap, affineChartMap_comp,
    AddMonoidHom.comp_id, AddMonoidHom.id_comp, LinearMap.comp_id, LinearMap.id_comp]

/-- The map of toric schemes over `R` induced by a morphism of fans. -/
noncomputable def finiteFanSchemeHom (f : FanHom Φ Ψ) :
    Φ.finiteFanScheme R ⟶ Ψ.finiteFanScheme R :=
  Φ.finiteFanSchemeDesc R (f.chartToScheme R) (f.faceAffineChartMap_comp_chartToScheme R)

/-- On the chart of `σ`, the induced morphism factors through the chart of any target cone
containing the image of `σ`. -/
@[reassoc]
theorem affineChartι_comp_finiteFanSchemeHom (f : FanHom Φ Ψ) (σ : Φ.cones)
    (τ : Ψ.cones) (hmaps : Set.MapsTo f.realMap (σ.val : Set V) (τ.val : Set V')) :
    Φ.affineChartι R σ ≫ f.finiteFanSchemeHom R =
      affineChartMap R Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hmaps ≫
        Ψ.affineChartι R τ := by
  have hface : (f.leastCone σ.property).IsFaceOf τ.val :=
    Ψ.isFaceOf_of_le τ.property (f.leastCone_mem σ.property)
      (f.leastCone_le σ.property τ.property fun _ ⟨y, hy, hyx⟩ ↦ hyx ▸ hmaps hy)
  rw [finiteFanSchemeHom, Fan.affineChartι_finiteFanSchemeDesc R Φ (f.chartToScheme R)
    (f.faceAffineChartMap_comp_chartToScheme R) σ, chartToScheme,
    ← Fan.faceAffineChartMap_comp_affineChartι R
      (τ := ⟨f.leastCone σ.property, f.leastCone_mem σ.property⟩) (σ := τ) hface,
    ← Category.assoc, faceAffineChartMap_eq_affineChartMap, affineChartMap_comp]
  simp only [AddMonoidHom.id_comp, LinearMap.id_comp]

/-- The induced map of toric schemes respects the structure morphisms to `Spec R`. -/
@[reassoc (attr := simp)]
theorem finiteFanSchemeHom_comp_finiteFanSchemeToSpec (f : FanHom Φ Ψ) :
    f.finiteFanSchemeHom R ≫ Ψ.finiteFanSchemeToSpec R = Φ.finiteFanSchemeToSpec R := by
  apply Fan.finiteFanScheme_hom_ext R Φ
  intro σ
  rw [affineChartι_comp_finiteFanSchemeHom_assoc R f σ
      ⟨f.leastCone σ.property, f.leastCone_mem σ.property⟩
      (fun x hx ↦ f.map_le_leastCone σ.property ⟨x, hx, rfl⟩)]
  simp only [Fan.affineChartι_finiteFanSchemeToSpec]
  exact affineChartMap_comp_specAlgebraMap R _ _ _ _ _ _

/-- The toric morphism of a map of fans is a morphism over the coefficient ring. -/
instance isOver_finiteFanSchemeHom (f : FanHom Φ Ψ) :
    (f.finiteFanSchemeHom R).IsOver (Spec (.of R)) where
  comp_over := by
    simp only [Fan.finiteFanScheme_over, finiteFanSchemeHom_comp_finiteFanSchemeToSpec]

/-- The identity fan morphism gives the identity morphism of the toric scheme. -/
@[simp]
theorem finiteFanSchemeHom_id (Φ : Fan i) :
    (FanHom.id Φ).finiteFanSchemeHom R = 𝟙 (Φ.finiteFanScheme R) := by
  apply Fan.finiteFanScheme_hom_ext R Φ
  intro σ
  have hid : Set.MapsTo (FanHom.id Φ).realMap (σ.val : Set V) (σ.val : Set V) := by
    simpa only [FanHom.id_realMap, LinearMap.id_coe] using Set.mapsTo_id (σ.val : Set V)
  rw [affineChartι_comp_finiteFanSchemeHom R (FanHom.id Φ) σ σ hid]
  simp

/-- The morphism of toric schemes induced by a composite is the composite of the induced maps. -/
@[simp]
theorem finiteFanSchemeHom_comp (g : FanHom Ψ Ω) (f : FanHom Φ Ψ) :
    (g.comp f).finiteFanSchemeHom R = f.finiteFanSchemeHom R ≫ g.finiteFanSchemeHom R := by
  apply Fan.finiteFanScheme_hom_ext R Φ
  intro σ
  let τ : Ψ.cones := ⟨f.leastCone σ.property, f.leastCone_mem σ.property⟩
  let υ : Ω.cones := ⟨g.leastCone τ.property, g.leastCone_mem τ.property⟩
  have hf : Set.MapsTo f.realMap (σ.val : Set V) (τ.val : Set V') :=
    fun x hx ↦ f.map_le_leastCone σ.property ⟨x, hx, rfl⟩
  have hg : Set.MapsTo g.realMap (τ.val : Set V') (υ.val : Set V'') :=
    fun x hx ↦ g.map_le_leastCone τ.property ⟨x, hx, rfl⟩
  have hgf : Set.MapsTo (g.comp f).realMap (σ.val : Set V) (υ.val : Set V'') := by
    simpa only [FanHom.comp_realMap, LinearMap.coe_comp] using hg.comp hf
  rw [affineChartι_comp_finiteFanSchemeHom R (g.comp f) σ υ hgf,
    affineChartι_comp_finiteFanSchemeHom_assoc R f σ τ hf,
    affineChartι_comp_finiteFanSchemeHom R g τ υ hg, ← Category.assoc, affineChartMap_comp]
  simp only [FanHom.comp_latticeMap, FanHom.comp_realMap]

/-- The induced toric morphisms commute with changing the coefficient ring. -/
@[reassoc]
theorem finiteFanSchemeHom_comp_finiteFanSchemeMap (f : FanHom Φ Ψ) :
    f.finiteFanSchemeHom S ≫ Ψ.finiteFanSchemeMap R S =
      Φ.finiteFanSchemeMap R S ≫ f.finiteFanSchemeHom R := by
  apply Fan.finiteFanScheme_hom_ext S Φ
  intro σ
  let τ : Ψ.cones := ⟨f.leastCone σ.property, f.leastCone_mem σ.property⟩
  have hmaps : Set.MapsTo f.realMap (σ.val : Set V) (τ.val : Set V') :=
    fun x hx ↦ f.map_le_leastCone σ.property ⟨x, hx, rfl⟩
  rw [affineChartι_comp_finiteFanSchemeHom_assoc S f σ τ hmaps,
    Fan.affineChartι_finiteFanSchemeMap, Fan.affineChartι_finiteFanSchemeMap_assoc,
    affineChartι_comp_finiteFanSchemeHom R f σ τ hmaps, affineChartMap_comp_coefficientMap_assoc]

end FanHom

namespace FanEquiv

variable {Φ : Fan i} {Ψ : Fan i'}

/-- An equivalence of fans induces an isomorphism of their toric schemes over the same ring. -/
noncomputable def finiteFanSchemeIso (e : FanEquiv Φ Ψ) :
    Φ.finiteFanScheme R ≅ Ψ.finiteFanScheme R where
  hom := e.toFanHom.finiteFanSchemeHom R
  inv := e.symm.toFanHom.finiteFanSchemeHom R
  hom_inv_id := by
    rw [← FanHom.finiteFanSchemeHom_comp, ← toFanHom_trans, self_trans_symm,
      toFanHom_refl, FanHom.finiteFanSchemeHom_id]
  inv_hom_id := by
    rw [← FanHom.finiteFanSchemeHom_comp, ← toFanHom_trans, symm_trans_self,
      toFanHom_refl, FanHom.finiteFanSchemeHom_id]

/-- The forward morphism is the toric morphism of the underlying fan map. -/
@[simp]
theorem finiteFanSchemeIso_hom (e : FanEquiv Φ Ψ) :
    (e.finiteFanSchemeIso R).hom = e.toFanHom.finiteFanSchemeHom R :=
  (rfl)

/-- The inverse morphism is the toric morphism of the inverse fan map. -/
@[simp]
theorem finiteFanSchemeIso_inv (e : FanEquiv Φ Ψ) :
    (e.finiteFanSchemeIso R).inv = e.symm.toFanHom.finiteFanSchemeHom R :=
  (rfl)

/-- The toric morphism of a fan equivalence is an isomorphism. -/
instance isIso_finiteFanSchemeHom (e : FanEquiv Φ Ψ) : IsIso (e.toFanHom.finiteFanSchemeHom R) :=
  inferInstanceAs (IsIso (e.finiteFanSchemeIso R).hom)

/-- A fan equivalence and its inverse induce inverse morphisms of schemes. -/
@[reassoc (attr := simp)]
theorem finiteFanSchemeHom_comp_symm (e : FanEquiv Φ Ψ) :
    e.toFanHom.finiteFanSchemeHom R ≫ e.symm.toFanHom.finiteFanSchemeHom R =
      𝟙 (Φ.finiteFanScheme R) :=
  (e.finiteFanSchemeIso R).hom_inv_id

/-- A fan equivalence carries a cone chart into the chart of the image cone. -/
theorem mapsTo_affineChartι (e : FanEquiv Φ Ψ) (σ : Φ.cones) :
    Set.MapsTo (e.toFanHom.finiteFanSchemeHom R) (Set.range (Φ.affineChartι R σ))
      (Set.range (Ψ.affineChartι R (e.coneEquiv σ))) := by
  rintro _ ⟨x, rfl⟩
  rw [← Scheme.Hom.comp_apply, e.toFanHom.affineChartι_comp_finiteFanSchemeHom R
    σ (e.coneEquiv σ) (e.mapsTo_coneEquiv σ), Scheme.Hom.comp_apply]
  exact Set.mem_range_self _

private theorem mapsTo_zeroChart (e : FanEquiv Φ Ψ)
    (hΦ : (⊥ : PointedCone ℝ V) ∈ Φ.cones) (hΨ : (⊥ : PointedCone ℝ V') ∈ Ψ.cones) :
    Set.MapsTo (e.toFanHom.finiteFanSchemeHom R)
      (Set.range (Φ.affineChartι R ⟨⊥, hΦ⟩)) (Set.range (Ψ.affineChartι R ⟨⊥, hΨ⟩)) := by
  have h : e.coneEquiv ⟨⊥, hΦ⟩ = ⟨⊥, hΨ⟩ := by
    apply Subtype.ext
    rw [e.coneEquiv_apply_coe]
    ext x
    simp [PointedCone.mem_map, eq_comm]
  rw [← h]
  exact e.mapsTo_affineChartι R _

/-- A fan equivalence identifies the preimage of the zero-cone chart. -/
theorem preimage_range_zeroChart (e : FanEquiv Φ Ψ)
    (hΦ : (⊥ : PointedCone ℝ V) ∈ Φ.cones) (hΨ : (⊥ : PointedCone ℝ V') ∈ Ψ.cones) :
    e.toFanHom.finiteFanSchemeHom R ⁻¹' Set.range (Ψ.affineChartι R ⟨⊥, hΨ⟩) =
      Set.range (Φ.affineChartι R ⟨⊥, hΦ⟩) := by
  refine Set.Subset.antisymm (fun x hx ↦ ?_) (e.mapsTo_zeroChart R hΦ hΨ)
  simpa only [← Scheme.Hom.comp_apply, finiteFanSchemeHom_comp_symm, Scheme.Hom.id_base,
    TopCat.coe_id, id_eq] using e.symm.mapsTo_zeroChart R hΨ hΦ hx

end FanEquiv

end TauCeti.Toric
