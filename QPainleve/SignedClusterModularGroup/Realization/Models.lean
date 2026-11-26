/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.Geometry.Toric.Fan.Boundary.Contraction
public import QPainleve.SignedClusterModularGroup.Realization.Boundary

/-!
# Nodal target models for geometric realizations

The nodal contraction condition records the geometry of a contracted toric fiber.
To compare two realized X maps by their marked actions, the target fibers must
admit such contractions with a common set of surviving rays.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric Scheme

namespace QPainleve.SignedClusterModularGroup

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Xtor[" r "]" => Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))
local notation "D[" P "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair P)))
local notation "center" c:arg => (fun j : Fin _ ↦ c (ofAdd (Pi.single j 1)))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n]
  {L : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily ((Φ.boundaryIdeal h₀).subscheme ↘ S)]
  {γ : Type*} {a : γ → ((Φ.boundaryIdeal h₀).subscheme ↘ S).smoothLocus}
  {toricCycle : NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ)}

namespace ContractedToricFiber

variable {c : Multiplicative (Fin r → ℤ) →* ℂˣ} {P : MarkedSurface ℂ n B Xtor[r]}
  (p : ContractedToricFiber b s hΦ toricCycle origin ι c P)

local notation "Model[" b "," s "," c "]" => Fan.internalBlowupTower b s (center c)

/-- The marked boundary is a Cartier cycle of rational curves and the specified
projection reverses a tower of blowups at boundary nodes. -/
structure IsNodalContraction : Prop where
  /-- The boundary is Cartier. -/
  cartier : D[P].IsEffectiveCartier
  /-- The boundary normalization has genus zero on every component. -/
  genus_zero :
    letI := P.prestable_boundaryImage
    ∀ v : irreducibleComponents (D[P].subscheme.singularLocus ℂ).blowup,
      (D[P].subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0
  /-- The nodal tower gives the specified projection from the ordered model. -/
  exists_tower : ∃ (l : ℕ) (W : Scheme) (A : BlowupTower P.surface l W)
    (_ : IsNodalBoundaryTower D[P] (P.surface ↘ S) (𝟙 P.surface) A)
    (e : W ≅ (Model[b,s,c]).1), e.inv ≫ A.toBase = p.projection

/-- The ray of a boundary prime of the marked surface, read from its strict transform
on the ordered model. -/
noncomputable def boundaryRayEmbedding : D[P].boundaryPrimes ↪ Φ.Ray :=
  Fan.contractedBoundaryRayEmbedding hΦ b s (center c) p.projection p.support_comap

/-- The marked embedding is the toric contraction embedding for the model's projection. -/
theorem boundaryRayEmbedding_def :
    p.boundaryRayEmbedding =
      Fan.contractedBoundaryRayEmbedding hΦ b s (center c) p.projection p.support_comap :=
  (rfl)

/-- The ray of a marked boundary prime is determined by the image of the strict prime. -/
theorem boundaryRayEmbedding_eq_iff (x : D[P].boundaryPrimes) (ρ : Φ.Ray) :
    p.boundaryRayEmbedding x = ρ ↔
      p.projection (Fan.internalBlowupBoundaryPrimeEquiv hΦ b s (center c) ρ).val = x.val := by
  rw [p.boundaryRayEmbedding_def, Fan.contractedBoundaryRayEmbedding_eq_iff]

/-- A ray occurs in the contracted boundary exactly when its strict prime projects
to a boundary prime on the marked surface. -/
theorem mem_range_boundaryRayEmbedding_iff (ρ : Φ.Ray) :
    ρ ∈ Set.range p.boundaryRayEmbedding ↔
      p.projection (Fan.internalBlowupBoundaryPrimeEquiv hΦ b s (center c) ρ).val ∈
        D[P].boundaryPrimes := by
  rw [p.boundaryRayEmbedding_def, Fan.mem_range_contractedBoundaryRayEmbedding_iff]

end ContractedToricFiber

namespace GeometricRealization

/-- Every center reached by `C` admits a contracted toric model with a rational nodal
boundary and the specified set of surviving rays. -/
abbrev HasNodalToricTargetModels
    {T₀ T₁ : Over S} {P : Point T₁ → MarkedSurface ℂ n B Xtor[r]}
    (centers : Point T₁ → Multiplicative (Fin r → ℤ) →* ℂˣ) (survives : Set Φ.Ray)
    (C : T₀.left.PartialMap T₁.left) [C.IsOver T₀.hom T₁.hom] : Prop :=
  ∀ x : CenterPoint C,
    let t := x ≫ C.domainTarget
    ∃ p : ContractedToricFiber b s hΦ toricCycle origin ι (centers t) (P t),
      p.IsNodalContraction ∧ Set.range p.boundaryRayEmbedding = survives

namespace HasNodalToricTargetModels

variable {T₀ T₁ T₂ : Over S} {P : Point T₂ → MarkedSurface ℂ n B Xtor[r]}
  {centers : Point T₂ → Multiplicative (Fin r → ℤ) →* ℂˣ} {survives : Set Φ.Ray}
  {D : T₁.left.PartialMap T₂.left} [D.IsOver T₁.hom T₂.hom]

/-- Models at every target center supply models for a partial center map. -/
theorem of_forall
    (h : ∀ t, ∃ p : ContractedToricFiber b s hΦ toricCycle origin ι (centers t) (P t),
      p.IsNodalContraction ∧ Set.range p.boundaryRayEmbedding = survives) :
    HasNodalToricTargetModels (b := b) (s := s) (hΦ := hΦ) (toricCycle := toricCycle)
      (origin := origin) (ι := ι) (P := P) centers survives D :=
  fun x ↦ h (x ≫ D.domainTarget (X := T₁) (Y := T₂))

/-- Precomposition preserves the nodal target model condition and its surviving rays. -/
theorem comp [PreirreducibleSpace T₀.left] [Nonempty T₁.left]
    (hD : HasNodalToricTargetModels (b := b) (s := s) (hΦ := hΦ) (toricCycle := toricCycle)
      (origin := origin) (ι := ι) (P := P) centers survives D)
    (C : T₀.left.PartialMap T₁.left) [IsDominant C.hom] [C.IsOver T₀.hom T₁.hom] :
    HasNodalToricTargetModels (b := b) (s := s) (hΦ := hΦ) (toricCycle := toricCycle)
      (origin := origin) (ι := ι) (P := P) centers survives (C.comp D) :=
  C.forall_comp_domainTarget (X := T₀) (Y := T₁) (Z := T₂) D
    (fun t ↦ ∃ p : ContractedToricFiber b s hΦ toricCycle origin ι (centers t) (P t),
      p.IsNodalContraction ∧ Set.range p.boundaryRayEmbedding = survives) hD

end HasNodalToricTargetModels

end GeometricRealization

end QPainleve.SignedClusterModularGroup
