/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Evaluation.Chart

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic

/-!
# Center-fiber charts of toric contractions

The dominant rational chart of a contracted ordered blowup model identifies its
fixed-center X evaluation with the restriction of the variable-center evaluation
in diagonalizable group-scheme coordinates. The comparison uses
`Fan.exists_dominant_chart_comp_contractedXEvaluation` and
`CharacterTorus.pullback_lift_comp_evaluation_comp_diagonalizableGroupSchemeIso`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open TauCeti DiagonalizableGroup TauCeti.AlgebraicGeometry
open QPainleve.CharacterTorus

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {r : ℕ}
  (b : Module.Basis (Fin 2) ℤ N) (s : Fin r → Φ.Ray)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Cent" => (Fin r → ℤ)
local notation "G[" U "]" => FGCommGrpCat.of (Multiplicative U)
local notation "Tor[" U "]" => groupScheme ℂ G[U]
local notation "τ[" U "]" => diagonalizableGroupSchemeIso ℂ G[U]
local notation "repr" => Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin r)

/-- On the dominant chart of a contracted toric model, fixed-center X evaluation
is evaluation on the charge torus at the same center. The output uses the Laurent
coordinates of the independent variables, even though the input center is a point of
the diagonalizable group scheme. -/
theorem exists_dominant_chart_comp_evaluationAtCenter
    (c : S ⟶ Tor[Cent].X.left) (hc : c ≫ Tor[Cent].X.hom = 𝟙 S) (hΦ : Φ.IsRegular)
    {Z : Scheme} [IsIntegral Z]
    (p : let pt : (S).asOver S ⟶ Tor[Cent].X :=
          Over.homMk c (hc.trans (Spec.map_id (CommRingCat.of ℂ)).symm)
        let χ : Multiplicative Cent →* ℂˣ :=
      schemePointsMulEquiv (R := ℂ) (A := ℂ) G[Cent] pt
        (internalBlowupTower b s (fun j ↦ χ (ofAdd (Pi.single j 1)))).1 ⟶ Z)
    [IsModification p] :
    letI : Module.Free ℤ N := .of_basis b
    letI : IsAddFG N := Module.Finite.iff_addGroup_fg.mp (.of_basis b)
    let pt : (S).asOver S ⟶ Tor[Cent].X :=
      Over.homMk c (hc.trans (Spec.map_id (CommRingCat.of ℂ)).symm)
    let χ : Multiplicative Cent →* ℂˣ :=
      schemePointsMulEquiv (R := ℂ) (A := ℂ) G[Cent] pt
    ∃ (j : Tor[N].X.left ⤏ Z) (_ : j.IsDominant),
      j.comp (contractedXEvaluation b s χ hΦ p) =
        (evaluationAtCenter ℂ (rayChargeMap s).toAddMonoidHom c hc ≫
          (τ[Cent]).hom ≫ map ℂ (repr).toAddEquiv.toAddMonoidHom).toRationalMap := by
  dsimp only
  let : Module.Free ℤ N := .of_basis b
  let : IsAddFG N := Module.Finite.iff_addGroup_fg.mp (.of_basis b)
  let pt : (S).asOver S ⟶ Tor[Cent].X :=
    Over.homMk c (hc.trans (Spec.map_id (CommRingCat.of ℂ)).symm)
  let χ : Multiplicative Cent →* ℂˣ :=
    schemePointsMulEquiv (R := ℂ) (A := ℂ) G[Cent] pt
  obtain ⟨j, hj, hchart⟩ := exists_dominant_chart_comp_contractedXEvaluation b s χ hΦ p
  let : j.IsDominant := hj
  let e : Tor[N].X.left ≅ scheme ℂ N := τ[N]
  let a := e.hom.toRationalMap
  let : a.IsDominant := inferInstanceAs (e.hom.toRationalMap.IsDominant)
  refine ⟨a.comp j, inferInstance, ?_⟩
  rw [Scheme.RationalMap.comp_assoc, hchart, Scheme.RationalMap.comp_toRationalMap,
    Scheme.Hom.toRationalMap_compHom]
  let t : Tor[Cent].X.left ≅ scheme ℂ Cent := τ[Cent]
  let v := (rayChargeMap s).toAddMonoidHom
  let f := (repr).toAddEquiv.toAddMonoidHom
  let m := map ℂ f
  have heval : evaluationAtCenter ℂ v c hc ≫ t.hom =
      e.hom ≫ affineCenterSlice χ ≫ affineEvaluation ℂ v := by
    -- Reduce the additive type tag on the character group in the scheme comparison.
    simpa only [evaluationAtCenter, Category.assoc] using!
      pullback_lift_comp_evaluation_comp_diagonalizableGroupSchemeIso v c hc
  apply congrArg Scheme.Hom.toRationalMap
  calc
    _ = e.hom ≫ affineCenterSlice χ ≫ affineEvaluation ℂ v ≫ m :=
      congrArg (e.hom ≫ ·) (affineCenterSlice_comp_affineEvaluation_naturality χ v f).symm
    _ = (e.hom ≫ affineCenterSlice χ ≫ affineEvaluation ℂ v) ≫ m := by
      simp only [Category.assoc]
    _ = (evaluationAtCenter ℂ v c hc ≫ t.hom) ≫ m := congrArg (· ≫ m) heval.symm
    _ = _ := Category.assoc (evaluationAtCenter ℂ v c hc) t.hom m

end TauCeti.Toric.Fan
