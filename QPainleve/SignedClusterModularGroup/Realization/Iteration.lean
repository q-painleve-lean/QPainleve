/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Mutation.Complete
public import QPainleve.SignedClusterModularGroup.Realization.Permutation.Contracted
public import QPainleve.SignedClusterModularGroup.Realization.Word

/-!
# Iterating marked toric presentations along cluster words

An inversion-free word acts on a marked family with ordered nodal contractions.
At each prefix, the transported presentation is valid at every center reached
by that prefix. Mutation can refine the fan before transporting the presentation,
and a permutation reorders the internal centers in the same fan. The realization
on the entire simultaneous noncollision open compares the marked Picard pullback
and the action on the numbered branches. The underlying elementary transformation
is the construction of Gross, Hacking and Keel in
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative PointedCone Quiver
open Module (Basis)
open QPainleve.BlowupTower QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan
open Scheme Scheme.PartialMap

namespace QPainleve.SignedClusterModularGroup

open GeometricRealization (Point CenterPoint)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)

variable (i) in
/-- The data common to the fibers of an ordered toric presentation on a complete
regular fan, with positive cyclic numbering and a fixed auxiliary Picard inclusion. -/
structure CompleteToricPresentation (b : Basis (Fin 2) ℤ N) (r : ℕ)
    (L : Type) [AddCommGroup L] (γ : Type) where
  /-- The complete regular fan of the toric surface. -/
  fan : Fan i
  /-- Completeness of the toric surface fan. -/
  complete : fan.IsComplete
  /-- Regularity of the fan. -/
  regular : fan.IsRegular
  /-- The ray of each internal center, in label order. -/
  rays : Fin r → fan.Ray
  /-- The toric boundary is a prestable curve. -/
  [prestable : PrestableFamily (Dtor[fan,complete.nonempty_cones] ↘ S)]
  /-- The number of components of the toric boundary. -/
  length : ℕ
  /-- The toric boundary has at least one component. -/
  [neZero : NeZero length]
  /-- The marked smooth points used in the boundary numbering. -/
  marks : γ → (Dtor[fan,complete.nonempty_cones] ↘ S).smoothLocus
  /-- The numbering of the components, nodes and branches of the toric boundary. -/
  cycle : Scheme.NodalCycleNumbering marks length
  /-- The ray indexing the first component of the contracted boundary. -/
  origin : ZMod length
  /-- The fixed pullback of the Picard marking in auxiliary toric coordinates. -/
  inclusion : L →ₗ[ℤ] Additive (LineBundleClass fan.algebraicRealization) × (Fin r → ℤ)
  /-- The rays in the order of the toric boundary numbering. -/
  rayOrder : ZMod length ≃ fan.Ray
  /-- The ray order agrees with the numbering of the normalized curve. -/
  component_eq (j : ZMod length) :
    letI := complete.nonempty_cones
    cycle.component j = fan.boundaryNormalizationComponentEquiv regular (rayOrder j)
  /-- Consecutive rays in the positive order span regular two-dimensional cones. -/
  positive (j : ZMod length) :
    b.detDualEquiv (rayOrder j).primitiveGenerator (rayOrder (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : fan.cones, (rayOrder j).toCone ≤ σ ∧ (rayOrder (j + 1)).toCone ≤ σ

variable {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n] {L : Type}
  [AddCommGroup L] {H : LinearMap.BilinForm ℤ L} {γ : Type}

local notation "A" => (Fin r → ℤ)
local notation "Centers" => Over.mk (structureMap ℂ A)
local notation "XTor" => scheme ℂ (Fin r →₀ ℤ)
local notation "χ(" c ")" => pointsEquiv ℂ A
  (Subtype.mk (CommaMorphism.left (c : Point Centers)) (Over.w (c : Point Centers)))
local notation "centers(" a ")" => fun j : Fin r ↦ (a) (ofAdd (Pi.single j 1))
local notation "Dₘ(" M ")" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "src(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainSource (X := Centers) (Y := Centers) C
local notation "dst(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainTarget (X := Centers) (Y := Centers) C

attribute [local instance] hasUniqueDiv_of_free_int

/-- A contracted fiber whose specified projection is realized by a nodal blowup tower. -/
def CompleteToricPresentation.HasNodalModel (Q : CompleteToricPresentation i b r L γ)
    (c : Point Centers) (M : MarkedSurface ℂ n H XTor) : Prop :=
  letI := Q.complete.nonempty_cones
  letI := Q.prestable
  letI := Q.neZero
  ∃ (p : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ(c) M)
    (Y : Scheme) (d : ℕ) (W : BlowupTower M.surface d Y)
    (e : Y ≅ (internalBlowupTower b Q.rays centers(χ(c))).1),
    IsNodalBoundaryTower Dₘ(M) (M.surface ↘ S) (𝟙 _) W ∧ p.projection = e.inv ≫ W.toBase

/-- A nodal model exposes the ordered toric contraction and a nodal tower
whose projection agrees with that contraction. -/
theorem CompleteToricPresentation.hasNodalModel_iff (Q : CompleteToricPresentation i b r L γ)
    (c : Point Centers) (M : MarkedSurface ℂ n H XTor) :
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    Q.HasNodalModel c M ↔
      ∃ (p : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ(c) M)
        (Y : Scheme) (d : ℕ) (W : BlowupTower M.surface d Y)
        (e : Y ≅ (internalBlowupTower b Q.rays centers(χ(c))).1),
        IsNodalBoundaryTower Dₘ(M) (M.surface ↘ S) (𝟙 _) W ∧ p.projection = e.inv ≫ W.toBase :=
  (Iff.rfl)

namespace GeometricRealization

variable {B E D : SkewExchangeMatrix (Fin r)} {P : ChargeSeed B N}
  {w : Word B E} {s : E ⟶ D}

local notation "Cw[" w "," P "]" => Quiver.Path.centerPartialMap ℂ w P
local notation "Cstep[" w "," s "," P "]" => Quiver.Path.centerStepPartialMap ℂ w s P
local notation "Cnext[" w "," s "," P "]" => Quiver.Path.centerPartialMap ℂ (Quiver.Path.cons w s) P

local instance : PreirreducibleSpace (Centers).left :=
  inferInstanceAs (PreirreducibleSpace (scheme ℂ A))

private abbrev NodalModelsOn (Q : CompleteToricPresentation i b r L γ)
    (M : Point Centers → MarkedSurface ℂ n H XTor)
    (C : (scheme ℂ A).PartialMap (scheme ℂ A)) [C.IsOver (Centers).hom (Centers).hom] :=
  ∀ c : CenterPoint (U := Centers) (V := Centers) C,
    Q.HasNodalModel (dst(C,c)) (M (dst(C,c)))

private theorem nodalModelsOn_congr (Q : CompleteToricPresentation i b r L γ)
    (M : Point Centers → MarkedSurface ℂ n H XTor)
    {C D : (scheme ℂ A).PartialMap (scheme ℂ A)}
    [C.IsOver (Centers).hom (Centers).hom] [D.IsOver (Centers).hom (Centers).hom]
    (h : C = D) : NodalModelsOn Q M C ↔ NodalModelsOn Q M D := by
  subst D
  rfl

private theorem hasNodalModel_stepSource (Q : CompleteToricPresentation i b r L γ)
    {M : Point Centers → MarkedSurface ℂ n H XTor} :
    NodalModelsOn (n := n) (H := H) Q M Cw[w,P] →
    ∀ c : CenterPoint (U := Centers) (V := Centers) Cstep[w,s,P],
      Q.HasNodalModel (src(Cstep[w,s,P],c)) (M (src(Cstep[w,s,P],c))) := by
  intro models c
  have hU : (Cstep[w,s,P]).domain ≤ (Cw[w,P]).hom.opensRange := by
    rw [Path.centerStepPartialMap_domain]
    exact inf_le_left
  have hr : Set.range (Cstep[w,s,P]).domain.ι ⊆ Set.range (Cw[w,P]).hom := by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
    exact hU
  let f := IsOpenImmersion.lift (Cw[w,P]).hom (Cstep[w,s,P]).domain.ι hr
  have hf : f ≫ (Cw[w,P]).hom = (Cstep[w,s,P]).domain.ι := IsOpenImmersion.lift_fac _ _ _
  have ho : f ≫ ((Cw[w,P]).domainOver (X := Centers) (Y := Centers)).hom =
      ((Cstep[w,s,P]).domainOver (X := Centers) (Y := Centers)).hom := by
    -- Expose the structure morphisms of the two domains to use the over-base equation.
    change f ≫ (Cw[w,P]).domain.ι ≫ (Centers).hom = (Cstep[w,s,P]).domain.ι ≫ (Centers).hom
    rw [← (Cw[w,P]).over (Centers).hom (Centers).hom, ← Category.assoc, hf]
  let a : (Cstep[w,s,P]).domainOver (X := Centers) (Y := Centers) ⟶
      (Cw[w,P]).domainOver (X := Centers) (Y := Centers) := Over.homMk f ho
  have ha : a ≫ (Cw[w,P]).domainTarget (X := Centers) (Y := Centers) =
      (Cstep[w,s,P]).domainSource (X := Centers) (Y := Centers) := by
    ext : 1
    simpa only [Over.comp_left, Over.homMk_left, domainTarget_left, domainSource_left, a] using hf
  simpa only [Category.assoc, ha] using models (c ≫ a)

private theorem hasNodalModel_appended (Q : CompleteToricPresentation i b r L γ)
    {M : Point Centers → MarkedSurface ℂ n H XTor} :
    NodalModelsOn (n := n) (H := H) Q M Cstep[w,s,P] →
    NodalModelsOn (n := n) (H := H) Q M Cnext[w,s,P] := by
  intro models c
  let f := (w.centerStepDomainIso ℂ s P).hom
  have hf : f ≫ (Cstep[w,s,P]).hom = (Cnext[w,s,P]).hom :=
    Path.centerStepDomainIso_hom_centerStepPartialMap_hom w s P
  have ho : f ≫ ((Cstep[w,s,P]).domainOver (X := Centers) (Y := Centers)).hom =
      ((Cnext[w,s,P]).domainOver (X := Centers) (Y := Centers)).hom := by
    -- Expose the structure morphisms of the two domains to use the over-base equations.
    change f ≫ (Cstep[w,s,P]).domain.ι ≫ (Centers).hom =
      (Cnext[w,s,P]).domain.ι ≫ (Centers).hom
    rw [← (Cstep[w,s,P]).over (Centers).hom (Centers).hom, ← Category.assoc, hf,
      (Cnext[w,s,P]).over (Centers).hom (Centers).hom]
  let a : (Cnext[w,s,P]).domainOver (X := Centers) (Y := Centers) ⟶
      (Cstep[w,s,P]).domainOver (X := Centers) (Y := Centers) := Over.homMk f ho
  have ha : a ≫ (Cstep[w,s,P]).domainTarget (X := Centers) (Y := Centers) =
      (Cnext[w,s,P]).domainTarget (X := Centers) (Y := Centers) := by
    ext : 1
    simpa only [Over.comp_left, Over.homMk_left, domainTarget_left, a] using hf
  simpa only [Category.assoc, ha] using models (c ≫ a)

private abbrev StepResult (w : Word B E) (s : E ⟶ D) (P : ChargeSeed B N)
    (M : Point Centers → MarkedSurface ℂ n H XTor) :=
  ∃ (γ' : Type) (Q' : CompleteToricPresentation i b r L γ')
    (M' : Point Centers → MarkedSurface ℂ n H XTor)
    (R : GeometricRealization (T₀ := Centers) (T₁ := Centers) M M' Cstep[w,s,P]
      (s.toPath.xRationalMap ℂ)),
    ((w.cons s).chargeTarget P).charge = rayChargeMap Q'.rays ∧
    R.picard = .refl H ∧ R.boundaryAction = 1 ∧
    ∀ c : CenterPoint (U := Centers) (V := Centers) Cstep[w,s,P],
      Q'.HasNodalModel (dst(Cstep[w,s,P],c)) (M' (dst(Cstep[w,s,P],c)))

private theorem exists_mutation_step {r : ℕ} {B E : SkewExchangeMatrix (Fin (r + 1))}
    (w : Word B E) (P : ChargeSeed B N) (k : Fin (r + 1))
    (Q : CompleteToricPresentation i b (r + 1) L γ)
    (hform : (w.chargeTarget P).form = b.detDualEquiv.toLinearMap)
    (hcharge : (w.chargeTarget P).charge = rayChargeMap Q.rays)
    (M : Point (Over.mk (structureMap ℂ (Fin (r + 1) → ℤ))) →
      MarkedSurface ℂ n H (scheme ℂ (Fin (r + 1) →₀ ℤ)))
    (models : NodalModelsOn Q M Cw[w,P]) :
    StepResult (b := b) (i := i) w ((Generator.mutate k).toStep E) P M := by
  let s := (Generator.mutate k).toStep E
  let U := (w.centerStepPartialMap ℂ s P).domain
  have hU := (w.centerStepPartialMap ℂ s P).dense_domain
  have hle : U ≤ (s.toPath.centerPartialMap ℂ (w.chargeTarget P)).domain := by
    simpa only [U, Path.centerStepPartialMap_domain] using inf_le_right
      (a := (w.centerPartialMap ℂ P).hom.opensRange)
  have hC := w.centerStepPartialMap_eq_restrict s P (K := ℂ)
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  obtain ⟨Ω, h, hΩ, hcΩ, hopp, hpre, l', hl', T', o', v, M', R, hv, hpos,
      hcharge', hpic, hact, hmodels⟩ :=
    exists_mutate_contracted_of_complete b Q.rays k Q.regular (w.chargeTarget P) hform
      hcharge U hU hle M Q.rayOrder Q.complete Q.component_eq Q.positive
      (T := Q.cycle) (o := Q.origin) (J := Q.inclusion) (by
        rw [← hC]
        exact hasNodalModel_stepSource Q models)
  let t := (h.liftRay ∘ Q.rays) k
  let Ψ := Ω.mutationFan b t.primitiveGenerator_ne_zero t.hull_primitiveGenerator_mem hopp
  let hcΨ := (Ω.isComplete_mutationFan_iff b t.primitiveGenerator_ne_zero
    t.hull_primitiveGenerator_mem hopp).mpr hcΩ
  let hΨ := (Ω.isRegular_mutationFan_iff b t.primitiveGenerator_ne_zero
    t.hull_primitiveGenerator_mem hopp).mpr hΩ
  let J' := (mutationPicardEquiv b (h.liftRay ∘ Q.rays) k hopp hΩ).symm.toLinearMap.comp
    ((LinearMap.prodMap (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive
      (LineBundleClass.pullbackHom (FanHom.algebraicMap (Fan.IsSubdivision.toFanHom h)))))
      LinearMap.id).comp Q.inclusion)
  let Q' : CompleteToricPresentation i b (r + 1) L Empty :=
    { fan := Ψ
      complete := hcΨ
      regular := hΨ
      rays := Ω.mutationFanCenterRays b (h.liftRay ∘ Q.rays) k hopp
      prestable := hpre
      length := l'
      neZero := hl'
      marks := Empty.elim
      cycle := T'
      origin := o'
      inclusion := J'
      rayOrder := v
      component_eq := hv
      positive := hpos }
  refine ⟨Empty, Q', M', R.congrMaps hC.symm rfl, ?_, (congrMaps_picard _ _ _).trans hpic,
    (congrMaps_boundaryAction _ _ _).trans hact, ?_⟩
  · simpa only [s, Path.chargeTarget_cons, Path.chargeTarget_nil, Hom.toPath, Q'] using hcharge'
  · refine (nodalModelsOn_congr Q' M' hC).mpr ?_
    intro c
    obtain ⟨_, _, _, p, Y, d, W, e, hW, hp⟩ := hmodels c
    exact ⟨p, Y, d, W, e, hW, hp⟩

private theorem exists_permutation_step (w : Word B E) (P : ChargeSeed B N)
    (σ : Equiv.Perm (Fin r)) (Q : CompleteToricPresentation i b r L γ)
    (hcharge : (w.chargeTarget P).charge = rayChargeMap Q.rays)
    (M : Point Centers → MarkedSurface ℂ n H XTor)
    (models : NodalModelsOn Q M Cw[w,P]) :
    StepResult (b := b) (i := i) w ((Generator.permute σ).toStep E) P M := by
  let s := (Generator.permute σ).toStep E
  let U := (w.centerStepPartialMap ℂ s P).domain
  have hU := (w.centerStepPartialMap ℂ s P).dense_domain
  have hle : U ≤ (s.toPath.centerPartialMap ℂ (w.chargeTarget P)).domain := by
    simpa only [U, Path.centerStepPartialMap_domain] using inf_le_right
      (a := (w.centerPartialMap ℂ P).hom.opensRange)
  have hC := w.centerStepPartialMap_eq_restrict s P (K := ℂ)
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  obtain ⟨R, hpic, hact, hmodels⟩ :=
    exists_permute_contracted σ (w.chargeTarget P) M hcharge hU hle
      (b := b) (hΦ := Q.regular) (T := Q.cycle) (o := Q.origin) (J := Q.inclusion) (by
        rw [← hC]
        exact hasNodalModel_stepSource Q models)
  let Q' : CompleteToricPresentation i b r L γ := { Q with
    rays := Q.rays ∘ σ
    inclusion := (LinearMap.prodMap LinearMap.id
      (LinearEquiv.funCongrLeft ℤ ℤ σ).toLinearMap).comp Q.inclusion }
  let M' : Point Centers → MarkedSurface ℂ n H XTor :=
    fun y ↦ (M (y ≫ (s.toPath.centerIsoOver ℂ).inv)).compEvaluation
      (Spec.map (CommRingCat.ofHom (TauCeti.LaurentRing.rename (R := ℂ) σ.toFun).toRingHom))
  refine ⟨γ, Q', M', R.congrMaps hC.symm rfl, ?_, (congrMaps_picard _ _ _).trans hpic,
    (congrMaps_boundaryAction _ _ _).trans hact, ?_⟩
  · rw [Path.chargeTarget_cons, Step.chargeTarget_permute_charge, hcharge]
    apply (Pi.basisFun ℤ (Fin r)).ext
    intro j
    have hj : LinearEquiv.funCongrLeft ℤ ℤ σ.symm (Pi.single j 1) = Pi.single (σ j) 1 := by
      funext a
      simpa only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp_apply,
        Equiv.symm_symm] using congrFun (Pi.single_comp_equiv σ.symm j (1 : ℤ)) a
    simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hj,
      rayChargeMap_single, Q', Function.comp_apply]
  · exact (nodalModelsOn_congr Q' M' hC).mpr (fun c ↦ hmodels c)

private theorem exists_step (w : Word B E) (s : E ⟶ D) (P : ChargeSeed B N)
    (hs : (Step.generator s).inversionCount = 0) (Q : CompleteToricPresentation i b r L γ)
    (hform : (w.chargeTarget P).form = b.detDualEquiv.toLinearMap)
    (hcharge : (w.chargeTarget P).charge = rayChargeMap Q.rays)
    (M : Point Centers → MarkedSurface ℂ n H XTor)
    (models : NodalModelsOn Q M Cw[w,P]) :
    StepResult (b := b) (i := i) w s P M := by
  obtain ⟨g, rfl⟩ := s
  have he : (⟨g, rfl⟩ : E ⟶ g.target E) = g.toStep E :=
    Step.ext (Generator.toStep_generator g E).symm
  rw [he]
  cases g with
  | mutate k =>
    cases r with
    | zero => exact Fin.elim0 k
    | succ r => exact exists_mutation_step w P k Q hform hcharge M models
  | permute σ => exact exists_permutation_step w P σ Q hcharge M models
  | invert => simp at hs

/-- Every inversion-free word starting at an ordered toric presentation on a
complete regular fan has a geometric realization on its entire simultaneous
noncollision open. The terminal family has an ordered presentation with the
word's transported charges and a fixed Picard inclusion in its auxiliary model.
The contracted Picard marking and every numbered branch are preserved. -/
theorem exists_realize_inversion_free_word (w : Word B E) (P : ChargeSeed B N)
    (hw : w.inversionCount = 0) (Q : CompleteToricPresentation i b r L γ)
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = rayChargeMap Q.rays)
    (M : Point Centers → MarkedSurface ℂ n H XTor)
    (models : ∀ c : CenterPoint (U := Centers) (V := Centers)
        ((Path.nil : Word B B).centerPartialMap ℂ P),
      let a := c ≫ ((Path.nil : Word B B).centerPartialMap ℂ P).domainTarget
        (X := Centers) (Y := Centers)
      Q.HasNodalModel a (M a)) :
    ∃ (γ' : Type) (Q' : CompleteToricPresentation i b r L γ')
      (M' : Point Centers → MarkedSurface ℂ n H XTor)
      (R : GeometricRealization (T₀ := Centers) (T₁ := Centers) M M' Cw[w,P] (w.xRationalMap ℂ)),
      (w.chargeTarget P).form = b.detDualEquiv.toLinearMap ∧
      (w.chargeTarget P).charge = rayChargeMap Q'.rays ∧
      R.picard = .refl H ∧ R.boundaryAction = 1 ∧
      ∀ c : CenterPoint (U := Centers) (V := Centers) Cw[w,P],
        Q'.HasNodalModel (dst(Cw[w,P],c)) (M' (dst(Cw[w,P],c))) := by
  induction w with
  | nil =>
    let step : WordStepRealizations (L := fun _ ↦ AddCommGrpCat.of L)
        (form := fun _ ↦ H) P (fun _ ↦ M) (Path.nil : Word B B) :=
      fun {D D'} ↦ WordStepRealizations.nil (k := ℂ) (n := n)
        (L := fun _ ↦ AddCommGrpCat.of L) (form := fun _ ↦ H) P (fun _ ↦ M) (D := D) (D' := D')
    let R := ofWord P Path.nil (@step)
    exact ⟨γ, Q, M, R, by simpa only [Path.chargeTarget_nil] using hform,
      by simpa only [Path.chargeTarget_nil] using hcharge, ofWord_nil_picard P (@step),
      ofWord_nil_boundaryAction P (@step), models⟩
  | @cons E D w s ih =>
    obtain ⟨hw, hs⟩ := Nat.add_eq_zero_iff.mp ((Path.inversionCount_cons w s).symm.trans hw)
    obtain ⟨γ₀, Q₀, M₀, R₀, hform₀, hcharge₀, hpic₀, hact₀, hmodels₀⟩ := ih hw
    obtain ⟨γ', Q', M', R', hcharge', hpic', hact', hmodels'⟩ :=
      exists_step w s P hs Q₀ hform₀ hcharge₀ M₀ hmodels₀
    let C := (w.centerPartialMap ℂ P).comp (w.centerStepPartialMap ℂ s P)
    have hC : (w.cons s).centerPartialMap ℂ P = C := Path.centerPartialMap_cons w s P
    let : C.IsOver (Centers).hom (Centers).hom := hC ▸ inferInstanceAs
      (((w.cons s).centerPartialMap ℂ P).IsOver (Centers).hom (Centers).hom)
    let R := (R₀.comp R').congrMaps hC.symm
      (by rw [← Path.xRationalMap_comp, Path.comp_toPath_eq_cons])
    have hform' : ((w.cons s).chargeTarget P).form = b.detDualEquiv.toLinearMap := by
      obtain ⟨g, rfl⟩ := s
      have he : (⟨g, rfl⟩ : E ⟶ g.target E) = g.toStep E :=
        Step.ext (Generator.toStep_generator g E).symm
      rw [he, Path.chargeTarget_cons]
      cases g <;> simp_all
    refine ⟨γ', Q', M', R, hform', hcharge', ?_, ?_, hasNodalModel_appended Q' hmodels'⟩
    · simp only [R, congrMaps_picard, comp_picard, hpic₀, hpic']
      exact DFunLike.ext _ _ fun _ ↦ rfl
    · simp only [R, congrMaps_boundaryAction, comp_boundaryAction, hact₀, hact', mul_one]

end GeometricRealization

end QPainleve.SignedClusterModularGroup
