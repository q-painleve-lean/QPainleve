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

A signed cluster word acts on a marked family with ordered nodal contractions.
At each prefix, the transported presentation is valid at every center reached
by that prefix. Mutation can refine the fan before transporting the presentation,
a permutation reorders the internal centers in the same fan, and inversion reverses
the frame and boundary numbering. The realization on the entire simultaneous
noncollision open compares the marked Picard pullback and the action on the
numbered branches. The underlying elementary transformation
is the construction of Gross, Hacking and Keel in
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
The signed inversion is the generator of Bershtein, Gavrylenko and Marshakov,
[*Cluster integrable systems, q-Painlevé equations and their quantization*, §3.1][BGM].

[BGM]: https://arxiv.org/abs/1711.02063
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative PointedCone Quiver
open Module (Basis)
open QPainleve.BlowupTower QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan
open Scheme Scheme.PartialMap

namespace QPainleve.SignedClusterModularGroup

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

open GeometricRealization (Point CenterPoint)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

variable {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n] {L : Type}
  [AddCommGroup L] {H : LinearMap.BilinForm ℤ L} {γ : Type}

local notation "A" => (Fin r → ℤ)
local notation "Centers" => Over.mk (structureMap k₀ A)
local notation "XTor" => scheme k₀ (Fin r →₀ ℤ)
local notation "src(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainSource (X := Centers) (Y := Centers) C
local notation "dst(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainTarget (X := Centers) (Y := Centers) C

attribute [local instance] hasUniqueDiv_of_free_int

namespace GeometricRealization

variable {B E D : SkewExchangeMatrix (Fin r)} {P : ChargeSeed B N}
  {w : Word B E} {s : E ⟶ D}

local notation "Cw[" w "," P "]" => Quiver.Path.centerPartialMap k₀ w P
local notation "Cstep[" w "," s "," P "]" => Quiver.Path.centerStepPartialMap k₀ w s P
local notation "Cnext[" w "," s "," P "]" => Quiver.Path.centerPartialMap k₀
  (Quiver.Path.cons w s) P

local instance : PreirreducibleSpace (Centers).left :=
  inferInstanceAs (PreirreducibleSpace (scheme k₀ A))

private abbrev NodalModelsOn (Q : CompleteToricPresentation k₀ i b r L γ)
    (M : Point Centers → MarkedSurface k₀ n H XTor)
    (C : (scheme k₀ A).PartialMap (scheme k₀ A)) [C.IsOver (Centers).hom (Centers).hom] :=
  ∀ c : CenterPoint (U := Centers) (V := Centers) C,
    Q.HasNodalModel (dst(C,c)) (M (dst(C,c)))

private theorem nodalModelsOn_congr (Q : CompleteToricPresentation k₀ i b r L γ)
    (M : Point Centers → MarkedSurface k₀ n H XTor)
    {C D : (scheme k₀ A).PartialMap (scheme k₀ A)}
    [C.IsOver (Centers).hom (Centers).hom] [D.IsOver (Centers).hom (Centers).hom]
    (h : C = D) : NodalModelsOn Q M C ↔ NodalModelsOn Q M D := by
  subst D
  rfl

private theorem hasNodalModel_stepSource (Q : CompleteToricPresentation k₀ i b r L γ)
    {M : Point Centers → MarkedSurface k₀ n H XTor} :
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

private theorem hasNodalModel_appended (Q : CompleteToricPresentation k₀ i b r L γ)
    {M : Point Centers → MarkedSurface k₀ n H XTor} :
    NodalModelsOn (n := n) (H := H) Q M Cstep[w,s,P] →
    NodalModelsOn (n := n) (H := H) Q M Cnext[w,s,P] := by
  intro models
  have hC := Path.centerPartialMap_cons (K := k₀) w s P
  let : ((Cw[w,P]).comp (Cstep[w,s,P])).IsOver (Centers).hom (Centers).hom :=
    hC ▸ inferInstanceAs ((Cnext[w,s,P]).IsOver (Centers).hom (Centers).hom)
  exact (nodalModelsOn_congr Q M hC).mpr
    ((Cw[w,P]).forall_comp_domainTarget (X := Centers) (Y := Centers) (Z := Centers)
      (Cstep[w,s,P]) (fun c ↦ Q.HasNodalModel c (M c)) models)

local notation "frameSwap" => (Equiv.swap 0 1 : Equiv.Perm (Fin 2))
local notation "reflection" => (DihedralGroup.sr (0 : ZMod n))

private abbrev StepResult (b : Basis (Fin 2) ℤ N)
    (w : Word B E) (s : E ⟶ D) (P : ChargeSeed B N)
    (M : Point Centers → MarkedSurface k₀ n H XTor) :=
  ∃ (γ' : Type) (Q' : CompleteToricPresentation k₀ i b r L γ')
    (M' : Point Centers → MarkedSurface k₀ n H XTor)
    (R : GeometricRealization (T₀ := Centers) (T₁ := Centers) M M' Cstep[w,s,P]
      (s.toPath.xRationalMap k₀)),
    ((w.cons s).chargeTarget P).form = b.detDualEquiv.toLinearMap ∧
    ((w.cons s).chargeTarget P).charge = rayChargeMap Q'.rays ∧
    R.picard = .refl H ∧ R.boundaryAction = reflection ^ (Step.generator s).inversionCount ∧
    ∀ c : CenterPoint (U := Centers) (V := Centers) Cstep[w,s,P],
      Q'.HasNodalModel (dst(Cstep[w,s,P],c)) (M' (dst(Cstep[w,s,P],c)))

private theorem exists_mutation_step {r : ℕ} {B E : SkewExchangeMatrix (Fin (r + 1))}
    (w : Word B E) (P : ChargeSeed B N) (k : Fin (r + 1))
    (Q : CompleteToricPresentation k₀ i b (r + 1) L γ)
    (hform : (w.chargeTarget P).form = b.detDualEquiv.toLinearMap)
    (hcharge : (w.chargeTarget P).charge = rayChargeMap Q.rays)
    (M : Point (Over.mk (structureMap k₀ (Fin (r + 1) → ℤ))) →
      MarkedSurface k₀ n H (scheme k₀ (Fin (r + 1) →₀ ℤ)))
    (models : NodalModelsOn Q M Cw[w,P]) :
    StepResult (i := i) b w ((Generator.mutate k).toStep E) P M := by
  let s := (Generator.mutate k).toStep E
  let U := (w.centerStepPartialMap k₀ s P).domain
  have hU := (w.centerStepPartialMap k₀ s P).dense_domain
  have hle : U ≤ (s.toPath.centerPartialMap k₀ (w.chargeTarget P)).domain := by
    simpa only [U, Path.centerStepPartialMap_domain] using inf_le_right
      (a := (w.centerPartialMap k₀ P).hom.opensRange)
  have hC := w.centerStepPartialMap_eq_restrict s P (K := k₀)
  obtain ⟨Q', M', R, hcharge', hpic, hact, hmodels, -⟩ :=
    Q.exists_mutated_presentation k (w.chargeTarget P) hform hcharge U hU hle M (by
      rw [← hC]
      exact hasNodalModel_stepSource Q models)
  refine ⟨Empty, Q', M', R.congrMaps hC.symm rfl, ?_, ?_,
    (congrMaps_picard _ _ _).trans hpic, ?_, ?_⟩
  · simpa only [Path.chargeTarget_cons, Step.chargeTarget_mutate_form] using hform
  · simpa only [s, Path.chargeTarget_cons, Path.chargeTarget_nil, Hom.toPath] using hcharge'
  · simpa only [congrMaps_boundaryAction, Generator.toStep_generator,
      Generator.inversionCount_mutate, pow_zero] using hact
  · refine (nodalModelsOn_congr Q' M' hC).mpr fun c ↦ ?_
    obtain ⟨_, _, _, hc⟩ := hmodels c
    exact hc

private theorem exists_permutation_step (w : Word B E) (P : ChargeSeed B N)
    (σ : Equiv.Perm (Fin r)) (Q : CompleteToricPresentation k₀ i b r L γ)
    (hform : (w.chargeTarget P).form = b.detDualEquiv.toLinearMap)
    (hcharge : (w.chargeTarget P).charge = rayChargeMap Q.rays)
    (M : Point Centers → MarkedSurface k₀ n H XTor)
    (models : NodalModelsOn Q M Cw[w,P]) :
    StepResult (i := i) b w ((Generator.permute σ).toStep E) P M := by
  let s := (Generator.permute σ).toStep E
  let U := (w.centerStepPartialMap k₀ s P).domain
  have hU := (w.centerStepPartialMap k₀ s P).dense_domain
  have hle : U ≤ (s.toPath.centerPartialMap k₀ (w.chargeTarget P)).domain := by
    simpa only [U, Path.centerStepPartialMap_domain] using inf_le_right
      (a := (w.centerPartialMap k₀ P).hom.opensRange)
  have hC := w.centerStepPartialMap_eq_restrict s P (K := k₀)
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  obtain ⟨R, hpic, hact, hmodels⟩ :=
    exists_permute_contracted σ (w.chargeTarget P) M hcharge hU hle
      (b := b) (hΦ := Q.regular) (T := Q.cycle) (o := Q.origin) (J := Q.inclusion) (by
        rw [← hC]
        intro c
        exact (Q.hasNodalModel_iff _ _).mp (hasNodalModel_stepSource Q models c))
  let Q' : CompleteToricPresentation k₀ i b r L γ := { Q with
    rays := Q.rays ∘ σ
    inclusion := (LinearMap.prodMap LinearMap.id
      (LinearEquiv.funCongrLeft ℤ ℤ σ).toLinearMap).comp Q.inclusion }
  let M' : Point Centers → MarkedSurface k₀ n H XTor :=
    fun y ↦ (M (y ≫ (s.toPath.centerIsoOver k₀).inv)).compEvaluation
      (Spec.map (CommRingCat.ofHom (TauCeti.LaurentRing.rename (R := k₀) σ.toFun).toRingHom))
  refine ⟨γ, Q', M', R.congrMaps hC.symm rfl, ?_, ?_,
    (congrMaps_picard _ _ _).trans hpic, ?_, ?_⟩
  · simpa only [Path.chargeTarget_cons, Step.chargeTarget_permute_form] using hform
  · rw [Path.chargeTarget_cons, Step.chargeTarget_permute_charge, hcharge]
    apply (Pi.basisFun ℤ (Fin r)).ext
    intro j
    have hj : LinearEquiv.funCongrLeft ℤ ℤ σ.symm (Pi.single j 1) = Pi.single (σ j) 1 := by
      funext a
      simpa only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp_apply,
        Equiv.symm_symm] using congrFun (Pi.single_comp_equiv σ.symm j (1 : ℤ)) a
    simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hj,
      rayChargeMap_single, Q', Function.comp_apply]
  · simpa only [congrMaps_boundaryAction, Generator.toStep_generator,
      Generator.inversionCount_permute, pow_zero] using hact
  · exact (nodalModelsOn_congr Q' M' hC).mpr fun c ↦
      (Q'.hasNodalModel_iff _ _).mpr (hmodels c)

private theorem exists_inversion_step (w : Word B E) (P : ChargeSeed B N)
    (Q : CompleteToricPresentation k₀ i b r L γ)
    (hform : (w.chargeTarget P).form = b.detDualEquiv.toLinearMap)
    (hcharge : (w.chargeTarget P).charge = rayChargeMap Q.rays)
    (M : Point Centers → MarkedSurface k₀ n H XTor)
    (models : NodalModelsOn Q M Cw[w,P]) :
    StepResult (i := i) (b.reindex frameSwap) w (Generator.invert.toStep E) P M := by
  let s := Generator.invert.toStep E
  let C := Cstep[w,s,P]
  let e := s.toPath.centerIsoOver k₀
  let M' : Point Centers → MarkedSurface k₀ n H XTor := fun y ↦ (M (y ≫ e.inv)).invert
  let C₀ := (s.toPath.centerIso k₀).hom.toPartialMap
  let : ((s.toPath.centerIso k₀).hom.toPartialMap).IsOver (Centers).hom (Centers).hom :=
    Hom.isOver_toPartialMap (s.toPath.centerIso_hom_structureMap k₀)
  let hle : C.domain ≤ C₀.domain := le_top
  let R := (invert E M).restrict C.domain C.dense_domain hle
  have hC : C₀.restrict C.domain C.dense_domain hle = C := by
    let U := s.toPath.centerOpen k₀ (w.chargeTarget P)
    have hU := s.toPath.dense_centerOpen (K := k₀) (w.chargeTarget P)
    have hstep : C.domain ≤ (s.toPath.centerPartialMap k₀ (w.chargeTarget P)).domain := by
      dsimp only [C]
      rw [Path.centerStepPartialMap_domain]
      exact inf_le_right
    have collapse (g : (scheme k₀ A).PartialMap (scheme k₀ A)) (hg : C.domain ≤ g.domain)
        (he : g = C₀.restrict U hU le_top) :
        g.restrict C.domain C.dense_domain hg = C₀.restrict C.domain C.dense_domain hle := by
      subst g
      exact PartialMap.restrict_restrict C₀ U hU le_top C.domain C.dense_domain hg
    exact (collapse _ hstep (Path.centerPartialMap_eq_restrict s.toPath _)).symm.trans
      (Path.centerStepPartialMap_eq_restrict w s P).symm
  let : IsDominant (C₀.restrict C.domain C.dense_domain hle).hom := hC.symm ▸
    inferInstanceAs (IsDominant (Cstep[w,s,P]).hom)
  refine ⟨γ, Q.invert, M', R.congrMaps hC rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Path.chargeTarget_cons, Step.chargeTarget_invert_form, hform]
    exact LinearMap.ext fun x ↦ (b.detDualEquiv_reindex_swap x).symm
  · rw [Path.chargeTarget_cons, Step.chargeTarget_invert_charge, hcharge]
    exact congrArg (rayChargeMap (Φ := Q.fan)) Q.invert_rays.symm
  · simp only [R, congrMaps_picard, restrict_picard, invert_picard]
  · simp only [R, congrMaps_boundaryAction, restrict_boundaryAction, invert_boundaryAction,
      Generator.toStep_generator, Generator.inversionCount_invert, pow_one]
  · intro c
    have hcenter : dst(C,c) ≫ e.inv = src(C,c) := by
      rw [Category.assoc]
      congr 1
      apply Over.OverMorphism.ext
      rw [Over.comp_left, domainTarget_left, domainSource_left, Path.centerStepPartialMap_hom]
      rw [← Path.centerIsoOver_hom_left, Category.assoc, ← Over.comp_left, Iso.hom_inv_id,
        Over.id_left]
      exact Category.comp_id _
    exact Q.hasNodalModel_invert E M (dst(C,c))
      (hcenter.symm ▸ hasNodalModel_stepSource Q models c)

private theorem exists_step (w : Word B E) (s : E ⟶ D) (P : ChargeSeed B N)
    (Q : CompleteToricPresentation k₀ i b r L γ)
    (hform : (w.chargeTarget P).form = b.detDualEquiv.toLinearMap)
    (hcharge : (w.chargeTarget P).charge = rayChargeMap Q.rays)
    (M : Point Centers → MarkedSurface k₀ n H XTor)
    (models : NodalModelsOn Q M Cw[w,P]) :
    StepResult (i := i) (b.reindex (frameSwap ^ (Step.generator s).inversionCount)) w s P M := by
  obtain ⟨g, rfl⟩ := s
  have he : (⟨g, rfl⟩ : E ⟶ g.target E) = g.toStep E :=
    Step.ext (Generator.toStep_generator g E).symm
  rw [he]
  cases g with
  | mutate k =>
    cases r with
    | zero => exact Fin.elim0 k
    | succ r =>
      simpa only [Generator.toStep_generator, Generator.inversionCount_mutate, pow_zero,
        Equiv.Perm.one_def, Basis.reindex_refl] using
        exists_mutation_step w P k Q hform hcharge M models
  | permute σ =>
    simpa only [Generator.toStep_generator, Generator.inversionCount_permute, pow_zero,
      Equiv.Perm.one_def, Basis.reindex_refl] using
      exists_permutation_step w P σ Q hform hcharge M models
  | invert =>
    simpa only [Generator.toStep_generator, Generator.inversionCount_invert, pow_one] using
      exists_inversion_step w P Q hform hcharge M models

/-- A signed word starting at a complete ordered toric presentation is realized on
its entire simultaneous noncollision open. The terminal presentation has the transported
charges in the frame obtained by swapping the two basis vectors at each inversion, and
its ordered nodal model exists at every reached center. In the transported markings the
Picard pullback is the identity, and each inversion reverses the numbered branches
around component zero. -/
theorem exists_realize_signed_word (w : Word B E) (P : ChargeSeed B N)
    (Q : CompleteToricPresentation k₀ i b r L γ)
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = rayChargeMap Q.rays)
    (M : Point Centers → MarkedSurface k₀ n H XTor)
    (models : ∀ c : CenterPoint (U := Centers) (V := Centers)
        ((Path.nil : Word B B).centerPartialMap k₀ P),
      let a := c ≫ ((Path.nil : Word B B).centerPartialMap k₀ P).domainTarget
        (X := Centers) (Y := Centers)
      Q.HasNodalModel a (M a)) :
    let b' := b.reindex (frameSwap ^ w.inversionCount)
    ∃ (γ' : Type) (Q' : CompleteToricPresentation k₀ i b' r L γ')
      (M' : Point Centers → MarkedSurface k₀ n H XTor)
      (R : GeometricRealization (T₀ := Centers) (T₁ := Centers) M M' Cw[w,P] (w.xRationalMap k₀)),
      (w.chargeTarget P).form = b'.detDualEquiv.toLinearMap ∧
      (w.chargeTarget P).charge = rayChargeMap Q'.rays ∧
      R.picard = .refl H ∧ R.boundaryAction = reflection ^ w.inversionCount ∧
      ∀ c : CenterPoint (U := Centers) (V := Centers) Cw[w,P],
        Q'.HasNodalModel (dst(Cw[w,P],c)) (M' (dst(Cw[w,P],c))) := by
  induction w with
  | nil =>
    let step : WordStepRealizations (L := fun _ ↦ AddCommGrpCat.of L)
        (form := fun _ ↦ H) P (fun _ ↦ M) (Path.nil : Word B B) :=
      fun {D D'} ↦ WordStepRealizations.nil (k := k₀) (n := n)
        (L := fun _ ↦ AddCommGrpCat.of L) (form := fun _ ↦ H) P (fun _ ↦ M) (D := D) (D' := D')
    let R := ofWord P Path.nil (@step)
    have hb : b.reindex (frameSwap ^ (Path.nil : Word B B).inversionCount) = b := by
      simp only [Path.inversionCount_nil, pow_zero, Equiv.Perm.one_def, Basis.reindex_refl]
    dsimp only
    rw [hb]
    exact ⟨γ, Q, M, R, by simpa only [Path.chargeTarget_nil] using hform,
      by simpa only [Path.chargeTarget_nil] using hcharge, ofWord_nil_picard P (@step),
      by simpa only [Path.inversionCount_nil, pow_zero] using ofWord_nil_boundaryAction P (@step),
      models⟩
  | @cons E D w s ih =>
    obtain ⟨γ₀, Q₀, M₀, R₀, hform₀, hcharge₀, hpic₀, hact₀, hmodels₀⟩ := ih
    obtain ⟨γ', Q', M', R', hform', hcharge', hpic', hact', hmodels'⟩ :=
      exists_step w s P Q₀ hform₀ hcharge₀ M₀ hmodels₀
    let C := (w.centerPartialMap k₀ P).comp (w.centerStepPartialMap k₀ s P)
    have hC : (w.cons s).centerPartialMap k₀ P = C := Path.centerPartialMap_cons w s P
    let : C.IsOver (Centers).hom (Centers).hom := hC ▸ inferInstanceAs
      (((w.cons s).centerPartialMap k₀ P).IsOver (Centers).hom (Centers).hom)
    let R := (R₀.comp R').congrMaps hC.symm
      (by rw [← Path.xRationalMap_comp, Path.comp_toPath_eq_cons])
    have hb : b.reindex (frameSwap ^ (w.cons s).inversionCount) =
        (b.reindex (frameSwap ^ w.inversionCount)).reindex
          (frameSwap ^ (Step.generator s).inversionCount) := by
      rw [Path.inversionCount_cons, Nat.add_comm w.inversionCount, pow_add, Equiv.Perm.mul_def]
      ext j
      simp only [Basis.reindex_apply, Equiv.symm_trans_apply]
    dsimp only
    rw [hb]
    refine ⟨γ', Q', M', R, hform', hcharge', ?_, ?_, hasNodalModel_appended Q' hmodels'⟩
    · simp only [R, congrMaps_picard, comp_picard, hpic₀, hpic']
      exact DFunLike.ext _ _ fun _ ↦ rfl
    · simp only [R, congrMaps_boundaryAction, comp_boundaryAction, hact₀, hact',
        Path.inversionCount_cons]
      rw [Nat.add_comm w.inversionCount, pow_add]

end GeometricRealization

end QPainleve.SignedClusterModularGroup
