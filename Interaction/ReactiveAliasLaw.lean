/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAliasStrategy
import GameTheoryExtensions.Protocol.HistoryProjection

/-! # Exact history laws for response normalization

Any raw profile whose local choice laws project to a normalized profile has
the same projected canonical-history law. This applies to the common alias
perturbations and to selectors used to analyze one decision information fiber.
-/

noncomputable section

namespace Interaction.ReactiveApplication.SubmissionNormalization

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (normal : app.SubmissionNormalization) (raw : app.ResponseMenu)
  (stable : ∀ who past view,
    raw.actions who (normal.recall who past) view = raw.actions who past view)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

def optionChoice (who : Principal) (observed : app.Info) (chosen : Option app.Action) :
    Option app.Action :=
  match observed with
  | none => chosen
  | some data => chosen.map (normal.action who data.1 data.2)

theorem choice_val (who : Principal) (observed : app.Info)
    (chosen : (raw.information initial horizon scheduler).Choice who observed) :
    (normal.choice raw stable initial horizon scheduler who observed chosen).1 =
      normal.optionChoice who observed chosen.1 := by
  cases observed <;> rfl

theorem choice_val_joint (before : app.ProtocolState) (who : Principal)
    (chosen : (raw.information initial horizon scheduler).Choice who (app.observe who before)) :
    (normal.choice raw stable initial horizon scheduler who (app.observe who before) chosen).1 =
      normal.joint before (fun _ => chosen.1) who := by
  rw [normal.choice_val]
  cases before with
  | none => rfl
  | some control =>
      by_cases active : control.actor = some who
      · simp only [optionChoice, observe, active, ↓reduceIte]
        rfl
      · have chosenNone : chosen.1 = none := by
          have member := chosen.2
          simpa only [observe, active, ↓reduceIte, ResponseMenu.information,
            Set.mem_singleton_iff] using member
        simp only [optionChoice, observe, active, ↓reduceIte, chosenNone, joint, Option.map_none]

variable (native : ∀ who, (raw.information initial horizon scheduler).BehavioralPolicy who)
  (source : ∀ who, ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
  (projects : ∀ who observed, (native who observed).map
    (normal.choice raw stable initial horizon scheduler who observed) =
      source who (normal.info who observed))

include projects in
theorem joint_marginal_projection {before}
    (prior : (raw.protocol initial horizon scheduler).Trace before) (who : Principal) :
    (((native who ((raw.information initial horizon scheduler).infoOf who prior)).map
      Subtype.val).map (fun action => normal.joint before (fun _ => action) who)) =
      (source who (((normal.menu raw).information initial horizon scheduler).infoOf who
        (normal.trace raw stable initial horizon scheduler prior))).map Subtype.val := by
  let nativeOptions (observed : app.Info) := (native who observed).map Subtype.val
  let sourceOptions (observed : app.Info) := (source who observed).map Subtype.val
  change (nativeOptions ((raw.signals initial horizon scheduler).infoOf who prior)).map _ =
    sourceOptions (((normal.menu raw).signals initial horizon scheduler).infoOf who _)
  rw [raw.info, ResponseMenu.info]
  dsimp only [nativeOptions, sourceOptions]
  calc
    _ = (native who (app.observe who before)).map (fun chosen =>
        (normal.choice raw stable initial horizon scheduler who (app.observe who before)
          chosen).1) := by
      rw [FinDist.map_comp]
      congr 1
      funext chosen
      exact (normal.choice_val_joint raw stable initial horizon scheduler before who chosen).symm
    _ = ((native who (app.observe who before)).map
        (normal.choice raw stable initial horizon scheduler who (app.observe who before))).map
          Subtype.val := (FinDist.map_comp ..).symm
    _ = (source who (normal.info who (app.observe who before))).map Subtype.val := by
      rw [projects]
    _ = _ := congrArg (fun observed => (source who observed).map Subtype.val)
      (normal.state_observe before who).symm

def legalJoint (before : app.ProtocolState)
    (choices : {choices // (raw.protocol initial horizon scheduler).Legal before choices}) :
    {choices // ((normal.menu raw).protocol initial horizon scheduler).Legal
      (normal.state before) choices} :=
  ⟨normal.joint before choices.1,
    normal.legal_joint raw stable initial horizon scheduler before choices.1 choices.2⟩

variable [Fintype Principal]

include projects in
theorem behavioralJoint_projection {before}
    (prior : (raw.protocol initial horizon scheduler).Trace before)
    (running : ¬ (raw.protocol initial horizon scheduler).terminal before) :
    ((raw.information initial horizon scheduler).behavioralJoint native prior running).map
        (normal.legalJoint raw stable initial horizon scheduler before) =
      ((normal.menu raw).information initial horizon scheduler).behavioralJoint source
        (normal.trace raw stable initial horizon scheduler prior)
        ((normal.state_terminal before).not.mpr running) := by
  apply FinDist.map_injective Subtype.val_injective
  rw [FinDist.map_comp, InformationModel.behavioralJoint_map_val]
  change (((raw.information initial horizon scheduler).behavioralJoint native prior running).map
      (fun choices => normal.joint before choices.1)) = _
  calc
    _ = (((raw.information initial horizon scheduler).behavioralJoint native prior running).map
        Subtype.val).map (normal.joint before) := (FinDist.map_comp ..).symm
    _ = (FinDist.pi fun who =>
        (native who ((raw.information initial horizon scheduler).infoOf who prior)).map
          Subtype.val).map (normal.joint before) := by
      rw [InformationModel.behavioralJoint_map_val]
    _ = FinDist.pi (fun who =>
        ((native who ((raw.information initial horizon scheduler).infoOf who prior)).map
          Subtype.val).map (fun action => normal.joint before (fun _ => action) who)) := by
      conv_rhs => rw [FinDist.pi_map]
      congr 1
      funext choices who
      cases before <;> rfl
    _ = _ := congrArg FinDist.pi (funext fun who =>
      normal.joint_marginal_projection raw stable initial horizon scheduler native source
        projects prior who)

omit [Fintype Principal] in
theorem extension_projection
    (current : (raw.protocol initial horizon scheduler).History)
    (choices : {choices // (raw.protocol initial horizon scheduler).Legal current.state choices}) :
    (((raw.protocol initial horizon scheduler).step current.state choices).bindOnSupport
      (fun _next realized => FinDist.pure (current.extend choices.2 realized))).map
        (normal.history raw stable initial horizon scheduler) =
      (((normal.menu raw).protocol initial horizon scheduler).step (normal.state current.state)
        (normal.legalJoint raw stable initial horizon scheduler
          current.state choices)).bindOnSupport
          (fun _next realized => FinDist.pure
            ((normal.history raw stable initial horizon scheduler current).extend
              (normal.legalJoint raw stable initial horizon scheduler current.state choices).2
              realized)) := by
  have valid := app.history_inputRecall initial horizon scheduler
    (raw.toRawTrace initial horizon scheduler current.trace)
  have law := normal.state_transition initial horizon scheduler current.state choices.1 valid
  let mapped := normal.legalJoint raw stable initial horizon scheduler current.state choices
  let continuation (next : app.ProtocolState)
      (realized : next ∈ ((app.transition initial horizon scheduler current.state choices.1).map
        normal.state).support) :=
    FinDist.pure ((normal.history raw stable initial horizon scheduler current).extend mapped.2
      (by rw [law] at realized; exact realized))
  rw [FinDist.map_bindOnSupport]
  simp only [FinDist.map_pure]
  calc
    _ = ((app.transition initial horizon scheduler current.state choices.1).map
        normal.state).bindOnSupport continuation := by
      rw [FinDist.bindOnSupport_map]
      apply FinDist.bindOnSupport_congr
      intro next realized
      rfl
    _ = _ := FinDist.bindOnSupport_congr_law law _ _ (fun _ _ _ => rfl)

include projects in
theorem oneStep_projection (current : (raw.protocol initial horizon scheduler).History) :
    ((raw.information initial horizon scheduler).runBehavioralFrom native 1 current).map
        (normal.history raw stable initial horizon scheduler) =
      ((normal.menu raw).information initial horizon scheduler).runBehavioralFrom source 1
        (normal.history raw stable initial horizon scheduler current) := by
  by_cases stopped : (raw.protocol initial horizon scheduler).terminal current.state
  · rw [(raw.information initial horizon scheduler).runBehavioralFrom_of_terminal native 1 stopped,
      ((normal.menu raw).information initial horizon scheduler).runBehavioralFrom_of_terminal
        (h := normal.history raw stable initial horizon scheduler current) source 1
        ((normal.state_terminal current.state).mpr stopped), FinDist.map_pure]
  · rw [(raw.information initial horizon scheduler).runBehavioralFrom_succ_of_not_terminal
      native 0 stopped,
      InformationModel.runBehavioralFrom_succ_of_not_terminal
        ((normal.menu raw).information initial horizon scheduler)
        (h := normal.history raw stable initial horizon scheduler current) source 0
        ((normal.state_terminal current.state).not.mpr stopped), FinDist.map_bind]
    let continuation (choices : {choices //
        ((normal.menu raw).protocol initial horizon scheduler).Legal
          (normal.state current.state) choices}) :=
      (((normal.menu raw).protocol initial horizon scheduler).step
        (normal.state current.state) choices).bindOnSupport fun _next realized =>
          FinDist.pure ((normal.history raw stable initial horizon scheduler current).extend
            choices.2 realized)
    calc
      _ = ((raw.information initial horizon scheduler).behavioralJoint native current.trace
          stopped).bind (fun choices => continuation
            (normal.legalJoint raw stable initial horizon scheduler current.state choices)) := by
        apply FinDist.bind_congr
        intro choices _
        exact normal.extension_projection raw stable initial horizon scheduler current choices
      _ = (((raw.information initial horizon scheduler).behavioralJoint native current.trace
          stopped).map (normal.legalJoint raw stable initial horizon scheduler current.state)).bind
            continuation := (FinDist.bind_map ..).symm
      _ = _ := by
        rw [normal.behavioralJoint_projection raw stable initial horizon scheduler
          native source projects current.trace stopped]
        rfl

include projects in
/-- Exact projection of every finite canonical-history continuation, from
arbitrary legal starting histories and under arbitrary projecting profiles. -/
theorem runBehavioral_projection (fuel : Nat)
    (current : (raw.protocol initial horizon scheduler).History) :
    ((raw.information initial horizon scheduler).runBehavioralFrom native fuel current).map
        (normal.history raw stable initial horizon scheduler) =
      ((normal.menu raw).information initial horizon scheduler).runBehavioralFrom source fuel
        (normal.history raw stable initial horizon scheduler current) := by
  apply ExecutionProtocol.runRandomizedFor_map_of_oneStep
  exact normal.oneStep_projection raw stable initial horizon scheduler native source projects

end Interaction.ReactiveApplication.SubmissionNormalization
