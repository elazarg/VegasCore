/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingSampleReplay
import Vegas.Pending.PhaseClearHistory
import Interaction.ReactiveEnvironmentMass

/-! # Actual clear sample atoms under directed physical repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired after image : (phaseApplication runtime leaks).Execution}

local notation "app" => phaseApplication runtime leaks

/-- The actual public sample value survives clear phase installation, so
paired supported sample outcomes have equal real conditional command atoms. -/
theorem sample_apply (frame : Frame runtime leaks memory owner original repaired)
    (afterFrame : Frame runtime leaks memory owner after image)
    (event : graph.EventId) (ready : original.application.current.native.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (node : nodeView graph event = .sample payload law outputEq codeEq)
    (allowed : original.application.commandAllowed (.executeSample event) = true)
    (leftMoved : after ∈ (original.environmentStep (app)
      (.application (.executeSample event))).support)
    (rightMoved : image ∈ (repaired.environmentStep (app)
      (.application (.executeSample event))).support) :
    (original.environmentStep (app) (.application (.executeSample event))) after =
      (repaired.environmentStep (app) (.application (.executeSample event))) image := by
  have beforePublic : original.application.current.native.publicView =
      repaired.application.current.native.publicView := frame.live.publicView
  have rightReady : repaired.application.current.native.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← beforePublic, State.publicView_eventReady]
    exact ready
  have rightAllowed : repaired.application.commandAllowed (.executeSample event) = true := by
    change (repaired.application.phases.head?.any _) = true
    rw [← frame.phases]
    exact allowed
  have available : (law.eval? original.application.current.native.config.store).isSome := by
    apply law.eval?_isSome
    intro field member
    apply original.application.current.native.config.read_available ready
    rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
    exact member
  let draw := (law.eval? original.application.current.native.config.store).get available
  have leftDraw : law.eval? original.application.current.native.config.store = some draw :=
    (Option.some_get _).symm
  have rightDraw : law.eval? repaired.application.current.native.config.store = some draw := by
    rw [← law.eval?_publicStore repaired.application.current.native.config.store,
      ← show graph.publicStore original.application.current.native.config.store =
          graph.publicStore repaired.application.current.native.config.store from
        congrArg (fun view : PublicView graph => view.observation.store) beforePublic,
      law.eval?_publicStore original.application.current.native.config.store]
    exact leftDraw
  let next (physical : (app).Execution)
      (ready : physical.application.current.native.config.cut.Ready event)
      (value : L.Val payload) :=
    PhaseRuntimeState.normalizeExecution runtime leaks
      (rawSample runtime leaks physical event payload outputEq ready value)
  have output (physical : (app).Execution)
      (ready : physical.application.current.native.config.cut.Ready event)
      (clear : physical.application.current.excluded = ∅) (value : L.Val payload) :
      (next physical ready value).application.current.native.config.outputs event =
        some (cast (congrArg EventField.Value outputEq.symm) value) := by
    let raw := rawSample runtime leaks physical event payload outputEq ready value
    have kept : (next physical ready value).application.current = raw.application.current :=
      (PhaseRuntimeState.settle_of_clear raw.application.phases raw.application.generation
        raw.application.entry raw.application.current raw.application.retired clear).1
    rw [kept]
    exact Config.complete_output_same _ _ _ _ _
  have injective (physical : (app).Execution)
      (ready : physical.application.current.native.config.cut.Ready event)
      (clear : physical.application.current.excluded = ∅) :
      Function.Injective (next physical ready) := by
    intro first second same
    have stored := congrArg (fun execution : (app).Execution =>
      execution.application.current.native.config.outputs event) same
    rw [output physical ready clear first, output physical ready clear second] at stored
    exact (cast_inj _).mp (Option.some.inj stored)
  have leftLaw := sample_environment_law runtime leaks original event ready payload law outputEq
    codeEq node allowed draw leftDraw
  have rightLaw := sample_environment_law runtime leaks repaired event rightReady payload law
    outputEq codeEq node rightAllowed draw rightDraw
  change original.environmentStep (app) (.application (.executeSample event)) =
    draw.map (next original ready) at leftLaw
  change repaired.environmentStep (app) (.application (.executeSample event)) =
    draw.map (next repaired rightReady) at rightLaw
  rw [leftLaw, PMF.support_map] at leftMoved
  obtain ⟨leftValue, _leftSupported, rfl⟩ := leftMoved
  rw [rightLaw, PMF.support_map] at rightMoved
  obtain ⟨rightValue, _rightSupported, rfl⟩ := rightMoved
  have sameValue : leftValue = rightValue := by
    have afterPublic : graph.publicStore
        (next original ready leftValue).application.current.native.config.store =
        graph.publicStore
          (next repaired rightReady rightValue).application.current.native.config.store :=
      congrArg (fun view : PublicView graph => view.observation.store) afterFrame.live.publicView
    have stored := congrFun afterPublic (.inr event)
    have visible : graph.fieldPublic (.inr event) := by
      change (graph.outputLayout event).IsPublic
      rw [outputEq]
      trivial
    rw [publicStore_of_public _ _ _ visible, publicStore_of_public _ _ _ visible] at stored
    simp only [Config.store_output] at stored
    rw [output original ready frame.clearOriginal leftValue,
      output repaired rightReady frame.clearRepaired rightValue] at stored
    exact (cast_inj _).mp (Option.some.inj stored)
  subst rightValue
  rw [leftLaw, rightLaw,
    pmf_map_apply_of_injective _ (injective original ready frame.clearOriginal),
    pmf_map_apply_of_injective _ (injective repaired rightReady frame.clearRepaired)]

/-- The same selected scheduler atom multiplies the exact clear sample mass,
so the full actual protocol transition atoms agree. -/
theorem sample_transition_apply (frame : Frame runtime leaks memory owner original repaired)
    (afterFrame : Frame runtime leaks memory owner after image)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat)
    (event : graph.EventId) (ready : original.application.current.native.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (node : nodeView graph event = .sample payload law outputEq codeEq)
    (allowed : original.application.commandAllowed (.executeSample event) = true)
    (leftMoved : after ∈ (original.environmentStep (app)
      (.application (.executeSample event))).support)
    (rightMoved : image ∈ (repaired.environmentStep (app)
      (.application (.executeSample event))).support)
    (firstJoint secondJoint : Player → Option (app).Action) :
    ((app).transition initial horizon scheduler (some ⟨remaining + 1, none, original⟩) firstJoint)
        (some ⟨remaining, none, after⟩) =
      ((app).transition initial horizon scheduler
        (some ⟨remaining + 1, none, repaired⟩) secondJoint)
        (some ⟨remaining, none, image⟩) := by
  have firstMass := (app).transition_environment_apply initial horizon scheduler remaining original
    after (.application (.executeSample event)) leftMoved firstJoint
  have secondMass := (app).transition_environment_apply initial horizon scheduler remaining repaired
    image (.application (.executeSample event)) rightMoved secondJoint
  simp only [ReactiveApplication.Command.actor?] at firstMass secondMass
  rw [firstMass, secondMass, frame.scheduler_law scheduler,
    frame.sample_apply afterFrame event ready payload law outputEq codeEq node allowed leftMoved
      rightMoved]

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
