/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseTraffic
import Vegas.Pending.PhaseProposalShadowSourceAcceptance
import Vegas.Pending.PhaseProposalShadowRejection
import Vegas.Pending.PhaseProposalShadowForeignBinding
import Interaction.ReactiveTrafficIdentity

/-! # Whole focal traffic under actual foreign binding inclusion

The original and comparison prefixes are genuine raw histories. Actual
candidate and checkpoint provenance supplies the handler's physical premises;
the existing private binding frame relates hidden results through normalization.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Raw initialized prefixes suffice for the exact accepting-or-rejecting
focal view law of any binding; no count-menu premise is required. -/
theorem phase_binding_handler_playerView (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (left right : (app).Control)
    (leftTrace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some left))
    (rightTrace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some right))
    {memory : BindingShadow graph} {hidden : Player}
    (frame : memory.PhaseStateFrame hidden left.execution.application right.execution.application)
    (owned : memory.OwnBindings hidden)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (supported : memory.CompletedAt right.execution.application.current.native.config)
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ left.execution.network.inputs)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (focal : Player) (different : focal ≠ hidden) :
    (left.execution.application.handle runtime message).map (fun state => state.playerView focal) =
      (right.execution.application.handle runtime message).map
        (fun state => state.playerView focal) := by
  have status := frame.binding_handler_isSome_eq owned runtime message event candidate call
  cases first : left.execution.application.handle runtime message with
  | none =>
    have second : right.execution.application.handle runtime message = none := by
      cases handled : right.execution.application.handle runtime message with
      | none => rfl
      | some state => simp only [first, handled, Option.isSome_none, Option.isSome_some,
          Bool.false_eq_true] at status
    rw [second]
  | some next =>
    have nativeAccepted : ∃ native, handle runtime left.execution.application.current.native
        ⟨message.id, .commitment event candidate⟩ = some native := by
      unfold PhaseRuntimeState.handle at first
      split at first
      · simp only [call, Option.map_eq_some_iff] at first
        obtain ⟨native, handled, _⟩ := first
        exact ⟨native, handled⟩
      · cases first
    obtain ⟨native, handled⟩ := nativeAccepted
    obtain ⟨_ready, _timely, actor, payload, binding, _code, _node, sender, candidateOwner,
        _vacant, _unused, _result⟩ :=
      (handle_commitment_iff runtime _ native message.id event candidate).mp handled
    by_cases acting : actor = hidden
    · have actualBinding : graph.outputLayout event = .binding hidden payload := by
        simpa only [acting] using binding
      obtain ⟨nextMemory, image, handled, nextOwned, _candidates, _valid, paired, _support,
          _refinement⟩ :=
        frame.repair_owned_binding_of_history runtime leaks plan inputs horizon scheduler left right
          leftTrace rightTrace owned valid supported message member event payload actualBinding
            candidate call next first
      rw [handled]
      exact congrArg some (paired.playerView_other nextOwned focal different)
    · have recalled := (app).history_inputRecall _ horizon scheduler leftTrace
      have output : message ∈ (app).outputs (left.execution.recall actor) := by
        rw [← recalled actor]
        exact List.mem_filter.mpr ⟨member, by simp only [Message.sender, sender, decide_true]⟩
      have signed := phaseOwnCommitmentsFixed_history runtime leaks _ horizon scheduler leftTrace
      have fixed : left.execution.application.current.native.candidates.lookup candidate ≠
          .fresh := by
        have candidateEq : candidate = (actor, candidate.2) := Prod.ext candidateOwner rfl
        rw [candidateEq]
        exact signed actor message output event candidate.2 (by rwa [← candidateEq])
      obtain ⟨nextMemory, image, handled, nextOwned, _candidates, paired, _support,
          _refinement⟩ := frame.repair_foreign_binding owned supported runtime actor acting event
        payload binding message candidate call fixed next first
      rw [handled]
      exact congrArg some (paired.playerView_other nextOwned focal different)

private theorem include_traffic_congr (left right : (app).Execution) (focal : Player)
    (same : phaseTraffic runtime leaks focal left = phaseTraffic runtime leaks focal right)
    (message : Message Player (CommitAttemptPacket graph))
    (found : left.network.lookup message.id = some message)
    (handler : (left.application.handle runtime message).map (fun state => state.playerView focal) =
      (right.application.handle runtime message).map (fun state => state.playerView focal)) :
    phaseTraffic runtime leaks focal (left.includePending (app) message.id) =
      phaseTraffic runtime leaks focal (right.includePending (app) message.id) := by
  have network : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.recall focal = right.recall focal :=
    congrArg (fun value => value.2.2.2.1) same
  have views : left.application.playerView focal = right.application.playerView focal :=
    congrArg (fun value => value.2.2.2.2) same
  have rightFound : right.network.lookup message.id = some message := by rw [← network]; exact found
  simp only [phaseTraffic, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending, rightFound, network, receipts, environments, recalled]
  have leftHandle : (app).handle left.application message =
      left.application.handle runtime message := rfl
  have rightHandle : (app).handle right.application message =
      right.application.handle runtime message := rfl
  rw [leftHandle, rightHandle]
  cases first : left.application.handle runtime message with
  | none =>
    cases second : right.application.handle runtime message with
    | none => simpa only [Option.getD_none, Option.isSome_none,
        MessageNetwork.includePending, rightFound] using
        congrArg (fun view => ((right.network.includePending message.id).2, right.receipts ++
          [(message.id, false)], right.environmentRecall, right.recall focal, view)) views
    | some state => simp [first, second] at handler
  | some state =>
    cases second : right.application.handle runtime message with
    | none => simp [first, second] at handler
    | some other =>
      simp only [first, second, Option.map_some] at handler
      have afterViews := Option.some.inj handler
      simpa only [Option.getD_some, Option.isSome_some,
        MessageNetwork.includePending, rightFound] using
        congrArg (fun view => ((right.network.includePending message.id).2, right.receipts ++
          [(message.id, true)], right.environmentRecall, right.recall focal, view)) afterViews

/-- Every actual raw foreign-binding inclusion preserves the whole focal
traffic under a compatible private frame, including the authentic receipt. -/
theorem phaseTraffic_include_binding_law (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (left right : (app).Control)
    (leftTrace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some left))
    (rightTrace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some right))
    {memory : BindingShadow graph} {hidden : Player}
    (frame : memory.PhaseStateFrame hidden left.execution.application right.execution.application)
    (owned : memory.OwnBindings hidden)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (supported : memory.CompletedAt right.execution.application.current.native.config)
    (focal : Player) (different : focal ≠ hidden)
    (same : phaseTraffic runtime leaks focal left.execution =
      phaseTraffic runtime leaks focal right.execution)
    (message : Message Player (CommitAttemptPacket graph))
    (found : left.execution.network.lookup message.id = some message)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate) :
    ((left.execution.environmentStep (app) (.include message.id)).map
      (phaseTraffic runtime leaks focal)) =
    ((right.execution.environmentStep (app) (.include message.id)).map
      (phaseTraffic runtime leaks focal)) := by
  have retained := (app).retained_envelopes_mem_inputs left.execution
    ((app).history_provenance _ horizon scheduler leftTrace)
    ((app).history_inputRecall _ horizon scheduler leftTrace)
  have coupled := include_traffic_congr runtime leaks left.execution right.execution focal same
    message found
    (phase_binding_handler_playerView runtime leaks plan inputs horizon scheduler left right
      leftTrace rightTrace frame owned valid supported message (retained.lookup _ _ found)
        event candidate call focal different)
  have network : left.execution.network = right.execution.network := congrArg Prod.fst same
  have receipts : left.execution.receipts = right.execution.receipts :=
    congrArg (fun value => value.2.1) same
  have environments : left.execution.environmentRecall = right.execution.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have before : left.execution.observeEnvironment (app) =
      right.execution.observeEnvironment (app) := by
    change (⟨left.execution.network.publicView, left.execution.application.publicView,
      left.execution.receipts⟩ : (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, frame.publicView owned]
    rfl
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  apply congrArg PMF.pure
  change ((left.execution.includePending (app) message.id).network,
    (left.execution.includePending (app) message.id).receipts,
    left.execution.environmentRecall ++
      [⟨left.execution.observeEnvironment (app), .include message.id⟩],
    (left.execution.includePending (app) message.id).recall focal,
    (left.execution.includePending (app) message.id).application.playerView focal) =
    ((right.execution.includePending (app) message.id).network,
    (right.execution.includePending (app) message.id).receipts,
    right.execution.environmentRecall ++
      [⟨right.execution.observeEnvironment (app), .include message.id⟩],
    (right.execution.includePending (app) message.id).recall focal,
    (right.execution.includePending (app) message.id).application.playerView focal)
  rw [before, environments]
  exact congrArg (fun value => (value.1, value.2.1,
    right.execution.environmentRecall ++
      [⟨right.execution.observeEnvironment (app), .include message.id⟩],
    value.2.2.2.1, value.2.2.2.2)) coupled

end Vegas.EventGraphRuntime
