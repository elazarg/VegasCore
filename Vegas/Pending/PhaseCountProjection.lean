/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCountVerdict
import Vegas.Pending.ReactiveOnePacketMenu

/-! # Actual local reconstruction of attempt-addressed signed envelopes -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Static installed-phase bounds, read from the actual public application view. -/
def allows (view : PhasePublicView graph) (call : Payload graph) : Bool :=
  match view.phase, call.event? graph with
  | some (_, low, high), some event => decide (low ≤ event.val ∧ event.val < high)
  | _, _ => false

/-- Public permanent exclusion masks every owned call independently of its value. -/
def excludedCall (view : PhasePublicView graph) (call : Payload graph) : Bool :=
  match call.event? graph with
  | none => false
  | some event => (graph.actor? event).any fun owner => decide (owner ∈ view.excluded)

/-- The signed token is masked before emission, rather than charged according
to an auditor's reconstruction of when it may have been emitted. -/
def maskPacket (view : PhasePublicView graph) (packet : WitnessedPacket graph) :
    WitnessedPacket graph :=
  let masked := if excludedCall view packet.call then { packet with token := none } else packet
  if allows view packet.call then masked else { masked with token := none }

omit [DecidableEq Player] in
theorem allows_publicView (state : PhaseRuntimeState graph) (call : Payload graph) :
    allows state.publicView call = state.allows call := by
  cases head : state.phases.head? <;> cases named : call.event? graph <;>
    simp only [allows, PhaseRuntimeState.publicView, PhaseRuntimeState.allows, head,
      named, Option.map_none, Option.map_some, RuntimePhase.mem_events]

theorem excludedCall_publicView (state : PhaseRuntimeState graph) (call : Payload graph) :
    excludedCall state.publicView call = state.current.excludedCall call := rfl

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Ordinary own recall fixes the next serial, all known signed evidence, the
post-preparation private candidate value, and the exact emitted attempt address. -/
def localEnvelope (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (material : (app).Submission) : Message Player (CommitAttemptPacket graph) :=
  ⟨(who, (app).submissionCount past),
    ⟨view.application.2.attempt, maskPacket view.application.2
      ⟨material.call.packet,
        material.evidence.resolve who
          (material.call.candidateAfter who view.application.1.candidates)
          ((ReactiveApplication.ResponseMenu.knownPackets past view).map nativeMessage),
        view.application.1.publicView.tokenFor material.call.packet⟩⟩⟩

/-- Submission changes neither the installed public descriptor nor the native
public state, although it may register fresh private preparation. -/
theorem submit_publicView (state : PhaseRuntimeState graph) (who : Player)
    (material : WitnessedSubmission graph) :
    (state.submit who material).publicView = state.publicView := by
  have native := (submitStep_publicView (material.call.register state.current.native who)
    who material.call.packet).trans (material.call.register_facts who state.current.native).2
  exact congrArg (fun view =>
    ({ state.publicView with native := view } : PhasePublicView graph)) native

/-- Exact materialization from one physical state, including the preparation
registered by the response and both public token masks. -/
theorem emit_after_submit (state : PhaseRuntimeState graph) (who : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (material : WitnessedSubmission graph) :
    (state.submit who material).emit who known material =
      ⟨state.attempt, maskPacket state.publicView
        ⟨material.call.packet,
          material.evidence.resolve who
            (material.call.candidateAfter who (state.current.native.playerView who).candidates)
            (known.map nativeMessage),
          state.current.native.publicView.tokenFor material.call.packet⟩⟩ := by
  let prepared : WitnessedPacket graph :=
    ⟨material.call.packet,
      material.evidence.resolve who
        (material.call.candidateAfter who (state.current.native.playerView who).candidates)
        (known.map nativeMessage),
      state.current.native.publicView.tokenFor material.call.packet⟩
  have nativePublic : (state.submit who material).current.native.publicView =
      state.current.native.publicView :=
    congrArg PhasePublicView.native (submit_publicView state who material)
  have candidates : (fun slot =>
      (state.submit who material).current.native.candidates.lookup (who, slot)) =
      material.call.candidateAfter who (state.current.native.playerView who).candidates := by
    funext slot
    exact material.call.candidateAfter_eq who state.current.native slot
  have nativeEmit : material.emit (state.submit who material).current.native who
      (known.map nativeMessage) = prepared := by
    rw [WitnessedSubmission.emit_eq_resolve, candidates, nativePublic]
  change (let packet := material.emit (state.submit who material).current.native who
              (known.map nativeMessage)
          let masked := if state.current.excludedCall packet.call then
              { packet with token := none } else packet
          (⟨state.attempt,
            if state.allows masked.call then masked else { masked with token := none }⟩ :
            CommitAttemptPacket graph)) = ⟨state.attempt, maskPacket state.publicView prepared⟩
  rw [nativeEmit]
  change (⟨state.attempt,
    if state.allows (if state.current.excludedCall prepared.call then
        { prepared with token := none } else prepared).call then
      (if state.current.excludedCall prepared.call then { prepared with token := none }
        else prepared)
    else { (if state.current.excludedCall prepared.call then { prepared with token := none }
        else prepared) with token := none }⟩ : CommitAttemptPacket graph) =
    ⟨state.attempt, maskPacket state.publicView prepared⟩
  unfold maskPacket
  rw [allows_publicView, excludedCall_publicView]
  cases excluded : state.current.excludedCall prepared.call <;>
    cases allowed : state.allows prepared.call <;>
      simp_all only [Bool.false_eq_true, ↓reduceIte]

/-- The local envelope is EXACTLY the envelope appended by an actual response. -/
theorem localEnvelope_eq_of_recall (execution : (app).Execution)
    (input : execution.InputRecall (app)) (serial : execution.SerialRecall (app))
    (who : Player) (material : (app).Submission) :
    localEnvelope runtime leaks who (execution.recall who) (execution.observe (app) who) material =
      ⟨(who, execution.network.nextSerial who), (app).packet
        ((app).submit execution.application who material) who (execution.network.known who)
        material⟩ := by
  have known : ReactiveApplication.ResponseMenu.knownPackets (execution.recall who)
      (execution.observe (app) who) = execution.network.known who :=
    ((app).known_from_recall execution who input).symm
  unfold localEnvelope
  change Message.mk (who, (app).submissionCount (execution.recall who)) _ = _
  rw [← serial who, known]
  apply congrArg (Message.mk (who, execution.network.nextSerial who))
  exact (emit_after_submit execution.application who (execution.network.known who) material).symm

end Vegas.EventGraphRuntime.PhaseCount
