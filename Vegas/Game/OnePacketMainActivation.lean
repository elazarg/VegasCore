/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketClearRegularity
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Source-main first-activation conditions on actual counted traces -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

/-- A foreign response at a first activation uses source-main support. No
condition is imposed on focal responses, scheduler moves, or later activations. -/
def MainActivationStep (source : setup.intendedModel.BehavioralAssessment) (focal : Player) :
    (application setup runtime leaks).ProtocolState →
      (Player → Option (application setup runtime leaks).Action) → Prop
  | none, _ => True
  | some before, joint => ∀ owner, before.actor = some owner → owner ≠ focal →
      FirstActivation setup runtime leaks owner (some (before.execution.recall owner,
        before.execution.observe (application setup runtime leaks) owner)) →
      responseChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler owner
        (some (before.execution.recall owner,
          before.execution.observe (application setup runtime leaks) owner))
        ((joint owner).getD ⟨none⟩) ∈
        (honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler source owner
          (some (before.execution.recall owner,
            before.execution.observe (application setup runtime leaks) owner))).support

/-- Every foreign first activation at or beyond a specified trace length uses
source-main support. Earlier play is retained without imposing this condition. -/
def MainActivationTraceAfter (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    (cutoff : Nat) :
    ∀ {state}, (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state → Prop
  | _, .start => True
  | _, .extend (source := before) prior joint _ _ =>
      MainActivationTraceAfter source focal cutoff prior ∧
        (cutoff ≤ prior.length → MainActivationStep setup runtime leaks bounds horizon scheduler
          source
          focal before joint)

variable {setup runtime leaks bounds horizon scheduler}

/-- No response in a trace precedes a boundary at least its own length. -/
theorem mainActivationTraceAfter_of_length_le
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    {state : (onePacketProtocol setup runtime leaks bounds horizon scheduler).State}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state)
    (cutoff : Nat) (length : trace.length ≤ cutoff) :
    MainActivationTraceAfter setup runtime leaks bounds horizon scheduler source focal cutoff
      trace := by
  induction trace with
  | start => trivial
  | extend prior joint legal realized ih =>
      refine ⟨ih (Nat.le_trans (Nat.le_succ prior.length) length), ?_⟩
      intro later
      simp only [Trace.length] at length
      omega

/-- The future-main condition at an actual endpoint holds at every prefix. -/
theorem mainActivationTraceAfter_of_tracePrefix
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player) (cutoff : Nat)
    {first final : (onePacketProtocol setup runtime leaks bounds horizon scheduler).State}
    {prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace first}
    {top : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace final}
    (isPrefix : TracePrefix prior top)
    (main : MainActivationTraceAfter setup runtime leaks bounds horizon scheduler source focal
      cutoff top) :
    MainActivationTraceAfter setup runtime leaks bounds horizon scheduler source focal cutoff
      prior := by
  induction isPrefix with
  | refl => exact main
  | extend _ _ _ _ ih => exact ih main.1

/-- The future-main condition reads back the actual supported response step at
any prefix whose source is beyond the comparison boundary. -/
theorem mainActivationStep_of_tracePrefix
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player) (cutoff : Nat)
    {first final : (onePacketProtocol setup runtime leaks bounds horizon scheduler).State}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace first)
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal first joint)
    {next : (onePacketProtocol setup runtime leaks bounds horizon scheduler).State}
    (realized : next ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step first
      ⟨joint, legal⟩).support)
    {top : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace final}
    (isPrefix : TracePrefix (prior.extend joint legal realized) top)
    (main : MainActivationTraceAfter setup runtime leaks bounds horizon scheduler source focal
      cutoff top)
    (later : cutoff ≤ prior.length) :
    MainActivationStep setup runtime leaks bounds horizon scheduler source focal first joint :=
  (mainActivationTraceAfter_of_tracePrefix (runtime := runtime) source focal cutoff isPrefix
    main).2 later

end Vegas
