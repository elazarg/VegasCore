/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketForcedBeliefs
import Vegas.Game.IntendedPreservation

/-! # Projecting native one-packet histories to intended histories

**Decoded points.** A native configuration of the default runtime is a prefix
of its completion order of at most one length; the source state it decodes to
at that length is its *decoded point* (`Vegas.decodedPoint`). At every
configuration with a source residual it is the residual's point
(`Vegas.decodedPoint_eq`), and completing the ready event moves it by the
source step of the decoded action (`Vegas.decodedPoint_step`).

**The acting joint.** A source step reads only the acting player's choice
(`Vegas.SourceProgram.ProtocolState.step_actingJoint`), so the decoded action
of a completion is the joint action that gives it to the acting player and
nothing to the others (`Vegas.actingJoint`).

**The intended history of a native history.** Replaying a native history,
the initial draw becomes the intended initial draw, a native step that
completes no event is skipped, and a native step that completes one event
becomes the intended step of its decoded action to the decoded point of the
new configuration, when that step is legal in the intended game
(`Vegas.intendedHistory?`). The replay fails exactly where a step is not legal
in the intended game, such as at a bad binding. Whenever it succeeds, the
intended history ends at the decoded point of the native state
(`Vegas.intendedHistory?_state`), so at a decision site of the observer it lies
at the intended site of the projected view
(`Vegas.intendedHistory?_infoOf`).
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **A source step reads only the acting player's choice.** Stepping with one
choice for every player is stepping with that choice for the acting player and
nothing for the others. -/
theorem step_actingJoint : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    (choice : Option (OwnAction Player L)) →
    step program state (fun _ => choice) =
      step program state (fun who =>
        if ProtocolView.actor who program (observe who program state) = some who then choice
        else none)
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, state, choice => by
      cases state with
      | inl config => rfl
      | inr rest =>
          simp only [step, Sum.elim_inr, observe, ProtocolView.actor]
          rw [step_actingJoint next rest choice]
  | _, _, .commit _ _ _ _ next, state, choice => by
      cases state with
      | inl config => simp [step, observe, ProtocolView.actor]
      | inr rest =>
          simp only [step, Sum.elim_inr, observe, ProtocolView.actor]
          rw [step_actingJoint next rest choice]
  | _, _, .reveal _ _ _ _ _ _ next, state, choice => by
      cases state with
      | inl config => simp [step, observe, ProtocolView.actor]
      | inr rest =>
          simp only [step, Sum.elim_inr, observe, ProtocolView.actor]
          rw [step_actingJoint next rest choice]

end Vegas.SourceProgram.ProtocolState

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

section Decoding

open Classical in
/-- **The decoded point** of a native configuration: the source state it decodes
to at the length of its completed prefix, and the state before setup if it is
not a prefix. -/
def decodedPoint (config : (graph setup).Config) : setup.ProtocolState :=
  if ordered : ∃ rank, config.cut.IsPrefix rank then
    sourceServicePrefix? setup ordered.choose config
  else none

variable {setup}

/-- At a configuration with a source residual, the decoded point is the
residual's point. -/
theorem decodedPoint_eq {profile : BehavioralProfile setup.program} {rank : Nat}
    {config : (graph setup).Config} (residual : SourceResidual setup profile rank config) :
    decodedPoint setup config =
      some (residual.lift (ProtocolState.entry residual.program residual.source)) := by
  have ordered : ∃ rank, config.cut.IsPrefix rank := ⟨rank, residual.checkpoint.ordered⟩
  unfold decodedPoint
  rw [dite_eq_left_of_eq_true (eq_true ordered), show ordered.choose = rank from
    isPrefix_unique ordered.choose_spec residual.checkpoint.ordered]
  exact residual.decode

/-- **Completing the ready event moves the decoded point by one source step.**
At a configuration with a source residual, completing the ready event with an
action reaches a configuration whose decoded point is in the support of the
source step of the decoded action from the previous decoded point. -/
theorem decodedPoint_step {profile : BehavioralProfile setup.program} {rank : Nat}
    {before : (graph setup).Config} (residual : SourceResidual setup profile rank before)
    (event : (graph setup).EventId) (ready : before.cut.Ready event)
    (action : (graph setup).Action event) (after : (graph setup).Config)
    (member : after ∈ (before.step event ready action).support) :
    ∃ point next, decodedPoint setup before = some point ∧
      decodedPoint setup after = some next ∧
      next ∈ (ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action)).support := by
  obtain ⟨next, reached⟩ := residual.step event ready action after member
  exact ⟨_, _, decodedPoint_eq residual, decodedPoint_eq next, reached⟩

end Decoding

section Joint

/-- **The acting joint** of a source choice at a setup state: the choice for the
acting player and nothing for the others; nothing for anybody before setup. -/
def actingJoint : setup.ProtocolState → Option (OwnAction Player L) →
    Player → Option (OwnAction Player L)
  | none, _ => fun _ => none
  | some point, choice => fun who =>
      if ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) =
          some who then choice
      else none

/-- The setup step with the acting joint of a choice is the source step with
that choice for everybody. -/
theorem protocolStep_actingJoint (point : ProtocolState setup.program)
    (choice : Option (OwnAction Player L)) :
    setup.protocolStep (some point) (actingJoint setup (some point) choice) =
      (ProtocolState.step setup.program point (fun _ => choice)).map some := by
  rw [ProtocolState.step_actingJoint]
  rfl

end Joint

section Replay

variable [Fintype Player] (leaks : MessageNetwork.ObservationRule Player
    (WitnessedPacket (graph setup))) (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

open Classical in
/-- Extend an intended history by the acting joint of a choice to a target
state, when that step is legal and reaches the target. -/
def extendIntended? (history : setup.intendedProtocol.History)
    (choice : Option (OwnAction Player L)) (target : setup.ProtocolState) :
    Option setup.intendedProtocol.History :=
  if legal : setup.intendedProtocol.Legal history.state
      (actingJoint setup history.state choice) then
    if reached : target ∈ (setup.intendedProtocol.step history.state
        ⟨actingJoint setup history.state choice, legal⟩).support then
      some ⟨target, history.trace.extend _ legal reached⟩
    else none
  else none

/-- The intended state of a native protocol state: the decoded point of its
configuration, and the state before setup before initialization. -/
def nativeDecodedState : (application setup leaks).ProtocolState → setup.ProtocolState
  | none => none
  | some control => decodedPoint setup control.execution.application.config

/-- Advance an intended history along one native transition: the initial
draw to the decoded initial point; no step when no event completes; the step of
the decoded action when one event completes; failure otherwise. -/
def advanceIntended? (history : setup.intendedProtocol.History) :
    (application setup leaks).ProtocolState → (application setup leaks).ProtocolState →
      Option setup.intendedProtocol.History
  | none, some after => extendIntended? setup history none
      (decodedPoint setup after.execution.application.config)
  | some before, some after =>
      match after.execution.application.config.history.drop
          before.execution.application.config.history.length with
      | [] => some history
      | [⟨event, action⟩] => extendIntended? setup history
          (decodeEventAction setup.program event action)
          (decodedPoint setup after.execution.application.config)
      | _ => none
  | _, none => none

/-- **The intended history of a native history**, when every completion along
it is a legal intended step. -/
def intendedHistory? : ∀ {state},
    (onePacketProtocol setup leaks bounds horizon scheduler).Trace state →
      Option setup.intendedProtocol.History
  | _, .start => some setup.intendedProtocol.initHistory
  | _, .extend (source := before) (target := after) prior _ _ _ =>
      (intendedHistory? prior).bind fun history =>
        advanceIntended? setup leaks history before after

variable {setup leaks bounds horizon scheduler}

omit [Fintype Player] in
theorem extendIntended?_state {history : setup.intendedProtocol.History}
    {choice : Option (OwnAction Player L)} {target : setup.ProtocolState}
    {result : setup.intendedProtocol.History}
    (extended : extendIntended? setup history choice target = some result) :
    result.state = target := by
  unfold extendIntended? at extended
  split at extended
  · split at extended
    · cases extended
      rfl
    · cases extended
  · cases extended

/-- **The replay ends at the decoded point.** Whenever the intended history of
a native history exists, its state is the decoded point of the native state. -/
theorem intendedHistory?_state : ∀ {state}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    {history : setup.intendedProtocol.History},
    intendedHistory? setup leaks bounds horizon scheduler trace = some history →
      history.state = nativeDecodedState setup leaks state
  | _, .start, history, replayed => by
      cases replayed
      rfl
  | _, .extend (source := before) (target := after) prior joint legal realized, history,
      replayed => by
      obtain ⟨previous, previousReplay, advanced⟩ := Option.bind_eq_some_iff.mp replayed
      have previousState := intendedHistory?_state prior previousReplay
      cases before with
      | none =>
          cases after with
          | none => cases advanced
          | some after => exact extendIntended?_state advanced
      | some before =>
          cases after with
          | none => cases advanced
          | some after =>
              change (match after.execution.application.config.history.drop
                  before.execution.application.config.history.length with
                | [] => some previous
                | [⟨event, action⟩] => extendIntended? setup previous
                    (decodeEventAction setup.program event action)
                    (decodedPoint setup after.execution.application.config)
                | _ => none) = some history at advanced
              have step := transition_configStep (initialLaw setup) horizon scheduler before after
                joint realized
              split at advanced
              · cases advanced
                rw [previousState]
                rcases step with same | ⟨event, ready, action, member⟩
                · change decodedPoint setup _ = decodedPoint setup _
                  rw [same]
                · rename_i dropped
                  rw [EventGraph.Config.step_history _ event ready action _ member,
                    List.drop_left] at dropped
                  cases dropped
              · exact extendIntended?_state advanced
              · cases advanced

/-- **The replay lies at the projected intended site.** At a native history of
a decision site of `who` with recall `past` and view `view`, an existing
intended replay is a history of the intended information state of the
projected view. -/
theorem intendedHistory?_infoOf {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (native : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    (seen : (onePacketInformation setup leaks bounds horizon scheduler).infoOf who native.trace =
      some (past, view))
    {history : setup.intendedProtocol.History}
    (replayed : intendedHistory? setup leaks bounds horizon scheduler native.trace = some history) :
    setup.intendedModel.infoOf who history.trace =
      projectView setup leaks who (some (past, view)) := by
  obtain ⟨state, trace⟩ := native
  rw [onePacket_infoOf] at seen
  cases state with
  | none => cases seen
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj seen)
        obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
          (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler trace control rfl
        rw [setup.intended_info, intendedHistory?_state trace replayed]
        change setup.protocolObserve who (decodedPoint setup _) = _
        rw [decodedPoint_eq residual, projectView_observe setup leaks who control.execution rank
          residual.checkpoint.ordered _ residual.decode]
      · simp [ReactiveApplication.observe, active] at seen

end Replay

end Vegas
