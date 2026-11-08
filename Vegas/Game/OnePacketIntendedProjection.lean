/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForced
import Vegas.Pending.ReactiveOnePacketMenu
import Vegas.Game.IntendedPreservation
import Vegas.Source.Exclusion

/-! # Current native endpoints and partial intended replay

The decoded point reads the actual current graph prefix and its full source
configuration. Every supported graph completion advances it by the corresponding
source step. The native state adapter always reads that actual endpoint.

A partial intended replay extends an intended history only when the existing
intended protocol admits the observed step and reaches the current decoded
endpoint. Transitions with no completion preserve the replay; a singleton
completion uses its actual recorded decision; multiple completions return none.
Every successful replay ends at the actual decoded endpoint and has the
projected source observation. No completeness claim is made for arbitrary
multi-completion transitions.
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
  | _, _, .commit _ owner _ _ next, state, choice => by
      cases state with
      | inl config =>
          by_cases inactive : owner ∈ config.defaulted
          · simp [step, observe, ProtocolView.actor, inactive, commitSuccessor]
          · simp [step, observe, ProtocolView.actor, inactive]
      | inr rest =>
          simp only [step, Sum.elim_inr, observe, ProtocolView.actor]
          rw [step_actingJoint next rest choice]
  | _, _, .reveal _ owner _ _ _ _ next, state, choice => by
      cases state with
      | inl config =>
          by_cases inactive : owner ∈ config.defaulted
          · simp [step, observe, ProtocolView.actor, inactive, revealSuccessor]
          · simp [step, observe, ProtocolView.actor, inactive]
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
  (timeouts : EventTimeouts (graph setup))

/-- A source point at which some history of the intended game ends. -/
def IntendedReached (point : ProtocolState setup.program) : Prop :=
  ∃ history : setup.intendedProtocol.History, history.state = some point

section Decoding

open Classical in
/-- Read the current source point at the configuration's completed prefix.
The total reader returns none when the cut or typed cells do not decode. -/
def decodedPoint (config : (graph setup).Config) : setup.ProtocolState :=
  if ordered : ∃ rank, config.cut.IsPrefix rank then
    sourceServicePrefix? setup ordered.choose config
  else none

variable {setup timeouts}

/-- At a completed prefix, the decoded point is the readout at that prefix. -/
theorem decodedPoint_eq_of_isPrefix {config : (graph setup).Config} {rank : Nat}
    (ordered : config.cut.IsPrefix rank) :
    decodedPoint setup config = sourceServicePrefix? setup rank config := by
  have exists_ordered : ∃ rank, config.cut.IsPrefix rank := ⟨rank, ordered⟩
  unfold decodedPoint
  rw [dite_eq_left_of_eq_true (eq_true exists_ordered), show exists_ordered.choose = rank from
    EventOrder.Cut.IsPrefix.unique exists_ordered.choose_spec ordered]

/-- A native endpoint's decoded source point has exactly its public defaults. -/
theorem decodedPoint_defaults {setup : Setup (Player := Player) (L := L)}
    {config : (graph setup).Config} {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point) :
    ProtocolState.defaults setup.program point = config.defaults := by
  unfold decodedPoint at decoded
  split at decoded
  · exact decodeSourcePrefix?_defaults _ _ _ _ _ _ _ _ _ _ decoded
  · cases decoded

/-- An intended source decoding certifies that the native default set is empty. -/
theorem defaulted_eq_empty_of_decodedIntended {setup : Setup (Player := Player) (L := L)}
    {config : (graph setup).Config} {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point)
    (intended : ProtocolState.Intended setup.program point) : config.defaulted = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro who present
  apply ProtocolState.not_excluded_of_intended who setup.program point intended
  unfold ProtocolState.Excluded
  rw [ProtocolState.defaulted_eq_defaults]
  rw [decodedPoint_defaults decoded]
  exact present

/-- At a decoded forced point, activity of the focal player makes every
player active: the forced point excludes defaults of all other players. -/
theorem defaulted_eq_empty_of_decodedForced {setup : Setup (Player := Player) (L := L)}
    {config : (graph setup).Config} {point : ProtocolState setup.program} {who : Player}
    (decoded : decodedPoint setup config = some point)
    (forced : ForcedPoint setup who point) (active : who ∉ config.defaulted) :
    config.defaulted = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro other present
  by_cases same : other = who
  · exact active (same ▸ present)
  · apply (forced.2 other same).1
    unfold ProtocolState.Excluded
    rw [ProtocolState.defaulted_eq_defaults, decodedPoint_defaults decoded]
    exact present

/-- At a configuration with a source residual, the decoded point is the
residual's point. -/
theorem decodedPoint_eq {profile : BehavioralProfile setup.program} {rank : Nat}
    {config : (graph setup).Config} (residual : SourceResidual setup profile rank config) :
    decodedPoint setup config =
      some (residual.lift (ProtocolState.entry residual.program residual.source)) := by
  have ordered : ∃ rank, config.cut.IsPrefix rank := ⟨rank, residual.checkpoint.ordered⟩
  unfold decodedPoint
  rw [dite_eq_left_of_eq_true (eq_true ordered), show ordered.choose = rank from
    EventOrder.Cut.IsPrefix.unique ordered.choose_spec residual.checkpoint.ordered]
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
  (scheduler : (application setup timeouts leaks).Scheduler)

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

/-- Read the source point of the actual current native configuration,
preserving none before initialization. The point may lie outside intended play. -/
def nativeDecodedState : (application setup timeouts leaks).ProtocolState → setup.ProtocolState
  | none => none
  | some control => decodedPoint setup control.execution.application.config

/-- Advance an intended history along one native transition: the initial
draw to the decoded initial point; no step when no event completes; the step of
the decoded action when one event completes; failure otherwise. -/
def advanceIntended? (history : setup.intendedProtocol.History) :
    (application setup timeouts leaks).ProtocolState → (application setup timeouts
      leaks).ProtocolState →
      Option setup.intendedProtocol.History
  | none, some after => extendIntended? setup history none
      (decodedPoint setup after.execution.application.config)
  | some before, some after =>
      match after.execution.application.config.history.drop
          before.execution.application.config.history.length with
      | [] => some history
      | [completion] => extendIntended? setup history
          (completion.decision.bind (decodeEventAction setup.program completion.event))
          (decodedPoint setup after.execution.application.config)
      | _ => none
  | _, none => none

/-- The partial intended replay, accepting only stuttering or singleton
completion transitions whose source steps are intended and actually reach the endpoint. -/
def intendedHistory? : ∀ {state},
    ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon scheduler).Trace
      state →
      Option setup.intendedProtocol.History
  | _, .start => some setup.intendedProtocol.initHistory
  | _, .extend (source := before) (target := after) prior _ _ _ =>
      (intendedHistory? prior).bind fun history =>
        advanceIntended? setup timeouts leaks history before after

variable {setup timeouts leaks bounds horizon scheduler}

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
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace state)
    {history : setup.intendedProtocol.History},
    intendedHistory? setup timeouts leaks bounds horizon scheduler trace = some history →
      history.state = nativeDecodedState setup timeouts leaks state
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
                | [completion] => extendIntended? setup previous
                    (completion.decision.bind (decodeEventAction setup.program completion.event))
                    (decodedPoint setup after.execution.application.config)
                | _ => none) = some history at advanced
              have path := reactive_protocol_graph_steps timeouts leaks (initialLaw setup)
                horizon scheduler before after joint realized
              split at advanced
              · rename_i dropped
                cases advanced
                rw [previousState]
                have small : after.execution.application.config.history.length ≤
                    before.execution.application.config.history.length := by
                  have emptyLength := congrArg List.length dropped
                  simp only [List.length_drop, List.length_nil] at emptyLength
                  omega
                change decodedPoint setup before.execution.application.config =
                  decodedPoint setup after.execution.application.config
                rw [EventGraph.Config.Step.path_eq_of_history_length_le path small]
              · exact extendIntended?_state advanced
              · cases advanced

/-- **The replay lies at the projected intended site.** At a native history of
a decision site of `who` with recall `past` and view `view`, an existing
intended replay is a history of the intended information state of the
projected view. -/
theorem intendedHistory?_infoOf {who : Player} {past : List (application setup timeouts
  leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    (native : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (seen : ((bounds.onePacketMenu timeouts leaks).information (initialLaw setup) horizon
      scheduler).infoOf who native.trace =
      some (past, view))
    {history : setup.intendedProtocol.History}
    (replayed : intendedHistory? setup timeouts leaks bounds horizon scheduler native.trace = some
      history) :
    setup.intendedModel.infoOf who history.trace =
      projectView setup timeouts leaks who (some (past, view)) := by
  obtain ⟨state, trace⟩ := native
  have observed : ((bounds.onePacketMenu timeouts leaks).information (initialLaw setup) horizon
      scheduler).infoOf who trace = (application setup timeouts leaks).observe who state :=
    (bounds.onePacketMenu timeouts leaks).info (initialLaw setup) horizon scheduler who trace
  rw [observed] at seen
  cases state with
  | none => cases seen
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj seen)
        obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (timeouts := timeouts) (failureProfile
          setup.program)
          (bounds.onePacketMenu timeouts leaks) horizon scheduler trace control rfl
        rw [setup.intended_info, intendedHistory?_state (timeouts := timeouts) trace replayed]
        change setup.protocolObserve who (decodedPoint setup _) = _
        rw [decodedPoint_eq residual, projectView_observe setup timeouts leaks who
          control.execution rank
          residual.checkpoint.ordered _ residual.decode]
      · simp [ReactiveApplication.observe, active] at seen

end Replay

end Vegas
