/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketProjectedDecision
import Vegas.Game.OnePacketDisclosureResolves

/-! # Own completions are intended where the player owes nothing

From a point intended for a player, a completion of the player's event whose
decoded action is not an intended action of the player leaves the player owing
a failure: a failed binding, a value its guard is predicted to reject, or a
withheld reveal
(`Vegas.SourceProgram.ProtocolState.intendedAvailable_of_decode_not_owesFor`).
Every decoded point is intended for the player or has the player owing
(`Vegas.decodedState_intendedFor_or_owes`), and debts persist. So along every
native history of the one-packet game whose decoded point has `who` owing
nothing, `who`'s own completions decode to intended actions
(`Vegas.ownCompletionsIntended_of_notOwes`), with no regularity of the history.
At a decision input where `who` owes nothing at any history, this holds at
every history (`Vegas.ownCompletionsIntended_of_siteNotOwes`).
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **A completion leaving its actor debt-free is intended.** At a point
intended for `actor` decoded after `count` events, stepping with the decoded
action of the event of index `count`, owned by `actor`, to a point at which
`actor` owes no failure means the decoded action is an intended action of
`actor`. -/
theorem intendedAvailable_of_decode_not_owesFor {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (state : ProtocolState program) (bound : count < eventCount program) (actor : Player)
      (action : EventGraph.EventField.Action (outputLayout program ⟨count, bound⟩))
      (target : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history =
          some state →
      IntendedFor actor program state →
      eventOwner? program ⟨count, bound⟩ = some actor →
      target ∈ (step program state
        (fun _ => decodeEventAction program ⟨count, bound⟩ action)).support →
      ¬ OwesFailure actor program target →
      ∃ act, decodeEventAction program ⟨count, bound⟩ action = some act ∧
        act ∈ ProtocolView.intendedAvailable actor program (observe actor program state) := by
  induction program with
  | ret _ =>
      intro count _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached notOwes
      cases count with
      | zero => cases owned
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended owned supported notOwes
  | @commit commitCtx commitNames name owner payload fresh guard next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached notOwes
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          change PublicationResult (L.Val payload) at action
          change ∃ act, some (OwnAction.commit owner name payload action) = some act ∧ _
          change ¬ OwesFailure owner (.commit name owner fresh guard next) (Sum.inr (entry next
            (commitSuccessor name guard ⟨cells, registry, revelations, history⟩
              (OwnAction.binding owner name payload
                (some (OwnAction.commit owner name payload action)))))) at notOwes
          rw [OwnAction.binding_commit] at notOwes
          cases action with
          | failure =>
              exact (notOwes (Or.inr (failedBinding_entry next _
                (Config.IntendedFor.failedBinding_commit intended fresh guard)))).elim
          | success value =>
              cases accepted : guard.predicts (sourceObserve owner cells) value with
              | true =>
                  exact ⟨_, rfl, value,
                    Or.inl ((mem_predictedValues_self guard _ value).mpr accepted), rfl⟩
              | false =>
                  exact (notOwes (Or.inl (indebted_entry next _
                    (Config.IntendedFor.indebted_commit intended fresh guard value
                      accepted)))).elim
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended owned supported notOwes
  | reveal published owner name fresh source unresolved next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached notOwes
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          change Bool at action
          change ∃ act, some (OwnAction.reveal owner name action) = some act ∧ _
          cases action with
          | true => exact ⟨_, rfl, rfl⟩
          | false =>
              refine (notOwes (Or.inl (Or.inl ⟨rfl, ?_⟩))).elim
              rw [base_entry]
              exact disclosureResult_false published source _
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended owned supported fun owes => notOwes (owes.elim
              (fun indebted => Or.inl (Or.inr indebted)) (fun failed => Or.inr (Or.inr failed)))

end Vegas.SourceProgram.ProtocolState

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- **Owing nothing reaches back along native transitions.** If `who` owes no
failure at the decoded point after a native transition of the one-packet game,
it owes none at the decoded point before it. -/
theorem notOwes_of_transition {who : Player} {before after : (application setup runtime
  leaks).Control}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some before))
    (joint : Player → Option (application setup runtime leaks).Action)
    (realized : some after ∈ ((application setup runtime leaks).transition (initialLaw setup)
      horizon
      scheduler (some before) joint).support)
    (notOwed : ∀ point, decodedPoint setup after.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point) :
    ∀ point, decodedPoint setup before.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point := by
  intro point decoded owes
  rcases transition_configStep (initialLaw setup) horizon scheduler before
    after joint realized
      with same | ⟨event, ready, action, member⟩
  · exact notOwed point (by rw [same]; exact decoded) owes
  · obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime) (failureProfile
      setup.program)
      (bounds.onePacketMenu runtime leaks) horizon scheduler prior before rfl
    obtain ⟨current, target, beforeEq, afterEq, supported⟩ :=
      decodedPoint_step residual event ready action _ member
    rw [beforeEq, Option.some.injEq] at decoded
    subst decoded
    exact notOwed target afterEq (ProtocolState.owesFailure_step who setup.program current _
      target owes supported)

/-- **Own completions are intended where the player owes nothing.** For a
well-formed setup, along a native history of the one-packet game whose decoded
point has `who` owing no failure, `who`'s own completions decode to intended
actions. -/
theorem ownCompletionsIntended_of_notOwes (wellFormed : setup.WellFormed) (who : Player) :
    ∀ {state} (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state)
      (control : (application setup runtime leaks).Control), state = some control →
      (∀ point, decodedPoint setup control.execution.application.config = some point →
        ¬ ProtocolState.OwesFailure who setup.program point) →
      OwnCompletionsIntended (runtime := runtime) (bounds := bounds) (horizon := horizon)
        (scheduler := scheduler)
        who trace
  | _, .start, _, current, _ => by cases current
  | _, .extend (source := before) (target := after) prior joint legal realized, control,
      current, notOwed => by
      have recursive := fun next same notOwedNext =>
        ownCompletionsIntended_of_notOwes wellFormed who prior next same
          notOwedNext
      subst current
      have realizedRaw : some control ∈ ((application setup runtime leaks).transition (initialLaw
        setup)
          horizon scheduler before joint).support := realized
      cases before with
      | none =>
          obtain rfl := trace_eq_start_of_none (runtime := runtime) prior
          exact ⟨trivial, fun current _ initialized => by cases initialized⟩
      | some current =>
          have notOwedCurrent := notOwes_of_transition (runtime := runtime) prior joint
            realizedRaw notOwed
          refine ⟨recursive current rfl notOwedCurrent, ?_⟩
          intro current' next same nextSame _ event ready action member acts point decodedCurrent
          cases Option.some.inj same
          cases Option.some.inj nextSame
          obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime)
            (failureProfile setup.program)
            (bounds.onePacketMenu runtime leaks) horizon scheduler prior current rfl
          obtain ⟨point', target, decodedCurrent', decodedNext, reachedPoint⟩ :=
            decodedPoint_step residual event ready action _ member
          rw [decodedCurrent, Option.some.injEq] at decodedCurrent'
          subst decodedCurrent'
          obtain ⟨forRank, ⟨forResidual⟩, forHolds⟩ :=
            decodedState_intendedFor_or_owes (runtime := runtime) wellFormed who (failureProfile
              setup.program)
              (bounds.onePacketMenu runtime leaks) horizon scheduler prior current rfl
          have intendedFor : ProtocolState.IntendedFor who setup.program point := by
            have holds := forHolds _ forResidual.decode
            have samePoint := Option.some.inj
              ((decodedPoint_eq forResidual).symm.trans decodedCurrent)
            subst samePoint
            rcases holds with intended | owes
            · exact intended
            · exact (notOwedCurrent _ (decodedPoint_eq forResidual) owes).elim
          have owned : eventOwner? setup.program ⟨event.val, event.isLt⟩ = some who := by
            rw [eventOwner?_eq_actor]
            exact acts
          exact ProtocolState.intendedAvailable_of_decode_not_owesFor setup.program event.val _ _ _
            _ _ _ point event.isLt who action target (decodedPoint_decode ready decodedCurrent)
            intendedFor owned reachedPoint (notOwed target decodedNext)

/-- **Own completions are intended at sites where the player owes nothing.** For
a well-formed setup, at a decision input of `who` at whose histories `who` owes
no failure at the decoded point, `who`'s own completions along every history of
the input decode to intended actions. -/
theorem ownCompletionsIntended_of_siteNotOwes (wellFormed : setup.WellFormed) {who : Player}
    {info : (onePacketInformation setup runtime leaks bounds horizon scheduler).InfoState who}
    (notOwed : ∀ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who info,
      ∀ point, nativeDecodedState setup runtime leaks history.1.state = some point →
        ¬ ProtocolState.OwesFailure who setup.program point)
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      info) :
    OwnCompletionsIntended (runtime := runtime) (bounds := bounds) (horizon := horizon) (scheduler
      := scheduler) who
      history.1.trace := by
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  cases state with
  | none =>
      obtain rfl := trace_eq_start_of_none (runtime := runtime) trace
      trivial
  | some control =>
      exact ownCompletionsIntended_of_notOwes (runtime := runtime) wellFormed who trace control rfl
        (notOwed ⟨⟨some control, trace⟩, seen⟩)

end Vegas
