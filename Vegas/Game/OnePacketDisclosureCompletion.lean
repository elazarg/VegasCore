/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketEventSuccess
import Vegas.Pending.ExclusionPolicyLaw
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryAtom


/-! # Full continuations at packet-completion boundaries

Stop when the submitted event completes or an additional public condition holds.
An accepting receipt identifies the actual handler transition at the first completion.
The certified graph completion and the actual drained endpoint have exactly the same
full continuation law under every graph profile, including when publication fails.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- A settled packet's first completion preserves the full remaining graph law.
Additional stops may retain the unchanged sending configuration while the event is pending. -/
theorem accepted_until_continuation
    (reference : (graph setup).BehavioralProfile)
    (certificate : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu runtime leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (extraStop : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).History → Prop)
    {who : Player} {entry : (application setup runtime leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} {action : (graph setup).Action event}
    {output : ((graph setup).outputLayout event).Value}
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control)
    (invariant : AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry
      message event sent action output (some control))
    (atSent : control.execution.application.config = sent)
    (settles : ∀ stop ∈ (((bounds.onePacketMenu runtime leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => (∃ final, history.state = some final ∧
          event ∈ final.execution.application.config.cut.completed) ∨ extraStop history)
        start).support,
      ∀ final, stop.state = some final → RecordsEntry setup runtime leaks who entry (some final) →
        event ∈ final.execution.application.config.cut.completed →
          (message.id, true) ∈ final.execution.receipts) :
    ∀ stop ∈ (((bounds.onePacketMenu runtime leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => (∃ final, history.state = some final ∧
          event ∈ final.execution.application.config.cut.completed) ∨ extraStop history)
        start).support,
      ∃ final, stop.state = some final ∧
        (event ∉ final.execution.application.config.cut.completed →
          final.execution.application.config = sent) ∧
        (event ∈ final.execution.application.config.cut.completed →
          ∃ ready : sent.cut.Ready event, sent.actualDecision event action = some action ∧
            (graph setup).runPlan
                ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
                final.execution.application.config.remaining final.execution.application.config =
              (graph setup).runPlan
                ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
                (sent.complete event ready action output).remaining
                (sent.complete event ready action output)) := by
  let menu := bounds.onePacketMenu runtime leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  let stopped := fun history : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    (∃ final, history.state = some final ∧
      event ∈ final.execution.application.config.cut.completed) ∨ extraStop history
  have initial : AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry
      message event sent action output start.state := current ▸ invariant
  have transports : ∀ {state} {trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
        state}, TracePrefix start.trace trace →
      AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry message event
        sent action output state := by
    intro state trace earlier
    induction earlier with
    | refl => exact initial
    | extend previous joint legal realized ih =>
        exact acceptanceInvariant_transition (runtime := runtime) bounds horizon scheduler who
          entry message event sent action output _ _ joint legal ih realized
  intro stop member
  have prefixed := model.runBehavioralUntil_support_prefix certificate players stopped start
    stop member
  have finalInvariant := transports prefixed
  cases state : stop.state with
  | none => rw [state] at finalInvariant; exact finalInvariant.elim
  | some final =>
      rw [state] at finalInvariant
      refine ⟨final, rfl, finalInvariant.2.2.2.2.2.1, ?_⟩
      intro completed
      have receipt := settles stop member final state finalInvariant.2.1 completed
      let receiptSeen : (application setup runtime leaks).ProtocolState → Prop :=
        fun found => found.elim False
          (fun current => (message.id, true) ∈ current.execution.receipts)
      have outside : ¬ receiptSeen start.state := by
        rw [current]
        change (message.id, true) ∉ control.execution.receipts
        intro priorReceipt
        have stored := (invariant.2.2.2.2.2.2 priorReceipt).1
        have done := (control.execution.application.config.output_available event).mp
          (by rw [stored]; rfl)
        rw [atSent] at done
        exact invariant.2.2.2.1.1 done
      have inside : receiptSeen stop.state := by rw [state]; exact receipt
      obtain ⟨before, after, prior, joint, legal, moved, earlier, later, wasOutside, isInside⟩ :=
        prefixed.exists_entering_transition receiptSeen outside inside
      have priorInvariant := transports earlier
      have afterInvariant := transports (earlier.extend joint legal moved)
      cases before with
      | none => exact priorInvariant.elim
      | some before =>
          cases after with
          | none => exact afterInvariant.elim
          | some after =>
              change (message.id, true) ∉ before.execution.receipts at wasOutside
              change (message.id, true) ∈ after.execution.receipts at isInside
              have done := (after.execution.application.config.output_available event).mp
                (by rw [(afterInvariant.2.2.2.2.2.2 isInside).1]; rfl)
              let afterHistory : (menu.protocol (initialLaw setup) horizon scheduler).History :=
                ⟨some after, prior.extend joint legal moved⟩
              have noShorter : ¬ (prior.extend joint legal moved).length < stop.trace.length := by
                intro shorter
                have running := model.runBehavioralUntil_support_first certificate players
                  stopped start stop member afterHistory (earlier.extend joint legal moved)
                  later shorter
                exact running (Or.inl ⟨after, rfl, done⟩)
              have sameLength : (prior.extend joint legal moved).length = stop.trace.length :=
                Nat.le_antisymm later.length_le (Nat.le_of_not_gt noShorter)
              have sameHistory := later.eq_of_length sameLength
              have sameState : some after = some final :=
                (congrArg (fun history : (menu.protocol (initialLaw setup) horizon
                  scheduler).History => history.state) sameHistory).trans state
              have sameControl := Option.some.inj sameState
              subst after
              have priorToFinal : TracePrefix prior stop.trace :=
                (TracePrefix.extend .refl joint legal moved).trans later
              have shorter : prior.length < stop.trace.length := by
                have lower := later.length_le
                simp only [Trace.length] at lower
                omega
              have going := model.runBehavioralUntil_support_first certificate players stopped
                start stop member ⟨some before, prior⟩ earlier priorToFinal shorter
              have pending : event ∉ before.execution.application.config.cut.completed :=
                fun done => going (Or.inl ⟨before, rfl, done⟩)
              have beforeAt := priorInvariant.2.2.2.2.2.1 pending
              obtain ⟨packet, found, handled⟩ :=
                (application setup runtime leaks).transition_new_accepted_receipt
                  (initialLaw setup) horizon scheduler before final joint moved message.id
                  isInside wasOutside
              have rawPrior := menu.toRawTrace (initialLaw setup) horizon scheduler prior
              have recalled := (application setup runtime leaks).history_inputRecall
                (initialLaw setup) horizon scheduler rawPrior
              have unique := (application setup runtime leaks).uniqueIds_history scheduler
                (initialLaw setup) horizon _ rawPrior
              obtain ⟨first, last, split⟩ := priorInvariant.2.1
              have recorded : message ∈ (application setup runtime leaks).outputs
                  (before.execution.recall who) := by
                rw [split]
                exact List.mem_filterMap.mpr ⟨entry, by simp, priorInvariant.2.2.1⟩
              rw [← recalled who] at recorded
              have named : packet.id = message.id := by
                have spec := List.find?_some found
                simpa using spec
              have packetEq : packet = message :=
                (unique.inputs message (List.mem_filter.mp recorded).1).lookup message.id packet
                  found named
              subst packet
              exact (priorInvariant.2.2.2.2.1).reactive_runPlan setup.eventGraph runtime leaks
                reference beforeAt handled

end Vegas
