/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingMiss
import Vegas.Game.SourceServiceFirstTurnRisk

/-! # Owner-local exclusion of public binding omissions

A recorded protected commitment of an owner following the turn-counted source
policy cannot become a public omission, whatever the other players do. Under
the asynchronous opportunity and timing requirements, exact first-turn play
keeps every owned binding omission flag clear. Silent deferrals remain distinct
from recorded binding calls.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

variable {setup leaks}

/-- An event actually recorded by the owner's turn-counted source policy cannot
become a public binding omission. The other players' raw policies are arbitrary. -/
theorem sourceServiceTurnPolicy_recorded_binding_no_miss {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who)
    (count : Nat) (within : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall who) event = true) :
    execution.application.publicView.missedBinding event = false := by
  let app := application setup leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    count within execution reached
  obtain ⟨calls, once, _⟩ := serialFacts_roundsFrom contract players who timing profile follows
    count within execution reached
  have conform : FreshCallsConform setup leaks execution who :=
    fun entry member material message transmitted emitted =>
      sourceServiceTurnPolicy_freshServiceEnvelope scheduler players who timing profile follows
        count execution reached entry member material transmitted message emitted
  have atTurn := (canonicalSlots_roundsFrom scheduler players who timing profile follows
    count execution reached).1
  exact owner_recorded_binding_no_miss contract.inclusion trace who calls conform once atTurn
    event payload outputEq codeEq node recorded

/-- Exact first-turn source play keeps this owner's binding event clear on every
supported scheduler round, with arbitrary raw policies of the other players. -/
theorem sourceServiceFirstTurn_binding_no_miss {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (count : Nat) (within : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) :
    execution.application.publicView.missedBinding event = false := by
  let app := application setup leaks
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, initial, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      obtain ⟨inputs, _, rfl⟩ := PMF.support_map .. ▸ initial
      simp only [PublicView.missedBinding, outputEq, ReactiveApplication.Execution.initial,
        State.initial, State.publicView, EventGraph.publicObserve, EventGraph.Config.initial,
        List.map_nil, List.not_mem_nil, decide_false, Bool.false_and]
  | succ count ih =>
      have reachedNext := reached
      rw [app.roundsFrom_succ] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have clear := ih (by omega) prior priorMem
      apply Bool.eq_false_of_not_eq_true
      intro missing
      by_cases recorded : (runtime setup).eventRecorded leaks (execution.recall who) event = true
      · have good := sourceServiceTurnPolicy_recorded_binding_no_miss contract players who
          (firstTurnTiming setup turns) profile follows (count + 1) within execution reachedNext
          event payload outputEq codeEq node recorded
        rw [good] at missing
        cases missing
      · obtain ⟨command, _, middle, dispatched, effect⟩ := round_cases setup leaks moved
        have middleMissing : middle.application.publicView.missedBinding event = true := by
          rcases effect with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
          · exact missing
          · have same := (runtime setup).reactive_respond_application leaks middle actor response
            exact (congrArg (fun view : PublicView (graph setup) => view.missedBinding event)
              same.2).symm.trans missing
        obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
          count (by omega) prior priorMem
        have facts := legalFacts setup leaks horizon scheduler _ trace
        obtain ⟨_, ready, entered, activated, due⟩ := new_binding_miss_expiry command facts.binding
          dispatched event who payload outputEq codeEq node clear middleMissing
        change (runtime setup).deadline event ≤ prior.application.clock - entered at due
        have owned := nodeView_bind_actor outputEq codeEq
        have delayFits := timely event (by rw [owned]; rfl)
        obtain ⟨entry, recalled, turn⟩ := opportunity_turn contract trace
          (roundsFrom_activationsAnswered count prior priorMem) owned ready entered activated
          (by change entered + delay event < prior.application.clock; omega)
        have turned := (sourceServiceFirstTurn_recallFacts contract timely players who turns
          profile follows count (by omega) prior priorMem).1
        have recordedPrior := turned entry recalled event who payload turn outputEq
        have grows : prior.recall who ⊆ execution.recall who := by
          have same := app.environmentStep_recall prior middle command dispatched
          rcases effect with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
          · rw [same]
          · rw [← same]
            exact app.respond_recall_mono middle actor who response
        obtain ⟨call, member, named⟩ := List.any_eq_true.mp recordedPrior
        exact recorded (List.any_eq_true.mpr ⟨call, grows member, named⟩)

/-- The owner's entire public omission detector is clear under exact first-turn
play. No restrictions are placed on the other players' raw responses. -/
theorem sourceServiceFirstTurn_no_public_miss {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (count : Nat) (within : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support) :
    execution.application.publicView.missedBindingBy who = false := by
  classical
  apply decide_eq_false
  rintro ⟨event, owned, missing⟩
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      simp only [PublicView.missedBinding, outputEq, Bool.false_eq_true] at missing
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [PublicView.missedBinding, outputEq, Bool.false_eq_true] at missing
  | bind owner payload outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst owner
      have clear := sourceServiceFirstTurn_binding_no_miss contract timely players who turns
        profile follows count within execution reached event payload outputEq codeEq node
      rw [clear] at missing
      cases missing

/-- Covers the actual public record at a pending activation as well as completed
scheduler rounds. An activation changes only the activated player's message sample. -/
theorem sourceServiceFirstTurn_no_public_miss_roundSupported {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (control : (application setup leaks).Control)
    (reached : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some control)) :
    control.execution.application.publicView.missedBindingBy who = false := by
  obtain ⟨remaining, actor, execution⟩ := control
  cases actor with
  | none =>
      have within : execution.environmentRecall.length ≤ horizon := by
        have lengths := reached.1
        change execution.environmentRecall.length + remaining = horizon at lengths
        omega
      exact sourceServiceFirstTurn_no_public_miss contract timely players who turns profile follows
        _ within execution reached.2
  | some responder =>
      obtain ⟨lengthEq, count, prior, command, _, priorMem, _, active, moved⟩ := reached
      have clear := sourceServiceFirstTurn_no_public_miss contract timely players who turns
        profile follows count (by omega) prior priorMem
      cases command with
      | activate actor =>
          rw [activation_application setup leaks prior execution actor moved]
          exact clear
      | wait | «include» id | application command => cases active

end Vegas
