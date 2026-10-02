/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstTurnNoMiss

/-! # Clear full service risk under exact first-turn play

The owner's submission recall and opportunity recall are clear, and its
public bindings do not miss. A ready unrecorded binding must therefore be
at its first own turn, which the asynchronous reaction budget protects.
These facts clear both the persistent signal and the current opportunity.

The result applies to every supported control, including the current private
recall before an own activation responds. Only this owner's prescribed policy
is fixed; foreign policies remain arbitrary. Clearing the menu flag does not
assert that the traffic audit collects zero charge.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- At a supported scheduler boundary, an unrecorded ready binding has had no
earlier own binding turn, so its current opportunity is still protected. -/
theorem sourceServiceFirstTurn_currentOpportunity_clear_roundsFrom {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who =
      sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile who)
    (count : Nat) (within : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support) :
    (runtime setup).firstUnprotectedBindingOpportunity leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false := by
  let app := application setup leaks
  apply Bool.eq_false_of_not_eq_true
  intro risky
  obtain ⟨_, event, owner, payload, turn, binding, unrecorded, unprotected⟩ :=
    ((runtime setup).firstUnprotectedBindingOpportunity_iff leaks bound who _ _).mp risky
  have turnActual : execution.application.publicView.ownTurn? who = some event := turn
  have turned := (sourceServiceFirstTurn_recallFacts contract timely players who turns profile
    follows count within execution reached).1
  have first : sourceServiceTurn setup leaks who event (execution.recall who)
      (execution.observe app who) = some 0 := by
    change (if execution.application.publicView.ownTurn? who = some event then
      some ((execution.recall who).countP fun entry =>
        decide (entry.beforeView.application.publicView.ownTurn? who = some event))
      else none) = some 0
    simp only [turnActual, ↓reduceIte]
    apply congrArg some
    apply List.countP_eq_zero.mpr
    intro entry member seen
    have recorded := turned entry member event owner payload (of_decide_eq_true seen) binding
    rw [unrecorded] at recorded
    cases recorded
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players count
    within execution reached
  have ownTurn := PublicView.ownTurn?_spec execution.application.publicView who event turnActual
  have fits := firstTurn_inclusionFits contract timely trace
    (roundsFrom_activationsAnswered count execution reached) ownTurn.2
    ((execution.application.publicView_eventReady event).mp ownTurn.1) first
  exact unprotected fits

/-- Pending activations change message knowledge but preserve the fields used
by the opportunity flag. Thus the current signal is clear at every control. -/
theorem sourceServiceFirstTurn_currentOpportunity_clear_roundSupported {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who =
      sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile who)
    (control : (application setup leaks).Control)
    (reached : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some control)) :
    (runtime setup).firstUnprotectedBindingOpportunity leaks bound who
      (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) = false := by
  let app := application setup leaks
  obtain ⟨remaining, actor, execution⟩ := control
  cases actor with
  | none =>
      have lengths := reached.1
      change execution.environmentRecall.length + remaining = horizon at lengths
      have within : execution.environmentRecall.length ≤ horizon := by omega
      exact sourceServiceFirstTurn_currentOpportunity_clear_roundsFrom contract timely players who
        turns profile follows execution.environmentRecall.length within execution reached.2
  | some responder =>
      obtain ⟨lengthEq, count, prior, command, counted, priorMem, _, active, moved⟩ := reached
      have commandEq : command = .activate responder := by
        cases command with
        | activate principal =>
            exact congrArg ReactiveApplication.Command.activate (Option.some.inj active)
        | wait | «include» _ | application _ => cases active
      subst commandEq
      have beforeClear := sourceServiceFirstTurn_currentOpportunity_clear_roundsFrom contract
        timely players who turns profile follows count (by omega) prior priorMem
      have appEq := activation_application setup leaks prior execution responder moved
      have recallEq := app.environmentStep_recall prior execution (.activate responder) moved
      have currentEq := (runtime setup).firstUnprotectedBindingOpportunity_congr leaks bound who
        (execution.recall who) (prior.recall who) (execution.observe app who)
        (prior.observe app who) rfl (congrArg State.publicView appEq)
        (congrArg (fun recalls => (runtime setup).submissionRecall leaks (recalls who)) recallEq)
      exact currentEq.trans beforeClear

/-- Exact first-turn play keeps the owner's entire menu expansion flag clear
at every supported control, while other owners' raw policies are unrestricted. -/
theorem sourceServiceFirstTurn_serviceRisk_clear_roundSupported {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who =
      sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile who)
    (control : (application setup leaks).Control)
    (reached : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some control)) :
    (runtime setup).serviceRisk leaks bound who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) = false := by
  have publicClear := sourceServiceFirstTurn_no_public_miss_roundSupported contract timely players
    who turns profile follows control reached
  have submittedClear := sourceServiceTurnPolicy_recalledSubmissionRisk_roundSupported scheduler
    players who (firstTurnTiming setup turns) profile follows horizon control reached
  have opportunityRecallClear := (sourceServiceFirstTurn_recallFacts_roundSupported contract timely
    players who turns profile follows control reached).2
  apply (runtime setup).serviceRisk_clear leaks bound
  · exact ((runtime setup).persistentServiceRisk_clear_iff leaks bound who _ _).mpr
      ⟨⟨publicClear, submittedClear⟩, opportunityRecallClear⟩
  · exact sourceServiceFirstTurn_currentOpportunity_clear_roundSupported contract timely players
      who turns profile follows control reached

end Vegas
