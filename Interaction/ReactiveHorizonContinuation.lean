/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveStopping
import Interaction.ReactiveRestrictedContinuation
import GameTheoryExtensions.Analysis.Protocol.Bayes

/-! # Local alternatives evaluated to the horizon, for every scheduler

A local lottery at a legal decision runs as the lottery over current
responses, each followed by the physical baseline up to the horizon. A fully
mixed restricted assessment puts positive mass on every legal response, so
every execution reached after a legal response, by complete rounds or at a
stopping point, is supported by the baseline from initialization. Neither
statement depends on the scheduler beyond its role as a protocol parameter.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

open Classical in
/-- A local response lottery followed by an admissible physical baseline, at
the complete assessment fuel, is the lottery over current responses followed
by the baseline run to the horizon. -/
theorem run_local_law_complete [Fintype Principal] (players : Principal → app.Policy)
    (covered : ∀ who, menu.Admissible initial horizon scheduler who (players who))
    (history : (menu.protocol initial horizon scheduler).History)
    (who : Principal) (remaining : Nat) (execution : app.Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    {info : (menu.information initial horizon scheduler).InfoState who}
    (observed : (menu.information initial horizon scheduler).infoOf who history.trace = info)
    (law : PMF ((menu.information initial horizon scheduler).Choice who info)) :
    let baseline := fun player => menu.restrictPolicy initial horizon scheduler player
      (players player)
    ((menu.information initial horizon scheduler).runBehavioralFrom
      (Profile.update (sig := (menu.information initial horizon scheduler).behavioralSignature)
        baseline who ((baseline who).withLaw info law))
      (2 * horizon + 1) history).map History.state =
      (law.map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
        (app.runToHorizon scheduler players horizon (execution.respond app who response)).map
          app.finished := by
  subst info
  intro baseline
  let updated := Profile.update
    (sig := (menu.information initial horizon scheduler).behavioralSignature) baseline who
    ((baseline who).withLaw
      ((menu.information initial horizon scheduler).infoOf who history.trace) law)
  have bounded := app.trace_bound initial horizon scheduler
    (menu.toRawTrace initial horizon scheduler history.trace)
  rw [menu.toRawTrace_length] at bounded
  have full := menu.run_eq_finish initial horizon scheduler updated (2 * horizon + 1) history
    (by omega)
  have trimmed := menu.run_eq_finish initial horizon scheduler updated
    (2 * horizon + 1 - history.trace.length) history (by omega)
  refine (full.trans trimmed.symm).trans ?_
  refine (menu.run_local_law_restrict_remaining initial horizon scheduler players covered history
    who remaining execution current law).trans ?_
  apply bind_congr_on_support _
  intro response _
  have traced : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have accounted := (menu.roundSupported_uniform initial horizon scheduler traced).1
  change execution.environmentRecall.length + remaining = horizon at accounted
  exact app.finish_eq_runToHorizon scheduler players initial horizon remaining _
    (by rw [app.respond_environmentRecall]; exact accounted)

section

variable (players : Principal → app.Policy)
  (covered : ∀ who, menu.Admissible initial horizon scheduler who (players who))
  (assessment : (menu.information initial horizon scheduler).BehavioralAssessment)
  (strategy : assessment.strategy = fun who =>
    menu.restrictPolicy initial horizon scheduler who (players who))
  (mixed : assessment.IsFullyMixed)

include covered strategy mixed

/-- All legal responses at a legal decision have positive physical mass under
a fully mixed restricted baseline. -/
theorem fullyMixed_response_support (who : Principal) (remaining : Nat)
    (execution : app.Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (response : app.Action)
    (allowed : response ∈ menu.actions who (execution.recall who) (execution.observe app who)) :
    response ∈ (players who (execution.recall who) (execution.observe app who)).support := by
  let model := menu.information initial horizon scheduler
  have observed : model.infoOf who trace =
      some (execution.recall who, execution.observe app who) := by
    change (menu.signals initial horizon scheduler).infoOf who trace = _
    rw [menu.info]
    simp only [ReactiveApplication.observe, ↓reduceIte]
  have permitted : some response ∈ model.menu who (model.infoOf who trace) := by
    rw [observed]
    exact ⟨response, allowed, rfl⟩
  let choice : model.Choice who (model.infoOf who trace) := ⟨some response, permitted⟩
  have running : ¬ (menu.protocol initial horizon scheduler).terminal
      (some ⟨remaining, some who, execution⟩) := by
    intro impossible
    have absent : (some who : Option Principal) = none := impossible.2
    cases absent
  have chosen := mixed.support_at_history ⟨_, trace⟩ running who choice
  have mapped : some response ∈ ((assessment.strategy who (model.infoOf who trace)).map
      Subtype.val).support := PMF.support_map .. ▸ ⟨choice, chosen, rfl⟩
  rw [strategy, observed, menu.restrictPolicy_map_val _ _ _ who _ _ _
    (covered who _ trace rfl), PMF.support_map] at mapped
  obtain ⟨actual, present, same⟩ := mapped
  exact Option.some.inj same ▸ present

/-- Every legal history is round-supported by a fully mixed restricted
baseline. -/
theorem fullyMixed_roundSupported {state}
    (trace : (menu.protocol initial horizon scheduler).Trace state) :
    app.RoundSupported initial horizon scheduler players state :=
  menu.roundSupported_history_of_reachable initial horizon scheduler players
    (fun remaining who execution decision action allowed =>
      menu.fullyMixed_response_support initial horizon scheduler players covered assessment
        strategy mixed who remaining execution decision action allowed) trace

/-- A legal response followed by complete baseline rounds stays supported by
the baseline from initialization. -/
theorem fullyMixed_response_rounds_support (who : Principal) (remaining : Nat)
    (execution : app.Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (response : app.Action)
    (allowed : response ∈ menu.actions who (execution.recall who) (execution.observe app who))
    (count : Nat) (final : app.Execution)
    (reached : final ∈
      (app.runRounds scheduler players count (execution.respond app who response)).support) :
    final ∈ (app.roundsFrom initial scheduler players final.environmentRecall.length).support := by
  obtain ⟨responded⟩ := menu.trace_respond initial horizon scheduler remaining execution who
    response trace allowed
  have start := (menu.fullyMixed_roundSupported initial horizon scheduler players covered
    assessment strategy mixed responded).2
  change execution.respond app who response ∈ (app.roundsFrom initial scheduler players
    (execution.respond app who response).environmentRecall.length).support at start
  rw [app.runRounds_environmentRecall_length scheduler players count _ final reached]
  exact app.roundsFrom_runRounds scheduler players initial _ count _ final start reached

/-- A legal response followed by baseline rounds to a stopping point stays
supported by the baseline from initialization. -/
theorem fullyMixed_response_stopped_support (who : Principal) (remaining : Nat)
    (execution : app.Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (response : app.Action)
    (allowed : response ∈ menu.actions who (execution.recall who) (execution.observe app who))
    (stop : app.Execution → Prop) [DecidablePred stop] (count : Nat) (stopped : app.Execution)
    (reached : stopped ∈
      (app.runUntil scheduler players stop count (execution.respond app who response)).support) :
    stopped ∈
      (app.roundsFrom initial scheduler players stopped.environmentRecall.length).support := by
  obtain ⟨used, _, rounds, _⟩ := app.runUntil_runRounds scheduler players stop count _ stopped
    reached
  exact menu.fullyMixed_response_rounds_support initial horizon scheduler players covered
    assessment strategy mixed who remaining execution trace response allowed used stopped rounds

end

end Interaction.ReactiveApplication.ResponseMenu
