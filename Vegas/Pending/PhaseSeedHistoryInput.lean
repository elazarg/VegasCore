/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedInformationInput
import Interaction.ReactiveRoundReachability

/-! # Actual protocol histories recover each callback's preceding local word -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private theorem wordRecall_of_roundsFrom (menu : (app).ResponseMenu)
    (initial : PMF (app).State) (scheduler : (app).Scheduler)
    (count : Nat) (execution : (app).Execution)
    (supported : execution ∈
      ((app).roundsFrom initial scheduler menu.uniformResponses count).support) :
    WordRecall runtime leaks execution := by
  obtain ⟨state, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  exact runRounds_wordRecall runtime leaks scheduler menu.uniformResponses count
    (ReactiveApplication.Execution.initial app state) execution (initial_wordRecall runtime leaks
      state) reached

/-- At genuine idle controls every previous callback is complete, so the
scheduler's full timed word is exactly reconstructed from actual own recall. -/
theorem idle_wordRecall_of_trace (menu : (app).ResponseMenu) (initial : PMF (app).State)
    (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat)
    (execution : (app).Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace (some ⟨remaining, none, execution⟩)) :
    WordRecall runtime leaks execution := by
  have supported := menu.roundSupported_uniform initial horizon scheduler trace
  exact wordRecall_of_roundsFrom runtime leaks menu initial scheduler _ execution supported.2

/-- A current active callback has an actual supported preceding idle execution.
Its pre-activation query is determined by the owner's post-activation full info. -/
theorem active_informationInput_of_trace (menu : (app).ResponseMenu)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩)) (coordinate : CommitAttemptEvent graph) :
    ∃ before, WordRecall runtime leaks before ∧
      (.activate owner : (app).Command) ∈
        (scheduler before.environmentRecall (before.observeEnvironment app)).support ∧
      execution ∈ (before.environmentStep app (.activate owner)).support ∧
      localInput runtime leaks coordinate owner before.environmentRecall
        (before.observeEnvironment app) =
          informationInput runtime leaks coordinate owner (execution.recall owner)
            (execution.observe app owner) := by
  have supported := menu.roundSupported_uniform initial horizon scheduler trace
  obtain ⟨count, before, command, _, prior, chosen, acting, reached⟩ := supported.2
  have commandEq : command = .activate owner := by
    cases command with
    | wait => cases acting
    | «include» identifier => cases acting
    | application native => cases acting
    | activate who =>
        have same : who = owner := Option.some.inj acting
        subst who
        rfl
  subst command
  have valid := wordRecall_of_roundsFrom runtime leaks menu initial scheduler count before prior
  exact ⟨before, valid, chosen, reached,
    activation_informationInput runtime leaks before execution owner coordinate valid reached⟩

end Vegas.EventGraphRuntime.PhaseSeedScheduler
