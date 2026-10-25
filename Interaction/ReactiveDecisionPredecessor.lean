/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveResponseMenu

/-! # Idle predecessors of reactive decision callbacks

A physical transition can enter a player callback only by activation. This
one-step fact supplies actual idle predecessor traces in both raw and finite
response-menu games without repeating the physical command analysis.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- A transition entering a decision callback came from an idle control with
one more scheduler decision remaining and the same application and player recalls. -/
theorem transition_decision_predecessor
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    {before : app.ProtocolState} (joint : Principal → Option app.Action)
    {remaining : Nat} {who : Principal} {execution : app.Execution}
    (realized : some ⟨remaining, some who, execution⟩ ∈
      (app.transition initial horizon scheduler before joint).support) :
    ∃ previous : app.Execution, before = some ⟨remaining + 1, none, previous⟩ ∧
      previous.application = execution.application ∧ previous.recall = execution.recall := by
  cases before with
  | none =>
      obtain ⟨_, _, same⟩ := PMF.support_map .. ▸ realized
      cases same
  | some control =>
      rcases control with ⟨priorRemaining, actor, priorExecution⟩
      cases actor with
      | some responder => cases (PMF.mem_support_pure_iff _ _).mp realized
      | none =>
          cases priorRemaining with
          | zero => cases (PMF.mem_support_pure_iff _ _).mp realized
          | succ priorRemaining =>
              obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
              obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ moved
              cases command with
              | activate activated =>
                  cases same
                  obtain ⟨updated, chosen, rfl⟩ := PMF.support_map .. ▸ supported
                  obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ chosen
                  exact ⟨priorExecution, rfl, rfl, rfl⟩
              | «include» id => cases same
              | wait => cases same
              | application command => cases same

/-- Every actual raw decision callback has a genuine idle predecessor trace. -/
theorem decision_predecessor (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    {state : app.ProtocolState} (trace : (app.protocol initial horizon scheduler).Trace state)
    {remaining : Nat} {who : Principal} {execution : app.Execution}
    (current : state = some ⟨remaining, some who, execution⟩) :
    ∃ previous : app.Execution,
      Nonempty ((app.protocol initial horizon scheduler).Trace
        (some ⟨remaining + 1, none, previous⟩)) ∧
      previous.application = execution.application ∧ previous.recall = execution.recall := by
  match state, trace, current with
  | _, .start, current => cases current
  | _, .extend (source := before) prior joint _ realized, current =>
      subst current
      obtain ⟨previous, source, applicationEq, recallEq⟩ :=
        app.transition_decision_predecessor initial horizon scheduler joint realized
      exact ⟨previous, ⟨source ▸ prior⟩, applicationEq, recallEq⟩

end Interaction.ReactiveApplication

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu)

/-- Every actual decision callback has a genuine idle predecessor in the same
finite response menu, with unchanged application and complete player recall. -/
theorem decision_predecessor (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    {state : app.ProtocolState} (trace : (menu.protocol initial horizon scheduler).Trace state)
    {remaining : Nat} {who : Principal} {execution : app.Execution}
    (current : state = some ⟨remaining, some who, execution⟩) :
    ∃ previous : app.Execution,
      Nonempty ((menu.protocol initial horizon scheduler).Trace
        (some ⟨remaining + 1, none, previous⟩)) ∧
      previous.application = execution.application ∧ previous.recall = execution.recall := by
  match state, trace, current with
  | _, .start, current => cases current
  | _, .extend (source := before) prior joint _ realized, current =>
      subst current
      obtain ⟨previous, source, applicationEq, recallEq⟩ :=
        app.transition_decision_predecessor initial horizon scheduler joint realized
      exact ⟨previous, ⟨source ▸ prior⟩, applicationEq, recallEq⟩

end Interaction.ReactiveApplication.ResponseMenu
