/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRoundTrace

/-! # Complete menu continuations retain genuine protocol traces -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat)
  (scheduler : app.Scheduler)

/-- Every physical outcome of a covered whole continuation is a genuine
history of the same menu, including a pending response at its subgame root. -/
theorem finish_trace (players : Principal → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ menu.actions who past view)
    (state : app.ProtocolState) (trace : (menu.protocol initial horizon scheduler).Trace state)
    (final : app.ProtocolState)
    (reached : final ∈ (app.finish initial horizon scheduler players state).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace final) := by
  cases state with
  | none =>
      obtain ⟨input, present, continued⟩ := Set.mem_iUnion₂.mp
        (PMF.support_bind .. ▸ reached)
      obtain ⟨after, supported, equal⟩ := PMF.support_map .. ▸ continued
      obtain ⟨started⟩ := menu.trace_initial initial horizon scheduler input present
      obtain ⟨completed⟩ := menu.trace_runRounds initial horizon scheduler players covered
        0 horizon (Execution.initial app input) after
          (by simpa only [Nat.zero_add] using started) supported
      exact ⟨equal ▸ completed⟩
  | some current =>
      obtain ⟨after, supported, equal⟩ := PMF.support_map .. ▸ reached
      obtain ⟨resumed, response, continued⟩ := Set.mem_iUnion₂.mp
        (PMF.support_bind .. ▸ supported)
      have ready : Nonempty ((menu.protocol initial horizon scheduler).Trace
          (some ⟨current.remaining, none, resumed⟩)) := by
        rcases current with ⟨remaining, actor, execution⟩
        cases actor with
        | none =>
            cases (PMF.mem_support_pure_iff _ _).mp response
            exact ⟨trace⟩
        | some owner =>
            obtain ⟨action, chosen, rfl⟩ := PMF.support_map .. ▸ response
            exact menu.trace_respond initial horizon scheduler remaining execution owner action
              trace (covered owner _ _ action chosen)
      obtain ⟨completed⟩ := menu.trace_runRounds initial horizon scheduler players covered
        0 current.remaining resumed after (by simpa only [Nat.zero_add] using ready.some)
          continued
      exact ⟨equal ▸ completed⟩

end Interaction.ReactiveApplication.ResponseMenu
