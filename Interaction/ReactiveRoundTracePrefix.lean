/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRoundTrace
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Actual scheduler rounds retain their literal history prefix -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}

/-- Expand SAME actual supported scheduler rounds into legal trace append steps,
retaining the original prefix and all original native executions. -/
theorem trace_runRounds_prefix (menu : app.ResponseMenu)
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (players : Principal → app.Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ menu.actions who past view)
    (remaining count : Nat) (before after : app.Execution)
    (prior : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + count, none, before⟩))
    (supported : after ∈ (app.runRounds scheduler players count before).support) :
    ∃ final : (menu.protocol initial horizon scheduler).Trace (some ⟨remaining, none, after⟩),
      TracePrefix prior final := by
  induction count generalizing before with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ⟨prior, .refl⟩
  | succ count ih =>
      obtain ⟨middle, moved, future⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      obtain ⟨observed, environment, resumed⟩ := Set.mem_iUnion₂.mp
        (PMF.support_bind .. ▸ dispatched)
      have legal : (menu.protocol initial horizon scheduler).Legal
          (some ⟨remaining + count + 1, none, before⟩) (fun _ => none) := by
        constructor
        · simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal]
        · intro who
          simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor]
      have reached : some (⟨remaining + count, command.actor? app, observed⟩ : app.Control) ∈
          (app.transition initial horizon scheduler
            (some ⟨remaining + count + 1, none, before⟩) (fun _ => none)).support := by
        rw [ReactiveApplication.transition, PMF.support_bind]
        refine Set.mem_iUnion₂.mpr ⟨command, selected, ?_⟩
        rw [PMF.support_map]
        exact ⟨observed, environment, rfl⟩
      have intermediate : ∃ next : (menu.protocol initial horizon scheduler).Trace
          (some ⟨remaining + count, none, middle⟩), TracePrefix prior next := by
        cases acting : command.actor? app with
        | none =>
            rw [acting] at reached
            let active := prior.extend (fun _ => none) legal reached
            change middle ∈ (app.resume players (command.actor? app) observed).support at resumed
            rw [acting] at resumed
            cases (PMF.mem_support_pure_iff _ _).mp resumed
            exact ⟨active, .extend .refl _ legal reached⟩
        | some owner =>
            rw [acting] at reached
            let active := prior.extend (fun _ => none) legal reached
            have activeKept : TracePrefix prior active := .extend .refl _ legal reached
            change middle ∈ (app.resume players (command.actor? app) observed).support at resumed
            rw [acting] at resumed
            obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ resumed
            let joint := fun who => if who = owner then some response else none
            have allowed : (menu.protocol initial horizon scheduler).Legal
                (some ⟨remaining + count, some owner, observed⟩) joint := by
              constructor
              · simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal]
              · intro who
                by_cases same : who = owner
                · subst who
                  simpa [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor,
                    ReactiveApplication.ResponseMenu.available, joint] using covered owner _ _
                      response chosen
                · simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor,
                    joint, same, Ne.symm same]
            have answered : some (⟨remaining + count, none,
                observed.respond app owner response⟩ : app.Control) ∈
                (app.transition initial horizon scheduler
                  (some ⟨remaining + count, some owner, observed⟩) joint).support := by
              change _ ∈ (PMF.pure _).support
              simp only [joint, ↓reduceIte, Option.getD_some, PMF.mem_support_pure_iff]
            exact ⟨active.extend joint allowed answered,
              .extend activeKept joint allowed answered⟩
      obtain ⟨next, nextKept⟩ := intermediate
      obtain ⟨final, finalKept⟩ := ih middle next future
      exact ⟨final, nextKept.trans finalKept⟩

end Interaction.ReactiveApplication.ResponseMenu
