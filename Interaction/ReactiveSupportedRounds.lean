/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRoundReachability
import Interaction.ReactiveResponseEvaluation

/-! # Supported play stays in the round evaluator

Every state that behavioral play of a response menu reaches with positive
probability is round-supported for the decoded profile: at scheduler control
it is the result of complete rounds of that profile, and at a pending
activation it follows an environment step from such a result
(`Interaction.ReactiveApplication.ResponseMenu.roundSupported_of_mem_run`).
Unlike `Interaction.ReactiveApplication.ResponseMenu.roundSupported_history`,
this needs no full support of the profile, only that the history is reached.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}

/-- One step of the canonical kernel of a profile keeps round support for that
profile. -/
theorem roundSupported_controlStep (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (before after : app.ProtocolState)
    (valid : app.RoundSupported initial horizon scheduler players before)
    (reached : after ∈ (app.controlStep initial horizon scheduler players before).support) :
    app.RoundSupported initial horizon scheduler players after := by
  cases before with
  | none =>
      obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
      refine ⟨by simp [Execution.initial], ?_⟩
      change Execution.initial app state ∈ (app.roundsFrom initial scheduler players 0).support
      rw [roundsFrom, PMF.support_bind]
      apply Set.mem_iUnion₂.mpr
      exact ⟨state, supported, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          obtain ⟨action, chosen, stepped⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          simp only [transition, ↓reduceIte, Option.getD_some] at stepped
          cases (PMF.mem_support_pure_iff _ _).mp stepped
          obtain ⟨accounted, count, prior, command, position, priorMem,
            commandMem, active, observed⟩ := valid
          change (execution.respond app who action).environmentRecall.length + remaining =
              horizon ∧ (execution.respond app who action) ∈
                (app.roundsFrom initial scheduler players
                  (execution.respond app who action).environmentRecall.length).support
          rw [app.respond_environmentRecall]
          refine ⟨accounted, ?_⟩
          rw [position, app.roundsFrom_succ, PMF.support_bind]
          apply Set.mem_iUnion₂.mpr
          refine ⟨prior, priorMem, ?_⟩
          rw [round, PMF.support_bind]
          apply Set.mem_iUnion₂.mpr
          refine ⟨command, commandMem, ?_⟩
          rw [dispatch, PMF.support_bind]
          apply Set.mem_iUnion₂.mpr
          refine ⟨execution, observed, ?_⟩
          simp only [resume, active, invoke, PMF.support_map]
          exact ⟨action, chosen, rfl⟩
      | none =>
          cases remaining with
          | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, selected, moved⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
              have advanced : next.environmentRecall.length =
                  execution.environmentRecall.length + 1 := by
                obtain ⟨updated, _, same⟩ := PMF.support_map .. ▸ supported
                cases same
                simp
              refine ⟨by have accounted := valid.1; dsimp at *; omega, ?_⟩
              cases active : command.actor? app with
              | some who =>
                  exact ⟨_, execution, command, advanced, valid.2, selected, active, supported⟩
              | none =>
                  change next ∈ (app.roundsFrom initial scheduler players
                    next.environmentRecall.length).support
                  rw [advanced, app.roundsFrom_succ, PMF.support_bind]
                  apply Set.mem_iUnion₂.mpr
                  refine ⟨execution, valid.2, ?_⟩
                  rw [round, PMF.support_bind]
                  apply Set.mem_iUnion₂.mpr
                  refine ⟨command, selected, ?_⟩
                  rw [dispatch, PMF.support_bind]
                  apply Set.mem_iUnion₂.mpr
                  exact ⟨next, supported, by simp [resume, active]⟩

/-- Every state the canonical kernel of a profile reaches from the initial
state is round-supported for that profile. -/
theorem roundSupported_of_mem_iterate (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (players : Principal → app.Policy) (fuel : Nat)
    (result : app.ProtocolState)
    (reached : result ∈ ((fun law => law.bind (app.controlStep initial horizon scheduler
      players))^[fuel] (PMF.pure none)).support) :
    app.RoundSupported initial horizon scheduler players result := by
  induction fuel generalizing result with
  | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; trivial
  | succ fuel ih =>
      rw [Function.iterate_succ_apply'] at reached
      obtain ⟨before, prior, stepped⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact roundSupported_controlStep initial horizon scheduler players before result
        (ih before prior) stepped

namespace ResponseMenu

variable [Fintype Principal] (menu : app.ResponseMenu) (initial : PMF app.State)
  (horizon : Nat) (scheduler : app.Scheduler)

/-- The states behavioral play of a response menu reaches are those the
canonical kernel of the decoded profile reaches. -/
theorem run_map_state_eq_iterate
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History) :
    ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history).map
        ExecutionProtocol.History.state =
      (fun law => law.bind (app.controlStep initial horizon scheduler
        (menu.decodeProfile initial horizon scheduler profile)))^[fuel]
        (PMF.pure history.state) := by
  have encoded : (fun who => app.encodePolicy
      (menu.decodeProfile initial horizon scheduler profile who)) =
        fun who => menu.embedPolicy initial horizon scheduler who (profile who) := by
    funext who
    exact app.encode_decodePolicy _
  calc
    _ = (((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history).map
          (menu.toRawHistory initial horizon scheduler)).map
            ExecutionProtocol.History.state := by
      rw [PMF.map_comp]
      rfl
    _ = ((app.information initial horizon scheduler).runBehavioralFrom
          (fun who => menu.embedPolicy initial horizon scheduler who (profile who)) fuel
          (menu.toRawHistory initial horizon scheduler history)).map
            ExecutionProtocol.History.state := by
      rw [menu.run_embed]
    _ = _ := by
      rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
        (app.information initial horizon scheduler) (app.singleMover initial horizon scheduler),
        ← encoded, app.run_map_state]
      rfl

/-- **Supported play is round-supported.** Every history that behavioral play
of a response menu reaches with positive probability is round-supported for
the decoded profile. -/
theorem roundSupported_of_mem_run
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (reached : history ∈ ((menu.information initial horizon scheduler).runBehavioral profile
      fuel).support) :
    app.RoundSupported initial horizon scheduler
      (menu.decodeProfile initial horizon scheduler profile) history.state := by
  have stateReached : history.state ∈ ((fun law => law.bind (app.controlStep initial horizon
      scheduler (menu.decodeProfile initial horizon scheduler profile)))^[fuel]
        (PMF.pure (menu.protocol initial horizon scheduler).initHistory.state)).support := by
    rw [← menu.run_map_state_eq_iterate initial horizon scheduler profile fuel]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨history, reached, rfl⟩
  exact roundSupported_of_mem_iterate initial horizon scheduler _ fuel history.state
    stateReached

end ResponseMenu

end Interaction.ReactiveApplication
