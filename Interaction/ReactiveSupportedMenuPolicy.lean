/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseKernel
import Interaction.ReactiveRoundReachability
import GameTheory.Protocol.BehavioralTerminal

/-! # Finite-menu representation along supported physical play

Restriction preserves initialized play when supported physical responses are
admitted at the legal menu histories physical play reaches. No admission is
required at other legal histories or inconsistent policy inputs. Equality
retains the complete execution state, including the network and private recall.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
  (players : Principal → app.Policy)

/-- A supported physical step preserves reachability by complete rounds or a
pending activation. Only the response actually chosen needs physical support. -/
theorem roundSupported_controlStep (before after : app.ProtocolState)
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
          obtain ⟨action, chosen, moved⟩ :=
            Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          cases (PMF.mem_support_pure_iff _ _).mp moved
          obtain ⟨accounted, count, prior, command, position, priorMem,
            commandMem, active, observed⟩ := valid
          simp only [↓reduceIte, Option.getD_some]
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

/-- Initialized physical kernel support supplies the actual round witness. -/
theorem roundSupported_iterate_controlStep (fuel : Nat) (state : app.ProtocolState)
    (reached : state ∈ ((fun law => law.bind
      (app.controlStep initial horizon scheduler players))^[fuel] (PMF.pure none)).support) :
    app.RoundSupported initial horizon scheduler players state := by
  induction fuel generalizing state with
  | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; trivial
  | succ fuel ih =>
      rw [Function.iterate_succ_apply', PMF.support_bind] at reached
      obtain ⟨prior, supported, moved⟩ := Set.mem_iUnion₂.mp reached
      exact app.roundSupported_controlStep initial horizon scheduler players prior state
        (ih prior supported) moved

namespace ResponseMenu

variable {app} (menu : app.ResponseMenu)

/-- Decoding the restriction preserves the response law at a covered input. -/
private theorem decode_restrictPolicy_at (who : Principal) (policy : app.Policy)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (covered : ∀ response ∈ (policy past view).support,
      response ∈ menu.actions who past view) :
    app.decodePolicy (menu.embedPolicy initial horizon scheduler who
        (menu.restrictPolicy initial horizon scheduler who policy)) past view =
      policy past view := by
  change ((menu.embedPolicy initial horizon scheduler who
    (menu.restrictPolicy initial horizon scheduler who policy)) (some (past, view))).map _ = _
  rw [menu.embed_restrictPolicy initial horizon scheduler who policy past view covered]
  exact congrFun (congrFun (app.decode_encodePolicy policy) past) view

variable [Fintype Principal]

/-- Every initialized prefix has the original physical state law. Admission
is checked only where legal menu history and actual physical support meet. -/
theorem run_restrict_supported_controlSteps
    (covered : ∀ who control,
      (menu.protocol initial horizon scheduler).Trace (some control) →
      app.RoundSupported initial horizon scheduler players (some control) →
      control.actor = some who → ∀ response ∈
        (players who (control.execution.recall who)
          (control.execution.observe app who)).support,
        response ∈ menu.actions who (control.execution.recall who)
          (control.execution.observe app who))
    (fuel : Nat) :
    ((menu.information initial horizon scheduler).runBehavioralFrom
      (fun who => menu.restrictPolicy initial horizon scheduler who (players who)) fuel
      (menu.protocol initial horizon scheduler).initHistory).map History.state =
      (fun law => law.bind (app.controlStep initial horizon scheduler players))^[fuel]
        (PMF.pure none) := by
  let profile := fun who => menu.restrictPolicy initial horizon scheduler who (players who)
  let decoded := menu.decodeProfile initial horizon scheduler profile
  rw [menu.run_map_controlStep]
  change (fun law => law.bind (app.controlStep initial horizon scheduler decoded))^[fuel]
      (PMF.pure none) = _
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      apply bind_congr_on_support _
      intro state reached
      have valid := app.roundSupported_iterate_controlStep initial horizon scheduler players
        fuel state reached
      have menuReached : state ∈
          (((menu.information initial horizon scheduler).runBehavioralFrom profile fuel
            (menu.protocol initial horizon scheduler).initHistory).map History.state).support := by
        rw [menu.run_map_controlStep]
        exact ih ▸ reached
      obtain ⟨history, _supported, same⟩ := PMF.support_map .. ▸ menuReached
      cases state with
      | none => rfl
      | some control =>
          have traced : (menu.protocol initial horizon scheduler).Trace (some control) :=
            same ▸ history.trace
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | none => rfl
          | some who =>
              have law : decoded who (execution.recall who) (execution.observe app who) =
                  players who (execution.recall who) (execution.observe app who) := by
                exact menu.decode_restrictPolicy_at initial horizon scheduler who (players who)
                  _ _ (covered who _ traced valid rfl)
              simpa only [controlStep, actor, Option.bind_some] using
                congrArg (fun responseLaw => responseLaw.bind fun response =>
                  app.transition initial horizon scheduler
                    (some ⟨remaining, some who, execution⟩)
                    (fun observer => if observer = who then some response else none)) law

/-- Terminal finite-menu play represents the complete initialized physical
execution, including its final network, application and all private recall. -/
theorem terminal_restrict_supported_finish
    (covered : ∀ who control,
      (menu.protocol initial horizon scheduler).Trace (some control) →
      app.RoundSupported initial horizon scheduler players (some control) →
      control.actor = some who → ∀ response ∈
        (players who (control.execution.recall who)
          (control.execution.observe app who)).support,
        response ∈ menu.actions who (control.execution.recall who)
          (control.execution.observe app who))
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories) :
    ((menu.information initial horizon scheduler).runBehavioralTerminalFrom certificate
      (fun who => menu.restrictPolicy initial horizon scheduler who (players who))
      (menu.protocol initial horizon scheduler).initHistory).map History.state =
      app.finish initial horizon scheduler players none := by
  rw [InformationModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded _ certificate
    (menu.bounded initial horizon scheduler),
    menu.run_restrict_supported_controlSteps initial horizon scheduler players covered,
    app.iterate_eq_finish initial horizon scheduler players _ _ (by rfl)]

end ResponseMenu
end Interaction.ReactiveApplication
