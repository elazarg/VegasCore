/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseKernel
import Interaction.ReactiveResponseConditioning
import Interaction.ReactivePolicyMixture

/-! # Private policy profiles through an actual history step -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

local notation "N" => menu.information initial horizon scheduler
local notation "E" => menu.protocol initial horizon scheduler

/-- A step without a responding actor preserves every actual private recall. -/
theorem run_one_inactive_recall
    (profile : ∀ who, (N).BehavioralPolicy who) (history : (E).History)
    (inactive : app.actor history.state = none) {final : (E).History}
    (member : final ∈ ((N).runBehavioralFrom profile 1 history).support) (who : Principal) :
    app.recallAt who final.state = app.recallAt who history.state := by
  have projected : final.state ∈
      (((N).runBehavioralFrom profile 1 history).map History.state).support := by
    rw [PMF.support_map]
    exact ⟨final, member, rfl⟩
  rw [menu.run_map_controlSteps, Function.iterate_one, PMF.pure_bind] at projected
  rcases history with ⟨state, trace⟩
  cases state with
  | none =>
      obtain ⟨state, _, same⟩ := PMF.support_map .. ▸ projected
      rw [← same]
      rfl
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      change actor = none at inactive
      subst actor
      cases remaining with
      | zero =>
          have same := (PMF.mem_support_pure_iff _ _).mp projected
          rw [same]
      | succ remaining =>
          change final.state ∈ ((scheduler execution.environmentRecall
            (execution.observeEnvironment app)).bind fun command =>
              (execution.environmentStep app command).map fun current =>
                some ⟨remaining, command.actor? app, current⟩).support at projected
          rw [PMF.mem_support_bind_iff] at projected
          obtain ⟨command, _, realized⟩ := projected
          obtain ⟨current, reached, same⟩ := PMF.support_map .. ▸ realized
          rw [← same]
          exact congrFun (app.environmentStep_recall execution current command reached) who

/-- Without a responding actor the actual full-history law uses no player's policy. -/
theorem run_one_inactive_eq
    (first second : ∀ who, (N).BehavioralPolicy who) (history : (E).History)
    (inactive : app.actor history.state = none) :
    (N).runBehavioralFrom first 1 history = (N).runBehavioralFrom second 1 history := by
  classical
  by_cases ended : (E).terminal history.state
  · rw [(N).runBehavioralFrom_of_terminal first 1 ended,
      (N).runBehavioralFrom_of_terminal second 1 ended]
  · rw [(N).runBehavioralFrom_succ_of_not_terminal first 0 ended,
      (N).runBehavioralFrom_succ_of_not_terminal second 0 ended]
    rw [(N).behavioralJoint_congr history.trace ended (fun who =>
      (N).behavioral_eq_of_not_active _ _ history.trace (by
        change ¬ app.actor history.state = some who
        rw [inactive]
        simp))]
    rfl

/-- The complete immutable private-member profile disintegrates through one
actual finite-menu history step. The continuation retains the full history
and every owner's private member, including an arbitrary outer entry tag. -/
theorem run_one_policyMixtures_joint {Memory : Principal → Type} {Result : Type}
    (priors : (who : Principal) → PMF (Memory who))
    (members : (who : Principal) → Memory who → app.Policy)
    (covered : ∀ who memory past view action, action ∈ (members who memory past view).support →
      action ∈ menu.actions who past view)
    (history : (E).History) (next : (E).History → ((who : Principal) → Memory who) → PMF Result) :
    (independentProduct (fun who => (app.policyMixture (priors who) (members who)).posterior
      (app.recallAt who history.state))).bind (fun memories =>
        ((N).runBehavioralFrom (fun who => menu.restrictPolicy initial horizon scheduler who
          (members who (memories who))) 1 history).bind (fun final => next final memories)) =
      ((N).runBehavioralFrom (fun who => menu.restrictPolicy initial horizon scheduler who
        (app.policyMixture (priors who) (members who)).policy) 1 history).bind fun final =>
          (independentProduct (fun who => (app.policyMixture (priors who) (members who)).posterior
            (app.recallAt who final.state))).bind (next final) := by
  classical
  let implementations := fun who => app.policyMixture (priors who) (members who)
  let posterior := fun state : app.ProtocolState => independentProduct (fun who =>
    (implementations who).posterior (app.recallAt who state))
  let profile := fun (memories : (who : Principal) → Memory who) who =>
    menu.restrictPolicy initial horizon scheduler who (members who (memories who))
  let realized := fun who => menu.restrictPolicy initial horizon scheduler who
    (implementations who).policy
  have mixCovered who past view action
      (present : action ∈ ((implementations who).policy past view).support) :
      action ∈ menu.actions who past view := by
    rw [ReactiveApplication.policyMixture_policy, PMF.mem_support_bind_iff] at present
    obtain ⟨memory, _, yes⟩ := present
    exact covered who memory past view action yes
  change (posterior history.state).bind (fun memories =>
    ((N).runBehavioralFrom (profile memories) 1 history).bind (fun final => next final memories)) =
      ((N).runBehavioralFrom realized 1 history).bind fun final =>
        (posterior final.state).bind (next final)
  cases actor : app.actor history.state with
  | none =>
      have same memories := menu.run_one_inactive_eq initial horizon scheduler
        (profile memories) realized history actor
      simp_rw [same]
      rw [PMF.bind_comm]
      apply bind_congr_on_support
      intro final member
      have recalls : posterior history.state = posterior final.state := by
        apply congrArg independentProduct
        funext who
        rw [menu.run_one_inactive_recall initial horizon scheduler realized history actor
          member who]
      rw [recalls]
  | some who =>
      rcases history with ⟨state, trace⟩
      cases state with
      | none => cases actor
      | some control =>
          rcases control with ⟨remaining, active, execution⟩
          change active = some who at actor
          subst active
          obtain ⟨kernel, law, states⟩ := menu.exists_response_history_kernel initial horizon
            scheduler realized who remaining execution trace
          have decoded memories : menu.decodeProfile initial horizon scheduler (profile memories) =
              fun owner => members owner (memories owner) := by
            funext owner
            exact menu.decode_restrictPolicy_of_covered initial horizon scheduler owner _
              (covered owner (memories owner))
          have decodedReal : menu.decodeProfile initial horizon scheduler realized =
              fun owner => (implementations owner).policy := by
            funext owner
            exact menu.decode_restrictPolicy_of_covered initial horizon scheduler owner _
              (mixCovered owner)
          simp_rw [law, decoded, decodedReal, PMF.bind_bind]
          have split := ReactiveApplication.response_action_disintegrate_profile implementations
            execution who (fun action memories =>
              (kernel action).bind fun final => next final memories)
          simp only [implementations, ReactiveApplication.policyMixture, PMF.bind_map,
            Function.comp_def, Function.update_eq_self] at split
          change (posterior (some ⟨remaining, some who, execution⟩)).bind
            (fun memories => (members who (memories who) (execution.recall who)
              (execution.observe app who)).bind fun action =>
                (kernel action).bind fun final => next final memories) = _
          refine split.trans ?_
          apply bind_congr_on_support
          intro action supported
          rw [PMF.bind_comm]
          apply bind_congr_on_support
          intro final reached
          have projected : final.state =
              some ⟨remaining, none, execution.respond app who action⟩ := by
            have stateMember : final.state ∈ ((kernel action).map History.state).support := by
              rw [PMF.support_map]
              exact ⟨final, reached, rfl⟩
            rw [states realized action (decodedReal ▸ supported),
              PMF.mem_support_pure_iff] at stateMember
            exact stateMember
          rw [projected]
          rfl

end Interaction.ReactiveApplication.ResponseMenu
