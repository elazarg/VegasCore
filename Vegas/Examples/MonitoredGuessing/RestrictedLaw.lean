/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.RestrictedValues
import Vegas.Examples.MonitoredGuessing.RestrictedSourceValues
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Joint initial-type, result and net-payoff preservation

The equality holds for every source profile. Both runtime liabilities vanish on
its restricted compilation, so the recorded payoff vector is the declared one.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def nativePayoffObservation (table : PayoffTable) (state : nativeApp.ProtocolState) :
    Bool × Results × (Player → ℝ) :=
  state.elim (false, ⟨.failure, .failure⟩, fun _ => 0) (fun control =>
    (observedAliceBit (control.execution.observe nativeApp alice),
      nativeResults control.execution.application.config,
      Enforcement.executionUtility table control.execution))

theorem nativePayoffObservation_normalization (table : PayoffTable)
    (state : nativeApp.ProtocolState) :
    nativePayoffObservation table (normalization.state state) =
      nativePayoffObservation table state := by
  cases state <;> rfl

def sourcePayoffObservation (table : PayoffTable) : sourceArena.State →
    Bool × Results × (Player → ℝ)
  | some (.inr (.inr config)) =>
      ((config.state.get (.there (.there .here))).getD false,
        sourceResults config.state, tableReward table (sourceResults config.state))
  | _ => (false, ⟨.failure, .failure⟩, fun _ => 0)

def decisionObservation (table : PayoffTable) (bit guess disclose : Bool) :
    Bool × Results × (Player → ℝ) :=
  (bit, decisionResult bit guess disclose, tableReward table (decisionResult bit guess disclose))

theorem source_done_payoff_observation (table : PayoffTable) (bit guess disclose : Bool) :
    sourcePayoffObservation table (SourcePath.done bit guess disclose).state =
      decisionObservation table bit guess disclose := by
  cases bit <;> cases guess <;> cases disclose <;> rfl

theorem alice_service_observation (table : PayoffTable) (players : Player → nativeApp.Policy)
    (bit guess disclose : Bool) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
      ((beforeAlice bit guess).respond nativeApp alice
        (choiceAction alicePublication aliceHandle bit disclose))).map
          (fun final => nativePayoffObservation table (nativeApp.finished final)) =
      PMF.pure (decisionObservation table bit guess disclose) := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro outcome supported
  obtain ⟨final, reached, rfl⟩ := PMF.support_map .. ▸ supported
  have payoffLaw := Enforcement.alice_service_payoff_law table players bit guess disclose
  rw [source_results] at payoffLaw
  have paired : (nativeResults final.application.config,
      Enforcement.executionUtility table final) =
        (decisionResult bit guess disclose,
          tableReward table (decisionResult bit guess disclose)) := by
    apply (PMF.mem_support_pure_iff _ _).mp
    have mapped : (nativeResults final.application.config,
        Enforcement.executionUtility table final) ∈
        ((nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
          ((beforeAlice bit guess).respond nativeApp alice
            (choiceAction alicePublication aliceHandle bit disclose))).map
              (fun final => (nativeResults final.application.config,
                Enforcement.executionUtility table final))).support := by
      rw [PMF.support_map]
      exact ⟨final, reached, rfl⟩
    exact payoffLaw ▸ mapped
  have fixed := resolution_plan_invariant players _ (native_fixed_invariant bit) _ _ final
    ((native_fixed_invariant bit).respond (beforeAlice bit guess) alice _
      (before_alice_fixed bit guess)) reached
  change (observedAliceBit (final.observe nativeApp alice), nativeResults final.application.config,
    Enforcement.executionUtility table final) = _
  rw [native_observed_alice_bit bit final fixed]
  exact congrArg (Prod.mk bit) paired

theorem bob_choice_observation (table : PayoffTable)
    (profile : Profile restrictedModel.behavioralSignature) (bit guess : Bool) :
    (nativeRuntime.runInteractionPlan nativeLeaks
      (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile)
      nativeNetwork
      ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication, .player alice] ++ resolutionTail)
      ((quietBob bit).respond nativeApp bob
        (choiceAction bobPublication bobHandle true guess))).map
          (fun final => nativePayoffObservation table (nativeApp.finished final)) =
      (targetDisclosures profile bit guess).map (decisionObservation table bit guess) := by
  rw [runInteractionPlan_append, bob_to_alice, decoded_alice_response, PMF.map_comp,
    PMF.bind_map, PMF.map_bind, ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro disclose _
  exact alice_service_observation table _ bit guess disclose

theorem bob_finish_observation (table : PayoffTable)
    (profile : Profile restrictedModel.behavioralSignature) (bit : Bool) :
    (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
      (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile)
      (some ⟨9, some bob, quietBob bit⟩)).map (nativePayoffObservation table) =
      (targetGuesses profile).bind fun guess =>
        (targetDisclosures profile bit guess).map (decisionObservation table bit guess) := by
  have finish := native_finish_response
    (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile)
    [.player alice, .player watcher, .wire, .grant bobPublication]
    ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
      .grant alicePublication, .player alice] ++ resolutionTail) bob rfl (quietBob bit) rfl
  change nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler _
    (some ⟨9, some bob, quietBob bit⟩) = _ at finish
  rw [finish, decoded_bob_response, PMF.bind_map, PMF.map_bind]
  apply bind_congr_on_support _
  intro guess _
  rw [Function.comp_apply, PMF.map_comp]
  exact bob_choice_observation table profile bit guess

theorem finish_quiet (profile : Profile restrictedModel.behavioralSignature) :
    nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
      (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile) none =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
          (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile)
          (some ⟨9, some bob, quietBob bit⟩) := by
  have prefixLaw := bob_prefix_law profile
  rw [InformationModel.runBehavioral, restrictedMenu.run_map_controlStep] at prefixLaw
  change ((fun law => law.bind (nativeApp.controlStep nativeInitialLaw nativeHorizon
    nativeScheduler (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
      profile)))^[8] (PMF.pure none)) = _ at prefixLaw
  have stopped := nativeApp.finish_after_steps nativeInitialLaw nativeHorizon nativeScheduler
    (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile)
    8 (PMF.pure none)
  rw [prefixLaw, PMF.bind_map, PMF.pure_bind] at stopped
  exact stopped.symm

theorem initialized_observation (table : PayoffTable)
    (profile : Profile restrictedModel.behavioralSignature) :
    ((restrictedModel.runBehavioral profile (2 * nativeHorizon + 1)).map History.state).map
      (nativePayoffObservation table) =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (targetGuesses profile).bind fun guess =>
          (targetDisclosures profile bit guess).map (decisionObservation table bit guess) := by
  rw [InformationModel.runBehavioral,
    restrictedMenu.run_eq_finish nativeInitialLaw nativeHorizon nativeScheduler profile
      (2 * nativeHorizon + 1) restrictedArena.initHistory (by rfl)]
  change (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler _ none).map _ = _
  rw [finish_quiet, PMF.map_bind]
  apply bind_congr_on_support _
  intro bit _
  exact bob_finish_observation table profile bit

/-- The fixed playerwise policy translation preserves the initial type jointly
with public results and the entire actually charged payoff vector. -/
theorem compile_joint_law (table : PayoffTable)
    (profile : Profile sourceModel.behavioralSignature) :
    ((sourceModel.runBehavioral profile 3).map History.state).map
        (sourcePayoffObservation table) =
      ((restrictedModel.runBehavioral (compile profile) (2 * nativeHorizon + 1)).map
        History.state).map (nativePayoffObservation table) := by
  rw [source_initialized_states_all, initialized_observation]
  simp only [compile, targetGuesses_responseProfile, targetDisclosures_responseProfile,
    PMF.map_bind, PMF.map_comp, Function.comp_def, source_done_payoff_observation]

end Vegas.Examples.MonitoredGuessing.Restricted
