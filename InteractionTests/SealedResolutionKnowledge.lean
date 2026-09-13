/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionCoupling

/-! # Hiding against an adaptive principal and full-pool environment

The honest principal privately registers and repeatedly publishes its opaque
handle. The other principal may run any randomized native policy, including
malformed messages, opening guesses, and replay. The environment may randomize
over delivery, inclusion, and clock commands using all pending payloads.
The joint adversary/environment observation law is independent of the sealed
value. Withholding and timeout resolution remain present in the actual runner.
-/

noncomputable section

namespace InteractionTests.SealedResolutionKnowledge

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

def runtime : SealedResolution Bool (Option Bool) :=
  ⟨⟨[⟨.commit false, []⟩, ⟨.reveal false 0, [0]⟩,
      ⟨.commit true, []⟩, ⟨.reveal true 2, [0, 2]⟩]⟩, none, 2⟩

abbrev app := runtime.messageApplication

def honestCommand (value : Option Bool) (history : List app.PlayerEntry) : app.PlayerCommand :=
  if history.isEmpty then .privateCommand ⟨(0, value)⟩
  else .submit (.commitment 0 (false, 0))

def players (value : Option Bool)
    (deviator : app.PlayerPolicy) : Bool → app.PlayerPolicy
  | false => fun history _ => FinDist.pure (honestCommand value history)
  | true => deviator

def observation (execution : app.PolicyExecution) :=
  (execution.principalHistory true, State.observe app execution.native true,
    execution.environmentHistory, State.environmentView app execution.native)

/-- This finite-run information-flow instance imposes no restriction on the
adversary's commands or on the randomized environment's inspection of the pool. -/
theorem hidden_value_law (leftValue rightValue : Option Bool)
    (deviator : app.PlayerPolicy)
    (environment : app.EnvironmentPolicy) (schedule : List (@Invocation Bool)) :
    (app.runPolicies (players leftValue deviator) environment schedule
        (PolicyExecution.initial app (State.initial app runtime.initial))).map observation =
      (app.runPolicies (players rightValue deviator) environment schedule
        (PolicyExecution.initial app (State.initial app runtime.initial))).map observation := by
  have hlaw := SealedResolution.firstRelease_observation_law (runtime := runtime)
    (known := fun handle => handle.1 = true)
    (players leftValue deviator) (players rightValue deviator) environment (fun _ => false)
    observation (fun _ _ _ => rfl) ?_ ?_ schedule _ _ SealedResolution.ExecutionRelated.initial
  · have hlast : PolicyTrace.firstRelease (app := app) (fun _ => false) = PolicyTrace.last := by
      funext trace
      exact trace.firstRelease_false_eq_last
    simpa only [hlast, app.tracePolicies_last] using hlaw
  · intro left right related
    have hh := (related.histories true).eq (fun _ => rfl)
    simp only [observation, hh, related.native.observe_eq true,
      related.environmentHistory, related.native.environmentView_eq]
  · intro left right related _ who
    cases who with
    | false =>
        have hlength := (related.histories false).length_eq
        have hempty : (left.principalHistory false).isEmpty =
            (right.principalHistory false).isEmpty := by
          cases hl : left.principalHistory false <;>
            cases hr : right.principalHistory false <;> simp_all
        refine ⟨FinDist.pure (honestCommand leftValue (left.principalHistory false),
          honestCommand rightValue (right.principalHistory false)),
          by simp only [players, FinDist.map_pure],
          by simp only [players, FinDist.map_pure], ?_⟩
        intro pair hpair
        simp only [FinDist.mem_support_pure] at hpair
        subst pair
        refine ⟨?_, ?_⟩
        · unfold honestCommand
          rw [← hempty]
          split
          · exact ⟨rfl, fun h => False.elim (Bool.false_ne_true h)⟩
          · rfl
        · intro payload hp
          unfold honestCommand at hp
          split at hp
          · cases hp
          · cases hp
            trivial
    | true =>
        have hh := (related.histories true).eq (fun _ => rfl)
        have hv := related.native.observe_eq true
        refine ⟨(deviator (left.principalHistory true) (State.observe app left.native true)).map
          (fun command => (command, command)), ?_, ?_, ?_⟩
        · simp only [players, FinDist.map_comp, Function.comp_def]
          exact (FinDist.map_id _).symm
        · simp only [players, FinDist.map_comp, Function.comp_def, hh, hv]
          exact (FinDist.map_id _).symm
        · intro pair hpair
          rw [FinDist.support_map] at hpair
          obtain ⟨command, _, rfl⟩ := hpair
          refine ⟨SealedProgram.CommandAgreement.refl _ true, ?_⟩
          intro payload _
          cases payload with
          | commitment | cleartext | malformed => trivial
          | opening => exact fun h => h.symm

end InteractionTests.SealedResolutionKnowledge

/-- info: 'InteractionTests.SealedResolutionKnowledge.hidden_value_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractionTests.SealedResolutionKnowledge.hidden_value_law
