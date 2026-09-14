/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidatePolicyEmbedding
import Interaction.SealedResolutionRounds

/-! # Candidate commitments in the shared stopped round driver

Both commitment hosts use the same roster, adaptive wire opportunities,
boundary clock command, and public completion test. Honest preparation
discipline yields an exact embedding through actual early stopping.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- The same operational driver instantiated with the candidate service. -/
abbrev candidateRoundDriver (runtime : SealedResolution Principal Value) :
    RoundDriver runtime.candidateApplication :=
  runtime.hostRoundDriver (Service := CommitmentCandidates Principal Nat Value)
    (fun state owner slot value => state.prepare owner slot value) runtime.candidateHandle

def candidateWirePolicy (runtime : SealedResolution Principal Value)
    (wire : runtime.messageApplication.WirePolicy) : runtime.candidateApplication.WirePolicy :=
  fun history view => wire
    (history.map fun entry =>
      ⟨⟨entry.beforeView.pool, entry.beforeView.application, entry.beforeView.receipts⟩,
        runtime.registeredEnvironmentCommand entry.command⟩)
    ⟨view.pool, view.application, view.receipts⟩

theorem candidateWirePolicy_surjective (runtime : SealedResolution Principal Value) :
    Function.Surjective runtime.candidateWirePolicy := by
  intro wire
  refine ⟨fun history view => wire
    (history.map fun entry =>
      ⟨⟨entry.beforeView.pool, entry.beforeView.application, entry.beforeView.receipts⟩,
        runtime.candidateEnvironmentCommand entry.command⟩)
    ⟨view.pool, view.application, view.receipts⟩, ?_⟩
  have hcommand : ∀ command : runtime.candidateApplication.EnvironmentPolicyCommand,
      runtime.candidateEnvironmentCommand
        (runtime.registeredEnvironmentCommand command) = command := by
    intro command
    cases command <;> rfl
  have hentry : ∀ entry : runtime.candidateApplication.EnvironmentEntry,
      (⟨⟨entry.beforeView.pool, entry.beforeView.application, entry.beforeView.receipts⟩,
        entry.command⟩ : runtime.candidateApplication.EnvironmentEntry) = entry := by
    intro ⟨⟨_, _, _⟩, _⟩
    rfl
  funext history view
  cases view
  simp only [candidateWirePolicy, List.map_map, Function.comp_def, hcommand, hentry,
    List.map_id_fun', id_eq]

private theorem candidate_wireEnvironment (runtime : SealedResolution Principal Value)
    (wire : runtime.messageApplication.WirePolicy) :
    runtime.candidateApplication.wireEnvironment (runtime.candidateWirePolicy wire) =
      runtime.candidateEnvironmentPolicy (runtime.messageApplication.wireEnvironment wire) := by
  funext history view
  simp only [wireEnvironment, candidateWirePolicy, candidateEnvironmentPolicy,
    FinDist.map_comp, Function.comp_def]
  congr 1
  funext command
  cases command <;> rfl

private theorem round_candidates (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy)
    (hsubmit : ∀ execution who payload,
      RegistrationMemory runtime execution →
      .submit payload ∈ (players who (execution.principalHistory who)
        (State.observe _ execution.native who)).support →
      ∀ serial, SealedProgram.PreparedSubmission execution.native.application.service
        ⟨(who, serial), payload⟩)
    (execution : runtime.messageApplication.PolicyExecution)
    (h : PreparedExecution runtime execution) :
    (runtime.roundDriver.round principals serviceSlots players wire execution).map
        runtime.candidateExecution =
      runtime.candidateRoundDriver.round principals serviceSlots
        (fun who => runtime.candidatePlayerPolicy (players who)) (runtime.candidateWirePolicy wire)
        (runtime.candidateExecution execution) := by
  simp only [RoundDriver.round, runtime.candidate_wireEnvironment wire,
    ← runtime.runPolicies_candidates players (runtime.messageApplication.wireEnvironment wire)
      hsubmit _ execution h, FinDist.map_bind, FinDist.bind_map]
  apply FinDist.bind_congr
  intro next hnext
  exact (runtime.environmentPolicyStep_candidates next
    (runtime.runPolicies_prepared players _ hsubmit _ execution next h hnext)
    (.application ⟨()⟩)).symm

/-- Exact stopped-round execution law for the prepared-message embedding.
The budget can end before completion, and clocks can resolve timeouts; neither
successful completion nor fairness is assumed by this operational equality. -/
theorem runRounds_candidates (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy)
    (hsubmit : ∀ execution who payload,
      RegistrationMemory runtime execution →
      .submit payload ∈ (players who (execution.principalHistory who)
        (State.observe _ execution.native who)).support →
      ∀ serial, SealedProgram.PreparedSubmission execution.native.application.service
        ⟨(who, serial), payload⟩)
    (count : Nat) (execution : runtime.messageApplication.PolicyExecution)
    (h : PreparedExecution runtime execution) :
    (runtime.roundDriver.runRounds principals serviceSlots players wire count execution).map
        runtime.candidateExecution =
      runtime.candidateRoundDriver.runRounds principals serviceSlots
        (fun who => runtime.candidatePlayerPolicy (players who)) (runtime.candidateWirePolicy wire)
        count (runtime.candidateExecution execution) := by
  apply runtime.roundDriver.runRounds_map runtime.candidateRoundDriver principals serviceSlots
    players wire _ _ runtime.candidateExecution (PreparedExecution runtime)
    (fun _ _ => rfl) (fun _ h => runtime.round_candidates principals serviceSlots players wire
      hsubmit _ h) ?_ count execution h
  intro current next hcurrent hnext
  simp only [RoundDriver.round, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  have hprepared := runtime.runPolicies_prepared players _ hsubmit _ current middle hcurrent hmiddle
  exact hprepared.environmentStep middle next (.application ⟨()⟩) hnext

end Interaction.SealedResolution
