/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionPolicy
import Vegas.EventGraph.KernelExecution
import Interaction.SealedCandidateRounds

/-! # Honest graph policies across commitment services

The registered and candidate hosts have identical public observations and
commands. Generated policies prepare their canonical handles before submission;
the checked host embedding therefore preserves their full execution law.
Arbitrary candidate deviations are not restricted by this honest-profile result.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Generated commitment packets carry a value already recorded in the
sender's private history and service. This is derived from the graph policy
compiler, not assumed of its messages. -/
private theorem resolvingPolicy_prepared (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player)
    (policy : CommitPolicy G who)
    (execution :
      (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hmemory : SealedResolution.RegistrationMemory
      (supported.resolvingRuntime nullValue window) execution)
    (payload : SealedProgram.Payload Player (L.Val ty))
    (hsubmit : .submit payload ∈
      (supported.resolvingPolicy nullValue window who policy
        (execution.principalHistory who)
        (MessageApplication.State.observe _ execution.native who)).support)
    (serial : Nat) :
    SealedProgram.PreparedSubmission execution.native.application.service
      ⟨(who, serial), payload⟩ := by
  intro site handle hpacket
  change payload = .commitment site handle at hpacket
  rcases supported.resolvingPolicy_submission nullValue window who _ _ _
    payload hsubmit with ⟨node, hcommit, hcache⟩ | ⟨node, actualHandle, value, hopen, _⟩
  · cases hcommit
    cases hpacket
    refine ⟨rfl, ?_⟩
    rw [hmemory who site]
    exact hcache
  · cases hopen
    cases hpacket

/-- The original graph profile's generated policies have exactly the same
full finite execution law in both commitment hosts, under lossless retyping.
The environment is adaptive and may delay, deliver, include, or advance clocks
without a fairness premise. This law includes timeout runs; successful graph
completion additionally requires the driver service conditions. Arbitrary
candidate-player deviations are not covered by the honest-host equality. -/
theorem candidatePolicies_law (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (profile : CommitPolicyProfile G)
    (environment : MessageApplication.EnvironmentPolicy
      (supported.resolvingRuntime nullValue window).messageApplication)
    (schedule : List (@MessageApplication.Invocation Player)) :
    let runtime := supported.resolvingRuntime nullValue window
    (runtime.messageApplication.runPolicies
        (fun who => supported.resolvingPolicy nullValue window who (profile who))
        environment schedule
        (MessageApplication.PolicyExecution.initial _ (MessageApplication.State.initial _
          runtime.initial))).map runtime.candidateExecution =
      runtime.candidateApplication.runPolicies
        (fun who => runtime.candidatePlayerPolicy
          (supported.resolvingPolicy nullValue window who (profile who)))
        (runtime.candidateEnvironmentPolicy environment) schedule
        (MessageApplication.PolicyExecution.initial _ (MessageApplication.State.initial _
          runtime.candidateInitial)) := by
  intro runtime
  exact runtime.runPolicies_candidates _ environment (by
    intro execution who payload hmemory hsubmit serial
    exact supported.resolvingPolicy_prepared nullValue window who (profile who)
      execution hmemory payload hsubmit serial) schedule _
    SealedResolution.PreparedExecution.initial

/-- Exact honest execution law for the common stopped-round driver. The two
hosts execute the same roster, wire opportunities, boundary clocks, and
completion test. This equality does not require fairness or completion. -/
theorem candidateRounds_law (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots : Nat)
    (profile : CommitPolicyProfile G)
    (wire : MessageApplication.WirePolicy
      (supported.resolvingRuntime nullValue window).messageApplication)
    (count : Nat) :
    let runtime := supported.resolvingRuntime nullValue window
    (runtime.roundDriver.runRounds principals serviceSlots
        (fun who => supported.resolvingPolicy nullValue window who (profile who))
        wire count
        (MessageApplication.PolicyExecution.initial _ (MessageApplication.State.initial _
          runtime.initial))).map runtime.candidateExecution =
      runtime.candidateRoundDriver.runRounds principals serviceSlots
        (fun who => runtime.candidatePlayerPolicy
          (supported.resolvingPolicy nullValue window who (profile who)))
        (runtime.candidateWirePolicy wire) count
        (MessageApplication.PolicyExecution.initial _ (MessageApplication.State.initial _
          runtime.candidateInitial)) := by
  intro runtime
  exact runtime.runRounds_candidates principals serviceSlots _ wire (by
    intro execution who payload hmemory hsubmit serial
    exact supported.resolvingPolicy_prepared nullValue window who (profile who)
      execution hmemory payload hsubmit serial) count _
    SealedResolution.PreparedExecution.initial

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidatePolicies_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidatePolicies_law
