/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionPolicy
import Interaction.SealedCandidateRounds

/-! # Source policies hosted by the candidate commitment service

The generated rules and honest policy code are unchanged. The candidate host
has a different private application-state type, but the player's command,
observation, and history components are identical. The policy translation
below only reconstructs these records at the registered host's carrier type;
it neither queries the candidate catalog nor erases observable input.

Arbitrary replacements are policies of the candidate host, with its additional
candidate-selection behavior. Their strategic simulation does not follow from
this lossless retyping of the honest policy.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- The original sample-once sealed policy running in the candidate host.
All visible components are retained; no private host state is an input. -/
def compileCandidatePolicy (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player)
    (policy : SourceBehavioralPolicy source.core.prog who) :
    (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy :=
  (compilation.supported.resolvingRuntime nullValue window).candidatePlayerPolicy
    (compilation.compileResolvingPolicy nullValue window who policy)

/-- Changing commitment service does not introduce a cleartext commitment
optimization into the generated honest policies. -/
theorem compileCandidatePolicy_no_cleartext (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player)
    (policy : SourceBehavioralPolicy source.core.prog who)
    (history : List
      (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry)
    (view : (compilation.supported.resolvingRuntime nullValue window).candidateApplication.View)
    (node : Nat) (value : L.Val ty) :
    .submit (.cleartext node value) ∉
      (compilation.compileCandidatePolicy nullValue window who policy history view).support :=
  compilation.supported.resolvingPolicy_no_cleartext nullValue window who _ _ _ node value

/-- Generated commitment packets carry a value already recorded in the
sender's private history and service. This is derived from the source policy
compiler, not assumed of its messages. -/
private theorem compileResolvingPolicy_prepared (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player)
    (policy : SourceBehavioralPolicy source.core.prog who)
    (execution :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hmemory : SealedResolution.RegistrationMemory
      (compilation.supported.resolvingRuntime nullValue window) execution)
    (payload : SealedProgram.Payload Player (L.Val ty))
    (hsubmit : .submit payload ∈
      (compilation.compileResolvingPolicy nullValue window who policy
        (execution.principalHistory who)
        (MessageApplication.State.observe _ execution.native who)).support)
    (serial : Nat) :
    SealedProgram.PreparedSubmission execution.native.application.service
      ⟨(who, serial), payload⟩ := by
  intro site handle hpacket
  change payload = .commitment site handle at hpacket
  rcases compilation.supported.resolvingPolicy_submission nullValue window who _ _ _
    payload hsubmit with ⟨node, hcommit, hcache⟩ | ⟨node, actualHandle, value, hopen, _⟩
  · cases hcommit
    cases hpacket
    refine ⟨rfl, ?_⟩
    rw [hmemory who site]
    exact hcache
  · cases hopen
    cases hpacket

/-- The original source profile's generated policies have exactly the same
full finite execution law in both commitment hosts, under lossless retyping.
The environment is adaptive and may delay, deliver, include, or advance clocks
without a fairness premise. This law includes timeout runs; successful source
completion additionally requires the driver service conditions. Arbitrary
candidate-player deviations are not covered by the honest-host equality. -/
theorem candidatePolicies_law (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (profile : SourceBehavioralProfile source.core.prog)
    (environment : MessageApplication.EnvironmentPolicy
      (compilation.supported.resolvingRuntime nullValue window).messageApplication)
    (schedule : List (@MessageApplication.Invocation Player)) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    (runtime.messageApplication.runPolicies
        (fun who => compilation.compileResolvingPolicy nullValue window who (profile who))
        environment schedule
        (MessageApplication.PolicyExecution.initial _ (MessageApplication.State.initial _
          runtime.initial))).map runtime.candidateExecution =
      runtime.candidateApplication.runPolicies
        (fun who => compilation.compileCandidatePolicy nullValue window who (profile who))
        (runtime.candidateEnvironmentPolicy environment) schedule
        (MessageApplication.PolicyExecution.initial _ (MessageApplication.State.initial _
          runtime.candidateInitial)) := by
  intro runtime
  exact runtime.runPolicies_candidates _ environment (by
    intro execution who payload hmemory hsubmit serial
    exact compilation.compileResolvingPolicy_prepared nullValue window who (profile who)
      execution hmemory payload hsubmit serial) schedule _
    SealedResolution.PreparedExecution.initial

/-- Exact honest execution law for the common stopped-round driver. The two
hosts execute the same roster, wire opportunities, boundary clocks, and
completion test. This equality does not require fairness or completion. -/
theorem candidateRounds_law (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots : Nat)
    (profile : SourceBehavioralProfile source.core.prog)
    (wire : MessageApplication.WirePolicy
      (compilation.supported.resolvingRuntime nullValue window).messageApplication)
    (count : Nat) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    (runtime.roundDriver.runRounds principals serviceSlots
        (fun who => compilation.compileResolvingPolicy nullValue window who (profile who))
        wire count
        (MessageApplication.PolicyExecution.initial _ (MessageApplication.State.initial _
          runtime.initial))).map runtime.candidateExecution =
      runtime.candidateRoundDriver.runRounds principals serviceSlots
        (fun who => compilation.compileCandidatePolicy nullValue window who (profile who))
        (runtime.candidateWirePolicy wire) count
        (MessageApplication.PolicyExecution.initial _ (MessageApplication.State.initial _
          runtime.candidateInitial)) := by
  intro runtime
  exact runtime.runRounds_candidates principals serviceSlots _ wire (by
    intro execution who payload hmemory hsubmit serial
    exact compilation.compileResolvingPolicy_prepared nullValue window who (profile who)
      execution hmemory payload hsubmit serial) count _
    SealedResolution.PreparedExecution.initial

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.candidatePolicies_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidatePolicies_law
