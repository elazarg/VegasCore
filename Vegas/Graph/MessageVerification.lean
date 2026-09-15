/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageApplication
import Interaction.MessageApplicationPolicyLaws

/-! # Persistence of graph-host verification material

Arbitrary native traffic cannot alter an already openable commitment. This
includes preparations by its owner, acceptance of competing handles, and all
deadline and chance transitions. The statement is about the actual runner,
not only the candidate catalog in isolation.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable {Δ : VCtx Player L}

private theorem privateStep_verification (runtime : GraphRuntime Player L Δ)
    (handle : Handle Player) (raw : Raw L) (state : State Player L Δ)
    (who : Player) (command : PrivateCommand L)
    (verified : state.candidates.verify handle raw = true) :
    (runtime.privateStep state who command).candidates.verify handle raw = true := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases command with
      | rememberDisclosure => exact verified
      | prepare slot value =>
          have lookup := (candidates.verify_eq_true_iff handle raw).mp verified
          apply (CommitmentCandidates.verify_eq_true_iff ..).mpr
          change (candidates.prepare who (.prepared slot) value).lookup handle = _
          rw [candidates.lookup_prepare_eq_of_not_fresh handle who (.prepared slot) value
            (by rw [lookup]; simp), lookup]

private theorem handle_verification (runtime : GraphRuntime Player L Δ)
    (handle : Handle Player) (raw : Raw L) (state : State Player L Δ)
    (message : Message Player (Payload Player L)) (next : State Player L Δ)
    (verified : state.candidates.verify handle raw = true)
    (accepted : runtime.handle state message = some next) :
    next.candidates.verify handle raw = true := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases graph with
      | ret | sample => cases message.payload <;> simp [GraphRuntime.handle] at accepted
      | bind name owner fresh tail =>
          cases packet : message.payload <;> simp only [GraphRuntime.handle, packet] at accepted
          · split_ifs at accepted
            cases accepted
            exact (candidates.verify_accept _ handle raw).trans verified
          all_goals contradiction
      | resolve output owner binding fresh source checks tail =>
          cases packet : message.payload with
          | commitment | malformed => simp [GraphRuntime.handle, packet] at accepted
          | withhold site =>
              simp only [GraphRuntime.handle, packet] at accepted
              split_ifs at accepted
              cases accepted
              exact verified
          | opening site candidate opening =>
              simp only [GraphRuntime.handle, packet] at accepted
              split_ifs at accepted
              cases typed : opening.as? _ with
              | none => rw [typed] at accepted; contradiction
              | some encoded => rw [typed] at accepted; cases accepted; exact verified

private theorem environmentStep_verification (runtime : GraphRuntime Player L Δ)
    (handle : Handle Player) (raw : Raw L) (state : State Player L Δ)
    (command : EnvironmentCommand) (next : State Player L Δ)
    (verified : state.candidates.verify handle raw = true)
    (supported : next ∈ (runtime.environmentStep state command).support) :
    next.candidates.verify handle raw = true := by
  cases command
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases graph with
      | ret =>
          simp only [environmentStep, tick, FinDist.mem_support_pure] at supported
          subst next
          exact verified
      | sample =>
          simp only [environmentStep, tick, FinDist.support_map, Set.mem_image] at supported
          obtain ⟨value, _, rfl⟩ := supported
          exact verified
      | bind | resolve =>
          simp only [environmentStep, tick] at supported
          split at supported <;>
            simp only [FinDist.mem_support_pure] at supported <;>
            subst next <;> exact verified

/-- Once an opening verifies, every supported policy-driven continuation
retains that exact verifier, even when all players and the environment deviate. -/
theorem runPolicies_preserves_verification (runtime : GraphRuntime Player L Δ)
    (handle : Handle Player) (raw : Raw L)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (verified : execution.native.application.candidates.verify handle raw = true)
    (supported : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    next.native.application.candidates.verify handle raw = true := by
  apply runtime.application.runPolicies_application_invariant
    (fun state => state.candidates.verify handle raw = true)
    (privateStep_verification runtime handle raw)
    (handle_verification runtime handle raw)
    (environmentStep_verification runtime handle raw)
    players environment schedule execution next verified supported

end Vegas.GraphRuntime
