/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageApplication
import Interaction.MessageApplicationPolicyLaws

/-! # Candidate-catalog transition laws

Checked public laws for verification-facing proofs. These expose exactly how
native graph transitions affect commitment candidates without requiring
downstream invariants to unfold the application handler or clock driver.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

@[simp] theorem privateStep_prepare_candidates
    (runtime : GraphRuntime Player L Δ) (state : State Player L Δ)
    (who : Player) (slot : Nat) (raw : Raw L) :
    (runtime.privateStep state who (.prepare slot raw)).candidates =
      state.candidates.prepare who (.prepared slot) raw := by
  cases state
  rfl

@[simp] theorem privateStep_rememberDisclosure_candidates
    (runtime : GraphRuntime Player L Δ) (state : State Player L Δ)
    (who : Player) (disclose : Bool) :
    (runtime.privateStep state who (.rememberDisclosure disclose)).candidates =
      state.candidates := by
  rfl

/-- Clock service never changes commitment meanings, including when it moves
to a graph suffix by sampling or deadline expiry. -/
theorem tick_candidates
    (runtime : GraphRuntime Player L Δ) (state next : State Player L Δ)
    (supported : next ∈ (runtime.tick state).support) :
    next.candidates = state.candidates := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases graph with
      | ret payoffs =>
          simp only [tick, FinDist.mem_support_pure] at supported
          subst next
          rfl
      | sample name fresh law tail =>
          simp only [tick, FinDist.support_map, Set.mem_image] at supported
          obtain ⟨value, _, rfl⟩ := supported
          rfl
      | bind name owner fresh tail =>
          simp only [tick] at supported
          split at supported <;> simp only [FinDist.mem_support_pure] at supported <;>
            subst next <;> rfl
      | resolve output owner binding fresh source checks tail =>
          simp only [tick] at supported
          split at supported <;> simp only [FinDist.mem_support_pure] at supported <;>
            subst next <;> rfl

/-- An accepted binding commitment applies `accept` to its advertised handle.
Every accepted disclosure packet leaves the candidate catalog unchanged. -/
theorem handle_candidates
    (runtime : GraphRuntime Player L Δ) (state next : State Player L Δ)
    (message : Message Player (Payload Player L))
    (accepted : runtime.handle state message = some next) :
    next.candidates = match message.payload with
      | .commitment _ handle => state.candidates.accept handle
      | .opening .. | .withhold _ | .malformed _ => state.candidates := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases message with
      | mk id payload =>
          cases graph with
          | ret => simp [handle] at accepted
          | sample => simp [handle] at accepted
          | bind name owner fresh tail =>
              cases payload <;> simp only [handle] at accepted
              · split_ifs at accepted
                cases accepted
                rfl
              all_goals contradiction
          | resolve output owner binding fresh source checks tail =>
              cases payload with
              | commitment | malformed => simp [handle] at accepted
              | opening site candidate raw =>
                  simp only [handle] at accepted
                  split_ifs at accepted
                  cases typed : raw.as? _ with
                  | none => rw [typed] at accepted; contradiction
                  | some encoded =>
                      rw [typed] at accepted
                      cases accepted
                      rfl
              | withhold site =>
                  simp only [handle] at accepted
                  split_ifs at accepted
                  cases accepted
                  rfl

/-- Binding admission checks that the candidate belongs to the authenticated
sender; merely naming another principal's slot cannot accept it. -/
theorem handle_commitment_sender (runtime : GraphRuntime Player L Δ)
    (state next : State Player L Δ) (message : Message Player (Payload Player L))
    (site : Nat) (candidate : Handle Player)
    (payload : message.payload = .commitment site candidate)
    (accepted : runtime.handle state message = some next) :
    candidate.1 = message.sender := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases graph with
      | ret | sample | resolve => simp [handle, payload] at accepted
      | bind name owner fresh tail =>
          simp only [handle, payload] at accepted
          split_ifs at accepted with authorized
          simp only [Bool.and_eq_true, decide_eq_true_eq] at authorized
          exact authorized.2.trans authorized.1.2.symm

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
    (players := players) (environment := environment) (schedule := schedule)
    (execution := execution) (next := next)
  · intro state who command valid
    cases command with
    | prepare slot value =>
        change (runtime.privateStep state who (.prepare slot value)).candidates.verify
          handle raw = true
        rw [runtime.privateStep_prepare_candidates, CommitmentCandidates.verify_eq_true_iff]
        have lookup := (state.candidates.verify_eq_true_iff handle raw).mp valid
        rw [state.candidates.lookup_prepare_eq_of_not_fresh handle who (.prepared slot) value
          (by rw [lookup]; simp), lookup]
    | rememberDisclosure disclose => exact valid
  · intro state message after valid accepted
    rw [runtime.handle_candidates state after message accepted]
    cases message.payload with
    | commitment site candidate =>
        exact (state.candidates.verify_accept candidate handle raw).trans valid
    | opening | withhold | malformed => exact valid
  · intro state command after valid happened
    cases command
    rw [runtime.tick_candidates state after happened]
    exact valid
  · exact verified
  · exact supported

end Vegas.GraphRuntime
