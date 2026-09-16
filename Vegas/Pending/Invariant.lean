/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.Application
import Interaction.MessageApplicationLaws
import Interaction.MessageApplicationPolicyLaws

/-! # Public-state invariants for the graph message host -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L] {Δ : VCtx Player L}

namespace State

/-- The concrete public store is exactly the public projection of the ideal
typed environment at the same graph prefix. -/
def PublicAgreement : State Player L Δ → Prop
  | .running (Γ := Γ) _ ideal publicValues _ _ _ _ _ =>
      (publicValues : PublicValues Γ) =
        (PublicValues.ofVEnv ideal : PublicValues Γ)

theorem initial_publicAgreement {Γ : VCtx Player L} (graph : Vegas.Graph Player L Γ Δ)
    (input : VEnv L Γ) : (State.initial graph input).PublicAgreement := by
  rfl

end State

theorem privateStep_preserves_publicAgreement (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) (who : Player) (command : PrivateCommand L)
    (agreement : state.PublicAgreement) :
    (runtime.privateStep state who command).PublicAgreement := by
  cases state with
  | running next ideal values bindings candidates pc clock enteredAt =>
      cases command <;> exact agreement

private theorem advanceBind_publicAgreement
    {Γ : VCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (next : Vegas.Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (pc clock : Nat)
    (handle : Handle Player)
    (agreement : (values : PublicValues Γ) =
      (PublicValues.ofVEnv ideal : PublicValues Γ)) :
    (advanceBind next ideal values bindings candidates pc clock handle).PublicAgreement := by
  simp only [advanceBind, State.PublicAgreement, PublicValues.ofVEnv_cons_sealed]
  exact congrArg PublicValues.consSealed agreement

private theorem advanceResolve_publicAgreement
    {Γ : VCtx Player L} {outputName : VarId} {payload : L.Ty}
    (next : Vegas.Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (pc clock : Nat)
    (result : PublicationResult (L.Val payload))
    (agreement : (values : PublicValues Γ) =
      (PublicValues.ofVEnv ideal : PublicValues Γ)) :
    (advanceResolve next ideal values bindings candidates pc clock result).PublicAgreement := by
  simp only [advanceResolve, State.PublicAgreement, PublicValues.ofVEnv_cons_public]
  exact congrArg (PublicValues.consPublic ((R.valueEquiv _).symm result)) agreement

/-- Every admitted authenticated message preserves agreement between concrete
public values and the ideal environment. -/
theorem handle_preserves_publicAgreement (runtime : GraphRuntime Player L Δ)
    (state nextState : State Player L Δ) (message : Message Player (Payload Player L))
    (agreement : state.PublicAgreement)
    (accepted : runtime.handle state message = some nextState) :
    nextState.PublicAgreement := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases message with
      | mk id payload =>
        cases graph with
        | ret payoffs => cases payload <;> simp [GraphRuntime.handle] at accepted
        | sample name fresh law next => cases payload <;> simp [GraphRuntime.handle] at accepted
        | bind name owner fresh next =>
            cases payload with
            | commitment site handle =>
                simp only [GraphRuntime.handle] at accepted
                split_ifs at accepted
                · cases accepted
                  exact advanceBind_publicAgreement next ideal values bindings candidates
                    pc clock handle agreement
            | opening => simp [GraphRuntime.handle] at accepted
            | withhold => simp [GraphRuntime.handle] at accepted
            | malformed => simp [GraphRuntime.handle] at accepted
        | resolve outputName owner bindingName fresh source checks next =>
            cases payload with
            | commitment => simp [GraphRuntime.handle] at accepted
            | opening site handle raw =>
                simp only [GraphRuntime.handle] at accepted
                split_ifs at accepted
                · cases typed : raw.as? (R.result _) with
                  | none =>
                    rw [typed] at accepted
                    contradiction
                  | some encoded =>
                    rw [typed] at accepted
                    cases accepted
                    exact advanceResolve_publicAgreement next ideal values bindings candidates
                      pc clock _ agreement
            | withhold site =>
                simp only [GraphRuntime.handle] at accepted
                split_ifs at accepted
                · cases accepted
                  exact advanceResolve_publicAgreement next ideal values bindings candidates
                    pc clock .failure agreement
            | malformed => simp [GraphRuntime.handle] at accepted

/-- Every state in the support of an environment transition preserves the
public-store invariant. -/
theorem environmentStep_preserves_publicAgreement
    (runtime : GraphRuntime Player L Δ) (state nextState : State Player L Δ)
    (command : EnvironmentCommand) (agreement : state.PublicAgreement)
    (supported : nextState ∈ (runtime.environmentStep state command).support) :
    nextState.PublicAgreement := by
  cases command
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases graph with
      | ret payoffs =>
          simp only [GraphRuntime.environmentStep, GraphRuntime.tick,
            FinDist.mem_support_pure] at supported
          subst nextState
          exact agreement
      | sample name fresh law next =>
          simp only [GraphRuntime.environmentStep, GraphRuntime.tick,
            FinDist.support_map] at supported
          rcases supported with ⟨value, _inSupport, rfl⟩
          simp only [State.PublicAgreement, PublicValues.ofVEnv_cons_public]
          exact congrArg (PublicValues.consPublic value) agreement
      | bind name owner fresh next =>
          simp only [GraphRuntime.environmentStep, GraphRuntime.tick] at supported
          split at supported
          · rw [FinDist.mem_support_pure] at supported
            subst nextState
            simp only [advanceBindFailure, State.PublicAgreement,
              PublicValues.ofVEnv_cons_sealed]
            exact congrArg PublicValues.consSealed agreement
          · rw [FinDist.mem_support_pure] at supported
            subst nextState
            exact agreement
      | resolve outputName owner bindingName fresh source checks next =>
          simp only [GraphRuntime.environmentStep, GraphRuntime.tick] at supported
          split at supported
          · rw [FinDist.mem_support_pure] at supported
            subst nextState
            exact advanceResolve_publicAgreement next ideal values bindings candidates
              pc (clock + 1) .failure agreement
          · rw [FinDist.mem_support_pure] at supported
            subst nextState
            exact agreement

/-- Public agreement holds after every supported finite native action run. -/
theorem run_preserves_publicAgreement (runtime : GraphRuntime Player L Δ)
    (state final : runtime.application.State)
    (actions : List runtime.application.Action)
    (agreement : state.application.PublicAgreement)
    (supported : final ∈ (runtime.application.run actions state).support) :
    final.application.PublicAgreement := by
  apply runtime.application.run_application_invariant State.PublicAgreement
    (runtime.privateStep_preserves_publicAgreement)
    (fun state message next => runtime.handle_preserves_publicAgreement state next message)
    (fun state command next =>
      runtime.environmentStep_preserves_publicAgreement state next command)
    state final actions agreement supported

/-- Public agreement holds throughout every supported policy-driven run. -/
theorem runPolicies_preserves_publicAgreement (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Interaction.MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (agreement : execution.native.application.PublicAgreement)
    (supported : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    next.native.application.PublicAgreement := by
  apply runtime.application.runPolicies_application_invariant State.PublicAgreement
    (runtime.privateStep_preserves_publicAgreement)
    (fun state message next => runtime.handle_preserves_publicAgreement state next message)
    (fun state command next =>
      runtime.environmentStep_preserves_publicAgreement state next command)
    players environment schedule execution next agreement supported

/-- Commitment admission at a binding site has one public result.  Candidate
materialization may change the private ideal head, but cannot reveal whether a
handle was openable or whether its materialized value had the expected type. -/
theorem bind_commitment_publicView_independent
    {Γ : VCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (runtime : GraphRuntime Player L Δ)
    (fresh : name ∉ Γ.map Prod.fst)
    (next : Vegas.Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (leftIdeal rightIdeal : VEnv L Γ)
    (values : PublicValues Γ) (bindings : Bindings Player)
    (leftCandidates rightCandidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt nonce : Nat) (handle : Handle Player)
    (handleOwner : handle.1 = owner) :
    Option.map State.publicView
        (runtime.handle
          (.running (.bind name owner fresh next) leftIdeal values bindings leftCandidates
            pc clock enteredAt)
          ⟨(owner, nonce), .commitment pc handle⟩) =
      Option.map State.publicView
        (runtime.handle
          (.running (.bind name owner fresh next) rightIdeal values bindings rightCandidates
            pc clock enteredAt)
          ⟨(owner, nonce), .commitment pc handle⟩) := by
  simp [GraphRuntime.handle, GraphRuntime.advanceBind, Message.sender, handleOwner,
    State.publicView]

end Vegas.GraphRuntime
