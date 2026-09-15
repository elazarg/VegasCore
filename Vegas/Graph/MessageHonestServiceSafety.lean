/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageBindingService
import Vegas.Graph.MessageDisclosureService
import Vegas.Graph.MessageServiceTermination
import Vegas.Graph.MessageInvariant

/-! # Honest service expiry safety

The complete service plan reserves expiry instructions after the honest
compiled owner has had two calls, all reaction rounds have run, and the newest
submission has been included.  This file proves that an expiry reached at a
binding or resolution phase therefore observes a program counter already past
that phase. -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Γ₀ Δ : VCtx Player L}

/-- At an actually reached binding head, the complete honest pre-expiry block
advances the public phase.  The premise is deliberately one supported run of
the block; the intermediate owner/reaction states are recovered internally. -/
theorem honest_service_bind_head_advances
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (_unique : (Γ₀.map Prod.fst).Nodup)
    (_discipline : whole.BindingDiscipline BindingOrigins.none)
    (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (site : Nat) (walk : Prefix Δ whole (.bind name owner fresh tail) site)
    (before suffix : List (ServiceInstruction Player)) (roster : List Player)
    (rounds : Nat) (wire : runtime.application.WirePolicy)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner =
      runtime.compilePlayerPolicy whole owner (profile owner))
    (execution afterBlock : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies
      players
      (runtime.serviceEnvironment
        (before ++ [.player owner, .player owner] ++
          (List.replicate rounds (reactionRound roster)).flatten ++
          .includeLatest owner :: suffix) wire)
      (before.map ServiceInstruction.invocation)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (follows : execution.native.application.Follows
      (.bind name owner fresh tail) site)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (supported : afterBlock ∈ (runtime.application.runPolicies
      players
      (runtime.serviceEnvironment
        (before ++ [.player owner, .player owner] ++
          (List.replicate rounds (reactionRound roster)).flatten ++
          .includeLatest owner :: suffix) wire)
      ((([.player owner, .player owner] : List (ServiceInstruction Player)) ++
        (List.replicate rounds (reactionRound roster)).flatten ++
        [ServiceInstruction.includeLatest owner]).map ServiceInstruction.invocation)
      execution).support) :
    site < afterBlock.native.application.phase := by
  let reactions := (List.replicate rounds (reactionRound roster)).flatten
  let environment := runtime.serviceEnvironment
    (before ++ [.player owner, .player owner] ++ reactions ++
      .includeLatest owner :: suffix) wire
  obtain ⟨length, phaseEq⟩ := State.follows_phase
    (.bind name owner fresh tail) site execution.native.application follows
  by_cases already : site < execution.native.application.phase
  · have monotone := runtime.runPolicies_phase_mono
      players environment _ execution afterBlock
      (by simpa [environment, reactions] using supported)
    exact already.trans_le monotone
  have atPhase : execution.native.application.phase = site := by
    rw [State.publicView_pc] at phaseEq
    omega
  rw [List.map_append, List.map_append, runtime.application.runPolicies_append] at supported
  simp only [FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨reacted, throughLeadAndReactions, includeSupported⟩ := supported
  rw [runtime.application.runPolicies_append] at throughLeadAndReactions
  simp only [FinDist.support_bind, Set.mem_iUnion] at throughLeadAndReactions
  obtain ⟨afterLead, leadSupported, reactionSupported⟩ := throughLeadAndReactions
  apply runtime.runPolicies_initial_bind_full_service_block_advances name owner whole
    (profile owner) fresh tail site walk input players ownerCompiled before suffix roster rounds
    wire (before.map ServiceInstruction.invocation)
    execution afterLead reacted
    afterBlock reached follows atPhase cursor
  · simpa [ServiceInstruction.invocation] using leadSupported
  · simpa [reactions] using reactionSupported
  · simpa [MessageApplication.runPolicies, ServiceInstruction.invocation] using includeSupported

/-- The corresponding aggregate pre-expiry progress law for a resolution
head.  Its exact running state is recovered from `Follows` and the public-view
agreement preserved from initialization. -/
theorem honest_service_resolve_head_advances
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (site : Nat) (walk : Prefix Δ whole
      (.resolve outputName owner bindingName fresh source checks tail) site)
    (before suffix : List (ServiceInstruction Player)) (roster : List Player)
    (rounds : Nat) (wire : runtime.application.WirePolicy)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner =
      runtime.compilePlayerPolicy whole owner (profile owner))
    (execution afterBlock : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies
      players
      (runtime.serviceEnvironment
        (before ++ [.player owner, .player owner] ++
          (List.replicate rounds (reactionRound roster)).flatten ++
          .includeLatest owner :: suffix) wire)
      (before.map ServiceInstruction.invocation)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (follows : execution.native.application.Follows
      (.resolve outputName owner bindingName fresh source checks tail) site)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (supported : afterBlock ∈ (runtime.application.runPolicies
      players
      (runtime.serviceEnvironment
        (before ++ [.player owner, .player owner] ++
          (List.replicate rounds (reactionRound roster)).flatten ++
          .includeLatest owner :: suffix) wire)
      ((([.player owner, .player owner] : List (ServiceInstruction Player)) ++
        (List.replicate rounds (reactionRound roster)).flatten ++
        [ServiceInstruction.includeLatest owner]).map ServiceInstruction.invocation)
      execution).support) :
    site < afterBlock.native.application.phase := by
  let reactions := (List.replicate rounds (reactionRound roster)).flatten
  let environment := runtime.serviceEnvironment
    (before ++ [.player owner, .player owner] ++ reactions ++
      .includeLatest owner :: suffix) wire
  obtain ⟨length, phaseEq⟩ := State.follows_phase
    (.resolve outputName owner bindingName fresh source checks tail) site
    execution.native.application follows
  by_cases already : site < execution.native.application.phase
  · have monotone := runtime.runPolicies_phase_mono
      players environment _ execution afterBlock
      (by simpa [environment, reactions] using supported)
    exact already.trans_le monotone
  have atPhase : execution.native.application.phase = site := by
    rw [State.publicView_pc] at phaseEq
    omega
  obtain ⟨ideal, values, bindings, candidates, clock, enteredAt, stateEq⟩ :=
    State.follows_at_base
      (.resolve outputName owner bindingName fresh source checks tail) site
      execution.native.application follows (by simpa [State.publicView_pc] using atPhase)
  have agreement := runtime.runPolicies_preserves_publicAgreement
    players environment
    (before.map ServiceInstruction.invocation) _ execution
    (State.initial_publicAgreement whole input) (by simpa [environment, reactions] using reached)
  rw [stateEq] at agreement
  change (values : PublicValues Γ) =
    (PublicValues.ofVEnv ideal : PublicValues Γ) at agreement
  rw [agreement] at stateEq
  rw [List.map_append, List.map_append, runtime.application.runPolicies_append] at supported
  simp only [FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨reacted, throughLeadAndReactions, includeSupported⟩ := supported
  rw [runtime.application.runPolicies_append] at throughLeadAndReactions
  simp only [FinDist.support_bind, Set.mem_iUnion] at throughLeadAndReactions
  obtain ⟨afterLead, leadSupported, reactionSupported⟩ := throughLeadAndReactions
  apply resolve_full_service_block_advances runtime whole input unique discipline
    outputName bindingName owner fresh source checks tail (profile owner) site walk
    players ownerCompiled before reactions suffix wire
    (before.map ServiceInstruction.invocation) execution afterLead reacted afterBlock
    ideal bindings candidates clock enteredAt
  · simpa [environment, reactions] using reached
  · exact stateEq
  · exact cursor
  · simpa [ServiceInstruction.invocation] using leadSupported
  · simpa [reactions] using reactionSupported
  · simpa [MessageApplication.runPolicies, ServiceInstruction.invocation]
      using includeSupported

end Vegas.GraphRuntime
