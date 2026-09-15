/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageHonestServiceSafety
import Vegas.Graph.MessageServiceSafetyComposition

/-! # Expiry safety of the complete honest graph service plan -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- Expiry safety of the remaining honest service plan at an actually reached
typed graph cursor.  The accumulated prefix keeps the concrete environment
history aligned with the single service policy used by the whole run. -/
theorem servicePlan_expirySafe_from
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (roster : List Player) (rounds : Nat) (wire : runtime.application.WirePolicy)
    (before : List (ServiceInstruction Player)) (phase : Nat)
    (graph : Graph Player L Γ Δ) (walk : Prefix Δ whole graph phase)
    (execution : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies
      (runtime.compileProfile whole profile)
      (runtime.serviceEnvironment
        (before ++ runtime.servicePlan roster rounds graph phase) wire)
      (before.map ServiceInstruction.invocation)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (follows : execution.native.application.Follows graph phase)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length) :
    ExpirySafe runtime (runtime.compileProfile whole profile)
      (runtime.serviceEnvironment
        (before ++ runtime.servicePlan roster rounds graph phase) wire)
      (runtime.servicePlan roster rounds graph phase) execution := by
  induction graph generalizing before phase with
  | ret outcome =>
      intro expiryBefore nominal after split
      simp only [servicePlan] at split
      simp at split
  | sample name fresh law tail ih =>
      intro expiryBefore nominal after split next supported
      cases expiryBefore with
      | nil =>
          simp only [servicePlan, List.nil_append] at split
          injection split with nominalEq _
          injection nominalEq with nominalEq
          subst nominal
          simp only [List.map_nil, MessageApplication.runPolicies,
            FinDist.mem_support_pure] at supported
          subst next
          by_cases same : execution.native.application.phase = phase
          · right
            obtain ⟨ideal, values, bindings, candidates, clock, enteredAt, stateEq⟩ :=
              State.follows_at_base (.sample name fresh law tail) phase
                execution.native.application follows same
            exact ⟨_, name, _, fresh, law, tail, ideal, values, bindings, candidates,
              phase, clock, enteredAt, stateEq⟩
          · exact Or.inl same
      | cons first rest =>
          simp only [servicePlan, List.cons_append] at split
          injection split with firstEq tailSplit
          subst first
          simp only [List.map_cons, MessageApplication.runPolicies,
            FinDist.support_bind, Set.mem_iUnion] at supported
          obtain ⟨middle, firstRun, restRun⟩ := supported
          have singleRun : middle ∈ (runtime.application.runPolicies
              (runtime.compileProfile whole profile)
              (runtime.serviceEnvironment
                (before ++ ServiceInstruction.expire phase ::
                  runtime.servicePlan roster rounds tail
                  (phase + 1)) wire)
              [.environment] execution).support := by
            simpa [servicePlan, MessageApplication.runPolicies,
              ServiceInstruction.invocation] using firstRun
          have advanced := runtime.runPolicies_sample_slot_advances
            (runtime.compileProfile whole profile) before
            (runtime.servicePlan roster rounds tail (phase + 1)) phase wire
            execution middle follows cursor singleRun
          have middleFollows := runtime.runPolicies_follows
            (.sample name fresh law tail) phase (runtime.compileProfile whole profile) _
            [.environment] execution middle follows singleRun
          have tailFollows := State.follows_sample_tail_of_lt phase
            middle.native.application middleFollows advanced
          have middleCursor := runtime.runPolicies_service_cursor
            (runtime.compileProfile whole profile) _ [ServiceInstruction.expire phase]
            execution middle singleRun
          have middleReached : middle ∈ (runtime.application.runPolicies
              (runtime.compileProfile whole profile)
              (runtime.serviceEnvironment
                ((before ++ [ServiceInstruction.expire phase]) ++
                  runtime.servicePlan roster rounds tail (phase + 1)) wire)
              ((before ++ [ServiceInstruction.expire phase]).map
                ServiceInstruction.invocation)
              (MessageApplication.PolicyExecution.initial runtime.application
                (MessageApplication.State.initial runtime.application
                  (State.initial whole input)))).support := by
            rw [List.map_append, runtime.application.runPolicies_append]
            simp only [FinDist.support_bind, Set.mem_iUnion]
            exact ⟨execution, by simpa [servicePlan, List.append_assoc] using reached,
              by simpa [List.append_assoc, ServiceInstruction.invocation] using singleRun⟩
          have tailSafe := ih runtime whole profile discipline wire
            (before ++ [ServiceInstruction.expire phase]) (phase + 1)
            (walk.trans (Prefix.sample (Prefix.refl tail))) middle
            (by simpa [List.append_assoc] using middleReached) tailFollows
            (by simpa [List.filterMap_append, cursor] using middleCursor)
          exact tailSafe rest nominal after tailSplit next
            (by simpa [servicePlan, List.append_assoc] using restRun)
  | bind name owner fresh tail ih =>
      rename_i payloadTy
      let head : List (ServiceInstruction Player) :=
        [.player owner, .player owner] ++
          (List.replicate rounds (reactionRound roster)).flatten ++ [.includeLatest owner]
      let expiry : List (ServiceInstruction Player) :=
        List.replicate (max 1 (runtime.deadline phase))
        (ServiceInstruction.expire phase)
      let tailPlan := runtime.servicePlan roster rounds tail (phase + 1)
      rw [show runtime.servicePlan roster rounds (.bind name owner fresh tail) phase =
        head ++ expiry ++ tailPlan by simp [servicePlan, head, expiry, tailPlan,
          List.append_assoc]]
      rw [List.append_assoc head expiry tailPlan]
      apply runtime.expirySafe_append_of_prefix (runtime.compileProfile whole profile)
        (runtime.serviceEnvironment (before ++ (head ++ (expiry ++ tailPlan))) wire)
        head (expiry ++ tailPlan) execution
      · intro nominal member
        simp [head, reactionRound] at member
      · intro afterHead headRun
        have passed := runtime.honest_service_bind_head_advances whole profile input unique
          discipline name owner fresh tail phase walk before (expiry ++ tailPlan) roster rounds
          wire execution afterHead (by simpa [servicePlan, head, expiry, tailPlan,
            List.append_assoc] using reached)
          follows cursor (by simpa [head, expiry, tailPlan, List.append_assoc] using headRun)
        apply runtime.expirySafe_append (runtime.compileProfile whole profile)
          (runtime.serviceEnvironment (before ++ (head ++ (expiry ++ tailPlan))) wire)
          expiry tailPlan afterHead
        · exact runtime.expirySafe_replicate_expire_of_lt _ _ afterHead phase _ passed
        · intro afterExpiry expiryRun
          have currentFollows := runtime.runPolicies_follows (.bind name owner fresh tail) phase
            (runtime.compileProfile whole profile) _
            ((head ++ expiry).map ServiceInstruction.invocation)
            execution afterExpiry follows (by
              simp only [List.map_append, runtime.application.runPolicies_append,
                FinDist.support_bind, Set.mem_iUnion]
              exact ⟨afterHead, headRun, expiryRun⟩)
          have later := passed.trans_le (runtime.runPolicies_phase_mono
            (runtime.compileProfile whole profile) _ (expiry.map ServiceInstruction.invocation)
            afterHead afterExpiry expiryRun)
          have tailFollows := State.follows_bind_tail_of_lt phase
            afterExpiry.native.application currentFollows later
          have reachedAfter : afterExpiry ∈ (runtime.application.runPolicies
              (runtime.compileProfile whole profile)
              (runtime.serviceEnvironment (before ++ (head ++ (expiry ++ tailPlan))) wire)
              ((before ++ head ++ expiry).map ServiceInstruction.invocation)
              (MessageApplication.PolicyExecution.initial runtime.application
                (MessageApplication.State.initial runtime.application
                  (State.initial whole input)))).support := by
            rw [List.map_append, List.map_append, runtime.application.runPolicies_append,
              runtime.application.runPolicies_append]
            simp only [FinDist.support_bind, Set.mem_iUnion]
            exact ⟨afterHead, ⟨execution, by
              simpa [servicePlan, head, expiry, tailPlan, List.append_assoc] using reached,
              headRun⟩, expiryRun⟩
          have cursorAfter := runtime.runPolicies_service_cursor
            (runtime.compileProfile whole profile) _ (head ++ expiry) execution afterExpiry (by
              simp only [List.map_append, runtime.application.runPolicies_append,
                FinDist.support_bind, Set.mem_iUnion]
              exact ⟨afterHead, headRun, expiryRun⟩)
          have recursive := ih runtime whole profile discipline wire
            (before ++ head ++ expiry) (phase + 1)
            (walk.trans (Prefix.bind (Prefix.refl tail))) afterExpiry
            (by simpa [head, expiry, tailPlan, List.append_assoc] using reachedAfter)
            tailFollows (by simpa [List.filterMap_append, cursor] using cursorAfter)
          simpa [tailPlan, List.append_assoc] using recursive
  | resolve output owner binding fresh source checks tail ih =>
      rename_i payloadTy
      let head : List (ServiceInstruction Player) :=
        [.player owner, .player owner] ++
          (List.replicate rounds (reactionRound roster)).flatten ++ [.includeLatest owner]
      let expiry : List (ServiceInstruction Player) :=
        List.replicate (max 1 (runtime.deadline phase))
        (ServiceInstruction.expire phase)
      let tailPlan := runtime.servicePlan roster rounds tail (phase + 1)
      rw [show runtime.servicePlan roster rounds
        (.resolve output owner binding fresh source checks tail) phase =
        head ++ expiry ++ tailPlan by simp [servicePlan, head, expiry, tailPlan,
          List.append_assoc]]
      rw [List.append_assoc head expiry tailPlan]
      apply runtime.expirySafe_append_of_prefix (runtime.compileProfile whole profile)
        (runtime.serviceEnvironment (before ++ (head ++ (expiry ++ tailPlan))) wire)
        head (expiry ++ tailPlan) execution
      · intro nominal member
        simp [head, reactionRound] at member
      · intro afterHead headRun
        have passed := runtime.honest_service_resolve_head_advances whole profile input unique
          discipline output binding owner fresh source checks tail phase walk before
          (expiry ++ tailPlan) roster rounds wire execution afterHead
          (by simpa [servicePlan, head, expiry, tailPlan, List.append_assoc] using reached)
          follows cursor (by simpa [head, expiry, tailPlan, List.append_assoc] using headRun)
        apply runtime.expirySafe_append (runtime.compileProfile whole profile)
          (runtime.serviceEnvironment (before ++ (head ++ (expiry ++ tailPlan))) wire)
          expiry tailPlan afterHead
        · exact runtime.expirySafe_replicate_expire_of_lt _ _ afterHead phase _ passed
        · intro afterExpiry expiryRun
          have currentFollows := runtime.runPolicies_follows
            (.resolve output owner binding fresh source checks tail) phase
            (runtime.compileProfile whole profile) _
            ((head ++ expiry).map ServiceInstruction.invocation)
            execution afterExpiry follows (by
              simp only [List.map_append, runtime.application.runPolicies_append,
                FinDist.support_bind, Set.mem_iUnion]
              exact ⟨afterHead, headRun, expiryRun⟩)
          have later := passed.trans_le (runtime.runPolicies_phase_mono
            (runtime.compileProfile whole profile) _ (expiry.map ServiceInstruction.invocation)
            afterHead afterExpiry expiryRun)
          have tailFollows := State.follows_resolve_tail_of_lt phase
            afterExpiry.native.application currentFollows later
          have reachedAfter : afterExpiry ∈ (runtime.application.runPolicies
              (runtime.compileProfile whole profile)
              (runtime.serviceEnvironment (before ++ (head ++ (expiry ++ tailPlan))) wire)
              ((before ++ head ++ expiry).map ServiceInstruction.invocation)
              (MessageApplication.PolicyExecution.initial runtime.application
                (MessageApplication.State.initial runtime.application
                  (State.initial whole input)))).support := by
            rw [List.map_append, List.map_append, runtime.application.runPolicies_append,
              runtime.application.runPolicies_append]
            simp only [FinDist.support_bind, Set.mem_iUnion]
            exact ⟨afterHead, ⟨execution, by
              simpa [servicePlan, head, expiry, tailPlan, List.append_assoc] using reached,
              headRun⟩, expiryRun⟩
          have cursorAfter := runtime.runPolicies_service_cursor
            (runtime.compileProfile whole profile) _ (head ++ expiry) execution afterExpiry (by
              simp only [List.map_append, runtime.application.runPolicies_append,
                FinDist.support_bind, Set.mem_iUnion]
              exact ⟨afterHead, headRun, expiryRun⟩)
          have recursive := ih runtime whole profile discipline wire
            (before ++ head ++ expiry) (phase + 1)
            (walk.trans (Prefix.resolve (Prefix.refl tail))) afterExpiry
            (by simpa [head, expiry, tailPlan, List.append_assoc] using reachedAfter)
            tailFollows (by simpa [List.filterMap_append, cursor] using cursorAfter)
          simpa [tailPlan, List.append_assoc] using recursive

/-- The complete honest service plan is expiry-safe from the canonical graph
runtime initialization. -/
theorem servicePlan_expirySafe
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (roster : List Player) (rounds : Nat) (wire : runtime.application.WirePolicy) :
    ExpirySafe runtime (runtime.compileProfile whole profile)
      (runtime.serviceEnvironment (runtime.servicePlan roster rounds whole 0) wire)
      (runtime.servicePlan roster rounds whole 0)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input))) := by
  apply runtime.servicePlan_expirySafe_from whole profile input unique discipline roster rounds
    wire [] 0 whole (Prefix.refl whole)
  · simp [MessageApplication.runPolicies]
  · exact State.initial_follows whole input
  · rfl

end Vegas.GraphRuntime
