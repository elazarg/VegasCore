/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageHonestServiceSafety
import Vegas.Graph.MessageServiceSafetyComposition

/-! # Expiry safety with one arbitrary player

Honest owners advance during their pre-expiry service block.  An arbitrary
focal owner may instead reach its reserved timeout; this is the sole additional
safe case compared with the fully honest service theorem. -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- The running cursor is a binding or resolution owned by `focal`. -/
def State.IsOwnedBy (state : State Player L Δ) (focal : Option Player) : Prop :=
  match state with
  | .running (.bind _ owner _ _) .. | .running (.resolve _ owner _ _ _ _ _) .. =>
      focal = some owner
  | _ => False

/-- Every reached expiry is stale, is a chance transition, or belongs to the
one player whose native policy is unrestricted. -/
def DeviationExpirySafe (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (focal : Option Player) (plan : List (ServiceInstruction Player))
    (execution : runtime.application.PolicyExecution) : Prop :=
  ∀ before phase after, plan = before ++ .expire phase :: after →
    ∀ next ∈ (runtime.application.runPolicies players environment
      (before.map ServiceInstruction.invocation) execution).support,
      next.native.application.phase ≠ phase ∨
        next.native.application.IsSample ∨ next.native.application.IsOwnedBy focal

theorem DeviationExpirySafe.of_expirySafe
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (focal : Option Player) (plan : List (ServiceInstruction Player))
    (execution : runtime.application.PolicyExecution)
    (safe : ExpirySafe runtime players environment plan execution) :
    DeviationExpirySafe runtime players environment focal plan execution := by
  intro before phase after split next supported
  exact (safe before phase after split next supported).imp_right Or.inl

theorem deviationExpirySafe_append_of_prefix
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (focal : Option Player)
    (left right : List (ServiceInstruction Player))
    (execution : runtime.application.PolicyExecution)
    (noExpiry : ∀ phase, .expire phase ∉ left)
    (suffixSafe : ∀ middle ∈ (runtime.application.runPolicies players environment
      (left.map ServiceInstruction.invocation) execution).support,
      DeviationExpirySafe runtime players environment focal right middle) :
    DeviationExpirySafe runtime players environment focal (left ++ right) execution := by
  intro before phase after split next supported
  rcases append_cons_split left right before after (.expire phase) split with hlocal | residual
  · rcases hlocal with ⟨leftBefore, leftAfter, leftEq, -, -⟩
    exact ((noExpiry phase) (leftEq ▸ by simp)).elim
  · rcases residual with ⟨rightBefore, rightAfter, rightEq, beforeEq, afterEq⟩
    subst before
    rw [List.map_append, runtime.application.runPolicies_append] at supported
    simp only [FinDist.support_bind, Set.mem_iUnion] at supported
    obtain ⟨middle, leftRun, rightRun⟩ := supported
    exact suffixSafe middle leftRun rightBefore phase rightAfter rightEq next rightRun

theorem deviationExpirySafe_append
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (focal : Option Player)
    (left right : List (ServiceInstruction Player))
    (execution : runtime.application.PolicyExecution)
    (leftSafe : DeviationExpirySafe runtime players environment focal left execution)
    (rightSafe : ∀ middle ∈ (runtime.application.runPolicies players environment
      (left.map ServiceInstruction.invocation) execution).support,
      DeviationExpirySafe runtime players environment focal right middle) :
    DeviationExpirySafe runtime players environment focal (left ++ right) execution := by
  intro before phase after split next supported
  rcases append_cons_split left right before after (.expire phase) split with hlocal | residual
  · rcases hlocal with ⟨leftBefore, leftAfter, leftEq, beforeEq, afterEq⟩
    subst before
    exact leftSafe leftBefore phase leftAfter leftEq next supported
  · rcases residual with ⟨rightBefore, rightAfter, rightEq, beforeEq, afterEq⟩
    subst before
    rw [List.map_append, runtime.application.runPolicies_append] at supported
    simp only [FinDist.support_bind, Set.mem_iUnion] at supported
    obtain ⟨middle, leftRun, rightRun⟩ := supported
    exact rightSafe middle leftRun rightBefore phase rightAfter rightEq next rightRun

theorem deviationExpirySafe_replicate_owned_bind
    (runtime : GraphRuntime Player L Δ) (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (owner : Player)
    (focal : Option Player) (isFocal : focal = some owner)
    (name : VarId) {payload : L.Ty} (fresh)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (phase count : Nat) (execution : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows (.bind name owner fresh tail) phase) :
    DeviationExpirySafe runtime players environment focal
      (List.replicate count (.expire phase)) execution := by
  intro before nominal after split next supported
  have member : (ServiceInstruction.expire nominal : ServiceInstruction Player) ∈
      List.replicate count (ServiceInstruction.expire phase) := by rw [split]; simp
  have nominalEq : nominal = phase := by simpa using List.eq_of_mem_replicate member
  subst nominal
  have nextFollows := runtime.runPolicies_follows (.bind name owner fresh tail) phase players
    environment (before.map ServiceInstruction.invocation) execution next follows supported
  by_cases same : next.native.application.phase = phase
  · right; right
    obtain ⟨ideal, values, bindings, candidates, clock, enteredAt, stateEq⟩ :=
      State.follows_at_base (.bind name owner fresh tail) phase next.native.application
        nextFollows (by simpa [State.publicView_pc] using same)
    simp [State.IsOwnedBy, stateEq, isFocal]
  · exact Or.inl same

theorem deviationExpirySafe_replicate_owned_resolve
    (runtime : GraphRuntime Player L Δ) (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (owner : Player)
    (focal : Option Player) (isFocal : focal = some owner)
    (output binding : VarId) {payload : L.Ty} (fresh) (source) (checks)
    (tail : Graph Player L ((output, .pub (R.result payload)) :: Γ) Δ)
    (phase count : Nat) (execution : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows
      (.resolve output owner binding fresh source checks tail) phase) :
    DeviationExpirySafe runtime players environment focal
      (List.replicate count (.expire phase)) execution := by
  intro before nominal after split next supported
  have member : (ServiceInstruction.expire nominal : ServiceInstruction Player) ∈
      List.replicate count (ServiceInstruction.expire phase) := by rw [split]; simp
  have nominalEq : nominal = phase := by simpa using List.eq_of_mem_replicate member
  subst nominal
  have nextFollows := runtime.runPolicies_follows
    (.resolve output owner binding fresh source checks tail) phase players environment
    (before.map ServiceInstruction.invocation) execution next follows supported
  by_cases same : next.native.application.phase = phase
  · right; right
    obtain ⟨ideal, values, bindings, candidates, clock, enteredAt, stateEq⟩ :=
      State.follows_at_base (.resolve output owner binding fresh source checks tail) phase
        next.native.application nextFollows (by simpa [State.publicView_pc] using same)
    simp [State.IsOwnedBy, stateEq, isFocal]
  · exact Or.inl same

/-- Expiry safety of a remaining service plan when only `focal` may use an
arbitrary native policy. Every other phase owner runs its compiled policy. -/
theorem servicePlan_deviationExpirySafe_from
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (focal : Option Player) (players : Player → runtime.application.PlayerPolicy)
    (compiled : ∀ owner, focal ≠ some owner →
      players owner = runtime.compilePlayerPolicy whole owner (profile owner))
    (roster : List Player) (rounds : Nat) (wire : runtime.application.WirePolicy)
    (before : List (ServiceInstruction Player)) (phase : Nat)
    (graph : Graph Player L Γ Δ) (walk : Prefix Δ whole graph phase)
    (execution : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (before ++ runtime.servicePlan roster rounds graph phase) wire)
      (before.map ServiceInstruction.invocation)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (follows : execution.native.application.Follows graph phase)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length) :
    DeviationExpirySafe runtime players
      (runtime.serviceEnvironment
        (before ++ runtime.servicePlan roster rounds graph phase) wire)
      focal (runtime.servicePlan roster rounds graph phase) execution := by
  induction graph generalizing before phase with
  | ret outcome =>
      intro expiryBefore nominal after split
      simp [servicePlan] at split
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
          · right; left
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
          have singleRun : middle ∈ (runtime.application.runPolicies players
              (runtime.serviceEnvironment
                (before ++ .expire phase :: runtime.servicePlan roster rounds tail
                  (phase + 1)) wire) [.environment] execution).support := by
            simpa [servicePlan, MessageApplication.runPolicies,
              ServiceInstruction.invocation] using firstRun
          have advanced := runtime.runPolicies_sample_slot_advances players before
            (runtime.servicePlan roster rounds tail (phase + 1)) phase wire execution middle
            follows cursor singleRun
          have middleFollows := runtime.runPolicies_follows (.sample name fresh law tail) phase
            players _ [.environment] execution middle follows singleRun
          have tailFollows := State.follows_sample_tail_of_lt phase
            middle.native.application middleFollows advanced
          have middleCursor := runtime.runPolicies_service_cursor players _
            [ServiceInstruction.expire phase] execution middle singleRun
          have middleReached : middle ∈ (runtime.application.runPolicies players
              (runtime.serviceEnvironment ((before ++ [ServiceInstruction.expire phase]) ++
                runtime.servicePlan roster rounds tail (phase + 1)) wire)
              ((before ++ [ServiceInstruction.expire phase]).map ServiceInstruction.invocation)
              (MessageApplication.PolicyExecution.initial runtime.application
                (MessageApplication.State.initial runtime.application
                  (State.initial whole input)))).support := by
            rw [List.map_append, runtime.application.runPolicies_append]
            simp only [FinDist.support_bind, Set.mem_iUnion]
            exact ⟨execution, by simpa [servicePlan, List.append_assoc] using reached,
              by simpa [ServiceInstruction.invocation] using singleRun⟩
          have tailSafe := ih runtime whole profile discipline players compiled wire
            (before ++ [ServiceInstruction.expire phase]) (phase + 1)
            (walk.trans (Prefix.sample (Prefix.refl tail))) middle
            (by simpa [List.append_assoc] using middleReached) tailFollows
            (by simpa [List.filterMap_append, cursor] using middleCursor)
          exact tailSafe rest nominal after tailSplit next
            (by simpa [servicePlan, List.append_assoc] using restRun)
  | bind name owner fresh tail ih =>
      rename_i payloadTy
      let head : List (ServiceInstruction Player) := [.player owner, .player owner] ++
        (List.replicate rounds (reactionRound roster)).flatten ++ [.includeLatest owner]
      let expiry : List (ServiceInstruction Player) :=
        List.replicate (max 1 (runtime.deadline phase))
        (ServiceInstruction.expire phase)
      let tailPlan := runtime.servicePlan roster rounds tail (phase + 1)
      rw [show runtime.servicePlan roster rounds (.bind name owner fresh tail) phase =
        head ++ expiry ++ tailPlan by simp [servicePlan, head, expiry, tailPlan,
          List.append_assoc], List.append_assoc head expiry tailPlan]
      apply runtime.deviationExpirySafe_append_of_prefix players
        (runtime.serviceEnvironment (before ++ (head ++ (expiry ++ tailPlan))) wire) focal
        head (expiry ++ tailPlan) execution
      · intro nominal member; simp [head, reactionRound] at member
      · intro afterHead headRun
        have headFollows := runtime.runPolicies_follows (.bind name owner fresh tail) phase
          players _ (head.map ServiceInstruction.invocation) execution afterHead follows headRun
        have executionOrdered := runtime.runPolicies_clockOrdered players _ _ _ execution
          (State.initial_clockOrdered whole input)
          (by simpa [servicePlan, head, expiry, tailPlan, List.append_assoc] using reached)
        have headOrdered := runtime.runPolicies_clockOrdered players _ _ execution afterHead
          executionOrdered headRun
        have headCursorStep := runtime.runPolicies_service_cursor players _ head execution
          afterHead headRun
        have headCursor : afterHead.environmentHistory.length =
            ((before ++ head).filterMap ServiceInstruction.environmentSlot).length := by
          rw [List.filterMap_append, List.length_append, headCursorStep, cursor]
        have tailSafeOf (afterExpiry : runtime.application.PolicyExecution)
            (expiryRun : afterExpiry ∈ (runtime.application.runPolicies players
              (runtime.serviceEnvironment (before ++ (head ++ (expiry ++ tailPlan))) wire)
              (expiry.map ServiceInstruction.invocation) afterHead).support)
            (advanced : phase < afterExpiry.native.application.phase) :
            DeviationExpirySafe runtime players
              (runtime.serviceEnvironment (before ++ (head ++ (expiry ++ tailPlan))) wire)
              focal tailPlan afterExpiry := by
          have currentFollows := runtime.runPolicies_follows (.bind name owner fresh tail) phase
            players _ ((head ++ expiry).map ServiceInstruction.invocation) execution afterExpiry
            follows (by
              simp only [List.map_append, runtime.application.runPolicies_append,
                FinDist.support_bind, Set.mem_iUnion]
              exact ⟨afterHead, headRun, expiryRun⟩)
          have tailFollows := State.follows_bind_tail_of_lt phase
            afterExpiry.native.application currentFollows advanced
          have reachedAfter : afterExpiry ∈ (runtime.application.runPolicies players
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
          have cursorAfter := runtime.runPolicies_service_cursor players _ (head ++ expiry)
            execution afterExpiry (by
              simp only [List.map_append, runtime.application.runPolicies_append,
                FinDist.support_bind, Set.mem_iUnion]
              exact ⟨afterHead, headRun, expiryRun⟩)
          have recursive := ih runtime whole profile discipline players compiled wire
            (before ++ head ++ expiry) (phase + 1)
            (walk.trans (Prefix.bind (Prefix.refl tail))) afterExpiry
            (by simpa [head, expiry, tailPlan, List.append_assoc] using reachedAfter)
            tailFollows (by simpa [List.filterMap_append, cursor] using cursorAfter)
          simpa [tailPlan, List.append_assoc] using recursive
        by_cases focalOwner : focal = some owner
        · apply runtime.deviationExpirySafe_append players _ focal expiry tailPlan afterHead
          · exact runtime.deviationExpirySafe_replicate_owned_bind players _ owner focal
              focalOwner name fresh tail phase _ afterHead headFollows
          · intro afterExpiry expiryRun
            have advanced := runtime.runPolicies_expire_advances
              (.bind name owner fresh tail) players (before ++ head) tailPlan phase wire
              afterHead afterExpiry headFollows headOrdered (by simp [remainingPhases])
              headCursor (by simpa [expiry, List.append_assoc] using expiryRun)
            exact tailSafeOf afterExpiry expiryRun advanced
        · have passed := runtime.honest_service_bind_head_advances whole profile input unique
              discipline name owner fresh tail phase walk before (expiry ++ tailPlan) roster
              rounds wire players (compiled owner focalOwner) execution afterHead
              (by simpa [servicePlan, head, expiry, tailPlan, List.append_assoc] using reached)
              follows cursor (by simpa [head, expiry, tailPlan, List.append_assoc] using headRun)
          apply runtime.deviationExpirySafe_append players _ focal expiry tailPlan afterHead
          · exact DeviationExpirySafe.of_expirySafe runtime players _ focal _ afterHead
              (runtime.expirySafe_replicate_expire_of_lt players _ afterHead phase _ passed)
          · intro afterExpiry expiryRun
            exact tailSafeOf afterExpiry expiryRun
              (passed.trans_le (runtime.runPolicies_phase_mono players _ _ afterHead afterExpiry
                expiryRun))
  | resolve output owner binding fresh source checks tail ih =>
      rename_i payloadTy
      let head : List (ServiceInstruction Player) := [.player owner, .player owner] ++
        (List.replicate rounds (reactionRound roster)).flatten ++ [.includeLatest owner]
      let expiry : List (ServiceInstruction Player) :=
        List.replicate (max 1 (runtime.deadline phase))
        (ServiceInstruction.expire phase)
      let tailPlan := runtime.servicePlan roster rounds tail (phase + 1)
      rw [show runtime.servicePlan roster rounds
        (.resolve output owner binding fresh source checks tail) phase =
        head ++ expiry ++ tailPlan by simp [servicePlan, head, expiry, tailPlan,
          List.append_assoc], List.append_assoc head expiry tailPlan]
      apply runtime.deviationExpirySafe_append_of_prefix players
        (runtime.serviceEnvironment (before ++ (head ++ (expiry ++ tailPlan))) wire) focal
        head (expiry ++ tailPlan) execution
      · intro nominal member; simp [head, reactionRound] at member
      · intro afterHead headRun
        have headFollows := runtime.runPolicies_follows
          (.resolve output owner binding fresh source checks tail) phase players _
          (head.map ServiceInstruction.invocation) execution afterHead follows headRun
        have executionOrdered := runtime.runPolicies_clockOrdered players _ _ _ execution
          (State.initial_clockOrdered whole input)
          (by simpa [servicePlan, head, expiry, tailPlan, List.append_assoc] using reached)
        have headOrdered := runtime.runPolicies_clockOrdered players _ _ execution afterHead
          executionOrdered headRun
        have headCursorStep := runtime.runPolicies_service_cursor players _ head execution
          afterHead headRun
        have headCursor : afterHead.environmentHistory.length =
            ((before ++ head).filterMap ServiceInstruction.environmentSlot).length := by
          rw [List.filterMap_append, List.length_append, headCursorStep, cursor]
        have tailSafeOf (afterExpiry : runtime.application.PolicyExecution)
            (expiryRun : afterExpiry ∈ (runtime.application.runPolicies players
              (runtime.serviceEnvironment (before ++ (head ++ (expiry ++ tailPlan))) wire)
              (expiry.map ServiceInstruction.invocation) afterHead).support)
            (advanced : phase < afterExpiry.native.application.phase) :
            DeviationExpirySafe runtime players
              (runtime.serviceEnvironment (before ++ (head ++ (expiry ++ tailPlan))) wire)
              focal tailPlan afterExpiry := by
          have currentFollows := runtime.runPolicies_follows
            (.resolve output owner binding fresh source checks tail) phase players _
            ((head ++ expiry).map ServiceInstruction.invocation) execution afterExpiry follows (by
              simp only [List.map_append, runtime.application.runPolicies_append,
                FinDist.support_bind, Set.mem_iUnion]
              exact ⟨afterHead, headRun, expiryRun⟩)
          have tailFollows := State.follows_resolve_tail_of_lt phase
            afterExpiry.native.application currentFollows advanced
          have reachedAfter : afterExpiry ∈ (runtime.application.runPolicies players
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
          have cursorAfter := runtime.runPolicies_service_cursor players _ (head ++ expiry)
            execution afterExpiry (by
              simp only [List.map_append, runtime.application.runPolicies_append,
                FinDist.support_bind, Set.mem_iUnion]
              exact ⟨afterHead, headRun, expiryRun⟩)
          have recursive := ih runtime whole profile discipline players compiled wire
            (before ++ head ++ expiry) (phase + 1)
            (walk.trans (Prefix.resolve (Prefix.refl tail))) afterExpiry
            (by simpa [head, expiry, tailPlan, List.append_assoc] using reachedAfter)
            tailFollows (by simpa [List.filterMap_append, cursor] using cursorAfter)
          simpa [tailPlan, List.append_assoc] using recursive
        by_cases focalOwner : focal = some owner
        · apply runtime.deviationExpirySafe_append players _ focal expiry tailPlan afterHead
          · exact runtime.deviationExpirySafe_replicate_owned_resolve players _ owner focal
              focalOwner output binding fresh source checks tail phase _ afterHead headFollows
          · intro afterExpiry expiryRun
            have advanced := runtime.runPolicies_expire_advances
              (.resolve output owner binding fresh source checks tail) players
              (before ++ head) tailPlan phase wire afterHead afterExpiry headFollows headOrdered
              (by simp [remainingPhases]) headCursor
              (by simpa [expiry, List.append_assoc] using expiryRun)
            exact tailSafeOf afterExpiry expiryRun advanced
        · have passed := runtime.honest_service_resolve_head_advances whole profile input unique
              discipline output binding owner fresh source checks tail phase walk before
              (expiry ++ tailPlan) roster rounds wire players (compiled owner focalOwner)
              execution afterHead
              (by simpa [servicePlan, head, expiry, tailPlan, List.append_assoc] using reached)
              follows cursor (by simpa [head, expiry, tailPlan, List.append_assoc] using headRun)
          apply runtime.deviationExpirySafe_append players _ focal expiry tailPlan afterHead
          · exact DeviationExpirySafe.of_expirySafe runtime players _ focal _ afterHead
              (runtime.expirySafe_replicate_expire_of_lt players _ afterHead phase _ passed)
          · intro afterExpiry expiryRun
            exact tailSafeOf afterExpiry expiryRun
              (passed.trans_le (runtime.runPolicies_phase_mono players _ _ afterHead afterExpiry
                expiryRun))

/-- Initial-state specialization for any policy profile whose nonfocal owners
are compiled from the graph profile. -/
theorem servicePlan_deviationExpirySafe
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (focal : Option Player) (players : Player → runtime.application.PlayerPolicy)
    (compiled : ∀ owner, focal ≠ some owner →
      players owner = runtime.compilePlayerPolicy whole owner (profile owner))
    (roster : List Player) (rounds : Nat) (wire : runtime.application.WirePolicy) :
    DeviationExpirySafe runtime players
      (runtime.serviceEnvironment (runtime.servicePlan roster rounds whole 0) wire)
      focal (runtime.servicePlan roster rounds whole 0)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input))) := by
  apply runtime.servicePlan_deviationExpirySafe_from whole profile input unique discipline
    focal players compiled roster rounds wire [] 0 whole (Prefix.refl whole)
  · simp [MessageApplication.runPolicies]
  · exact State.initial_follows whole input
  · rfl

/-- The exact unilateral-deviation profile used by the serviced game: only
`focal` is replaced, so every other phase owner retains its compiled policy. -/
theorem servicePlan_unilateralDeviation_expirySafe
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (focal : Player) (replacement : runtime.application.PlayerPolicy)
    (roster : List Player) (rounds : Nat) (wire : runtime.application.WirePolicy) :
    DeviationExpirySafe runtime
      (Profile.update
        (sig := MessageApplication.policySignature Player runtime.application)
        (runtime.compileProfile whole profile) focal replacement)
      (runtime.serviceEnvironment (runtime.servicePlan roster rounds whole 0) wire)
      (some focal) (runtime.servicePlan roster rounds whole 0)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input))) := by
  apply runtime.servicePlan_deviationExpirySafe whole profile input unique discipline
    (some focal)
  intro owner different
  have ne : owner ≠ focal := by
    intro same
    subst owner
    exact different rfl
  rw [Profile.update_of_ne _ _ ne]
  rfl

end Vegas.GraphRuntime

/-- info: 'Vegas.GraphRuntime.servicePlan_unilateralDeviation_expirySafe' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.servicePlan_unilateralDeviation_expirySafe
