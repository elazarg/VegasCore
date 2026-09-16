/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.DeviationConservation
import Vegas.Pending.DeviationFocalAdvance

/-! # Supported focal environment invocations -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

private def bindRealizationShape :
    State Player L Δ → OwnAction Player L → State Player L Δ → Prop
  | .running (.bind name owner (payload := payload) _fresh next) ideal values _bindings _candidates
      site _clock _enteredAt, action, after =>
      ∃ choice nextBindings nextCandidates nextClock,
        action = .bind owner name payload choice ∧
        after = .running next (VEnv.cons ((R.valueEquiv payload).symm choice) ideal)
          (PublicValues.consSealed values) nextBindings nextCandidates
          (site + 1) nextClock nextClock
  | _, _, _ => True

private theorem State.RealizesOwnAction.bind_shape
    {before after : State Player L Δ} {action : OwnAction Player L}
    (realizes : State.RealizesOwnAction before action after) :
    bindRealizationShape before action after := by
  cases realizes <;> simp [bindRealizationShape]

private def resolveRealizationShape :
    State Player L Δ → OwnAction Player L → State Player L Δ → Prop
  | .running (.resolve _output owner binding (payload := payload) _fresh source checks next)
      ideal values _bindings _candidates site _clock _enteredAt, action, after =>
      ∃ disclose result nextClock,
        action = .resolve owner binding disclose ∧
        acceptedResult source checks ideal disclose = result ∧
        after = .running next (VEnv.cons ((R.valueEquiv payload).symm result) ideal)
          (PublicValues.consPublic ((R.valueEquiv payload).symm result) values)
          _bindings _candidates (site + 1) nextClock nextClock
  | _, _, _ => True

private theorem State.RealizesOwnAction.resolve_shape
    {before after : State Player L Δ} {action : OwnAction Player L}
    (realizes : State.RealizesOwnAction before action after) :
    resolveRealizationShape before action after := by
  cases realizes with
  | bind => trivial
  | resolveFailure => simp [resolveRealizationShape, acceptedResult, proposedResult]
  | resolveSuccess value accepted nextClock =>
      simp [resolveRealizationShape, accepted]

/-- One actually supported environment invocation at a focal bind cursor
preserves the extracted deviation continuation. A same-phase successor is a
frame change only; an advancing successor itself supplies the reached source
action used by the extracted observation policy. -/
theorem Prefix.deviationContinuationAt_focal_bind_environment
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (inputs : FinDist (VEnv L Γ₀)) (input : VEnv L Γ₀)
    (inputMem : input ∈ inputs.support)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule before rest : List (@MessageApplication.Invocation Player))
    (split : schedule = before ++ .environment :: rest) (focal : Player)
    (locality : ∀ {target} (suffix : Graph Player L target Δ) site
      (observation : Observation L focal target) (left right : OwnAction Player L),
      ReachedOwnAction runtime whole inputs players environment schedule focal
        suffix site observation left →
      ReachedOwnAction runtime whole inputs players environment schedule focal
        suffix site observation right → left = right)
    (profile : BehavioralProfile whole)
    (focalPolicy : profile focal = runtime.extractedObservationPolicy whole inputs
      players environment schedule focal)
    (site : Nat) (name : VarId) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed focal (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole (.bind name focal fresh next) site)
    (execution after : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies players environment before
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (supported : after ∈
      (runtime.application.invoke players environment execution .environment).support)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (atCursor : execution.native.application =
      .running (.bind name focal fresh next) ideal values bindings candidates
        site clock enteredAt)
    (follows : execution.native.application.Follows whole 0)
    (unique : (Γ.map Prod.fst).Nodup) :
    deviationContinuationAt runtime whole profile focal after.principalHistory
        after.native.application
        (runtime.invoke_follows whole 0 players environment .environment
          execution after follows supported) =
      deviationContinuationAt runtime whole profile focal execution.principalHistory
        execution.native.application follows := by
  have afterFollows := runtime.invoke_follows whole 0 players environment .environment
    execution after follows supported
  have invokeSupport := supported
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨command, _commandMem, stepMem⟩ := supported
  have histories := runtime.application.environmentStep_principalHistory execution command after
    stepMem
  have monotone := runtime.environmentPolicyStep_phase_mono execution after command stepMem
  rw [atCursor] at monotone
  by_cases samePhase : after.native.application.phase = site
  · have runMem : after ∈ (runtime.application.runPolicies players environment
        [.environment] execution).support := by
      simpa [MessageApplication.runPolicies] using invokeSupport
    obtain ⟨candidates', clock', enteredAt', atAfter⟩ :=
      runtime.runPolicies_running_eq_of_phase_eq (.bind name focal fresh next) ideal values
        bindings candidates site clock enteredAt players environment [.environment] execution
        after atCursor runMem samePhase
    have independent : IgnoresOwnHistory whole profile focal := by
      change PolicyIgnoresOwnHistory focal whole (profile focal)
      rw [focalPolicy]
      exact runtime.extractedObservationPolicy_ignoresOwnHistory whole inputs players environment
        schedule focal
    rw [runtime.deviationContinuationAt_eq_erased whole profile focal independent after
      afterFollows (.bind name focal fresh next) site walk ideal values bindings candidates'
      clock' enteredAt' atAfter]
    rw [runtime.deviationContinuationAt_eq_erased whole profile focal independent execution
      follows (.bind name focal fresh next) site walk ideal values bindings candidates clock
      enteredAt atCursor]
    dsimp only
    have erasedHistories :
        (eraseFocalExecution runtime focal after).principalHistory =
          (eraseFocalExecution runtime focal execution).principalHistory := by
      exact congrArg (eraseFocalHistory focal) histories
    rw [erasedHistories]
  · have phaseMono : site ≤ after.native.application.phase := by
      simpa [State.phase] using monotone
    have advanced : site < after.native.application.phase := by omega
    rcases runtime.application.invoke_native_step players environment execution after .environment
      invokeSupport with nativeSame | ⟨action, actionStep⟩
    · have phaseSame := congrArg (fun state => state.application.phase) nativeSame
      rw [atCursor] at phaseSame
      exact (samePhase phaseSame).elim
    · have nativeEq : execution.native =
          ⟨.running (.bind name focal fresh next) ideal values bindings candidates
            site clock enteredAt, execution.native.pool, execution.native.receipts⟩ := by
        cases hnative : execution.native with
        | mk application pool receipts =>
            rw [hnative] at atCursor
            simp only at atCursor
            subst application
            rfl
      rw [nativeEq] at actionStep
      obtain ⟨choice, realizes⟩ := runtime.phaseChangingStep_bind_realizes ideal values bindings
        candidates site clock enteredAt execution.native.pool execution.native.receipts action
        after.native actionStep advanced
      have realizesActual : State.RealizesOwnAction execution.native.application
          (.bind focal name payload choice) after.native.application :=
        atCursor.symm ▸ realizes
      have actionReached : ReachedOwnAction runtime whole inputs players environment schedule focal
          (.bind name focal fresh next) site (observe focal ideal)
          (.bind focal name payload choice) := by
        refine ⟨rfl, input, inputMem, before, .environment, rest, split, execution, after,
          reached, invokeSupport, ideal, values, bindings, candidates, clock, enteredAt,
          atCursor, rfl, realizesActual⟩
      have shape := realizes.bind_shape
      simp only [bindRealizationShape] at shape
      obtain ⟨selected, nextBindings, nextCandidates, nextClock, actionEq, atAfter⟩ := shape
      injection actionEq with choiceEq
      subst selected
      exact (walk.deviationContinuationAt_bind_realizes runtime whole inputs players
        environment schedule focal locality profile focalPolicy site name fresh next ideal
        values bindings candidates clock enteredAt choice nextBindings nextCandidates
        nextClock execution after atCursor atAfter actionReached histories follows
        afterFollows unique).symm

/-- Resolve analogue of `deviationContinuationAt_focal_bind_environment`.
Public agreement and binding soundness are derived from the initialized prefix,
so verified openings and timeout failures normalize to exact source actions. -/
theorem Prefix.deviationContinuationAt_focal_resolve_environment
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (inputs : FinDist (VEnv L Γ₀)) (input : VEnv L Γ₀)
    (inputMem : input ∈ inputs.support) (unique : (Γ₀.map Prod.fst).Nodup)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule before rest : List (@MessageApplication.Invocation Player))
    (split : schedule = before ++ .environment :: rest) (focal : Player)
    (locality : ∀ {target} (suffix : Graph Player L target Δ) site
      (observation : Observation L focal target) (left right : OwnAction Player L),
      ReachedOwnAction runtime whole inputs players environment schedule focal
        suffix site observation left →
      ReachedOwnAction runtime whole inputs players environment schedule focal
        suffix site observation right → left = right)
    (profile : BehavioralProfile whole)
    (focalPolicy : profile focal = runtime.extractedObservationPolicy whole inputs
      players environment schedule focal)
    (site : Nat) (outputName bindingName : VarId) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed focal (R.result payload)))
    (checks : List (GuardCheck ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole
      (.resolve outputName focal bindingName fresh source checks next) site)
    (execution after : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies players environment before
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (supported : after ∈
      (runtime.application.invoke players environment execution .environment).support)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (atCursor : execution.native.application =
      .running (.resolve outputName focal bindingName fresh source checks next)
        ideal values bindings candidates site clock enteredAt)
    (follows : execution.native.application.Follows whole 0) :
    deviationContinuationAt runtime whole profile focal after.principalHistory
        after.native.application
        (runtime.invoke_follows whole 0 players environment .environment
          execution after follows supported) =
      deviationContinuationAt runtime whole profile focal execution.principalHistory
        execution.native.application follows := by
  have afterFollows := runtime.invoke_follows whole 0 players environment .environment
    execution after follows supported
  have invokeSupport := supported
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨command, _commandMem, stepMem⟩ := supported
  have histories := runtime.application.environmentStep_principalHistory execution command after
    stepMem
  have monotone := runtime.environmentPolicyStep_phase_mono execution after command stepMem
  rw [atCursor] at monotone
  by_cases samePhase : after.native.application.phase = site
  · have runMem : after ∈ (runtime.application.runPolicies players environment
        [.environment] execution).support := by
      simpa [MessageApplication.runPolicies] using invokeSupport
    obtain ⟨candidates', clock', enteredAt', atAfter⟩ :=
      runtime.runPolicies_running_eq_of_phase_eq
        (.resolve outputName focal bindingName fresh source checks next) ideal values bindings
        candidates site clock enteredAt players environment [.environment] execution after
        atCursor runMem samePhase
    have independent : IgnoresOwnHistory whole profile focal := by
      change PolicyIgnoresOwnHistory focal whole (profile focal)
      rw [focalPolicy]
      exact runtime.extractedObservationPolicy_ignoresOwnHistory whole inputs players environment
        schedule focal
    rw [runtime.deviationContinuationAt_eq_erased whole profile focal independent after
      afterFollows (.resolve outputName focal bindingName fresh source checks next) site walk ideal
      values bindings candidates' clock' enteredAt' atAfter]
    rw [runtime.deviationContinuationAt_eq_erased whole profile focal independent execution
      follows (.resolve outputName focal bindingName fresh source checks next) site walk ideal
      values bindings candidates clock enteredAt atCursor]
    dsimp only
    have erasedHistories :
        (eraseFocalExecution runtime focal after).principalHistory =
          (eraseFocalExecution runtime focal execution).principalHistory := by
      exact congrArg (eraseFocalHistory focal) histories
    rw [erasedHistories]
  · have phaseMono : site ≤ after.native.application.phase := by
      simpa [State.phase] using monotone
    have advanced : site < after.native.application.phase := by omega
    rcases runtime.application.invoke_native_step players environment execution after .environment
      invokeSupport with nativeSame | ⟨action, actionStep⟩
    · have phaseSame := congrArg (fun state => state.application.phase) nativeSame
      rw [atCursor] at phaseSame
      exact (samePhase phaseSame).elim
    · have nativeEq : execution.native =
          ⟨.running (.resolve outputName focal bindingName fresh source checks next)
            ideal values bindings candidates site clock enteredAt,
            execution.native.pool, execution.native.receipts⟩ := by
        cases hnative : execution.native with
        | mk application pool receipts =>
            rw [hnative] at atCursor
            simp only at atCursor
            subst application
            rfl
      rw [nativeEq] at actionStep
      have agreement := runtime.runPolicies_preserves_publicAgreement players environment before _
        execution (State.initial_publicAgreement whole input) reached
      rw [atCursor] at agreement
      change (values : PublicValues Γ) = (PublicValues.ofVEnv ideal : PublicValues Γ) at agreement
      have sound := runtime.runPolicies_initial_bindingSoundness whole input unique players
        environment before execution reached
      rw [atCursor] at sound
      obtain ⟨disclose, realizes⟩ := runtime.phaseChangingStep_resolve_realizes ideal values
        bindings candidates site clock enteredAt execution.native.pool execution.native.receipts
        agreement sound action after.native actionStep advanced
      have realizesActual : State.RealizesOwnAction execution.native.application
          (.resolve focal bindingName disclose) after.native.application := atCursor.symm ▸ realizes
      have actionReached : ReachedOwnAction runtime whole inputs players environment schedule focal
          (.resolve outputName focal bindingName fresh source checks next) site
          (observe focal ideal) (.resolve focal bindingName disclose) := by
        refine ⟨rfl, input, inputMem, before, .environment, rest, split, execution, after,
          reached, invokeSupport, ideal, values, bindings, candidates, clock, enteredAt,
          atCursor, rfl, realizesActual⟩
      have shape := realizes.resolve_shape
      simp only [resolveRealizationShape] at shape
      obtain ⟨selected, result, nextClock, actionEq, accepted, atAfter⟩ := shape
      injection actionEq with discloseEq
      subst selected
      exact (walk.deviationContinuationAt_resolve_realizes runtime whole inputs players
        environment schedule focal locality profile focalPolicy site outputName bindingName fresh
        source checks next ideal values bindings candidates clock enteredAt disclose result
        nextClock execution after atCursor accepted atAfter actionReached histories follows
        afterFollows (walk.target_names_nodup unique)).symm

end Vegas.GraphRuntime
