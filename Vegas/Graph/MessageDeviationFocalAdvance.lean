/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageDeviationAdvance
import Vegas.Graph.MessageReachedActions

/-! # Actual focal advancement conserves extracted deviation continuations -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

theorem Prefix.deviationContinuationAt_bind_realizes
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (inputs : FinDist (VEnv L Γ₀))
    (nativePlayers : Player → runtime.application.PlayerPolicy)
    (nativeEnvironment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) (focal : Player)
    (locality : ∀ {target} (suffix : Graph Player L target Δ) site
      (observation : Observation L focal target) (left right : OwnAction Player L),
      ReachedOwnAction runtime whole inputs nativePlayers nativeEnvironment schedule focal
        suffix site observation left →
      ReachedOwnAction runtime whole inputs nativePlayers nativeEnvironment schedule focal
        suffix site observation right → left = right)
    (profile : BehavioralProfile whole)
    (focalPolicy : profile focal = runtime.extractedObservationPolicy whole inputs
      nativePlayers nativeEnvironment schedule focal)
    (site : Nat) (name : VarId) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed focal (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole (.bind name focal fresh next) site)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (choice : PublicationResult (L.Val payload))
    (nextBindings : Bindings Player)
    (nextCandidates : CommitmentCandidates Player Slot (Raw L)) (nextClock : Nat)
    (execution after : runtime.application.PolicyExecution)
    (atCursor : execution.native.application =
      .running (.bind name focal fresh next) ideal values bindings candidates
        site clock enteredAt)
    (atAfter : after.native.application = .running next
      (VEnv.cons ((R.valueEquiv payload).symm choice) ideal)
      (PublicValues.consSealed values) nextBindings nextCandidates
      (site + 1) nextClock nextClock)
    (reached : ReachedOwnAction runtime whole inputs nativePlayers nativeEnvironment schedule
      focal (.bind name focal fresh next) site (observe focal ideal)
      (.bind focal name payload choice))
    (histories : after.principalHistory = execution.principalHistory)
    (beforeFollows : execution.native.application.Follows whole 0)
    (afterFollows : after.native.application.Follows whole 0)
    (unique : (Γ.map Prod.fst).Nodup) :
    runtime.deviationContinuationAt whole profile focal execution.principalHistory
        execution.native.application beforeFollows =
      runtime.deviationContinuationAt whole profile focal after.principalHistory
        after.native.application afterFollows := by
  have extracted := runtime.extractedObservationPolicy_realizesAt whole inputs nativePlayers
    nativeEnvironment schedule focal locality walk
  have selected : bindKernel (walk.profileTail profile) (observe focal ideal, []) =
      FinDist.pure choice := by
    change (walk.policyTail focal (profile focal)).1 rfl (observe focal ideal, []) = _
    rw [focalPolicy]
    exact extracted.1 rfl (observe focal ideal) [] choice reached
  have independent : IgnoresOwnHistory whole profile focal := by
    change PolicyIgnoresOwnHistory focal whole (profile focal)
    rw [focalPolicy]
    exact runtime.extractedObservationPolicy_ignoresOwnHistory whole inputs nativePlayers
      nativeEnvironment schedule focal
  rw [runtime.deviationContinuationAt_running whole profile focal execution beforeFollows
    (.bind name focal fresh next) site walk ideal values bindings candidates clock enteredAt
    atCursor]
  rw [runtime.deviationContinuationAt_running whole profile focal after afterFollows next
    (site + 1) (walk.trans (.bind (.refl next)))
    (VEnv.cons ((R.valueEquiv payload).symm choice) ideal)
    (PublicValues.consSealed values) nextBindings nextCandidates nextClock nextClock atAfter]
  rw [histories]
  exact walk.deviationContinuation_bind_advance runtime whole profile focal independent
    site name fresh next ideal execution.principalHistory choice selected unique

theorem Prefix.deviationContinuationAt_resolve_realizes
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (inputs : FinDist (VEnv L Γ₀))
    (nativePlayers : Player → runtime.application.PlayerPolicy)
    (nativeEnvironment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) (focal : Player)
    (locality : ∀ {target} (suffix : Graph Player L target Δ) site
      (observation : Observation L focal target) (left right : OwnAction Player L),
      ReachedOwnAction runtime whole inputs nativePlayers nativeEnvironment schedule focal
        suffix site observation left →
      ReachedOwnAction runtime whole inputs nativePlayers nativeEnvironment schedule focal
        suffix site observation right → left = right)
    (profile : BehavioralProfile whole)
    (focalPolicy : profile focal = runtime.extractedObservationPolicy whole inputs
      nativePlayers nativeEnvironment schedule focal)
    (site : Nat) (outputName bindingName : VarId) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed focal (R.result payload)))
    (checks : List (GuardCheck ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole
      (.resolve outputName focal bindingName fresh source checks next) site)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (disclose : Bool) (result : PublicationResult (L.Val payload))
    (nextClock : Nat) (execution after : runtime.application.PolicyExecution)
    (atCursor : execution.native.application =
      .running (.resolve outputName focal bindingName fresh source checks next)
        ideal values bindings candidates site clock enteredAt)
    (accepted : acceptedResult source checks ideal disclose = result)
    (atAfter : after.native.application = .running next
      (VEnv.cons ((R.valueEquiv payload).symm result) ideal)
      (PublicValues.consPublic ((R.valueEquiv payload).symm result) values)
      bindings candidates (site + 1) nextClock nextClock)
    (reached : ReachedOwnAction runtime whole inputs nativePlayers nativeEnvironment schedule
      focal (.resolve outputName focal bindingName fresh source checks next) site
      (observe focal ideal) (.resolve focal bindingName disclose))
    (histories : after.principalHistory = execution.principalHistory)
    (beforeFollows : execution.native.application.Follows whole 0)
    (afterFollows : after.native.application.Follows whole 0)
    (unique : (Γ.map Prod.fst).Nodup) :
    runtime.deviationContinuationAt whole profile focal execution.principalHistory
        execution.native.application beforeFollows =
      runtime.deviationContinuationAt whole profile focal after.principalHistory
        after.native.application afterFollows := by
  have extracted := runtime.extractedObservationPolicy_realizesAt whole inputs nativePlayers
    nativeEnvironment schedule focal locality walk
  have selected : resolveKernel (walk.profileTail profile) (observe focal ideal, []) =
      FinDist.pure disclose := by
    change (walk.policyTail focal (profile focal)).1 rfl (observe focal ideal, []) = _
    rw [focalPolicy]
    exact extracted.1 rfl (observe focal ideal) [] disclose reached
  have independent : IgnoresOwnHistory whole profile focal := by
    change PolicyIgnoresOwnHistory focal whole (profile focal)
    rw [focalPolicy]
    exact runtime.extractedObservationPolicy_ignoresOwnHistory whole inputs nativePlayers
      nativeEnvironment schedule focal
  rw [runtime.deviationContinuationAt_running whole profile focal execution beforeFollows
    (.resolve outputName focal bindingName fresh source checks next) site walk ideal values
    bindings candidates clock enteredAt atCursor]
  rw [runtime.deviationContinuationAt_running whole profile focal after afterFollows next
    (site + 1) (walk.trans (.resolve (.refl next)))
    (VEnv.cons ((R.valueEquiv payload).symm result) ideal)
    (PublicValues.consPublic ((R.valueEquiv payload).symm result) values)
    bindings candidates nextClock nextClock atAfter]
  rw [histories]
  rw [← accepted]
  exact walk.deviationContinuation_resolve_advance runtime whole profile focal independent
    site outputName bindingName fresh source checks next ideal execution.principalHistory
    disclose selected unique

/-- info: 'Vegas.GraphRuntime.Prefix.deviationContinuationAt_bind_realizes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.Prefix.deviationContinuationAt_bind_realizes

/-- info: 'Vegas.GraphRuntime.Prefix.deviationContinuationAt_resolve_realizes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.Prefix.deviationContinuationAt_resolve_realizes

end Vegas.GraphRuntime
