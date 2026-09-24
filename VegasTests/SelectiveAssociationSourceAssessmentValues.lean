/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceGuessOptimality
import VegasTests.SelectiveAssociationSourceOpeningPayoffs
import Interaction.ReactiveAssessmentEvaluation

/-! # Source assessment values in the actual interaction evaluator

Continuation deviations are whole behavioral policies. Their values are the
belief expectations of the existing bounded interaction evaluator, with the
same history, private recall, pending messages, and remaining calendar.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

theorem information_control (Claim : Type) [Fintype Claim] (who : Player)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (history : (model Claim).InformationHistory who (some (past, view))) :
    ∃ control : (application Claim).Control, history.1.state = some control ∧
      control.actor = some who ∧ control.execution.recall who = past ∧
      control.execution.observe (application Claim) who = view := by
  rcases history with ⟨⟨state, trace⟩, observed⟩
  rw [history_observe] at observed
  cases state with
  | none => cases observed
  | some control =>
      change (if control.actor = some who then some (control.execution.recall who,
        control.execution.observe (application Claim) who) else none) =
          some (past, view) at observed
      split at observed
      · rename_i active
        exact ⟨control, rfl, active, (Prod.mk.inj (Option.some.inj observed)).1,
          (Prod.mk.inj (Option.some.inj observed)).2⟩
      · cases observed

theorem decision_remaining (Claim : Type) [Fintype Claim] (event : Event)
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some (eventOwner event))
    (granted : control.execution.application.visit = some event) :
    control.remaining = (afterResponse event).length ∧
      control.execution.environmentRecall.length = (beforeResponse event).length + 1 := by
  have position := (decision_cursor Claim event control trace (eventOwner event) active granted).2
  have counted := ((menu Claim).roundSupported_uniform
    (FinDist.pure initial) horizon (scheduler Claim) trace).1
  have lengths := congrArg List.length (response_split event)
  simp only [List.length_append, List.length_cons] at lengths
  change _ + _ = calendar.length at counted
  exact ⟨by omega, position⟩

def decodedAlternative (Claim : Type) [Fintype Claim] (who : Player)
    (alternative : (model Claim).BehavioralPolicy who) : (application Claim).Policy :=
  (application Claim).decodePolicy
    ((menu Claim).embedPolicy (FinDist.pure initial) horizon (scheduler Claim) who alternative)

theorem decoded_update_profile (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (who : Player) (alternative : (model Claim).BehavioralPolicy who) :
    (menu Claim).decodeProfile (FinDist.pure initial) horizon (scheduler Claim)
        (Profile.update (sig := (model Claim).behavioralSignature)
          (profile Claim defaultClaim) who alternative) =
      Function.update (policy Claim defaultClaim) who
        (decodedAlternative Claim who alternative) := by
  funext other past view
  by_cases same : other = who
  · subst other
    simp only [ReactiveApplication.ResponseMenu.decodeProfile, Profile.update,
      Function.update_self]
    rfl
  · simp only [ReactiveApplication.ResponseMenu.decodeProfile, Profile.update,
      Function.update_of_ne same]
    exact decode_profile Claim defaultClaim other past view

theorem context_value_finish (Claim : Type) [Fintype Claim]
    (assessment : (model Claim).BehavioralAssessment) (who : Player)
    (site : (model Claim).InformationSite who) (alternative : (model Claim).BehavioralPolicy who) :
    (assessment.continuationContext site (payoff who) (2 * horizon + 1)).value alternative =
      (assessment.belief who site).expect (fun history =>
        ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
          ((menu Claim).decodeProfile (FinDist.pure initial) horizon (scheduler Claim)
            (Profile.update (sig := (model Claim).behavioralSignature)
              assessment.strategy who alternative)) history.1.state).expect
                (fun state => utility (protocolResults state) who)) := by
  exact (menu Claim).context_value_finish (FinDist.pure initial) horizon (scheduler Claim)
    assessment who site (fun state => utility (protocolResults state) who) alternative

theorem prescribed_context_value_finish (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (assessment : (model Claim).BehavioralAssessment)
    (strategy : assessment.strategy = profile Claim defaultClaim) (who : Player)
    (site : (model Claim).InformationSite who) (alternative : (model Claim).BehavioralPolicy who) :
    (assessment.continuationContext site (payoff who) (2 * horizon + 1)).value alternative =
      (assessment.belief who site).expect (fun history =>
        ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
          (Function.update (policy Claim defaultClaim) who
            (decodedAlternative Claim who alternative)) history.1.state).expect
              (fun state => utility (protocolResults state) who)) := by
  rw [context_value_finish, strategy, decoded_update_profile]

theorem prescribed_context_baseline (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (assessment : (model Claim).BehavioralAssessment)
    (strategy : assessment.strategy = profile Claim defaultClaim) (who : Player)
    (site : (model Claim).InformationSite who) :
    (assessment.continuationContext site (payoff who) (2 * horizon + 1)).value
        (assessment.strategy who) =
      (assessment.belief who site).expect (fun history =>
        ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
          (policy Claim defaultClaim) history.1.state).expect
            (fun state => utility (protocolResults state) who)) := by
  rw [context_value_finish, Profile.update_eq_self, strategy]
  have decoded : (menu Claim).decodeProfile (FinDist.pure initial) horizon (scheduler Claim)
      (profile Claim defaultClaim) = policy Claim defaultClaim := by
    funext other past view
    exact decode_profile Claim defaultClaim other past view
  rw [decoded]

end VegasTests.SelectiveAssociation.NamedSource
