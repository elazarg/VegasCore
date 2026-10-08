/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.CompleteObservationPosterior
import Vegas.Examples.LateLeak.CompleteObservationValue

/-! # Public protected-opening beliefs for arbitrary native play

If every type opens at its protected turn, the complete native history weight
of that opening is its initial prior. This conclusion uses the actual runner
and does not require the canonical profile or a prescribed perturbation.
On-path Bayes consistency consequently gives the uniform conditional label
posterior, independently of the profile's unreached continuations.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : LateLeakParameters}

private theorem public_one_step_apply (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G)
    (start target : (lateLeakExecution G true).History) :
    (lateOpeningPublicModel G).runBehavioralFrom profile 1 start target =
      lateOpeningPublicKernel G profile start.state target.state := by
  have projected := congrArg (fun law : PMF LateLeakState => law target.state)
    (lateOpeningPublic_run_map_state G profile 1 start)
  rw [pmf_map_apply_of_injective _
    (fun _ _ same => lateLeak_history_eq_of_state_eq same) target] at projected
  simpa only [Function.iterate_one, PMF.pure_bind] using projected

theorem lateOpeningPublicKernel_initial (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G) :
    lateOpeningPublicKernel G profile .initial =
      lateLeakPrior.map LateLeakState.protectedTurn := by
  change lateOpeningPublicKernel G profile (lateLeakExecution G true).initHistory.state = _
  rw [lateOpeningPublicKernel_move_law G profile
    (lateLeakExecution G true).initHistory (by change ¬ False; exact not_false), PMF.bind_map]
  change (_ : PMF _).bind (fun _ => lateLeakPrior.map LateLeakState.protectedTurn) = _
  exact PMF.bind_const _ _

/-- The private type is drawn with its original prior under every native
behavioral profile. -/
theorem lateOpeningPublic_type_reach_weight (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G) (secret : LateLeakType) :
    (lateOpeningPublicModel G).historyReachWeight profile
      (lateLeakTypeHistory G true secret) = lateLeakPrior secret := by
  change (lateOpeningPublicModel G).runBehavioralFrom profile 1
    (lateLeakExecution G true).initHistory (lateLeakTypeHistory G true secret) = _
  rw [public_one_step_apply]
  change lateOpeningPublicKernel G profile .initial (.protectedTurn secret) = _
  rw [lateOpeningPublicKernel_initial]
  exact pmf_map_apply_of_injective _ (fun _ _ same => LateLeakState.protectedTurn.inj same) _

/-- Sure protected opening has exactly the type-prior prefix weight, whatever
behavior is prescribed at subsequent or unreached native decisions. -/
theorem lateOpeningPublic_protected_reach_weight (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G)
    (opens : ∀ secret,
      ((profile .sender) ((lateOpeningPublicModel G).infoOf .sender
        (lateLeakTypeHistory G true secret).trace)).map Subtype.val =
          PMF.pure (some (.opening true)))
    (secret : LateLeakType) :
    (lateOpeningPublicModel G).historyReachWeight profile
      (lateLeakOpenedHistory G true secret) = lateLeakPrior secret := by
  rw [(lateOpeningPublicModel G).historyReachWeight_eq_prior_mul profile
    (lateLeakOpenedHistory G true secret) (by change 0 < 2; decide)]
  change (lateOpeningPublicModel G).historyReachWeight profile
      (lateLeakTypeHistory G true secret) *
    (lateOpeningPublicModel G).runBehavioralFrom profile 1
      (lateLeakTypeHistory G true secret) (lateLeakOpenedHistory G true secret) = _
  rw [lateOpeningPublic_type_reach_weight, public_one_step_apply,
    lateOpeningPublicKernel_move_law G profile (lateLeakTypeHistory G true secret)
      (by change ¬ False; exact not_false)]
  change lateLeakPrior secret *
    ((((profile .sender) ((lateOpeningPublicModel G).infoOf .sender
      (lateLeakTypeHistory G true secret).trace)).map Subtype.val).bind
      (lateLeakAdvance G (.protectedTurn secret))) (.answering secret .protectedOpen) = _
  rw [opens, PMF.pure_bind]
  simp [lateLeakAdvance]

/-- Every Bayes-consistent assessment opening surely at every type has equal
protected-success label beliefs at its actual public information sites. -/
theorem lateOpeningPublic_protected_bayes_label_uniform
    (assessment : (lateOpeningPublicModel G).BehavioralAssessment)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (lateOpeningPublicModel G) assessment
      (lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain)
    (opens : ∀ secret,
      ((assessment.strategy .sender) ((lateOpeningPublicModel G).infoOf .sender
        (lateLeakTypeHistory G true secret).trace)).map Subtype.val =
          PMF.pure (some (.opening true)))
    (bit : Bool) (first second : LateLeakLabel) :
    assessment.belief .listener (lateOpeningPublicListenerSite G bit .protectedOpen)
        (lateOpeningPublicAnswerMember G bit .protectedOpen first) =
      assessment.belief .listener (lateOpeningPublicListenerSite G bit .protectedOpen)
        (lateOpeningPublicAnswerMember G bit .protectedOpen second) := by
  have positive : 0 < (lateOpeningPublicModel G).informationMass assessment.strategy .listener
      (lateOpeningPublicListenerSite G bit .protectedOpen) := by
    apply ((lateOpeningPublicModel G).informationMass_pos_iff _ _ _).mpr
    refine ⟨lateOpeningPublicAnswerMember G bit .protectedOpen first, ?_⟩
    change 0 < (lateOpeningPublicModel G).historyReachWeight assessment.strategy
      (lateLeakOpenedHistory G true (bit, first))
    rw [lateOpeningPublic_protected_reach_weight G assessment.strategy opens]
    exact pos_iff_ne_zero.mpr (lateLeakPrior_ne_zero _)
  rw [bayes .listener _ positive, bayes .listener _ positive]
  change (lateOpeningPublicModel G).historyReachWeight assessment.strategy
      (lateLeakOpenedHistory G true (bit, first)) / _ =
    (lateOpeningPublicModel G).historyReachWeight assessment.strategy
      (lateLeakOpenedHistory G true (bit, second)) / _
  rw [lateOpeningPublic_protected_reach_weight G assessment.strategy opens,
    lateOpeningPublic_protected_reach_weight G assessment.strategy opens]
  rfl

end Vegas
