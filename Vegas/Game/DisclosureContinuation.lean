/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.DisclosureContinuation
import Vegas.Game.DisclosureBeliefs
import GameTheoryExtensions.Math.Probability.Conditioning

/-! # Uniform legal deviations at actual source information fibers

A compressed continuation lifts to one admitted original-source policy at
each original observation. The policy is fixed over the entire information
fiber. It reproduces the full terminal state law from every hidden state in
that fiber, using the existing source protocol continuation evaluator.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {who : Player}

private theorem liftDisclosure_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (alternative : BehavioralPolicy who program)
    (recall : DecisionView who Γ → List (OwnAction Player L))
    (view : DecisionView who Γ) (config : Config Player L Γ)
    (observed : config.view who = view) :
    runFrom program (Function.update profile who
        (alternative.rebaseHistory view.2.length (recall view) program)) config =
      runFrom program (Function.update profile who alternative)
        (config.withOwnHistory who (recall (config.view who))) := by
  rw [observed]
  exact rebaseHistory_runFrom program profile alternative view.2 (recall view) config
    (congrArg Prod.snd observed)

/-- Every whole compressed continuation has one admitted lift at each
original information fiber. The lift is chosen from the observed site, not
from its hidden configuration. No reach or equilibrium hypothesis is used. -/
theorem exists_disclosure_continuation_lift {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (profile : BehavioralProfile program) → (alternative : BehavioralPolicy who program) →
    alternative.Admitted program admission →
    (recall : DecisionView who Γ → List (OwnAction Player L)) →
    (view : ProtocolView who program) →
    ∃ lifted : BehavioralPolicy who program,
      lifted.Admitted program admission ∧
      ∀ state : ProtocolState program, ProtocolState.observe who program state = view →
        ProtocolState.continuationLaw program (Function.update profile who lifted) state =
          ProtocolState.continuationLaw program (Function.update profile who alternative)
            (ProtocolState.normalizeDisclosureRecall program recall state)
  | _, _, .ret _, _, _, _, _, _, _ => ⟨PUnit.unit, trivial, fun _ _ => rfl⟩
  | _, _, .sample name fresh law next, admission, profile, alternative, permitted,
      recall, view => by
      cases view with
      | inl current =>
          refine ⟨alternative.rebaseHistory current.2.length (recall current) _,
            alternative.rebaseHistory_admitted _ admission permitted _ _, ?_⟩
          intro state observed
          cases state with
          | inl config =>
              exact liftDisclosure_entry _ profile alternative recall current config
                (Sum.inl.inj observed)
          | inr _ => cases observed
      | inr later =>
          obtain ⟨lifted, legal, realizes⟩ := exists_disclosure_continuation_lift next admission
            profile alternative permitted (fun current => recall (current.back false)) later
          refine ⟨lifted, legal, ?_⟩
          intro state observed
          cases state with
          | inl _ => cases observed
          | inr state => exact realizes state (Sum.inr.inj observed)
  | _, _, .commit (payload := payload) name owner fresh guard next, admission, profile,
      alternative, permitted, recall, view => by
      cases view with
      | inl current =>
          refine ⟨alternative.rebaseHistory current.2.length (recall current) _,
            alternative.rebaseHistory_admitted _ admission permitted _ _, ?_⟩
          intro state observed
          cases state with
          | inl config =>
              exact liftDisclosure_entry _ profile alternative recall current config
                (Sum.inl.inj observed)
          | inr _ => cases observed
      | inr later =>
          obtain ⟨lifted, legal, realizes⟩ := exists_disclosure_continuation_lift next
            (fun site => admission (some site)) (afterCommit profile) alternative.2 permitted.2
            (bindingRecall name owner payload recall) later
          refine ⟨(alternative.1, lifted), ⟨permitted.1, legal⟩, ?_⟩
          intro state observed
          cases state with
          | inl _ => cases observed
          | inr state =>
              change ProtocolState.continuationLaw next
                (afterCommit (Function.update profile who (alternative.1, lifted))) state =
                  ProtocolState.continuationLaw next
                    (afterCommit (Function.update profile who alternative))
                    (ProtocolState.normalizeDisclosureRecall next
                      (bindingRecall name owner payload recall) state)
              rw [afterCommit_update, afterCommit_update]
              exact realizes state (Sum.inr.inj observed)
  | _, _, .reveal (payload := payload) published owner name fresh selected unresolved next,
      admission, profile, alternative, permitted, recall, view => by
      cases view with
      | inl current =>
          refine ⟨alternative.rebaseHistory current.2.length (recall current) _,
            alternative.rebaseHistory_admitted _ admission permitted _ _, ?_⟩
          intro state observed
          cases state with
          | inl config =>
              exact liftDisclosure_entry _ profile alternative recall current config
                (Sum.inl.inj observed)
          | inr _ => cases observed
      | inr later =>
          obtain ⟨lifted, legal, realizes⟩ := exists_disclosure_continuation_lift next admission
            (afterReveal profile) alternative.2 permitted
            (publicationRecall published name owner payload recall) later
          refine ⟨(alternative.1, lifted), legal, ?_⟩
          intro state observed
          cases state with
          | inl _ => cases observed
          | inr state =>
              change ProtocolState.continuationLaw next
                (afterReveal (Function.update profile who (alternative.1, lifted))) state =
                  ProtocolState.continuationLaw next
                    (afterReveal (Function.update profile who alternative))
                    (ProtocolState.normalizeDisclosureRecall next
                      (publicationRecall published name owner payload recall) state)
              rw [afterReveal_update, afterReveal_update]
              exact realizes state (Sum.inr.inj observed)

/-- At an actual positive original source observation, the same admitted
lift matches a whole deviation under the corresponding normalized posterior.
Both beliefs here are computed from actual initialized source prefix laws. -/
theorem normalized_disclosure_prefix_deviation [Fintype Player]
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (profile : BehavioralProfile program) (policy alternative : BehavioralPolicy who program)
    (permitted : alternative.Admitted program admission)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (initial : PMF (Config Player L Γ))
    (registryEq : ∀ config ∈ initial.support, config.registry = registry)
    (revelationsEq : ∀ config ∈ initial.support, @config.revelations = @revelations)
    (count : Nat) :
    let original := initial.bind fun config =>
      (fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who policy)))^[count]
          (PMF.pure (ProtocolState.entry program config))
    let normalized := initial.bind fun config =>
      (fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who (policy.normalizeDisclosures program registry revelations))))
          ^[count] (PMF.pure (ProtocolState.entry program config))
    ∀ observed ∈ (original.map (ProtocolState.observe who program)).support,
      ∃ lifted : BehavioralPolicy who program, lifted.Admitted program admission ∧
        ((fiberConditional original (ProtocolState.observe who program) observed).bind
          (ProtocolState.continuationLaw program (Function.update profile who lifted))) =
        (fiberConditional normalized (ProtocolState.observe who program)
          (ProtocolView.normalizeDisclosureRecall program (fun view => view.2) observed)).bind
            (ProtocolState.continuationLaw program (Function.update profile who alternative)) := by
  classical
  dsimp only
  intro observed present
  obtain ⟨lifted, admitted, realizes⟩ := exists_disclosure_continuation_lift program admission
    profile alternative permitted (fun view => view.2) observed
  refine ⟨lifted, admitted, ?_⟩
  have posterior := normalized_disclosure_prefix_posterior program profile policy registry
    revelations initial registryEq revelationsEq count observed present
  rw [← posterior, PMF.bind_map]
  apply bind_congr_on_support _
  intro state member
  apply realizes state
  obtain ⟨witness, supported, equal⟩ := PMF.support_map .. ▸ present
  have meets : ∃ state ∈ (ProtocolState.observe who program) ⁻¹' {observed},
      state ∈ (initial.bind fun config =>
        (fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
          (Function.update profile who policy)))^[count]
            (PMF.pure (ProtocolState.entry program config))).support :=
    ⟨witness, equal, supported⟩
  rw [fiberConditional, dite_eq_left meets] at member
  exact ((PMF.mem_support_filter_iff _).mp member).1

end Vegas.SourceProgram
