/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.DisclosureEnforcement

/-! # Information and continuation values for one optional disclosure

The sender and the disclosed receiver know the private state. The silent
receiver's information fiber contains exactly one history per prior state.
Full prior support is used to represent that fiber on the complete state type.
-/

noncomputable section

namespace GameTheory.Protocol.DisclosureEnforcement

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

variable {Secret Decision : Type} [Nonempty Decision]
variable (prior : FinDist Secret) (full : ∀ secret, secret ∈ prior.support)

def senderSite (secret : Secret) :
    (model (Decision := Decision) prior true).InformationSite false :=
  (model prior true).informationSite false (senderHistory prior full true secret) false
    (by exact id) rfl

def receiverSilentSite (ambient : Bool) :
    (model (Decision := Decision) prior ambient).InformationSite true :=
  (model prior ambient).informationSite true
    (receiverHistory prior full ambient prior.support_nonempty.choose false) (fallback true)
    (by exact id) (by cases ambient <;> rfl)

def receiverDisclosedSite (secret : Secret) :
    (model (Decision := Decision) prior true).InformationSite true :=
  (model prior true).informationSite true (receiverHistory prior full true secret true)
    (fallback true) (by exact id) rfl

theorem history_at_sender (secret : Secret)
    (history : (model (Decision := Decision) prior true).InformationHistory false
      (senderSite prior full secret).1) :
    history.1 = senderHistory prior full true secret := by
  have observed := history.2
  rw [info_state] at observed
  have known : Classified prior full true history.1 := classified prior full true history.1.trace
  rcases known with same | ⟨other, same⟩ | ⟨other, ask, same⟩ | ⟨other, ask, guess, same⟩
  all_goals rw [same] at observed
  all_goals try cases observed
  exact same

theorem history_at_disclosed (secret : Secret)
    (history : (model (Decision := Decision) prior true).InformationHistory true
      (receiverDisclosedSite prior full secret).1) :
    history.1 = receiverHistory prior full true secret true := by
  have observed := history.2
  rw [info_state] at observed
  have known : Classified prior full true history.1 := classified prior full true history.1.trace
  rcases known with same | ⟨other, same⟩ | ⟨other, ask, same⟩ | ⟨other, ask, guess, same⟩
  all_goals rw [same] at observed
  all_goals try cases observed
  cases ask
  · cases observed
  · cases observed
    exact same

theorem history_at_silent (ambient : Bool)
    (history : (model (Decision := Decision) prior ambient).InformationHistory true
      (receiverSilentSite prior full ambient).1) :
    ∃ secret, history.1 = receiverHistory prior full ambient secret false := by
  have observed := history.2
  rw [info_state] at observed
  have known : Classified prior full ambient history.1 :=
    classified prior full ambient history.1.trace
  rcases known with same | ⟨secret, same⟩ | ⟨secret, ask, same⟩ | ⟨secret, ask, guess, same⟩
  all_goals rw [same] at observed
  all_goals try cases observed
  cases ambient
  · exact ⟨secret, same⟩
  · cases ask
    · exact ⟨secret, same⟩
    · cases observed

instance (secret : Secret) :
    Subsingleton ((model (Decision := Decision) prior true).InformationHistory false
      (senderSite prior full secret).1) :=
  ⟨fun first second => Subtype.ext ((history_at_sender prior full secret first).trans
    (history_at_sender prior full secret second).symm)⟩

instance (secret : Secret) :
    Subsingleton ((model (Decision := Decision) prior true).InformationHistory true
      (receiverDisclosedSite prior full secret).1) :=
  ⟨fun first second => Subtype.ext ((history_at_disclosed prior full secret first).trans
    (history_at_disclosed prior full secret second).symm)⟩

theorem sender_site_eq
    (decision : (model (Decision := Decision) prior true).InformationSite false) :
    ∃ secret, decision = senderSite prior full secret := by
  obtain ⟨history, _, _, _⟩ := decision.2
  have active := InformationModel.InformationSite.active (model prior true) decision history
  have known : Classified prior full true history.1 := classified prior full true history.1.trace
  rcases known with same | ⟨secret, same⟩ | ⟨secret, ask, same⟩ | ⟨secret, ask, guess, same⟩
  all_goals rw [same] at active
  all_goals try simp [arena, actor, senderHistory, receiverHistory, terminalHistory,
    senderJoint, receiverJoint] at active
  refine ⟨secret, Subtype.ext ?_⟩
  have observed := history.2.symm
  rw [same] at observed
  exact observed

theorem receiver_site_cases (ambient : Bool)
    (decision : (model (Decision := Decision) prior ambient).InformationSite true) :
    decision = receiverSilentSite prior full ambient ∨
      ∃ secret, ambient = true ∧ decision.1 = some (some secret) := by
  obtain ⟨history, _, _, _⟩ := decision.2
  have active := InformationModel.InformationSite.active (model prior ambient) decision history
  have known : Classified prior full ambient history.1 :=
    classified prior full ambient history.1.trace
  rcases known with same | ⟨secret, same⟩ | ⟨secret, ask, same⟩ | ⟨secret, ask, guess, same⟩
  all_goals rw [same] at active
  all_goals try simp [arena, actor, senderHistory, receiverHistory, terminalHistory,
    senderJoint, receiverJoint] at active
  have observed := history.2.symm
  rw [same] at observed
  cases ambient
  · exact Or.inl (Subtype.ext observed)
  · cases ask
    · exact Or.inl (Subtype.ext observed)
    · exact Or.inr ⟨secret, rfl, observed⟩

theorem target_receiver_site_eq
    (decision : (model (Decision := Decision) prior true).InformationSite true) :
    decision = receiverSilentSite prior full true ∨
      ∃ secret, decision = receiverDisclosedSite prior full secret := by
  rcases receiver_site_cases prior full true decision with same | ⟨secret, _, same⟩
  · exact Or.inl same
  · exact Or.inr ⟨secret, Subtype.ext same⟩

theorem source_receiver_site_eq
    (decision : (model (Decision := Decision) prior false).InformationSite true) :
    decision = receiverSilentSite prior full false := by
  rcases receiver_site_cases prior full false decision with same | ⟨_, impossible, _⟩
  · exact same
  · cases impossible

theorem source_no_sender_site
    (decision : (model (Decision := Decision) prior false).InformationSite false) :
    False := by
  obtain ⟨history, _, _, _⟩ := decision.2
  have active := InformationModel.InformationSite.active (model prior false) decision history
  cases state : history.1.state <;> simp_all [arena, actor]

def silentHistory (ambient : Bool) (secret : Secret) :
    (model (Decision := Decision) prior ambient).InformationHistory true
      (receiverSilentSite prior full ambient).1 :=
  ⟨receiverHistory prior full ambient secret false, by cases ambient <;> rfl⟩

theorem silentHistory_injective (ambient : Bool) :
    Function.Injective (silentHistory (Decision := Decision) prior full ambient) := by
  intro first second same
  have states := congrArg (fun history => history.1.state) same
  change State.receiver first _ = State.receiver second _ at states
  exact (State.receiver.inj states).1

def silentHistories (ambient : Bool) :
    Secret ≃ (model (Decision := Decision) prior ambient).InformationHistory true
      (receiverSilentSite prior full ambient).1 :=
  Equiv.ofBijective (silentHistory prior full ambient)
    ⟨silentHistory_injective prior full ambient, fun history => by
      obtain ⟨secret, same⟩ := history_at_silent prior full ambient history
      exact ⟨secret, Subtype.ext same.symm⟩⟩

theorem sender_context (assessment : (model (Decision := Decision) prior true).BehavioralAssessment)
    (secret : Secret) (utility : State Secret Decision → ℝ)
    (alternative : (model (Decision := Decision) prior true).BehavioralPolicy false) :
    (assessment.continuationContext (senderSite prior full secret)
      (fun h => utility h.state) 3).value alternative =
      ((model prior true).runSingleMoverBehavioralFrom (single prior true)
        (Profile.update (sig := (model prior true).behavioralSignature)
          assessment.strategy false alternative) 3 (senderHistory prior full true secret)).expect
            (fun h => utility h.state) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    FinDist.eq_pure_of_subsingleton (assessment.belief false (senderSite prior full secret))
      ⟨senderHistory prior full true secret, rfl⟩, FinDist.pure_bind,
    ← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
      (model prior true) (single prior true)]

theorem disclosed_context
    (assessment : (model (Decision := Decision) prior true).BehavioralAssessment)
    (secret : Secret) (utility : State Secret Decision → ℝ)
    (alternative : (model (Decision := Decision) prior true).BehavioralPolicy true) :
    (assessment.continuationContext (receiverDisclosedSite prior full secret)
        (fun h => utility h.state) 3).value alternative =
      ((model prior true).runSingleMoverBehavioralFrom (single prior true)
        (Profile.update (sig := (model prior true).behavioralSignature)
          assessment.strategy true alternative) 3
            (receiverHistory prior full true secret true)).expect
            (fun h => utility h.state) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    FinDist.eq_pure_of_subsingleton
      (assessment.belief true (receiverDisclosedSite prior full secret))
      ⟨receiverHistory prior full true secret true, rfl⟩, FinDist.pure_bind,
    ← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
      (model prior true) (single prior true)]

theorem value_receiver {ambient : Bool}
    (profile : Profile (model (Decision := Decision) prior ambient).behavioralSignature)
    (secret : Secret) (disclose : Bool) (utility : State Secret Decision → ℝ) :
    ((model prior ambient).runSingleMoverBehavioralFrom (single prior ambient) profile 3
      (receiverHistory prior full ambient secret disclose)).expect (fun h => utility h.state) =
        (resultLaw profile secret (ambient && disclose)).expect utility := by
  have mapped := congrArg (fun law => law.expect utility)
    (run_receiver full profile secret disclose)
  simpa only [FinDist.expect_map] using mapped

theorem value_sender {ambient : Bool}
    (profile : Profile (model (Decision := Decision) prior ambient).behavioralSignature)
    (secret : Secret) (utility : State Secret Decision → ℝ) :
    ((model prior ambient).runSingleMoverBehavioralFrom (single prior ambient) profile 3
      (senderHistory prior full ambient secret)).expect (fun h => utility h.state) =
        (choiceLaw profile false (some (some secret))).expect
          (fun disclose => (resultLaw profile secret (ambient && disclose)).expect utility) := by
  have mapped := congrArg (fun law => law.expect utility) (run_sender full profile secret)
  simpa only [FinDist.expect_map, FinDist.expect_bind] using mapped

end GameTheory.Protocol.DisclosureEnforcement
