/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterPrefixNoise
import Vegas.Game.RevealServicePrefixInformation
import Interaction.ReactiveObservation
import GameTheoryExtensions.Math.Probability.Support

/-! # Owner information during a revelation roster

Before final inclusion, the owner already knows the unique possible opening.
The actual partial-roster transcript is therefore conditionally ancillary for
the unchanged source state. This includes off-path early own openings and all
of the owner's subsequent private recall.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_owner_window_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program)
    (left right : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player)
    (actor : (graph setup).actor? event = some owner)
    (leftSole : left.application.publicView.SoleReady event)
    (rightSole : right.application.publicView.SoleReady event)
    (leftCandidate rightCandidate : Handle (graph setup)) (leftRaw rightRaw : Raw L)
    (leftOpening : rosterOpening? setup leaks owner event
      (left.observe (application setup leaks) owner) = some (leftCandidate, leftRaw))
    (rightOpening : rosterOpening? setup leaks owner event
      (right.observe (application setup leaks) owner) = some (rightCandidate, rightRaw))
    (owned : leftCandidate.1 = owner)
    (leftValid : left.application.candidates.lookup leftCandidate = .openable leftRaw)
    (rightValid : right.application.candidates.lookup rightCandidate = .openable rightRaw)
    (leftOffset : (left.recall owner).length ≤ rosterOffset setup rosters owner event)
    (rightOffset : (right.recall owner).length ≤ rosterOffset setup rosters owner event)
    (leftRecall : left.InputRecall (application setup leaks))
    (rightRecall : right.InputRecall (application setup leaks))
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (observed : left.observe (application setup leaks) owner =
      right.observe (application setup leaks) owner)
    (readouts : ((application setup leaks).messageView left, left.recall owner) =
      ((application setup leaks).messageView right, right.recall owner)) :
    ((runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
      network (visits.map ServiceInstruction.player) left).map (fun final =>
        ((application setup leaks).messageView final, final.recall owner)) =
    ((runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
      network (visits.map ServiceInstruction.player) right).map (fun final =>
        ((application setup leaks).messageView final, final.recall owner)) := by
  have messages := congrArg Prod.fst readouts
  have recall := congrArg Prod.snd readouts
  have openings : (leftCandidate, leftRaw) = (rightCandidate, rightRaw) :=
    Option.some.inj (leftOpening.symm.trans
      ((congrArg (rosterOpening? setup leaks owner event) observed).trans rightOpening))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj openings
  have choices := congrArg (sourceChoiceLaw setup leaks profile owner) observed
  have privateView := congrArg ReactiveApplication.PlayerView.application observed
  have publicView := congrArg ReactivePlayerView.publicView privateView
  rw [rosterPolicy_window_eq setup leaks rosters timing profile left left event owner leftSole
    actor leftCandidate leftRaw leftOpening rfl network visits,
    rosterPolicy_window_eq setup leaks rosters timing profile right right event owner rightSole
    actor leftCandidate leftRaw rightOpening rfl network visits]
  rw [openingWindowMixture_law _ _ _ _ _ _ _ _ _ _ _ leftOffset,
    openingWindowMixture_law _ _ _ _ _ _ _ _ _ _ _ rightOffset, choices]
  simp only [PMF.map_bind]
  apply bind_congr_on_support _
  intro selected _
  exact (runtime setup).openingWindow_coupling leaks owner event leftCandidate leftRaw
    (rosterOffset setup rosters owner event) selected network visits owner left right leftRecall
      rightRecall messages recall publicView privateView owned (fun _ => ⟨leftValid, rightValid⟩)

/-- The actual next passive sample preserves the owner-information coupling. -/
theorem roster_owner_activation_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program)
    (left right : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player)
    (actor : (graph setup).actor? event = some owner)
    (leftSole : left.application.publicView.SoleReady event)
    (rightSole : right.application.publicView.SoleReady event)
    (leftCandidate rightCandidate : Handle (graph setup)) (leftRaw rightRaw : Raw L)
    (leftOpening : rosterOpening? setup leaks owner event
      (left.observe (application setup leaks) owner) = some (leftCandidate, leftRaw))
    (rightOpening : rosterOpening? setup leaks owner event
      (right.observe (application setup leaks) owner) = some (rightCandidate, rightRaw))
    (owned : leftCandidate.1 = owner)
    (leftValid : left.application.candidates.lookup leftCandidate = .openable leftRaw)
    (rightValid : right.application.candidates.lookup rightCandidate = .openable rightRaw)
    (leftOffset : (left.recall owner).length ≤ rosterOffset setup rosters owner event)
    (rightOffset : (right.recall owner).length ≤ rosterOffset setup rosters owner event)
    (leftRecall : left.InputRecall (application setup leaks))
    (rightRecall : right.InputRecall (application setup leaks))
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (observed : left.observe (application setup leaks) owner =
      right.observe (application setup leaks) owner)
    (readouts : ((application setup leaks).messageView left, left.recall owner) =
      ((application setup leaks).messageView right, right.recall owner)) :
    (((runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
      network (visits.map ServiceInstruction.player) left).bind fun current =>
        current.environmentStep (application setup leaks) (.activate owner)).map (fun final =>
          (final.recall owner, final.observe (application setup leaks) owner)) =
    (((runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
      network (visits.map ServiceInstruction.player) right).bind fun current =>
        current.environmentStep (application setup leaks) (.activate owner)).map (fun final =>
          (final.recall owner, final.observe (application setup leaks) owner)) := by
  have coupled := roster_owner_window_coupling setup leaks rosters timing profile left right
    event owner actor leftSole rightSole leftCandidate rightCandidate leftRaw rightRaw
    leftOpening rightOpening owned leftValid rightValid leftOffset rightOffset leftRecall
    rightRecall network visits observed readouts
  simp only [PMF.map_bind]
  apply bind_eq_of_map_eq _ _ _ _ coupled
  intro leftFinal leftSupport rightFinal rightSupport same
  have leftApplication := rosterPolicy_run_application setup leaks rosters timing profile network
    visits left leftFinal leftSupport
  have rightApplication := rosterPolicy_run_application setup leaks rosters timing profile network
    visits right rightFinal rightSupport
  have messages := congrArg Prod.fst same
  apply (application setup leaks).activation_info_congr leftFinal rightFinal owner
    (congrArg Prod.fst messages) (congrArg (fun value => value.2.1) messages) _
    (congrArg Prod.snd same)
  rw [leftApplication, rightApplication]
  exact congrArg ReactiveApplication.PlayerView.application observed

/-- At supported source checkpoints, the owner's actual next input
remains an observation-dependent channel of the original source state. The
coupling is derived from the roster interpreter, including early own openings. -/
theorem roster_owner_information_kernel
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program)
    (event : (graph setup).EventId) (owner : Player)
    (actor : (graph setup).actor? event = some owner)
    (prior : PMF (application setup leaks).Execution)
    (checkpoint : ∀ execution ∈ prior.support, ∃ initial state,
      PublicPrefixCheckpoint setup leaks initial setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) (outputRef setup.program)
        0 event.val state execution ∧
      sourcePrefix? setup event.val execution.application.config = some state)
    (grant : Option (graph setup).EventId)
    (granted : ∀ execution ∈ prior.support, execution.application.serviceGrant = grant)
    (opening : ∀ execution ∈ prior.support, ∃ candidate raw,
      rosterOpening? setup leaks owner event (execution.observe (application setup leaks) owner) =
        some (candidate, raw) ∧ candidate.1 = owner ∧
      execution.application.candidates.lookup candidate = .openable raw)
    (offset : ∀ execution ∈ prior.support,
      (execution.recall owner).length ≤ rosterOffset setup rosters owner event)
    (recalls : ∀ execution ∈ prior.support, execution.InputRecall (application setup leaks))
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (noise : setup.ProtocolView owner → PMF ((application setup leaks).MessageReadout ×
      List (application setup leaks).PlayerEntry))
    (factor : prior.map (fun execution =>
        (sourcePrefix? setup event.val execution.application.config,
          ((application setup leaks).messageView execution, execution.recall owner))) =
      (prior.map fun execution => sourcePrefix? setup event.val execution.application.config).bind
        fun state => (noise (setup.protocolObserve owner state)).map fun extra => (state, extra)) :
    ∃ channel : setup.ProtocolView owner → PMF
        (List (application setup leaks).PlayerEntry × (application setup leaks).PlayerView),
      (prior.bind fun execution =>
        (((runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
          network (visits.map ServiceInstruction.player) execution).bind fun current =>
            current.environmentStep (application setup leaks) (.activate owner)).map fun final =>
              (sourcePrefix? setup event.val execution.application.config,
                (final.recall owner, final.observe (application setup leaks) owner))) =
      (prior.map fun execution => sourcePrefix? setup event.val execution.application.config).bind
        fun state => (channel (setup.protocolObserve owner state)).map fun input =>
          (state, input) :=
    by
  obtain ⟨channel, law⟩ := exists_updated_observation_kernel_of_readout prior
    (fun execution => sourcePrefix? setup event.val execution.application.config)
    (fun execution => ((application setup leaks).messageView execution, execution.recall owner))
    (setup.protocolObserve owner) noise factor (fun _ => PMF.pure ())
    (fun state _ => state) (setup.protocolObserve owner)
    (fun execution _ =>
      (((runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
        network (visits.map ServiceInstruction.player) execution).bind fun current =>
          current.environmentStep (application setup leaks) (.activate owner)).map fun final =>
            (final.recall owner, final.observe (application setup leaks) owner))
    (fun _ _ _ _ _ _ _ _ same => same) (by
      intro left leftSupport _ _ right rightSupport _ _ same readouts
      obtain ⟨leftInitial, leftState, leftCheckpoint, leftDecoded⟩ := checkpoint left leftSupport
      obtain ⟨rightInitial, rightState, rightCheckpoint, rightDecoded⟩ :=
        checkpoint right rightSupport
      have sourceView : ProtocolState.observe owner setup.program leftState =
          ProtocolState.observe owner setup.program rightState := by
        rw [leftDecoded, rightDecoded] at same
        exact Option.some.inj same
      have networks := congrArg Prod.fst (congrArg Prod.fst readouts)
      have observed := (PublicPrefixCheckpoint.observe_eq_iff owner setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) (outputRef setup.program) 0 event.val
        leftState rightState left right leftCheckpoint rightCheckpoint
        ((granted left leftSupport).trans (granted right rightSupport).symm)
        (congrArg (fun net => net.leaked owner) networks)).mp sourceView
      obtain ⟨leftCandidate, leftRaw, leftOpening, owned, leftValid⟩ := opening left leftSupport
      obtain ⟨rightCandidate, rightRaw, rightOpening, _, rightValid⟩ :=
        opening right rightSupport
      exact roster_owner_activation_coupling setup leaks rosters timing profile left right event
        owner
        actor
        (soleReady_of_ready setup left.application
          (leftCheckpoint.ready event (Nat.zero_add _).symm))
        (soleReady_of_ready setup right.application
          (rightCheckpoint.ready event (Nat.zero_add _).symm))
        leftCandidate rightCandidate
        leftRaw rightRaw leftOpening rightOpening owned leftValid rightValid
        (offset left leftSupport)
        (offset right rightSupport) (recalls left leftSupport) (recalls right rightSupport)
        network visits observed readouts)
  refine ⟨channel, ?_⟩
  simpa only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure,
    PMF.map_comp, Function.comp_def] using law

end Vegas
