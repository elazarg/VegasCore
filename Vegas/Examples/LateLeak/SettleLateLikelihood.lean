/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.SettleLateConsistency
import GameTheoryExtensions.Analysis.Protocol.AsymptoticLikelihood

/-! # Execution-likelihood families for the settle-late game

The checked likelihood interface is instantiated with the actual complete
histories and reach weights of the settle-late game. This does not identify
that comparison game with the compiled message runtime.
-/

noncomputable section

namespace Vegas

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability Filter

variable {G : SettleLateParameters}

private theorem seenMember_injective (secret : LateLeakType) (ping : Bool) :
    Function.Injective (settleLateSeenMember G secret ping) := by
  intro first second same
  have states := congrArg (fun history => history.1.state) same
  change SettleLateState.answering
      (settleLateCoreRecord secret (.opening true) ping
        (if first then .opening else .silent) .first) =
    SettleLateState.answering
      (settleLateCoreRecord secret (.opening true) ping
        (if second then .opening else .silent) .first) at states
  cases first <;> cases second <;> simp_all [settleLateCoreRecord]

private theorem quietMember_injective (secret : LateLeakType) (ping : Bool) :
    Function.Injective (settleLateQuietMember G secret ping) := by
  intro first second same
  have states := congrArg (fun history => history.1.state) same
  change SettleLateState.answering (first.record secret ping) =
    SettleLateState.answering (second.record secret ping) at states
  cases first <;> cases second <;>
    simp_all [SettleLateQuietPath.record, settleLateCoreRecord]

/-- All histories of one label in a successful first-sighted information set. -/
def settleLateSeenHistories (bit ping : Bool) (label : LateLeakLabel) :
    Finset ((settleLateModel G true).InformationHistory .listener
      (settleLateSeenSuccessSite G bit ping).1) := by
  classical
  exact Finset.univ.image (settleLateSeenMember G (bit, label) ping)

/-- All histories of one label in a successful previously-unsighted information set. -/
def settleLateQuietHistories (bit ping : Bool) (label : LateLeakLabel) :
    Finset ((settleLateModel G true).InformationHistory .listener
      (settleLateQuietSuccessSite G bit ping).1) := by
  classical
  exact Finset.univ.image (settleLateQuietMember G (bit, label) ping)

private theorem seenReach (profile : SettleLateProfile G true)
    (bit ping : Bool) (label : LateLeakLabel) :
    finiteHistoryReach profile .listener (settleLateSeenSuccessSite G bit ping)
        (settleLateSeenHistories bit ping label) =
      settleLateDeferMass profile (bit, label) *
        ((settleLateFirstLaw G .opening (.opening true)).toReal *
          settleLatePingMass profile (.opening bit) ping) *
        (settleLateFirstMass profile (bit, label) .opening *
          settleLateSeenFactor profile (bit, label) ping) := by
  classical
  unfold finiteHistoryReach settleLateSeenHistories
  rw [Finset.sum_image (fun _ _ _ _ same => seenMember_injective (bit, label) ping same),
    Fintype.sum_bool]
  rw [add_comm, settleLate_seen_weights]
  ring

private theorem quietReach (profile : SettleLateProfile G true)
    (bit ping : Bool) (label : LateLeakLabel) :
    finiteHistoryReach profile .listener (settleLateQuietSuccessSite G bit ping)
        (settleLateQuietHistories bit ping label) =
      settleLateDeferMass profile (bit, label) * settleLatePingMass profile .nothing ping *
        settleLateQuietFactor profile (bit, label) ping := by
  classical
  unfold finiteHistoryReach settleLateQuietHistories
  rw [Finset.sum_image (fun _ _ _ _ same => quietMember_injective (bit, label) ping same)]
  have enumerate : (Finset.univ : Finset SettleLateQuietPath) = {.send, .hold, .retry} := by
    ext path
    cases path <;> simp
  rw [enumerate, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [← add_assoc, settleLate_quiet_weights]
  ring

/-- The observed-opening family, with shared actual prior and root deferral. -/
def settleLateSeenLikelihood (bit : Bool) :
    FactoredHistoryLikelihood (M := settleLateModel G true) .listener Bool LateLeakLabel
      (fun profile label => settleLateDeferMass profile (bit, label)) where
  site := settleLateSeenSuccessSite G bit
  histories := settleLateSeenHistories bit
  observationFactor profile ping :=
    (settleLateFirstLaw G .opening (.opening true)).toReal *
      settleLatePingMass profile (.opening bit) ping
  timingFactor profile ping label :=
    settleLateFirstMass profile (bit, label) .opening *
      settleLateSeenFactor profile (bit, label) ping
  reach_factored profile ping label := seenReach profile bit ping label
  timing_tendsto sequence A converges ping label := by
    have first := settleLateFirstMass_tendsto converges (bit, label) .opening
    have second (packet : SettleLatePacket) :=
      settleLateSecondMass_tendsto converges (bit, label) (.opening true) ping packet
    unfold settleLateSeenFactor
    exact first.mul (((second .silent).mul tendsto_const_nhds).add
      ((second .opening).mul tendsto_const_nhds))

/-- The unsighted-opening family, with the same actual prior and root deferral. -/
def settleLateQuietLikelihood (bit : Bool) :
    FactoredHistoryLikelihood (M := settleLateModel G true) .listener Bool LateLeakLabel
      (fun profile label => settleLateDeferMass profile (bit, label)) where
  site := settleLateQuietSuccessSite G bit
  histories := settleLateQuietHistories bit
  observationFactor profile ping := settleLatePingMass profile .nothing ping
  timingFactor profile ping label := settleLateQuietFactor profile (bit, label) ping
  reach_factored profile ping label := quietReach profile bit ping label
  timing_tendsto sequence A converges ping label := by
    have first (packet : SettleLatePacket) :=
      settleLateFirstMass_tendsto converges (bit, label) packet
    have opened (packet : SettleLatePacket) :=
      settleLateSecondMass_tendsto converges (bit, label) (.opening true) ping packet
    have held (packet : SettleLatePacket) :=
      settleLateSecondMass_tendsto converges (bit, label) .silent ping packet
    simp only [SettleLateFirst.packet] at opened held
    unfold settleLateQuietFactor
    exact (((first .silent).mul tendsto_const_nhds).mul
      ((held .opening).mul tendsto_const_nhds)).add
        (((first .opening).mul tendsto_const_nhds).mul
          (((opened .silent).mul tendsto_const_nhds).add
            ((opened .opening).mul tendsto_const_nhds)))

/-- Actual factored execution weights force exclusion across a whole family
of listener information sets under opposing limiting sender timing factors. -/
theorem settleLate_consistent_likelihood_face
    {A : (settleLateModel G true).BehavioralAssessment}
    (consistent : A.IsSequentiallyConsistent (settleLate_antichain G true))
    (bit : Bool) (sender holder : LateLeakLabel)
    (nonzero : ∀ seen unseen,
      settleLateCross A.strategy (bit, sender) (bit, holder) seen unseen ≠ 0)
    (zero : ∀ seen unseen,
      settleLateCross A.strategy (bit, holder) (bit, sender) seen unseen = 0) :
    (∀ seen retry,
      A.belief .listener (settleLateSeenSuccessSite G bit seen)
        (settleLateSeenMember G (bit, holder) seen retry) = 0) ∨
    (∀ unseen path,
      A.belief .listener (settleLateQuietSuccessSite G bit unseen)
        (settleLateQuietMember G (bit, sender) unseen path) = 0) := by
  classical
  obtain ⟨sequence, approximate, converges⟩ := consistent
  have face := ((settleLateSeenLikelihood (G := G) bit).alongSequence converges).belief_face
    ((settleLateQuietLikelihood bit).alongSequence converges) (settleLate_antichain G true)
      (fun n => (approximate n).1) (fun n => (approximate n).2) converges sender holder
        nonzero zero
  rcases face with seen | unseen
  · left
    intro ping retry
    exact seen ping _ (Finset.mem_image.mpr ⟨retry, Finset.mem_univ _, rfl⟩)
  · right
    intro ping path
    exact unseen ping _ (Finset.mem_image.mpr ⟨path, Finset.mem_univ _, rfl⟩)

/-- Opposite pure first-turn choices and the rational core second-turn choices
produce the likelihood degeneracy used by the general consistency theorem. -/
theorem settleLate_opposite_timing_excludes_label
    {A : (settleLateModel G true).BehavioralAssessment}
    (consistent : A.IsSequentiallyConsistent (settleLate_antichain G true))
    (bit : Bool) (sender holder : LateLeakLabel)
    (sends : settleLateSenderLaw A.strategy (.firstTurn (bit, sender) none) =
      PMF.pure (some (.emit .opening)))
    (holds : settleLateSenderLaw A.strategy (.firstTurn (bit, holder) none) =
      PMF.pure (some (.emit .silent)))
    (senderCore : SettleLateCorePlay A.strategy (bit, sender))
    (holderCore : SettleLateCorePlay A.strategy (bit, holder)) :
    (∀ seen retry,
      A.belief .listener (settleLateSeenSuccessSite G bit seen)
        (settleLateSeenMember G (bit, holder) seen retry) = 0) ∨
    (∀ unseen path,
      A.belief .listener (settleLateQuietSuccessSite G bit unseen)
        (settleLateQuietMember G (bit, sender) unseen path) = 0) := by
  have pureMass (view : SettleLateView) (choice other : Option SettleLateMove)
      (law : settleLateSenderLaw A.strategy view = PMF.pure choice) :
      (settleLateSenderLaw A.strategy view other).toReal = if other = choice then 1 else 0 := by
    rw [law, PMF.pure_apply]
    split <;> simp
  apply settleLate_consistent_likelihood_face consistent bit sender holder
  · intro seen unseen
    have crossValue : settleLateCross A.strategy (bit, sender) (bit, holder) seen unseen =
        lateLeakInclusionProb G.toLateLeakParameters *
          lateLeakInclusionProb G.toLateLeakParameters := by
      simp only [settleLateCross, settleLateSeenFactor, settleLateQuietFactor,
        settleLateFirstMass, settleLateSecondMass, pureMass _ _ _ sends,
        pureMass _ _ _ holds, pureMass _ _ _ (senderCore seen).2,
        pureMass _ _ _ (holderCore unseen).1, settleLateFateLaw_seenHold_included,
        settleLateFateLaw_send_included]
      simp [settleLateFirstLaw]
    rw [crossValue]
    exact mul_ne_zero (lateLeakInclusionProb_pos G.toLateLeakParameters).ne'
      (lateLeakInclusionProb_pos G.toLateLeakParameters).ne'
  · intro seen unseen
    simp only [settleLateCross, settleLateFirstMass, pureMass _ _ _ holds]
    simp

end Vegas
