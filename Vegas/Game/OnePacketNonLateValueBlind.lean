/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateValueBlind
import Vegas.Game.OnePacketPrescribedSites
import Vegas.Game.OnePacketSilentShape

/-! # Value-blind completion away from late deliveries

A forced site away from late deliveries with a pending event is a first
activation (`Vegas.firstActivation_of_nonLate`). There a compared choice is
silence or transmits a packet naming the pending reveal.

**Silence.** From every forced history of a debt-free first activation, the
profile installing a late option or silence plays the late owner shape from the
site (`Vegas.certificate_firstActivation_lateOwnerShapeFrom`), so its completion
value is near one less its failure probability times the continuation value
(`Vegas.certificate_firstActivation_historyNear`). The certificate lumps there,
so waiting fails near the lumped failure of its record, and silence fails within
one less the slot retention of waiting.

**The value blindness.** With the disclosure exact up to the unforced mass and
the prescribed component within thirty times the scale, along an assembled
sequence of vanishing scale with vanishing unforced mass and decorrelation, the
compared choices and the prescribed component are value-blind away from late
deliveries with a vanishing error (`Vegas.nonLateValueBlind_of_bounds`).
-/

noncomputable section

namespace Vegas


open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

/-- **Away from late deliveries a pending site is a first activation.** A site
of an agent that is neither free nor a keyed late delivery, with a pending
event, is a first activation. -/
theorem firstActivation_of_nonLate {who : Player} (site : (onePacketN).InformationSite who)
    (notFree : ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    (notKeyed : ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
      ((onePacketN).agentAt site))
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event) :
    FirstActivation setup leaks who site.1 := by
  have notLate : ¬ LateDelivery setup leaks who site.1 := fun late => notKeyed ⟨late, notFree⟩
  obtain ⟨past, view, atSite⟩ : ∃ past view, site.1 = some (past, view) := by
    cases info : site.1 with
    | none =>
        rw [info] at pending
        cases pending
    | some input => exact ⟨input.1, input.2, rfl⟩
  refine ⟨past, view, event, atSite, pending, fun entry member activated => notLate ?_⟩
  exact ⟨past, view, event, atSite, pending, entry, member, activated⟩

/-- **The certificate's completion value at a first activation.** At a debt-free
first activation of `who` for its pending event, from a forced history of the
site, the profile installing a late option or silence at the site has
completion value within a multiple of the cube of the scale, times the payoff
bound, of one less its failure probability times the history's continuation
value. -/
theorem certificate_firstActivation_historyNear
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount) {who : Player}
    (site : (onePacketN).InformationSite who) (first : FirstActivation setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (law : PMF ((onePacketN).Choice who site.1))
    (lawShape : (∃ option : LateOption slots, law = onePacketLate setup leaks bounds horizon
        scheduler sequence scale scale_pos scale_le_one n ((onePacketN).agentAt site) option) ∨
      law = PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        site.1))
    (history : (onePacketN).InformationHistory who site.1)
    (forced : ForcedState setup leaks who history.1.state)
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound) :
    |historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site law
        history.1 -
      (1 - siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site law
          history) *
        decodedPointValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          (setup.intendedOpeningProfile (sequence n).strategy) who (siteRank site.1) history.1| ≤
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
          (2 * horizon + 1) + 2 * (scale n ^ 3 * (2 * horizon + 1))) * bound :=
  certificate_pending_historyNear setup leaks bounds horizon scheduler parameter utility
    excludedPayoff wellFormed sequence scale scale_pos scale_le_one weights targetSequence
    assembled n completes covers capacity slotsLe site (Or.inr first) debtFree siteKey pending
    atSite law history forced (fun {remaining execution} current => by
      obtain ⟨remaining', execution', current', recallEq, observeEq⟩ :=
        state_of_site setup leaks bounds horizon scheduler atSite history
      rw [current] at current'
      cases current'
      exact certificate_firstActivation_lateOwnerShapeFrom setup leaks bounds horizon scheduler
        sequence scale scale_pos scale_le_one weights targetSequence assembled n site pending
        law lawShape history current (by rw [atSite, recallEq, observeEq]) forced)
    readoutBounded excludedBounded

open Classical Filter in
/-- **Value blindness away from late deliveries.** Under the asynchronous
contract with timely delays and retention of first covered canonical packets,
along an assembled sequence of vanishing scale, let a vanishing drift bound the
belief mass outside the forced region and let the beliefs decorrelate the
operational records and the decoded points up to a vanishing error, at every
pending site away from late deliveries of an agent that is neither free nor
owing. With bounded payoffs, the compared choices and the prescribed component
have completion value one less their failure probability times the site's
continuation value, up to a vanishing error. -/
theorem nonLateValueBlind_of_bounds
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (wellFormed : setup.WellFormed) {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (scale_vanishing : Tendsto scale atTop (nhds 0))
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount)
    (unforcedDrift decorrelation : ℕ → ℝ)
    (unforcedLimit : Tendsto unforcedDrift atTop (nhds 0))
    (decorrelationLimit : Tendsto decorrelation atTop (nhds 0))
    (unforced : ∀ n who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site) →
      pendingEvent setup leaks who site.1 ≠ none →
      expect ((targetSequence n).belief who site) (fun history =>
        if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤ unforcedDrift n)
    (decorrelated : ∀ n who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site) →
      pendingEvent setup leaks who site.1 ≠ none →
      BeliefDecorrelated ((targetSequence n).belief who site)
        (fun history => operationalRecord setup leaks bounds horizon scheduler history.1.trace)
        (fun history => nativeDecodedState setup leaks history.1.state) (decorrelation n))
    {payoffBound : ℝ} (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤
        payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ blindError : ℕ → ℝ, Tendsto blindError atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        pendingEvent setup leaks who site.1 ≠ none →
        (∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
          |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
              (PMF.pure choice) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (PMF.pure choice)) *
            siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
            blindError n) ∧
        |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
            (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
            (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one n ((onePacketN).agentAt site)) -
          (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
            site (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
              scale_pos scale_le_one n ((onePacketN).agentAt site))) *
          siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
            (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
          blindError n := by
  let pathError := fun n => ((2 * horizon + 1 : ℕ) : ℝ) * (scale n ^ 3 + scale n ^ 3)
  let valueError := fun n => (2 * (scale n ^ 3 + pathError n) * (2 * horizon + 1) +
    2 * (scale n ^ 3 * (2 * horizon + 1))) * payoffBound
  let silenceError := fun n => 1 - slotRetention (scale n)
  let silencePart := fun n => valueError n + 2 * payoffBound * |unforcedDrift n| +
    (2 * payoffBound * (pathError n + silenceError n + |unforcedDrift n|) +
      2 * payoffBound * |decorrelation n|)
  let error := fun n => silencePart n + 4 * payoffBound * |unforcedDrift n| +
    (5 * (6 * scale n) * payoffBound + 4 * payoffBound * |unforcedDrift n|)
  have cube := scale_vanishing.pow 3
  have pathLimit : Tendsto pathError atTop (nhds 0) := by
    simpa [pathError] using (cube.add cube).const_mul ((2 * horizon + 1 : ℕ) : ℝ)
  have silenceLimit : Tendsto silenceError atTop (nhds 0) := by
    have square := scale_vanishing.pow 2
    have retention : Tendsto (fun n => slotRetention (scale n)) atTop (nhds 1) := by
      unfold slotRetention
      simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub cube).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub square)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub scale_vanishing)
    simpa [silenceError] using (tendsto_const_nhds (x := (1 : ℝ))).sub retention
  refine ⟨error, ?_, ?_⟩
  · have valueLimit : Tendsto valueError atTop (nhds 0) := by
      simpa [valueError] using ((((cube.add pathLimit).const_mul 2).mul_const
        ((2 * horizon + 1 : ℕ) : ℝ)).add ((cube.mul_const ((2 * horizon + 1 : ℕ) : ℝ)).const_mul
          2)).mul_const payoffBound
    have silenceLimit' : Tendsto silencePart atTop (nhds 0) := by
      simpa [silencePart] using (valueLimit.add (unforcedLimit.abs.const_mul (2 * payoffBound))).add
        ((((pathLimit.add silenceLimit).add unforcedLimit.abs).const_mul (2 * payoffBound)).add
          (decorrelationLimit.abs.const_mul (2 * payoffBound)))
    have prescribedLimit := ((scale_vanishing.const_mul 6).const_mul 5).mul_const payoffBound
    simpa [error] using (silenceLimit'.add (unforcedLimit.abs.const_mul (4 * payoffBound))).add
      (prescribedLimit.add (unforcedLimit.abs.const_mul (4 * payoffBound)))
  intro n who site notFree notOwing notKeyed pendingSome
  have boundNonneg : 0 ≤ payoffBound := (abs_nonneg _).trans (excludedBounded who)
  have retentionLe := slotRetention_le_one (scale_pos n).le (scale_le_one n)
  have silenceNonneg : 0 ≤ silenceError n := by
    simp only [silenceError]
    linarith
  have pathNonneg : 0 ≤ pathError n :=
    mul_nonneg (Nat.cast_nonneg _) (by have := pow_nonneg (scale_pos n).le 3; linarith)
  have valueNonneg : 0 ≤ valueError n := by
    have := pow_nonneg (scale_pos n).le 3
    simp only [valueError]
    positivity
  have silencePartNonneg : 0 ≤ silencePart n := by
    simp only [silencePart]
    have := abs_nonneg (unforcedDrift n)
    have := abs_nonneg (decorrelation n)
    positivity
  have prescribedNonneg : 0 ≤ 5 * (6 * scale n) * payoffBound := by
    have := (scale_pos n).le
    positivity
  have unforcedNonneg : 0 ≤ 4 * payoffBound * |unforcedDrift n| := by positivity
  have debtFree : SiteDebtFree setup leaks bounds horizon scheduler site :=
    fun history point decoded owes => notOwing ⟨history, point, decoded, owes⟩
  obtain ⟨event, pending⟩ := Option.ne_none_iff_exists'.mp pendingSome
  have first := firstActivation_of_nonLate setup leaks bounds horizon scheduler site notFree
    notKeyed pending
  have notLate : ¬ LateDelivery setup leaks who site.1 := fun late => notKeyed ⟨late, notFree⟩
  obtain ⟨past, view, _, atSite, _, _⟩ := id first
  have : Finite ((onePacketN).Choice who site.1) :=
    (onePacketN).finite_choice_of_played ((onePacketN).site_mem_playedInformation site)
  have unforcedAbs := (unforced n who site notFree notOwing notKeyed pendingSome).trans
    (le_abs_self (unforcedDrift n))
  have mass4 : 4 * payoffBound * expect ((targetSequence n).belief who site) (fun history =>
      if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤
      4 * payoffBound * |unforcedDrift n| :=
    mul_le_mul_of_nonneg_left unforcedAbs (by positivity)
  constructor
  · intro choice compared
    obtain ⟨response, selected, _⟩ := choice_response setup leaks bounds horizon scheduler site
      atSite choice
    cases sends : response.transmission with
    | none =>
        -- Silence: through waiting, whose failure lumps at the first activation.
        have responseEq : response = ⟨none⟩ := by
          cases response
          simp only at sends
          rw [sends]
        have silent : ∀ info, info = some (past, view) →
            (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
              info).1 = some ⟨none⟩ := by
          intro info infoEq
          subst infoEq
          simp only [silenceChoice, responseChoice]
          split <;> rfl
        have isSilence : choice = silenceChoice setup leaks bounds (initialLaw setup) horizon
            scheduler who site.1 := by
          apply Subtype.ext
          rw [selected, responseEq]
          exact (silent site.1 atSite).symm
        subst isSilence
        obtain ⟨key, siteKey⟩ : ∃ key, lateKey setup leaks who site.1 = some key :=
          ⟨_, by rw [atSite]; rfl⟩
        have decidedOf : ∀ history : (onePacketN).InformationHistory who site.1,
            decidedEvent key = some event := by
          intro history
          obtain ⟨remaining, execution, current, recallEq, _⟩ :=
            state_of_site setup leaks bounds horizon scheduler atSite history
          have pendingAt := pending
          rw [atSite] at pendingAt
          have siteKeyAt := siteKey
          rw [atSite] at siteKeyAt
          exact decidedEvent_eq_of_pending setup leaks horizon scheduler pendingAt
            ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
              scheduler (current ▸ history.1.trace)) recallEq siteKeyAt
        let lumping := certificateLumping setup leaks bounds horizon scheduler sequence scale
          scale_pos scale_le_one covers capacity slotsLe weights targetSequence assembled n who
        have lumpedUnit : ∀ option record, 0 ≤ lumpedFailure setup leaks bounds horizon
            scheduler lumping (2 * horizon + 1) key option record ∧ lumpedFailure setup leaks
              bounds horizon scheduler lumping (2 * horizon + 1) key option record ≤ 1 := by
          intro option record
          unfold lumpedFailure
          exact ⟨expect_nonneg _ _ fun image _ => (lumping.failure_unit key image).1,
            expect_le_const _ _ (payoffIntegrable_of_bounded _ _ (C := 1) fun image => by
                have := lumping.failure_unit key image
                rw [abs_le]
                constructor <;> linarith) 1
              fun image _ => (lumping.failure_unit key image).2⟩
        have waitNear : ∀ history ∈ ((targetSequence n).belief who site).support,
            ForcedState setup leaks who history.1.state →
            |siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site
                (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one (slots := slots) n ((onePacketN).agentAt site) none) history -
              lumpedFailure setup leaks bounds horizon scheduler lumping (2 * horizon + 1) key
                none (operationalRecord setup leaks bounds horizon scheduler history.1.trace)| ≤
              pathError n := by
          intro history supported forced
          exact lateHistoryFailure_near_lumped setup leaks bounds horizon scheduler sequence
            scale scale_pos scale_le_one n (targetSequence n) who lumping site
              ⟨Or.inr first, debtFree⟩ key siteKey
            none (fun other _ _ final reached =>
              onePacketFailed_iff_decisionFailed_of_pending setup leaks bounds horizon scheduler
                contract.completes site (decidedOf other) pending other _ final reached)
            history supported forced
        have silenceNear : ∀ history ∈ ((targetSequence n).belief who site).support,
            ForcedState setup leaks who history.1.state →
            |siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site
                (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler
                  who site.1)) history -
              lumpedFailure setup leaks bounds horizon scheduler lumping (2 * horizon + 1) key
                none (operationalRecord setup leaks bounds horizon scheduler history.1.trace)| ≤
              pathError n + silenceError n := by
          intro history supported forced
          have near := waitNear history supported forced
          rw [siteHistoryFailure_eq_expect setup leaks bounds horizon scheduler
            (targetSequence n) site atSite] at near
          have mass : slotRetention (scale n) ≤ ((onePacketLate setup leaks bounds horizon
              scheduler sequence scale scale_pos scale_le_one (slots := slots) n
              ((onePacketN).agentAt site) none) (silenceChoice setup leaks bounds (initialLaw setup)
                horizon scheduler who site.1)).toReal := by
            have main := slotTrembledChoice_ge_main setup leaks bounds (initialLaw setup) horizon
              scheduler (scale_pos n).le (scale_le_one n) who site.1
              (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n)
                who site.1 (none : LateOption slots))
              (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler
                who site.1))
              (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n)
                who site.1) (silenceChoice setup leaks bounds (initialLaw setup) horizon
                  scheduler who site.1)
            have waiting : ∀ info, info = some (past, view) →
                (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler
                  (sequence n) who info (none : LateOption slots)
                  (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
                    info)).toReal = 1 := by
              intro info infoEq
              subst infoEq
              simp only [lateChoice, lateResponse, PMF.pure_map, silenceChoice,
                PMF.pure_apply_self, ENNReal.toReal_one]
            have mainMass := waiting site.1 atSite
            rw [mainMass, mul_one] at main
            exact main
          have spread := abs_expect_sub_apply_le (onePacketLate setup leaks bounds horizon
            scheduler sequence scale scale_pos scale_le_one (slots := slots) n
            ((onePacketN).agentAt site) none) (fun choice => siteHistoryFailure setup leaks
            bounds horizon scheduler (targetSequence n) site (PMF.pure choice) history)
            (fun choice => by
              unfold siteHistoryFailure
              exact ⟨expect_nonneg _ _ fun final _ => by split <;> norm_num,
                expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1 fun final _ => by
                  split <;> norm_num⟩)
            (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who site.1)
          calc _ ≤ |siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n)
                  site (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon
                    scheduler who site.1)) history -
                expect (onePacketLate setup leaks bounds horizon scheduler sequence scale
                  scale_pos scale_le_one (slots := slots) n ((onePacketN).agentAt site) none)
                  (fun choice => siteHistoryFailure setup leaks bounds horizon scheduler
                    (targetSequence n) site (PMF.pure choice) history)| +
                |expect (onePacketLate setup leaks bounds horizon scheduler sequence scale
                  scale_pos scale_le_one (slots := slots) n ((onePacketN).agentAt site) none)
                  (fun choice => siteHistoryFailure setup leaks bounds horizon scheduler
                    (targetSequence n) site (PMF.pure choice) history) -
                lumpedFailure setup leaks bounds horizon scheduler lumping (2 * horizon + 1) key
                  none (operationalRecord setup leaks bounds horizon scheduler
                    history.1.trace)| :=
                abs_sub_le _ _ _
            _ ≤ silenceError n + pathError n := by
                refine add_le_add ?_ near
                rw [abs_sub_comm]
                simp only [silenceError]
                linarith
            _ = _ := add_comm _ _
        have decorrelatedAbs : BeliefDecorrelated ((targetSequence n).belief who site)
            (fun history => operationalRecord setup leaks bounds horizon scheduler
              history.1.trace)
            (fun history => nativeDecodedState setup leaks history.1.state)
            |decorrelation n| :=
          (decorrelated n who site notFree notOwing notKeyed pendingSome).mono (le_abs_self _)
        have siteBound := abs_siteStopValue_sub_le_of_forced setup leaks bounds horizon
          scheduler parameter utility excludedPayoff (targetSequence n)
          (setup.intendedOpeningProfile (sequence n).strategy) site atSite _
          (lumpedFailure setup leaks bounds horizon scheduler lumping (2 * horizon + 1) key none)
          (lumpedUnit none) valueNonneg (add_nonneg pathNonneg silenceNonneg)
          (fun history _ forced => certificate_firstActivation_historyNear setup leaks bounds
            horizon scheduler parameter utility excludedPayoff wellFormed sequence scale
            scale_pos scale_le_one weights targetSequence assembled n contract.completes covers
            capacity slotsLe site first debtFree siteKey pending atSite _ (Or.inr rfl) history
            forced (readoutBounded who) (excludedBounded who))
          silenceNear unforcedAbs decorrelatedAbs (readoutBounded who) (excludedBounded who)
        refine siteBound.trans ?_
        change _ ≤ silencePart n + _ + _
        linarith
    | some material =>
        -- A transmission names the pending reveal and is the disclosure.
        obtain ⟨named, payload, binding, checks, outputEq, codeEq, node⟩ :=
          compared_transmission_names setup leaks bounds horizon scheduler site pending choice
            compared selected sends
        have disclosure := abs_siteStopValue_disclosure_sub_le_unforced setup leaks bounds
          horizon scheduler parameter utility excludedPayoff wellFormed contract timely
          (sequence n) (targetSequence n) site pending notLate debtFree node
          (readoutBounded who) (excludedBounded who) choice selected sends named
        refine disclosure.trans ?_
        change _ ≤ silencePart n + _ + _
        linarith
  · -- The prescribed component.
    have prescribed := abs_siteStopValue_prescribed_sub_le_unforced setup leaks bounds horizon
      scheduler parameter utility excludedPayoff wellFormed contract timely retains (sequence n)
      (scale_pos n).le (scale_le_one n) (targetSequence n) site pending notLate debtFree
      (readoutBounded who) (excludedBounded who)
    refine prescribed.trans ?_
    change _ ≤ silencePart n + _ + _
    linarith

end Vegas
