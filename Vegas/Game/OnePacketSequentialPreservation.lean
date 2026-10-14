/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketExtension
import Vegas.Game.OnePacketLawApproximation
import Vegas.Game.OnePacketExclusionPayoff
import GameTheoryExtensions.Analysis.Protocol.CopiedSiteLimit
import GameTheoryExtensions.Analysis.Protocol.FreeKeyedPools
import Vegas.Game.OnePacketDelivery

/-! # Sequential preservation for the one-packet game

The source is the intended game of a well-formed setup, observed through its
typed readout and the exclusion payoff it determines
(`Vegas.intendedReadoutExclusion`); the target is the one-packet game of the
default runtime, observed through its typed readout and native exclusion
payoff (`Vegas.readoutExclusion`). The utility of either observation is its
payoff component.

**From certificates.** If, for every fully mixed Bayes sequence converging to an
intended sequential equilibrium, a pooled component family on the one-packet
game meets the obligations of a pooled limit certificate, then some sequential
equilibrium of the one-packet game under the exclusion payoff has the intended
joint law of typed readout and exclusion payoff
(`Vegas.onePacket_intended_sequentialEquilibrium_of_certificates`). Every
intended sequential equilibrium is sequentially rational against the exclusion
payoff (`Vegas.SourceProgram.Setup.intended_exclusionSource`), which supplies
the source side of the limit theorem.

**The raw runtime.** Composed with the extension of one-packet equilibria to the
bounded raw runtime under the count audit, the same certificates give a
sequential equilibrium of the bounded raw runtime, under the exclusion payoff
minus the deposit for each collected count charge, that charges nobody on its
paths and whose joint law of normalized typed readout and exclusion payoff is
the intended one (`Vegas.onePacket_intended_raw_sequentialEquilibrium`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- The utility of an observation of readout and payoffs: its payoff component. -/
abbrev payoffComponent (outcome : Option (State L setup.program.terminalCtx) × (Player → ℝ))
    (who : Player) : ℝ :=
  outcome.2 who

open Classical in
/-- **Sequential equilibrium of the one-packet game from certificates.** For a
well-formed setup, every sequential equilibrium of the intended game, and a
pooled limit certificate on the one-packet game for every fully mixed Bayes
sequence converging to it, there is a sequential equilibrium of the one-packet
game under the exclusion payoff whose joint law of typed readout and exclusion
payoff is the intended one. -/
theorem onePacket_intended_sequentialEquilibrium_of_certificates
    (wellFormed : setup.WellFormed)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    (certificates : ∀ sequence : ℕ → setup.intendedModel.BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed) →
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent setup.intendedModel
        (sequence n) setup.intended_decision_antichain) →
      InformationModel.BehavioralAssessmentConvergesPointwise sequence intended →
      InformationModel.PooledLimitCertificate
        (N := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler)
        (intendedReadoutExclusion setup parameter utility excludedPayoff)
        (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
          utility excludedPayoff)
        (instructionCount setup.program + 1) (2 * horizon + 1)
        ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
          scheduler)
        ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall (initialLaw setup) horizon
          scheduler)
        (payoffComponent setup) sequence) :
    ∃ target : (onePacketModel setup leaks bounds (initialLaw setup) horizon
        scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        ((bounds.onePacketMenu (runtime setup) leaks).decisionInformationAntichain
          (initialLaw setup) horizon scheduler)
        ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories
        (fun who final => exclusionBase setup parameter utility excludedPayoff leaks final.state
          who) ∧
      ((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).map
          (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
            utility excludedPayoff) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  obtain ⟨sequence, mixed, bayes, converges, rational⟩ :=
    setup.intended_exclusionSource wellFormed parameter utility excludedPayoff intended
      equilibrium
  obtain ⟨target, targetSE, law⟩ :=
    (certificates sequence mixed bayes converges).exists_sequentialEquilibrium intended converges
      rational
  let bounded := (bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
    scheduler
  exact ⟨target, (target.isSequentialEquilibrium_iff_truncated_of_bounded _ _
    bounded.wellFoundedHistories bounded _).mpr targetSE, law⟩

open Classical in
/-- **Sequential equilibrium of the bounded raw runtime from certificates.**
Under the hypotheses of
`Vegas.onePacket_intended_sequentialEquilibrium_of_certificates`, bounds on the
utility, and a count-evidence service with a deposit covering the spread of
the exclusion payoff, there is a sequential equilibrium of the bounded raw
runtime under the exclusion payoff minus the deposit for each collected count
charge, that charges nobody on its paths, whose joint law of typed readout and
realized payoffs is the intended joint law of typed readout and exclusion
payoff. -/
theorem onePacket_intended_raw_sequentialEquilibrium (wellFormed : setup.WellFormed)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    (certificates : ∀ sequence : ℕ → setup.intendedModel.BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed) →
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent setup.intendedModel
        (sequence n) setup.intended_decision_antichain) →
      InformationModel.BehavioralAssessmentConvergesPointwise sequence intended →
      InformationModel.PooledLimitCertificate
        (N := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler)
        (intendedReadoutExclusion setup parameter utility excludedPayoff)
        (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
          utility excludedPayoff)
        (instructionCount setup.program + 1) (2 * horizon + 1)
        ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
          scheduler)
        ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall (initialLaw setup) horizon
          scheduler)
        (payoffComponent setup) sequence)
    (service : EvidenceReportService (CountEvidence (graph setup)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (deposit : Player → ℝ) (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      max 0 (max (excludedPayoff who) (upperUtility who)) -
          min 0 (min (excludedPayoff who) (lowerUtility who)) ≤
        observationRate who * deliveryRate who * deposit who) :
    let raw := bounds.rawMenu (runtime setup) leaks
    let observe := (application setup leaks).stateTraffic
    let audit := (runtime setup).countAudit leaks service.sample
    let base := exclusionBase setup parameter utility excludedPayoff leaks
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∃ target : (raw.information (initialLaw setup) horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (raw.decisionInformationAntichain (initialLaw setup) horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => payoff history.state who) (2 * horizon + 1)) ∧
      (∀ final ∈ ((raw.information (initialLaw setup) horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information (initialLaw setup) horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).bind
          (fun final => (settle final.state).map fun payoffs =>
            (sourceReadout setup leaks final.state, payoffs)) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  intro raw observe audit base payoff settle
  obtain ⟨native, nativeSE, law⟩ := onePacket_intended_sequentialEquilibrium_of_certificates
    setup leaks bounds horizon scheduler parameter utility excludedPayoff wellFormed intended
    equilibrium certificates
  obtain ⟨target, targetSE, clean, _, joint⟩ :=
    bounds.onePacket_raw_sequentialEquilibrium (runtime setup) leaks (initialLaw setup) horizon
      scheduler service observationRate deliveryRate delivery_nonnegative coverage
      (fun state who => base state who)
      (fun state => exclusionBase_normalization setup parameter utility excludedPayoff leaks state)
      (fun who => min 0 (min (excludedPayoff who) (lowerUtility who)))
      (fun who => max 0 (max (excludedPayoff who) (upperUtility who))) deposit
      (fun state who => (exclusionBase_mem_Icc setup parameter utility excludedPayoff
        leaks lowerUtility upperUtility lower_le le_upper state who).1)
      (fun state who => (exclusionBase_mem_Icc setup parameter utility excludedPayoff
        leaks lowerUtility upperUtility lower_le le_upper state who).2)
      deposit_nonnegative sufficient native nativeSE
  refine ⟨target, targetSE, clean, ?_⟩
  have pairs := congrArg (PMF.map (Prod.map (sourceReadout setup leaks) id)) joint
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Prod.map_apply, id_eq,
    sourceReadout_normalization] at pairs
  rw [pairs, ← law]
  rfl

section Components

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

variable [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
  scheduler).InfoState who)]

/-- The agents of the one-packet game outside the forced region. -/
def UnforcedAgent (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) : Prop :=
  ¬ forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
    scheduler agent.1 agent.2.1

/-- **The pools of the one-packet certificate.** An unforced agent sits alone,
choosing among its choices; forced late deliveries sharing a late-delivery key
form a pool with the late options as parts; every other agent sits in one pool
with one part. -/
abbrev onePacketPool :=
  freeKeyedPool (UnforcedAgent setup leaks bounds horizon scheduler)
    (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
    (agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler)

/-- The parts of the pools of the one-packet certificate. -/
abbrev OnePacketPart (slots : Nat) :=
  FreeKeyedPart (UnforcedAgent setup leaks bounds horizon scheduler)
    (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
    (agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler) (LateOption slots)

/-- The free law of an unforced agent's choice: the choice trembled toward the
uniform law over its menu with weight `scale`. -/
def unforcedLaw (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (choice : (onePacketN).Choice agent.1 agent.2.1) :
    PMF ((onePacketN).Choice agent.1 agent.2.1) :=
  mix scale nonnegative le_one
    ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy (initialLaw setup) horizon
      scheduler agent.1 agent.2.1) (PMF.pure choice)

/-- **The components of the one-packet certificate.** Unforced agents tremble
each choice; forced late deliveries play the late component of each option;
every other agent plays the slot-trembled prescribed component, all with the
intended assessment `assessment` and the tremble scale `scale`. -/
def onePacketComponent (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) :
    OnePacketPart setup leaks bounds horizon scheduler slots
        (onePacketPool setup leaks bounds horizon scheduler agent) →
      PMF ((onePacketN).Choice agent.1 agent.2.1) :=
  freeKeyedComponent (unforcedLaw setup leaks bounds horizon scheduler scale nonnegative le_one)
    (fun agent => slotPrescribedComponent setup leaks bounds (initialLaw setup) horizon scheduler
      assessment scale nonnegative le_one agent.1 agent.2.1)
    (fun agent option => lateComponent setup leaks bounds (initialLaw setup) horizon scheduler
      assessment scale nonnegative le_one agent.1 agent.2.1 option) agent

omit [Finite setup.intendedProtocol.History] in
theorem unforcedLaw_fullSupport {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (choice : (onePacketN).Choice agent.1 agent.2.1) :
    FullSupport (unforcedLaw setup leaks bounds horizon scheduler scale positive.le le_one agent
      choice) := by
  intro other
  let := Fintype.ofFinite ((onePacketN).Choice agent.1 agent.2.1)
  exact mem_support_mix_left _ _ _ positive (PMF.mem_support_uniformOfFintype other)

omit [Finite setup.intendedProtocol.History] in
theorem onePacketComponent_fullSupport (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (part : OnePacketPart setup leaks bounds horizon scheduler slots
      (onePacketPool setup leaks bounds horizon scheduler agent)) :
    FullSupport (onePacketComponent setup leaks bounds horizon scheduler assessment scale
      positive.le le_one agent part) :=
  freeKeyedComponent_fullSupport _ _ _
    (unforcedLaw_fullSupport setup leaks bounds horizon scheduler positive le_one)
    (fun agent => by
      unfold slotPrescribedComponent
      exact slotTrembledChoice_fullSupport setup leaks bounds (initialLaw setup) horizon
        scheduler positive le_one agent.1 agent.2.1 _ _ _)
    (fun agent option => lateComponent_fullSupport setup leaks bounds (initialLaw setup) horizon
      scheduler assessment positive le_one agent.1 agent.2.1 option) agent part

end Components

section Certificate

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

variable [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
  scheduler).InfoState who)]

/-- The fallback of the one-packet certificate: some choice at every information
state. -/
def onePacketFallback (who : Player) :
    (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Policy who :=
  fun _ => Classical.arbitrary _

/-- The free laws of the one-packet certificate along a scale sequence. -/
def onePacketUnforced (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n)
    (scale_le_one : ∀ n, scale n ≤ 1) (n : ℕ) :=
  unforcedLaw setup leaks bounds horizon scheduler (scale n) (scale_pos n).le (scale_le_one n)

/-- The prescribed laws of the one-packet certificate along a source sequence
and a scale sequence. -/
def onePacketPrescribed (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1) (n : ℕ)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) :
    PMF ((onePacketN).Choice agent.1 agent.2.1) :=
  slotPrescribedComponent setup leaks bounds (initialLaw setup) horizon scheduler (sequence n)
    (scale n) (scale_pos n).le (scale_le_one n) agent.1 agent.2.1

/-- The late laws of the one-packet certificate along a source sequence and a
scale sequence. -/
def onePacketLate (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (n : ℕ)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (option : LateOption slots) : PMF ((onePacketN).Choice agent.1 agent.2.1) :=
  lateComponent setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) (scale n)
    (scale_pos n).le (scale_le_one n) agent.1 agent.2.1 option

open Classical in
/-- **The open inputs of the one-packet certificate** for one source sequence:
the tremble scales, the event-level failure sets paying the exclusion payoff,
and the obligations not yet discharged, named after their mathematical
content. -/
structure OnePacketCertificateInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (slots : Nat) where
  /-- The tremble scale at each index. -/
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  scale_le_one : ∀ n, scale n ≤ 1
  scale_vanishing : Tendsto scale atTop (nhds 0)
  /-- The failure set of each agent's event. -/
  failed : (onePacketN).InformationAgent (onePacketN).playedInformation →
    Set ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History
  /-- Failure pays exactly the exclusion payoff. -/
  failed_pays : ∀ agent, ∀ history ∈ failed agent,
    payoffComponent setup (readoutExclusion setup leaks bounds (initialLaw setup) horizon
      scheduler parameter utility excludedPayoff history) agent.1 = excludedPayoff agent.1
  /-- A bound on the gap between a continuation value and the exclusion payoff. -/
  gapBound : ℝ
  gapBound_nonneg : 0 ≤ gapBound
  /-- The marked choices of each site. -/
  compared : ∀ who (site : (onePacketN).InformationSite who), (onePacketN).Choice who site.1 → Prop
  /-- **The one-dimensional decomposition of late delivery, with its value
  bounds and site-level commonness.** At every forced late-delivery decision
  site, failure pays the exclusion payoff at most the site's continuation value
  up to a vanishing error with gap at most the gap bound, the successful part of
  each late option is its success probability times that continuation value up
  to the error, and each option fails, belief-averaged, within a vanishing drift
  of one minus its score at the site's late-delivery key. -/
  decomposition : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler
      slots p))
          (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
        (∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior
            (onePacketN).playedInformation (onePacketFallback setup leaks bounds horizon scheduler)
          fun agent => (weights n (onePacketPool setup leaks bounds horizon scheduler agent)).bind
            (freeKeyedComponent ((onePacketUnforced setup leaks bounds horizon scheduler scale
                scale_pos
            scale_le_one) n) ((onePacketPrescribed setup leaks bounds horizon scheduler sequence
                scale
            scale_pos scale_le_one) n) ((onePacketLate setup leaks bounds horizon scheduler
                sequence scale scale_pos
            scale_le_one (slots := slots)) n) agent)) →
        (∀ n, (targetSequence n).IsFullyMixed) →
        (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
          ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
            (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
        ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
          (score : ℕ → Option (LateKey setup leaks) → LateOption slots → ℝ) (error drift : ℕ → ℝ),
          Tendsto error atTop (nhds 0) ∧ Tendsto drift atTop (nhds 0) ∧ (∀ n, 0 ≤ drift n) ∧
          ∀ n (agent : (onePacketN).InformationAgent (onePacketN).playedInformation), ownedKeyed
              (UnforcedAgent setup leaks bounds horizon scheduler)
              (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler) agent →
            ∀ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
            excludedPayoff agent.1 ≤ continuation n agent + error n ∧
            continuation n agent - excludedPayoff agent.1 ≤ gapBound ∧
            (∀ option, |localSuccessValue (2 * horizon + 1) (readoutExclusion setup leaks bounds
                (initialLaw setup) horizon
            scheduler parameter utility excludedPayoff) (payoffComponent setup) (targetSequence n)
                (who := agent.1) ⟨agent.2.1, decision⟩ (failed agent) ((onePacketLate setup leaks
                    bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots)) n agent option) -
              (1 - localFailure (2 * horizon + 1) (targetSequence n) (who := agent.1) ⟨agent.2.1,
                  decision⟩
                (failed agent) ((onePacketLate setup leaks bounds horizon scheduler sequence scale
                    scale_pos
            scale_le_one (slots := slots)) n agent option)) * continuation n agent| ≤ error n) ∧
            ∀ option, |localFailure (2 * horizon + 1) (targetSequence n) (who := agent.1)
                ⟨agent.2.1, decision⟩
                (failed agent) ((onePacketLate setup leaks bounds horizon scheduler sequence scale
                    scale_pos
            scale_le_one (slots := slots)) n agent option) - (1 - score n (agentLateKey setup leaks
                bounds (initialLaw setup) horizon scheduler agent) option)| ≤
              drift n
  /-- **The ranking of marked choices.** At every forced site, each marked
  choice decomposes the same way; at a late delivery it fails within the drift
  of one minus the score of some option, or surely; at a first activation the
  prescribed component fails at most as often up to a vanishing slack, or the
  choice fails surely. -/
  ranking : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
          (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
        (∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior
            (onePacketN).playedInformation (onePacketFallback setup leaks bounds horizon scheduler)
          fun agent => (weights n (onePacketPool setup leaks bounds horizon scheduler agent)).bind
            (freeKeyedComponent ((onePacketUnforced setup leaks bounds horizon scheduler scale
                scale_pos
            scale_le_one) n) ((onePacketPrescribed setup leaks bounds horizon scheduler sequence
                scale
            scale_pos scale_le_one) n) ((onePacketLate setup leaks bounds horizon scheduler
                sequence scale scale_pos
            scale_le_one (slots := slots)) n) agent)) →
        (∀ n, (targetSequence n).IsFullyMixed) →
        (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
          ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
            (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
        ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
          (score : ℕ → Option (LateKey setup leaks) → LateOption slots → ℝ) (error drift slack : ℕ
              → ℝ),
          Tendsto error atTop (nhds 0) ∧ Tendsto drift atTop (nhds 0) ∧
          Tendsto slack atTop (nhds 0) ∧ (∀ n, 0 ≤ drift n) ∧ (∀ n, 0 ≤ slack n) ∧
          ∀ n who (site : (onePacketN).InformationSite who) (choice : (onePacketN).Choice who
              site.1),
            ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
                compared who site choice →
            ((excludedPayoff who ≤ continuation n ((onePacketN).agentAt site) + error n ∧
                continuation n ((onePacketN).agentAt site) - excludedPayoff who ≤ gapBound) ∨
              failed ((onePacketN).agentAt site) = ∅) ∧
            |localSuccessValue (2 * horizon + 1) (readoutExclusion setup leaks bounds (initialLaw
                setup) horizon
            scheduler parameter utility excludedPayoff) (payoffComponent setup) (targetSequence n)
                site (failed ((onePacketN).agentAt site))
                (PMF.pure choice) -
              (1 - localFailure (2 * horizon + 1) (targetSequence n) site
                (failed ((onePacketN).agentAt site)) (PMF.pure choice)) *
                continuation n ((onePacketN).agentAt site)| ≤ error n ∧
            (ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
              (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
                  ((onePacketN).agentAt site) →
              (∀ option, |localSuccessValue (2 * horizon + 1) (readoutExclusion setup leaks bounds
                  (initialLaw setup) horizon
            scheduler parameter utility excludedPayoff) (payoffComponent setup) (targetSequence n)
                site
                  (failed ((onePacketN).agentAt site)) ((onePacketLate setup leaks bounds horizon
                      scheduler sequence scale scale_pos
            scale_le_one (slots := slots)) n ((onePacketN).agentAt site) option) -
                (1 - localFailure (2 * horizon + 1) (targetSequence n) site (failed
                    ((onePacketN).agentAt site))
                  ((onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots)) n ((onePacketN).agentAt site) option)) * continuation n
                ((onePacketN).agentAt site)| ≤
                error n) ∧
              (∀ option, |localFailure (2 * horizon + 1) (targetSequence n) site (failed
                  ((onePacketN).agentAt site))
                  ((onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots)) n ((onePacketN).agentAt site) option) -
                (1 - score n (agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler
              ((onePacketN).agentAt site)) option)| ≤ drift n) ∧
              ((∃ option, |localFailure (2 * horizon + 1) (targetSequence n) site (failed
                  ((onePacketN).agentAt site))
                  (PMF.pure choice) - (1 - score n (agentLateKey setup leaks bounds (initialLaw
                      setup) horizon scheduler
              ((onePacketN).agentAt site)) option)| ≤ drift n) ∨
                localFailure (2 * horizon + 1) (targetSequence n) site
                  (failed ((onePacketN).agentAt site)) (PMF.pure choice) = 1)) ∧
            (¬ ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
              (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
                  ((onePacketN).agentAt site) →
              |localSuccessValue (2 * horizon + 1) (readoutExclusion setup leaks bounds (initialLaw
                  setup) horizon
            scheduler parameter utility excludedPayoff) (payoffComponent setup) (targetSequence n)
                site
                (failed ((onePacketN).agentAt site))
                  ((onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
            scale_pos scale_le_one) n ((onePacketN).agentAt site)) -
                (1 - localFailure (2 * horizon + 1) (targetSequence n) site (failed
                    ((onePacketN).agentAt site))
                  ((onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
            scale_pos scale_le_one) n ((onePacketN).agentAt site))) * continuation n
                ((onePacketN).agentAt site)| ≤ error n ∧
              (localFailure (2 * horizon + 1) (targetSequence n) site (failed ((onePacketN).agentAt
                  site))
                  ((onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
            scale_pos scale_le_one) n ((onePacketN).agentAt site)) ≤
                localFailure (2 * horizon + 1) (targetSequence n) site
                  (failed ((onePacketN).agentAt site)) (PMF.pure choice) + slack n ∨
                localFailure (2 * horizon + 1) (targetSequence n) site
                  (failed ((onePacketN).agentAt site)) (PMF.pure choice) = 1))
  /-- **The comparisons of unmarked choices.** Every unmarked choice at a forced
  site meets one of the three local comparisons of a pooled limit certificate
  on its own: values outside the intended menu, bad bindings, charged packets. -/
  otherComparisons : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler
      slots p))
          (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
        (∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior
            (onePacketN).playedInformation (onePacketFallback setup leaks bounds horizon scheduler)
          fun agent => (weights n (onePacketPool setup leaks bounds horizon scheduler agent)).bind
            (freeKeyedComponent ((onePacketUnforced setup leaks bounds horizon scheduler scale
                scale_pos
            scale_le_one) n) ((onePacketPrescribed setup leaks bounds horizon scheduler sequence
                scale
            scale_pos scale_le_one) n) ((onePacketLate setup leaks bounds horizon scheduler
                sequence scale scale_pos
            scale_le_one (slots := slots)) n) agent)) →
        (∀ n, (targetSequence n).IsFullyMixed) →
        (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
          ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
            (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
        (∀ n (alternative : ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
            p,
          ∑ agent ∈ Finset.univ.filter (fun agent => onePacketPool setup leaks bounds horizon
              scheduler agent = p),
            (if decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1 then
              let comparison := (onePacketN).assessmentComparisonWith ((onePacketN).truncatedRunner
                  (2 * horizon + 1))
                (readoutExclusion setup leaks bounds (initialLaw setup) horizon
            scheduler parameter utility excludedPayoff) (targetSequence n) agent.1
                (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                  ((alternative (onePacketPool setup leaks bounds horizon scheduler agent)).bind
                    (freeKeyedComponent ((onePacketUnforced setup leaks bounds horizon scheduler
                        scale scale_pos
            scale_le_one) n) ((onePacketPrescribed setup leaks bounds horizon scheduler sequence
                scale
            scale_pos scale_le_one) n) ((onePacketLate setup leaks bounds horizon scheduler
                sequence scale scale_pos
            scale_le_one (slots := slots)) n) agent)))
              expect comparison.alternative ((payoffComponent setup) · agent.1) -
                expect comparison.prescribed ((payoffComponent setup) · agent.1)
            else 0) ≤ 0) →
        ∃ otherError : ℕ → ℝ, Tendsto otherError atTop (nhds 0) ∧
          ∀ n who (site : (onePacketN).InformationSite who), (onePacketN).agentAt site ∉
              Finset.univ.filter (UnforcedAgent setup leaks bounds horizon scheduler) →
            ∀ choice : (onePacketN).Choice who site.1, ¬ compared who site choice →
            let gain := fun law : PMF ((onePacketN).Choice who site.1) =>
              let comparison := (onePacketN).assessmentComparisonWith ((onePacketN).truncatedRunner
                  (2 * horizon + 1)) (readoutExclusion setup leaks bounds (initialLaw setup) horizon
            scheduler parameter utility excludedPayoff) (targetSequence n)
                who (site, ((targetSequence n).strategy who).withLaw site.1 law)
              expect comparison.alternative ((payoffComponent setup) · who) -
                expect comparison.prescribed ((payoffComponent setup) · who)
            gain (PMF.pure choice) ≤ otherError n ∨
              (∃ alternative : PMF (OnePacketPart setup leaks bounds horizon scheduler slots
                  (onePacketPool setup leaks bounds horizon scheduler ((onePacketN).agentAt site))),
                gain (PMF.pure choice) ≤
                  gain (alternative.bind (freeKeyedComponent ((onePacketUnforced setup leaks bounds
                      horizon scheduler scale scale_pos
            scale_le_one) n) ((onePacketPrescribed setup leaks bounds horizon scheduler sequence
                scale
            scale_pos scale_le_one) n) ((onePacketLate setup leaks bounds horizon scheduler
                sequence scale scale_pos
            scale_le_one (slots := slots)) n)
                    ((onePacketN).agentAt site))) + otherError n) ∨
              ∃ mixture : PMF (setup.intendedModel.AssessmentDeviation who),
                gain (PMF.pure choice) ≤
                  expect mixture (fun deviation =>
                    let sourceComparison := setup.intendedModel.assessmentComparisonWith
                        (setup.intendedModel.truncatedRunner
                        (instructionCount setup.program + 1)) (intendedReadoutExclusion setup
                            parameter utility excludedPayoff)
                      (sequence n) who deviation
                    expect sourceComparison.alternative ((payoffComponent setup) · who) -
                      expect sourceComparison.prescribed ((payoffComponent setup) · who)) +
                          otherError n
  /-- **The law approximation.** The one-packet law of typed readout and
  exclusion payoff approaches the perturbed intended law, as the law
  approximation for slot-trembled components provides. -/
  lawApproximation : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler
      slots p)) (targetSequence : ℕ →
      (onePacketN).BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior (onePacketN).playedInformation
          (onePacketFallback setup leaks bounds horizon scheduler)
        fun agent => (weights n (onePacketPool setup leaks bounds horizon scheduler agent)).bind
            (freeKeyedComponent (onePacketUnforced setup leaks bounds horizon scheduler scale
            scale_pos
          scale_le_one n) (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
          scale_pos scale_le_one n) (onePacketLate setup leaks bounds horizon scheduler sequence
          scale scale_pos scale_le_one (slots := slots) n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
        ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
          (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => onePacketPool setup leaks bounds horizon
            scheduler agent = p),
          (if decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1 then
            let comparison := (onePacketN).assessmentComparisonWith ((onePacketN).truncatedRunner
                (2 * horizon + 1))
              (readoutExclusion setup leaks bounds (initialLaw setup) horizon
          scheduler parameter utility excludedPayoff) (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (onePacketPool setup leaks bounds horizon scheduler agent)).bind
                    (freeKeyedComponent (onePacketUnforced setup leaks bounds horizon scheduler
                    scale scale_pos
          scale_le_one n) (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
          scale_pos scale_le_one n) (onePacketLate setup leaks bounds horizon scheduler sequence
          scale scale_pos scale_le_one (slots := slots) n) agent)))
            expect comparison.alternative ((payoffComponent setup) · agent.1) -
              expect comparison.prescribed ((payoffComponent setup) · agent.1)
          else 0) ≤ 0) →
      ∃ lawError : ℕ → ℝ, Tendsto lawError atTop (nhds 0) ∧
        ∀ n outcome,
          |((((onePacketN).runBehavioral (targetSequence n).strategy (2 * horizon + 1)).map
              (readoutExclusion setup leaks bounds (initialLaw setup) horizon
          scheduler parameter utility excludedPayoff))
              outcome).toReal -
            (((setup.intendedModel.runBehavioral (sequence n).strategy (instructionCount
                setup.program + 1)).map (intendedReadoutExclusion setup parameter utility
                excludedPayoff))
              outcome).toReal| ≤ lawError n

open Classical in
/-- **The one-packet certificate.** The pooled limit certificate on the
one-packet game built from its open inputs: unforced agents tremble each
choice and span their laws; forced late deliveries pool by late-delivery key
over the late options; every other agent plays the slot-trembled prescribed
component. Member rationality and the local comparisons are derived from the
inputs; the law approximation is an input. -/
def onePacketCertificate (sequence : ℕ → setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (inputs : OnePacketCertificateInputs setup leaks bounds horizon scheduler parameter utility
      excludedPayoff sequence slots) :
    InformationModel.PooledLimitCertificate
      (N := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler)
      (intendedReadoutExclusion setup parameter utility excludedPayoff)
      (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
        utility excludedPayoff)
      (instructionCount setup.program + 1) (2 * horizon + 1)
      ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon scheduler)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall (initialLaw setup) horizon
        scheduler)
      (payoffComponent setup) sequence where
  fallback := onePacketFallback setup leaks bounds horizon scheduler
  Pool := FreeKeyedPool (UnforcedAgent setup leaks bounds horizon scheduler)
    (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
    (agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler)
  poolDecidable := inferInstance
  pool := onePacketPool setup leaks bounds horizon scheduler
  Part := OnePacketPart setup leaks bounds horizon scheduler slots
  component n := freeKeyedComponent
    (onePacketUnforced setup leaks bounds horizon scheduler inputs.scale inputs.scale_pos
      inputs.scale_le_one n)
    (onePacketPrescribed setup leaks bounds horizon scheduler sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one n)
    (onePacketLate setup leaks bounds horizon scheduler sequence inputs.scale inputs.scale_pos
      inputs.scale_le_one (slots := slots) n)
  componentFull n agent part := onePacketComponent_fullSupport setup leaks bounds horizon
    scheduler (sequence n) (inputs.scale_pos n) (inputs.scale_le_one n) agent part
  free := Finset.univ.filter (UnforcedAgent setup leaks bounds horizon scheduler)
  freeSpanning := freeKeyedSpanning
    (fun n => onePacketUnforced setup leaks bounds horizon scheduler inputs.scale
      inputs.scale_pos inputs.scale_le_one n)
    (fun n => onePacketPrescribed setup leaks bounds horizon scheduler sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one n)
    (fun n => onePacketLate setup leaks bounds horizon scheduler sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one (slots := slots) n)
    (fun agent choice => pmfConvergesPointwise_mix_zero inputs.scale
      (fun n => (inputs.scale_pos n).le) inputs.scale_le_one inputs.scale_vanishing _ _)
  memberRational := by
    convert freeKeyedMemberRational (2 * horizon + 1)
      ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon scheduler)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall (initialLaw setup) horizon
        scheduler)
      (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
        excludedPayoff) (payoffComponent setup) (onePacketFallback setup leaks bounds horizon
          scheduler)
      (UnforcedAgent setup leaks bounds horizon scheduler)
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
      (agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler)
      (fun n => onePacketUnforced setup leaks bounds horizon scheduler inputs.scale
        inputs.scale_pos inputs.scale_le_one n)
      (fun n => onePacketPrescribed setup leaks bounds horizon scheduler sequence inputs.scale
        inputs.scale_pos inputs.scale_le_one n)
      (fun n => onePacketLate setup leaks bounds horizon scheduler sequence inputs.scale
        inputs.scale_pos inputs.scale_le_one (slots := slots) n)
      inputs.failed excludedPayoff inputs.failed_pays inputs.gapBound inputs.gapBound_nonneg
      inputs.decomposition
  localComparisons := by
    convert freeKeyedLocalComparisons (2 * horizon + 1)
      ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon scheduler)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall (initialLaw setup) horizon
        scheduler)
      (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
        excludedPayoff) (payoffComponent setup) (onePacketFallback setup leaks bounds horizon
          scheduler)
      (UnforcedAgent setup leaks bounds horizon scheduler)
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
      (agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler)
      (intendedReadoutExclusion setup parameter utility excludedPayoff)
      (instructionCount setup.program + 1) sequence
      (fun n => onePacketUnforced setup leaks bounds horizon scheduler inputs.scale
        inputs.scale_pos inputs.scale_le_one n)
      (fun n => onePacketPrescribed setup leaks bounds horizon scheduler sequence inputs.scale
        inputs.scale_pos inputs.scale_le_one n)
      (fun n => onePacketLate setup leaks bounds horizon scheduler sequence inputs.scale
        inputs.scale_pos inputs.scale_le_one (slots := slots) n)
      inputs.compared inputs.failed excludedPayoff inputs.failed_pays inputs.gapBound
      inputs.gapBound_nonneg inputs.ranking
      (by convert inputs.otherComparisons)
  lawApproximation := by convert inputs.lawApproximation

open Classical in
/-- **Sequential equilibrium of the one-packet game from its open inputs.** For
a well-formed setup and every sequential equilibrium of the intended game, if
every fully mixed Bayes sequence converging to it supplies the open inputs of
the one-packet certificate, there is a sequential equilibrium of the one-packet
game under the exclusion payoff whose joint law of typed readout and exclusion
payoff is the intended one. -/
theorem onePacket_intended_sequentialEquilibrium_of_inputs (wellFormed : setup.WellFormed)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    {slots : Nat}
    (inputs : ∀ sequence : ℕ → setup.intendedModel.BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed) →
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent setup.intendedModel
        (sequence n) setup.intended_decision_antichain) →
      InformationModel.BehavioralAssessmentConvergesPointwise sequence intended →
      OnePacketCertificateInputs setup leaks bounds horizon scheduler parameter utility
        excludedPayoff sequence slots) :
    ∃ target : (onePacketModel setup leaks bounds (initialLaw setup) horizon
        scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        ((bounds.onePacketMenu (runtime setup) leaks).decisionInformationAntichain
          (initialLaw setup) horizon scheduler)
        ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories
        (fun who final => exclusionBase setup parameter utility excludedPayoff leaks final.state
          who) ∧
      ((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).map
          (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
            utility excludedPayoff) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) :=
  onePacket_intended_sequentialEquilibrium_of_certificates setup leaks bounds horizon scheduler
    parameter utility excludedPayoff wellFormed intended equilibrium
    fun sequence mixed bayes converges => by
      convert onePacketCertificate setup leaks bounds horizon scheduler parameter utility
        excludedPayoff sequence (inputs sequence mixed bayes converges)

open Classical in
/-- **Sequential equilibrium of the bounded raw runtime from the open inputs.**
Under the hypotheses of `Vegas.onePacket_intended_sequentialEquilibrium_of_inputs`,
bounds on the utility, and a count-evidence service with a deposit covering the
spread of the exclusion payoff, there is a sequential equilibrium of the bounded
raw runtime under the exclusion payoff minus the deposit for each collected
count charge, that charges nobody on its paths, whose joint law of typed
readout and realized payoffs is the intended joint law of typed readout and
exclusion payoff. -/
theorem onePacket_intended_raw_sequentialEquilibrium_of_inputs (wellFormed : setup.WellFormed)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    {slots : Nat}
    (inputs : ∀ sequence : ℕ → setup.intendedModel.BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed) →
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent setup.intendedModel
        (sequence n) setup.intended_decision_antichain) →
      InformationModel.BehavioralAssessmentConvergesPointwise sequence intended →
      OnePacketCertificateInputs setup leaks bounds horizon scheduler parameter utility
        excludedPayoff sequence slots)
    (service : EvidenceReportService (CountEvidence (graph setup)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (deposit : Player → ℝ) (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      max 0 (max (excludedPayoff who) (upperUtility who)) -
          min 0 (min (excludedPayoff who) (lowerUtility who)) ≤
        observationRate who * deliveryRate who * deposit who) :
    let raw := bounds.rawMenu (runtime setup) leaks
    let observe := (application setup leaks).stateTraffic
    let audit := (runtime setup).countAudit leaks service.sample
    let base := exclusionBase setup parameter utility excludedPayoff leaks
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∃ target : (raw.information (initialLaw setup) horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (raw.decisionInformationAntichain (initialLaw setup) horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => payoff history.state who) (2 * horizon + 1)) ∧
      (∀ final ∈ ((raw.information (initialLaw setup) horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information (initialLaw setup) horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).bind
          (fun final => (settle final.state).map fun payoffs =>
            (sourceReadout setup leaks final.state, payoffs)) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) :=
  onePacket_intended_raw_sequentialEquilibrium setup leaks bounds horizon scheduler parameter
    utility excludedPayoff wellFormed intended equilibrium
    (fun sequence mixed bayes converges => by
      convert onePacketCertificate setup leaks bounds horizon scheduler parameter utility
        excludedPayoff sequence (inputs sequence mixed bayes converges))
    service observationRate deliveryRate delivery_nonnegative coverage lowerUtility upperUtility
    lower_le le_upper deposit deposit_nonnegative sufficient

end Certificate

end Vegas
