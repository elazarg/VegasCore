/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketExtension
import Vegas.Game.OnePacketLawApproximation
import GameTheoryExtensions.Analysis.Protocol.FreeKeyedPools
import Vegas.Game.OnePacketDelivery
import Vegas.Game.OnePacketIntendedProjection

/-! # The pooled components of the one-packet certificate

The source is the intended game of a well-formed setup, observed through its
typed readout and the exclusion payoff it determines
(`Vegas.intendedReadoutExclusion`); the target is the one-packet game of the
default runtime, observed through its typed readout and native exclusion
payoff (`Vegas.readoutExclusion`). The utility of either observation is its
payoff component (`Vegas.payoffComponent`).

The agents outside the forced region are free, and each sits alone in its pool
(`Vegas.FreeAgent`); forced late deliveries sharing a late-delivery key form a
pool with the late options as parts, and every other agent sits in a pool with
one part (`Vegas.onePacketPool`). Unforced agents tremble each choice, forced
late deliveries play the late component of each option, and every other agent
plays the slot-trembled prescribed component (`Vegas.onePacketComponent`); at a
positive scale every component has full support
(`Vegas.onePacketComponent_fullSupport`). The tremble scales, the
failure sets and the obligations of the certificate for one source sequence
are collected in `Vegas.OnePacketCertificateInputs`.
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

section Components

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

variable [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
  scheduler).InfoState who)]

/-- The agents of the one-packet game outside the forced region. -/
def UnforcedAgent (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) : Prop :=
  ¬ forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
    scheduler agent.1 agent.2.1

/-- An agent owing a failure: it owes one at the decoded point of some history
of its information state. -/
def OwingAgent (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) : Prop :=
  ∃ history : (onePacketN).InformationHistory agent.1 agent.2.1, ∃ point,
    nativeDecodedState setup leaks history.1.state = some point ∧
      ProtocolState.OwesFailure agent.1 setup.program point

/-- **The free agents of the one-packet certificate**: the agents outside the
forced region. A free agent sits alone in its pool, choosing among its choices.
An agent owing a failure is not free: it plays its usual component, and is
indifferent among its local laws. -/
def FreeAgent (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) : Prop :=
  UnforcedAgent setup leaks bounds horizon scheduler agent

omit [Finite setup.intendedProtocol.History] in
/-- An agent that is not free is in the forced region. -/
theorem forcedAgent_of_not_free
    {agent : (onePacketN).InformationAgent (onePacketN).playedInformation}
    (notFree : ¬ FreeAgent setup leaks bounds horizon scheduler agent) :
    forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler agent.1 agent.2.1 :=
  Classical.not_not.mp notFree

/-- **The pools of the one-packet certificate.** A free agent sits alone,
choosing among its choices; forced late deliveries sharing a late-delivery key
form a pool with the late options as parts; every other agent sits in one pool
with one part. -/
abbrev onePacketPool :=
  freeKeyedPool (FreeAgent setup leaks bounds horizon scheduler)
    (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
    (agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler)

/-- The parts of the pools of the one-packet certificate. -/
abbrev OnePacketPart (slots : Nat) :=
  FreeKeyedPart (FreeAgent setup leaks bounds horizon scheduler)
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
  /-- **Owing agents gain nothing.** At the site of an agent owing a failure,
  no local law changes the agent's expected exclusion payoff. -/
  owing_noGain : ∀ (assessment : (onePacketN).BehavioralAssessment) who
      (site : (onePacketN).InformationSite who),
    OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) → ∀ law,
      localGain (2 * horizon + 1) (readoutExclusion setup leaks bounds (initialLaw setup) horizon
        scheduler parameter utility excludedPayoff) (payoffComponent setup) assessment site law = 0
  /-- **The one-dimensional decomposition of late delivery, with its value
  bounds and site-level commonness.** At every forced late-delivery decision
  site of an agent owing no failure, failure pays the exclusion payoff at most
  the site's continuation value up to a vanishing error with gap at most the gap
  bound, the successful part of each late option is its success probability
  times that continuation value up to the error, and each option fails,
  belief-averaged, within a vanishing drift of one minus its score at the site's
  late-delivery key. -/
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
              (FreeAgent setup leaks bounds horizon scheduler)
              (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler) agent →
            ¬ OwingAgent setup leaks bounds horizon scheduler agent →
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
  /-- **The ranking of marked choices.** At every forced site of an agent
  owing no failure, each marked
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
            ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
              ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
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
            (ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
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
            (¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
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
  site of an agent owing no failure meets one of the three local comparisons of
  a pooled limit certificate on its own: values outside the intended menu, bad
  bindings, charged packets. -/
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
              Finset.univ.filter (FreeAgent setup leaks bounds horizon scheduler) →
            ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
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

end Certificate

end Vegas
