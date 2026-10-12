/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketExclusionPayoff
import Vegas.Game.OnePacketTrembles
import GameTheoryExtensions.Analysis.Protocol.SuccessRanking

/-! # Delivery is one-dimensional under the exclusion payoff

Read through the typed readout of the default runtime, the outcomes at which a
player has a failed reveal (`Vegas.FailedReadout`) pay it exactly its exclusion
payoff (`Vegas.exclusionReadoutUtility_of_failedReadout`). A source debt or
failed binding read through the native decoding reaches only such outcomes
under terminal play (`Vegas.decoded_owesFailure_failedReadout`), whatever
anyone plays afterwards.

So at every site of a native response menu, the exclusion value of a local
law is its successful part plus its failure probability times the exclusion
payoff (`Vegas.exclusionValue_eq_successValue_add`). When the successful part
is the success probability times a continuation value that does not depend on
the law, up to an error, laws are ranked by success probability alone as soon
as the continuation value is at least the exclusion payoff up to that error
(`Vegas.exclusionGain_le_of_failure_le`).

On the one-packet game, pooling the late-delivery sites whose parts share a
success probability yields the member-rationality obligation of a pooled limit
certificate under the exclusion payoff
(`Vegas.onePacket_memberRational_of_success`), from three facts at every member
site and index: the one-dimensional decomposition of each component's value,
a continuation value at least the player's least utility up to the error, and
a best part whose failure probability is least at every member up to a
vanishing slack. The exclusion payoff is assumed at most that least utility.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The typed readouts at which `who` has a failed reveal. -/
def FailedReadout (who : Player) : Set (Option (State L setup.program.terminalCtx)) :=
  {readout | ∃ terminal, readout = some terminal ∧
    1 ≤ failedReveals setup.program who (publicOutcome setup.program terminal)}

/-- A failed readout pays exactly the exclusion payoff. -/
theorem exclusionReadoutUtility_of_failedReadout {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) :
    ∀ readout ∈ FailedReadout setup who,
      exclusionReadoutUtility setup parameter utility excludedPayoff readout who =
        excludedPayoff who := by
  rintro _ ⟨terminal, rfl, failed⟩
  exact exclusionTerminalUtility_of_failed setup parameter utility excludedPayoff failed

/-- **Decoded failures reach only failed readouts.** Under the hypotheses of
`Vegas.decoded_owesFailure_failedReveals`, every terminal continuation of the
history reads out a failed reveal of `who`. -/
theorem decoded_owesFailure_failedReadout [Fintype Player]
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {profile : BehavioralProfile setup.program}
    (menu : (application setup leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (certificate : (menu.protocol (initialLaw setup) horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (owed : DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program)
      history.state) :
    ∀ final ∈ ((menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
        certificate players history).support,
      sourceReadout setup leaks final.state ∈ FailedReadout setup who := by
  intro final supported
  obtain ⟨terminal, read, failed⟩ := decoded_owesFailure_failedReveals menu horizon scheduler
    completes certificate players who history owed final supported
  exact ⟨terminal, read, failed⟩

section Menu

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  (menu : (application setup leaks).ResponseMenu) (initial : PMF (application setup leaks).State)
  (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
  [∀ who, DecidableEq ((menu.information initial horizon scheduler).InfoState who)]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ) (fuel : Nat)
  (assessment : (menu.information initial horizon scheduler).BehavioralAssessment)
  {who : Player} (site : (menu.information initial horizon scheduler).InformationSite who)

/-- **Failure pays the exclusion payoff.** The exclusion value of a local law
is its successful part plus its failure probability times the exclusion
payoff. -/
theorem exclusionValue_eq_successValue_add
    [Finite (menu.protocol initial horizon scheduler).History]
    (law : PMF ((menu.information initial horizon scheduler).Choice who site.1)) :
    localValue fuel (fun history => sourceReadout setup leaks history.state)
        (exclusionReadoutUtility setup parameter utility excludedPayoff) assessment site law =
      localSuccessValue fuel (fun history => sourceReadout setup leaks history.state)
          (exclusionReadoutUtility setup parameter utility excludedPayoff) assessment site
          (FailedReadout setup who) law +
        localFailure fuel (fun history => sourceReadout setup leaks history.state) assessment site
          (FailedReadout setup who) law * excludedPayoff who :=
  localValue_eq_successValue_add fuel _ _ assessment site (FailedReadout setup who)
    (excludedPayoff who)
    (exclusionReadoutUtility_of_failedReadout setup parameter utility excludedPayoff who) law

/-- **Delivery is one-dimensional.** At a site of a native response menu,
suppose the successful part of two local laws is their success probability
times a common continuation value up to `error`, the exclusion payoff is at
most the player's least utility `lower`, and the continuation value is at
least `lower` up to `error`, and exceeds the exclusion payoff by at most
`bound`. A law whose success probability exceeds that of `best` by at most
`slack` then gains at most that of `best` plus `slack * bound + 3 * error`
under the exclusion payoff. -/
theorem exclusionGain_le_of_failure_le [Finite (menu.protocol initial horizon scheduler).History]
    (lower : ℝ) (excluded_le_lower : excludedPayoff who ≤ lower)
    (continuation error slack bound : ℝ)
    (law best : PMF ((menu.information initial horizon scheduler).Choice who site.1))
    (lawNear : |localSuccessValue fuel (fun history => sourceReadout setup leaks history.state)
        (exclusionReadoutUtility setup parameter utility excludedPayoff) assessment site
        (FailedReadout setup who) law -
      (1 - localFailure fuel (fun history => sourceReadout setup leaks history.state) assessment
        site (FailedReadout setup who) law) * continuation| ≤ error)
    (bestNear : |localSuccessValue fuel (fun history => sourceReadout setup leaks history.state)
        (exclusionReadoutUtility setup parameter utility excludedPayoff) assessment site
        (FailedReadout setup who) best -
      (1 - localFailure fuel (fun history => sourceReadout setup leaks history.state) assessment
        site (FailedReadout setup who) best) * continuation| ≤ error)
    (ranked : localFailure fuel (fun history => sourceReadout setup leaks history.state)
        assessment site (FailedReadout setup who) best ≤
      localFailure fuel (fun history => sourceReadout setup leaks history.state) assessment site
        (FailedReadout setup who) law + slack)
    (slack_nonneg : 0 ≤ slack) (lower_le : lower - error ≤ continuation)
    (gap_le : continuation - excludedPayoff who ≤ bound) (bound_nonneg : 0 ≤ bound) :
    localGain fuel (fun history => sourceReadout setup leaks history.state)
        (exclusionReadoutUtility setup parameter utility excludedPayoff) assessment site law ≤
      localGain fuel (fun history => sourceReadout setup leaks history.state)
          (exclusionReadoutUtility setup parameter utility excludedPayoff) assessment site best +
        slack * bound + 3 * error :=
  localGain_le_of_failure_le fuel _ _ assessment site (FailedReadout setup who)
    (excludedPayoff who)
    (exclusionReadoutUtility_of_failedReadout setup parameter utility excludedPayoff who)
    continuation error slack bound law best lawNear bestNear ranked slack_nonneg
    (by linarith) gap_le bound_nonneg

end Menu

section OnePacket

variable [Fintype Player]
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (application setup leaks).State)
  (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
  [Fintype ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds initial horizon scheduler).InfoState who)]

open Classical in
/-- **Pooled late delivery is rational under the exclusion payoff.** On the
one-packet game observed through its typed readout, fix pools of agents with
common component weights, among them the delivery pools, and a best part of
each pool. Suppose that, for every weights family the pooled completion may
choose and every index, at every decision site of a delivery pool: the
successful part of each component is its success probability times a
continuation value of the site up to `error n`; that continuation value is at
least the player's least utility `lower` up to `error n` and exceeds its
exclusion payoff by at most `bound`; and the best part fails with probability
at most that of every other part up to `slack n`. If the exclusion payoff is at
most `lower`, `error` and `slack` vanish, and the members of the other pools
are rational up to a vanishing error, the member-rationality obligation of a
pooled limit certificate holds under the exclusion payoff. -/
theorem onePacket_memberRational_of_success (fuel : Nat)
    (bounded : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).BoundedHorizon fuel)
    (targetRecall : (onePacketModel setup leaks bounds initial horizon scheduler).DecisionRecall)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff lower : Player → ℝ) (excluded_le_lower : ∀ who, excludedPayoff who ≤ lower who)
    (fallback : ∀ who, (onePacketModel setup leaks bounds initial horizon scheduler).Policy who)
    {Pool : Type} [Finite Pool] [DecidableEq Pool]
    (pool : (onePacketModel setup leaks bounds initial horizon scheduler).InformationAgent
      (onePacketModel setup leaks bounds initial horizon scheduler).playedInformation → Pool)
    {Part : Pool → Type} [∀ p, Finite (Part p)]
    (component : ℕ → ∀ agent, Part (pool agent) →
      PMF (((onePacketModel setup leaks bounds initial horizon scheduler).agentForm fallback
        bounded.wellFoundedHistories).sig.Strategy agent))
    (delivery : Set Pool) (best : ∀ p, Part p) (bound : ℝ) (bound_nonneg : 0 ≤ bound)
    (oneDimensional : ∀ (weights : ℕ → ∀ p, PMF (Part p))
        (targetSequence : ℕ →
          (onePacketModel setup leaks bounds initial horizon scheduler).BehavioralAssessment),
      (∀ n, (targetSequence n).strategy =
        (onePacketModel setup leaks bounds initial horizon scheduler).agentBehavior
          (onePacketModel setup leaks bounds initial horizon scheduler).playedInformation fallback
          fun agent => (weights n (pool agent)).bind (component n agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent _ (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      ∃ (continuation : ℕ → (onePacketModel setup leaks bounds initial horizon
          scheduler).InformationAgent (onePacketModel setup leaks bounds initial horizon
          scheduler).playedInformation → ℝ) (error slack : ℕ → ℝ),
        Tendsto error atTop (nhds 0) ∧ Tendsto slack atTop (nhds 0) ∧ (∀ n, 0 ≤ slack n) ∧
        ∀ n agent, pool agent ∈ delivery →
          ∀ decision : (onePacketModel setup leaks bounds initial horizon
            scheduler).IsDecisionInfo agent.1 agent.2.1,
          lower agent.1 - error n ≤ continuation n agent ∧
          continuation n agent - excludedPayoff agent.1 ≤ bound ∧
          (∀ part, |localSuccessValue fuel (fun history => sourceReadout setup leaks history.state)
              (exclusionReadoutUtility setup parameter utility excludedPayoff) (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩ (FailedReadout setup agent.1)
              (component n agent part) -
            (1 - localFailure fuel (fun history => sourceReadout setup leaks history.state)
              (targetSequence n) (who := agent.1) ⟨agent.2.1, decision⟩
              (FailedReadout setup agent.1) (component n agent part)) * continuation n agent| ≤
            error n) ∧
          ∀ part, localFailure fuel (fun history => sourceReadout setup leaks history.state)
              (targetSequence n) (who := agent.1) ⟨agent.2.1, decision⟩
              (FailedReadout setup agent.1) (component n agent (best (pool agent))) ≤
            localFailure fuel (fun history => sourceReadout setup leaks history.state)
              (targetSequence n) (who := agent.1) ⟨agent.2.1, decision⟩
              (FailedReadout setup agent.1) (component n agent part) + slack n)
    (otherMembers : ∀ (weights : ℕ → ∀ p, PMF (Part p))
        (targetSequence : ℕ →
          (onePacketModel setup leaks bounds initial horizon scheduler).BehavioralAssessment),
      (∀ n, (targetSequence n).strategy =
        (onePacketModel setup leaks bounds initial horizon scheduler).agentBehavior
          (onePacketModel setup leaks bounds initial horizon scheduler).playedInformation fallback
          fun agent => (weights n (pool agent)).bind (component n agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent _ (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (Part p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
          (if decision : (onePacketModel setup leaks bounds initial horizon
              scheduler).IsDecisionInfo agent.1 agent.2.1 then
            localGain fuel (fun history => sourceReadout setup leaks history.state)
              (exclusionReadoutUtility setup parameter utility excludedPayoff) (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩
              ((alternative (pool agent)).bind (component n agent))
          else 0) ≤ 0) →
      ∃ otherError : ℕ → ℝ, Tendsto otherError atTop (nhds 0) ∧
        ∀ n who (site : (onePacketModel setup leaks bounds initial horizon
            scheduler).InformationSite who),
          pool ((onePacketModel setup leaks bounds initial horizon scheduler).agentAt site) ∉
            delivery →
          ∀ alternative : PMF (Part (pool ((onePacketModel setup leaks bounds initial horizon
            scheduler).agentAt site))),
          localGain fuel (fun history => sourceReadout setup leaks history.state)
              (exclusionReadoutUtility setup parameter utility excludedPayoff) (targetSequence n)
              site (alternative.bind (component n
                ((onePacketModel setup leaks bounds initial horizon scheduler).agentAt site))) ≤
            otherError n) :
    ∀ (weights : ℕ → ∀ p, PMF (Part p))
      (targetSequence : ℕ →
        (onePacketModel setup leaks bounds initial horizon scheduler).BehavioralAssessment),
      (∀ n, (targetSequence n).strategy =
        (onePacketModel setup leaks bounds initial horizon scheduler).agentBehavior
          (onePacketModel setup leaks bounds initial horizon scheduler).playedInformation fallback
          fun agent => (weights n (pool agent)).bind (component n agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent _ (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (Part p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
          (if decision : (onePacketModel setup leaks bounds initial horizon
              scheduler).IsDecisionInfo agent.1 agent.2.1 then
            let comparison := (onePacketModel setup leaks bounds initial horizon
              scheduler).assessmentComparisonWith
              ((onePacketModel setup leaks bounds initial horizon scheduler).truncatedRunner fuel)
              (fun history => sourceReadout setup leaks history.state) (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (pool agent)).bind (component n agent)))
            expect comparison.alternative
                (exclusionReadoutUtility setup parameter utility excludedPayoff · agent.1) -
              expect comparison.prescribed
                (exclusionReadoutUtility setup parameter utility excludedPayoff · agent.1)
          else 0) ≤ 0) →
      ∃ memberError : ℕ → ℝ, Tendsto memberError atTop (nhds 0) ∧
        ∀ n who (site : (onePacketModel setup leaks bounds initial horizon
            scheduler).InformationSite who)
          (alternative : PMF (Part (pool ((onePacketModel setup leaks bounds initial horizon
            scheduler).agentAt site)))),
          let comparison := (onePacketModel setup leaks bounds initial horizon
            scheduler).assessmentComparisonWith
            ((onePacketModel setup leaks bounds initial horizon scheduler).truncatedRunner fuel)
            (fun history => sourceReadout setup leaks history.state) (targetSequence n) who
            (site, ((targetSequence n).strategy who).withLaw site.1
              (alternative.bind (component n
                ((onePacketModel setup leaks bounds initial horizon scheduler).agentAt site))))
          expect comparison.alternative
              (exclusionReadoutUtility setup parameter utility excludedPayoff · who) -
            expect comparison.prescribed
              (exclusionReadoutUtility setup parameter utility excludedPayoff · who) ≤
            memberError n :=
  memberRational_of_success fuel bounded targetRecall _ _ fallback pool component delivery
    (FailedReadout setup) excludedPayoff
    (fun who => exclusionReadoutUtility_of_failedReadout setup parameter utility excludedPayoff who)
    best bound bound_nonneg
    (fun weights targetSequence played mixed bayes => by
      obtain ⟨continuation, error, slack, errorVanishes, slackVanishes, slack_nonneg, facts⟩ :=
        oneDimensional weights targetSequence played mixed bayes
      refine ⟨continuation, error, slack, errorVanishes, slackVanishes, slack_nonneg,
        fun n agent inDelivery decision => ?_⟩
      obtain ⟨lower_le, gap_le, near, ranked⟩ := facts n agent inDelivery decision
      exact ⟨by linarith [excluded_le_lower agent.1], gap_le, near, ranked⟩)
    otherMembers

end OnePacket

end Vegas
