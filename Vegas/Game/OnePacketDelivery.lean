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

**The late-delivery rule.** A late option waits or sends now at one of finitely
many prepared slots (`Vegas.LateOption`); sending is the as-if-honest value
committed at that slot at a binding, and the as-if-honest opening at a reveal,
which has no slot (`Vegas.lateResponse`). A scheduler may treat slots
differently for late packets, so the rule chooses both the time and the slot.
Given a success score of each option at each late-delivery key, the prescribed
option is one of greatest score (`Vegas.lateBest`), so the rule reads an
information state only through its late-delivery key (`Vegas.lateRule`,
`Vegas.lateRule_eq_of_lateKey_eq`), and never reads a committed value; its law
over one-packet choices is `Vegas.latePrescribed`, and each option has a fully
supported trembled component (`Vegas.lateComponent`). If, from every history
of a site's belief, each option's component fails with probability within a
drift of one minus its score at the site's key, the prescribed option fails
least up to twice the drift, with the same option at every site of that key
(`Vegas.lateBest_failure_le`).

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

section LateRule

variable (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- A late-delivery option among `slots` prepared slots: wait, or send now at
a slot. A reveal has no slot, and every slot sends its opening. -/
abbrev LateOption (slots : Nat) := Option (Fin slots)

/-- **A late response.** Waiting is silence. Sending at a slot is, at a binding
of the player's turn, the as-if-honest value committed at that prepared slot,
normalized as a canonical decision is; at any other event it is the
as-if-honest response; and silence when it is not the player's turn or the law
chooses no encodable action. -/
def lateResponse (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    LateOption slots → PMF (application setup leaks).Action
  | none => PMF.pure ⟨none⟩
  | some slot =>
      match view.application.publicView.ownTurn? who with
      | none => PMF.pure ⟨none⟩
      | some event =>
          match nodeView (graph setup) event with
          | .bind _owner payload outputEq _codeEq =>
              (asIfHonestProfile setup leaks assessment who (some (past, view))).map fun choice =>
                match choice.bind (encodeEventAction? setup.program event) with
                | none => ⟨none⟩
                | some action => ((runtime setup).reactiveNormalization leaks).action who past view
                    ((runtime setup).reactiveBinding leaks who event payload
                      (cast (congrArg EventGraph.EventField.Action outputEq) action) slot.val)
          | _ => honestResponse setup leaks assessment who past view

/-- **The prescribed late-delivery option.** Given a success score of each
option at each late-delivery key, an option of greatest score, chosen by a
fixed rule from the key and the score alone. -/
def lateBest {slots : Nat} (success : LateKey setup leaks → LateOption slots → ℝ)
    (key : LateKey setup leaks) : LateOption slots :=
  (Finset.univ.exists_max_image (success key) Finset.univ_nonempty).choose

theorem le_lateBest {slots : Nat} (success : LateKey setup leaks → LateOption slots → ℝ)
    (key : LateKey setup leaks) (option : LateOption slots) :
    success key option ≤ success key (lateBest setup leaks success key) :=
  (Finset.univ.exists_max_image (success key) Finset.univ_nonempty).choose_spec.2 option
    (Finset.mem_univ option)

/-- The option of the prescribed late-delivery rule at an information state:
the best option of its late-delivery key, and waiting at a non-decision input.
It reads the information state only through `Vegas.lateKey`. -/
def lateRule {slots : Nat} (success : LateKey setup leaks → LateOption slots → ℝ)
    (who : Player) (info : (application setup leaks).Info) : LateOption slots :=
  (lateKey setup leaks who info).elim none (lateBest setup leaks success)

/-- Information states with the same late-delivery key get the same option. -/
theorem lateRule_eq_of_lateKey_eq {slots : Nat}
    (success : LateKey setup leaks → LateOption slots → ℝ) (who : Player)
    {info info' : (application setup leaks).Info}
    (same : lateKey setup leaks who info = lateKey setup leaks who info') :
    lateRule setup leaks success who info = lateRule setup leaks success who info' := by
  unfold lateRule
  rw [same]

variable [Fintype Player] (bounds : MessageBounds (graph setup))
  (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- A late option as a law over one-packet choices. -/
def lateChoice (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (who : Player) :
    (info : (application setup leaks).Info) → LateOption slots →
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info)
  | none, _ => PMF.pure ⟨none, rfl⟩
  | some (past, view), option => (lateResponse setup leaks assessment who past view option).map
      (responseChoice setup leaks bounds initial horizon scheduler who (some (past, view)))

/-- **The late component of an option.** The late option trembled toward the
uniform law, with silence as its timing deviation. -/
def lateComponent (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info) (option : LateOption slots) :
    PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :=
  trembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one who info
    (lateChoice setup leaks bounds initial horizon scheduler assessment who info option)
    (PMF.pure (silenceChoice setup leaks bounds initial horizon scheduler who info))

theorem lateComponent_fullSupport (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info) (option : LateOption slots) :
    FullSupport (lateComponent setup leaks bounds initial horizon scheduler assessment scale
      positive.le le_one who info option) :=
  trembledChoice_fullSupport setup leaks bounds initial horizon scheduler positive le_one who info
    _ _

/-- **The prescribed late-delivery law.** The late choice of the prescribed
late-delivery option. -/
def latePrescribed (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (success : LateKey setup leaks → LateOption slots → ℝ) (who : Player)
    (info : (application setup leaks).Info) :
    PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :=
  lateChoice setup leaks bounds initial horizon scheduler assessment who info
    (lateRule setup leaks success who info)

variable [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds initial horizon scheduler).InfoState who)]

open Classical in
/-- **The prescribed late-delivery option is a common best response.** Let
`success` score each late option at each late-delivery key. At a site whose
late-delivery key is `key`, suppose that from every history of the site's
belief, each option's component fails with probability within `drift` of one
minus its score at `key`, as a value-blind scheduler and observation rule are
to provide. Then the component of the prescribed option fails with probability
at most that of every option up to `2 * drift`. The prescribed option depends
on the site only through its key, so this holds with the same option at every
site of a pool of sites sharing a key. -/
theorem lateBest_failure_le (fuel : Nat)
    (assessment : (onePacketModel setup leaks bounds initial horizon
      scheduler).BehavioralAssessment) {slots : Nat}
    (success : LateKey setup leaks → LateOption slots → ℝ) (drift : ℝ) {who : Player}
    (site : (onePacketModel setup leaks bounds initial horizon scheduler).InformationSite who)
    (key : LateKey setup leaks)
    (component : LateOption slots →
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who site.1))
    (common : ∀ option, ∀ history ∈ (assessment.belief who site).support,
      |expect (localHistoryLaw fuel (fun history => sourceReadout setup leaks history.state)
          assessment site (component option) history)
        (fun outcome => if outcome ∈ FailedReadout setup who then 1 else 0) -
        (1 - success key option)| ≤ drift) (option : LateOption slots) :
    localFailure fuel (fun history => sourceReadout setup leaks history.state) assessment site
        (FailedReadout setup who) (component (lateBest setup leaks success key)) ≤
      localFailure fuel (fun history => sourceReadout setup leaks history.state) assessment site
        (FailedReadout setup who) (component option) + 2 * drift := by
  have near (option : LateOption slots) :=
    localFailure_near_of_histories fuel _ assessment site (FailedReadout setup who)
      (component option) (1 - success key option) drift (common option)
  have best := (abs_le.mp (near (lateBest setup leaks success key))).2
  have other := (abs_le.mp (near option)).1
  linarith [le_lateBest setup leaks success key option]

end LateRule

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
    (delivery : Set Pool) (bound : ℝ) (bound_nonneg : 0 ≤ bound)
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
          scheduler).playedInformation → ℝ) (best : ℕ → ∀ p, Part p) (error slack : ℕ → ℝ),
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
              (FailedReadout setup agent.1) (component n agent (best n (pool agent))) ≤
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
    bound bound_nonneg
    (fun weights targetSequence played mixed bayes => by
      obtain ⟨continuation, best, error, slack, errorVanishes, slackVanishes, slack_nonneg,
        facts⟩ := oneDimensional weights targetSequence played mixed bayes
      refine ⟨continuation, best, error, slack, errorVanishes, slackVanishes, slack_nonneg,
        fun n agent inDelivery decision => ?_⟩
      obtain ⟨lower_le, gap_le, near, ranked⟩ := facts n agent inDelivery decision
      exact ⟨by linarith [excluded_le_lower agent.1], gap_le, near, ranked⟩)
    otherMembers

end OnePacket

end Vegas
