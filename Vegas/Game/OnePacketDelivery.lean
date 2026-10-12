/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketExclusionPayoff
import Vegas.Game.OnePacketSlotTrembles
import GameTheoryExtensions.Analysis.Protocol.KeyedPools

/-! # Delivery is one-dimensional under the exclusion payoff

Read through the typed readout of the default runtime, the outcomes at which a
player has a failed reveal (`Vegas.FailedReadout`) pay it exactly its exclusion
payoff (`Vegas.exclusionReadoutUtility_of_failedReadout`,
`Vegas.exclusionReadoutUtility_of_failedReadout_history`). A source debt or
failed binding read through the native decoding reaches only such outcomes
under terminal play (`Vegas.decoded_owesFailure_failedReadout`), whatever
anyone plays afterwards.

**One dimension.** Fix any set of failed histories paying the player exactly
its exclusion payoff, such as the failed completion of its event. At every
site of a native response menu, the exclusion value of a local law is its
successful part plus its failure probability times the exclusion payoff
(`Vegas.exclusionValue_eq_successValue_add`). When the successful part is the
success probability times a continuation value that does not depend on the
law, up to an error, laws are ranked by success probability alone as soon as
the continuation value is at least the exclusion payoff up to that error
(`Vegas.exclusionGain_le_of_failure_le`).

**The late-delivery rule.** A late option waits or sends now at one of the
first prepared slots (`Vegas.LateOption`); sending takes the slot tier's
response at that slot with the as-if-honest source choice: the value committed
at that slot at a binding, the canonical decision at a reveal, which has no
slot (`Vegas.lateResponse`). A scheduler may treat slots differently for late
packets, so the rule chooses both the time and the slot. Given a success score
of each option at each late-delivery key, the prescribed option is one of
greatest score (`Vegas.lateBest`), so the rule reads an information state only
through its late-delivery key (`Vegas.lateRule`,
`Vegas.lateRule_eq_of_lateKey_eq`) and never reads a committed value; its law
over one-packet choices is `Vegas.latePrescribed`. Each option has a fully
supported slot-trembled component (`Vegas.lateComponent`,
`Vegas.lateComponent_fullSupport`) keeping all but three times the scale of the
option's mass (`Vegas.lateComponent_ge`). If at a site each option's component
fails, belief-averaged, with probability within a drift of one minus its score
at the site's key, the prescribed option fails least up to twice the drift,
with the same option at every site of that key (`Vegas.lateBest_failure_le`),
also against any law whose failure probability is near one minus the score of
some option, such as a single late choice (`Vegas.lateBest_failure_le_of_near`).

**Pools.** The late-delivery agents sharing a late-delivery key form one pool
whose parts are the late options, and every other agent sits in one pool with
its slot-trembled prescribed component (`Vegas.latePool`,
`Vegas.lateKeyedComponent`, `Vegas.lateKeyedComponent_fullSupport`). The
member-rationality and local-comparison obligations of a pooled limit
certificate for these pools are
`GameTheory.Protocol.InformationModel.keyedMemberRational` and
`GameTheory.Protocol.InformationModel.keyedLocalComparisons`; at a first
activation the prescribed component's ranking follows from a mass bound
against a reliable main law
(`GameTheory.Protocol.InformationModel.localFailure_le_add_of_mass`).
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

/-- The histories of a response menu whose typed readout records a failed
reveal of the player pay it exactly its exclusion payoff. -/
theorem exclusionReadoutUtility_of_failedReadout_history
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (menu : (application setup leaks).ResponseMenu) (initial : PMF (application setup leaks).State)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) :
    ∀ history ∈ {history : (menu.protocol initial horizon scheduler).History |
        sourceReadout setup leaks history.state ∈ FailedReadout setup who},
      exclusionReadoutUtility setup parameter utility excludedPayoff
        (sourceReadout setup leaks history.state) who = excludedPayoff who :=
  fun _ member =>
    exclusionReadoutUtility_of_failedReadout setup parameter utility excludedPayoff who _ member

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

/-- **Failure pays the exclusion payoff.** For a set of failed histories on
which the player receives exactly its exclusion payoff, such as the
completion of its event by a failure, the exclusion value of a local law is
its successful part plus its failure probability times the exclusion
payoff. -/
theorem exclusionValue_eq_successValue_add
    [Finite (menu.protocol initial horizon scheduler).History]
    (failed : Set (menu.protocol initial horizon scheduler).History)
    (pays : ∀ history ∈ failed, exclusionReadoutUtility setup parameter utility excludedPayoff
      (sourceReadout setup leaks history.state) who = excludedPayoff who)
    (law : PMF ((menu.information initial horizon scheduler).Choice who site.1)) :
    localValue fuel (fun history => sourceReadout setup leaks history.state)
        (exclusionReadoutUtility setup parameter utility excludedPayoff) assessment site law =
      localSuccessValue fuel (fun history => sourceReadout setup leaks history.state)
          (exclusionReadoutUtility setup parameter utility excludedPayoff) assessment site
          failed law +
        localFailure fuel assessment site failed law * excludedPayoff who :=
  localValue_eq_successValue_add fuel _ _ assessment site failed (excludedPayoff who) pays law

/-- **Delivery is one-dimensional.** At a site of a native response menu, fix
a set of failed histories paying exactly the exclusion payoff. Suppose the
successful part of two local laws is their success probability times a common
continuation value up to an error, the exclusion payoff is at most the
player's least utility, and the continuation value is at least that least
utility up to the error and exceeds the exclusion payoff by at most a bound. A
law whose success probability exceeds that of the other by at most a slack
then gains at most what the other gains, plus the slack times the bound and
three times the error, under the exclusion payoff. -/
theorem exclusionGain_le_of_failure_le [Finite (menu.protocol initial horizon scheduler).History]
    (failed : Set (menu.protocol initial horizon scheduler).History)
    (pays : ∀ history ∈ failed, exclusionReadoutUtility setup parameter utility excludedPayoff
      (sourceReadout setup leaks history.state) who = excludedPayoff who)
    (lower : ℝ) (excluded_le_lower : excludedPayoff who ≤ lower)
    (continuation error slack bound : ℝ)
    (law best : PMF ((menu.information initial horizon scheduler).Choice who site.1))
    (lawNear : |localSuccessValue fuel (fun history => sourceReadout setup leaks history.state)
        (exclusionReadoutUtility setup parameter utility excludedPayoff) assessment site
        failed law -
      (1 - localFailure fuel assessment site failed law) * continuation| ≤ error)
    (bestNear : |localSuccessValue fuel (fun history => sourceReadout setup leaks history.state)
        (exclusionReadoutUtility setup parameter utility excludedPayoff) assessment site
        failed best -
      (1 - localFailure fuel assessment site failed best) * continuation| ≤ error)
    (ranked : localFailure fuel assessment site failed best ≤
      localFailure fuel assessment site failed law + slack)
    (slack_nonneg : 0 ≤ slack) (lower_le : lower - error ≤ continuation)
    (gap_le : continuation - excludedPayoff who ≤ bound) (bound_nonneg : 0 ≤ bound) :
    localGain fuel (fun history => sourceReadout setup leaks history.state)
        (exclusionReadoutUtility setup parameter utility excludedPayoff) assessment site law ≤
      localGain fuel (fun history => sourceReadout setup leaks history.state)
          (exclusionReadoutUtility setup parameter utility excludedPayoff) assessment site best +
        slack * bound + 3 * error :=
  localGain_le_of_failure_le fuel _ _ assessment site failed (excludedPayoff who) pays
    continuation error slack bound law best lawNear bestNear ranked slack_nonneg
    (by linarith) gap_le bound_nonneg

end Menu

section LateRule

variable (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- A late-delivery option among the first `slots` prepared slots: wait, or
send now at a slot. A reveal has no slot, and every slot sends its opening. -/
abbrev LateOption (slots : Nat) := Option (Fin slots)

/-- **A late response.** Waiting is silence. Sending at a slot draws the
as-if-honest source choice and, at the player's turn, takes the slot tier's
response at that slot (`Vegas.slotResponse`): at a binding the encoded value
committed at the slot, normalized as a canonical decision is, and at any other
event the canonical decision. It is silence away from the player's turn. -/
def lateResponse (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    LateOption slots → PMF (application setup leaks).Action
  | none => PMF.pure ⟨none⟩
  | some slot =>
      match view.application.publicView.ownTurn? who with
      | none => PMF.pure ⟨none⟩
      | some event => (asIfHonestProfile setup leaks assessment who (some (past, view))).map
          (slotResponse setup leaks who past view event slot.val)

/-- **The prescribed late-delivery option.** Given a success score of each
option at each late-delivery key, an option of greatest score, chosen by a
fixed rule from the key and the score alone. -/
def lateBest {slots : Nat} (success : LateKey setup leaks → LateOption slots → ℝ)
    (key : LateKey setup leaks) : LateOption slots :=
  scoreArgmax (success key)

theorem le_lateBest {slots : Nat} (success : LateKey setup leaks → LateOption slots → ℝ)
    (key : LateKey setup leaks) (option : LateOption slots) :
    success key option ≤ success key (lateBest setup leaks success key) :=
  le_scoreArgmax (success key) option

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

/-- **The late component of an option.** The late option slot-trembled, with
silence as its timing deviation and the value-preserving slot tier. -/
def lateComponent (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info) (option : LateOption slots) :
    PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :=
  slotTrembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one who info
    (lateChoice setup leaks bounds initial horizon scheduler assessment who info option)
    (PMF.pure (silenceChoice setup leaks bounds initial horizon scheduler who info))
    (slotChoice setup leaks bounds initial horizon scheduler assessment who info)

theorem lateComponent_fullSupport (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info) (option : LateOption slots) :
    FullSupport (lateComponent setup leaks bounds initial horizon scheduler assessment scale
      positive.le le_one who info option) :=
  slotTrembledChoice_fullSupport setup leaks bounds initial horizon scheduler positive le_one who
    info _ _ _

/-- The late component of an option keeps at least `1 - 3 scale` of the mass
of the option's late choice. -/
theorem lateComponent_ge (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info) (option : LateOption slots)
    (choice : (onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :
    (1 - 3 * scale) *
        (lateChoice setup leaks bounds initial horizon scheduler assessment who info option
          choice).toReal ≤
      (lateComponent setup leaks bounds initial horizon scheduler assessment scale nonnegative
        le_one who info option choice).toReal := by
  have main := slotTrembledChoice_ge_main setup leaks bounds initial horizon scheduler
    nonnegative le_one who info
    (lateChoice setup leaks bounds initial horizon scheduler assessment who info option)
    (PMF.pure (silenceChoice setup leaks bounds initial horizon scheduler who info))
    (slotChoice setup leaks bounds initial horizon scheduler assessment who info) choice
  have factor := slotFactor_ge nonnegative le_one
  have mass : 0 ≤ (lateChoice setup leaks bounds initial horizon scheduler assessment who info
      option choice).toReal := ENNReal.toReal_nonneg
  exact (mul_le_mul_of_nonneg_right factor mass).trans main

/-- **The prescribed late-delivery law.** The late choice of the prescribed
late-delivery option. -/
def latePrescribed (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (success : LateKey setup leaks → LateOption slots → ℝ) (who : Player)
    (info : (application setup leaks).Info) :
    PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :=
  lateChoice setup leaks bounds initial horizon scheduler assessment who info
    (lateRule setup leaks success who info)

variable
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds initial horizon scheduler).InfoState who)]

/-- **The prescribed late-delivery option is a common best response.** Let a
success score rate each late option at each late-delivery key. At a site whose
late-delivery key is the given key, suppose each option's component fails,
belief-averaged over the site, with probability within a drift of one minus
its score at the key, as value-blindness of the scheduler and observation rule
is to provide. Then the component of the prescribed option fails with
probability at most that of every option up to twice the drift. The prescribed
option depends on the site only through its key, so the same option is best at
every site sharing the key. -/
theorem lateBest_failure_le (fuel : Nat)
    (assessment : (onePacketModel setup leaks bounds initial horizon
      scheduler).BehavioralAssessment) {slots : Nat}
    (success : LateKey setup leaks → LateOption slots → ℝ) (drift : ℝ) {who : Player}
    (site : (onePacketModel setup leaks bounds initial horizon scheduler).InformationSite who)
    (failed : Set ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).History)
    (key : LateKey setup leaks)
    (component : LateOption slots →
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who site.1))
    (common : ∀ option, |localFailure fuel assessment site failed (component option) -
      (1 - success key option)| ≤ drift) (option : LateOption slots) :
    localFailure fuel assessment site failed (component (lateBest setup leaks success key)) ≤
      localFailure fuel assessment site failed (component option) + 2 * drift :=
  localFailure_scoreArgmax_le fuel assessment site failed (success key) drift component common
    (component option) option (common option)

/-- **A late choice ranks below the prescribed option.** With the components
as in `Vegas.lateBest_failure_le`, any law at the site that fails, belief-averaged,
with probability within the drift of one minus the score of some option, such
as a single late choice, fails at least as often as the prescribed option's
component up to twice the drift. -/
theorem lateBest_failure_le_of_near (fuel : Nat)
    (assessment : (onePacketModel setup leaks bounds initial horizon
      scheduler).BehavioralAssessment) {slots : Nat}
    (success : LateKey setup leaks → LateOption slots → ℝ) (drift : ℝ) {who : Player}
    (site : (onePacketModel setup leaks bounds initial horizon scheduler).InformationSite who)
    (failed : Set ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).History)
    (key : LateKey setup leaks)
    (component : LateOption slots →
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who site.1))
    (common : ∀ option, |localFailure fuel assessment site failed (component option) -
      (1 - success key option)| ≤ drift)
    (law : PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who site.1))
    (option : LateOption slots)
    (lawNear : |localFailure fuel assessment site failed law - (1 - success key option)| ≤
      drift) :
    localFailure fuel assessment site failed (component (lateBest setup leaks success key)) ≤
      localFailure fuel assessment site failed law + 2 * drift :=
  localFailure_scoreArgmax_le fuel assessment site failed (success key) drift component common
    law option lawNear

end LateRule

section Pools

variable [Fintype Player]
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (application setup leaks).State)
  (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
  [Fintype ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds initial horizon scheduler).InfoState who)]

/-- The late-delivery key of a played agent of the one-packet game. -/
def agentLateKey (agent : (onePacketModel setup leaks bounds initial horizon
    scheduler).InformationAgent (onePacketModel setup leaks bounds initial horizon
    scheduler).playedInformation) : Option (LateKey setup leaks) :=
  lateKey setup leaks agent.1 agent.2.1

/-- **The late pools of the one-packet game.** The late-delivery agents
sharing a late-delivery key form one pool, whose parts are the late options;
every other agent sits in the unkeyed pool with one part. -/
abbrev latePool (late : (onePacketModel setup leaks bounds initial horizon
    scheduler).InformationAgent (onePacketModel setup leaks bounds initial horizon
    scheduler).playedInformation → Prop) :=
  keyedPool late (agentLateKey setup leaks bounds initial horizon scheduler)

/-- **The late components of the one-packet game.** A late-delivery agent's
component of an option is the late component of that option; every other
agent's single component is its slot-trembled prescribed component. -/
def lateKeyedComponent (late : (onePacketModel setup leaks bounds initial horizon
    scheduler).InformationAgent (onePacketModel setup leaks bounds initial horizon
    scheduler).playedInformation → Prop)
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat} (scale : ℝ)
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (onePacketModel setup leaks bounds initial horizon scheduler).InformationAgent
      (onePacketModel setup leaks bounds initial horizon scheduler).playedInformation) :
    KeyedPart late (agentLateKey setup leaks bounds initial horizon scheduler) (LateOption slots)
        (latePool setup leaks bounds initial horizon scheduler late agent) →
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice agent.1
        agent.2.1) :=
  keyedComponent
    (fun agent => slotPrescribedComponent setup leaks bounds initial horizon scheduler assessment
      scale nonnegative le_one agent.1 agent.2.1)
    (fun agent option => lateComponent setup leaks bounds initial horizon scheduler assessment
      scale nonnegative le_one agent.1 agent.2.1 option) agent

theorem lateKeyedComponent_fullSupport (late : (onePacketModel setup leaks bounds initial
    horizon scheduler).InformationAgent (onePacketModel setup leaks bounds initial horizon
    scheduler).playedInformation → Prop)
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat} {scale : ℝ}
    (positive : 0 < scale) (le_one : scale ≤ 1)
    (agent : (onePacketModel setup leaks bounds initial horizon scheduler).InformationAgent
      (onePacketModel setup leaks bounds initial horizon scheduler).playedInformation)
    (part : KeyedPart late (agentLateKey setup leaks bounds initial horizon scheduler)
      (LateOption slots) (latePool setup leaks bounds initial horizon scheduler late agent)) :
    FullSupport (lateKeyedComponent setup leaks bounds initial horizon scheduler late assessment
      scale positive.le le_one agent part) :=
  keyedComponent_fullSupport _ _
    (fun agent => slotTrembledChoice_fullSupport setup leaks bounds initial horizon scheduler
      positive le_one agent.1 agent.2.1 _ _ _)
    (fun agent option => lateComponent_fullSupport setup leaks bounds initial horizon scheduler
      assessment positive le_one agent.1 agent.2.1 option) agent part

end Pools

end Vegas
