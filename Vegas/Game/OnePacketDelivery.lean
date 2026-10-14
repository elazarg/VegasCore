/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketExclusionPayoff
import Vegas.Game.OnePacketSlotTrembles
import Vegas.Game.OnePacketPrescribedSupport
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
(`GameTheory.Protocol.InformationModel.localFailure_le_add_of_mass`). With the
late-delivery agents (`Vegas.LateDeliveryAgent`) keyed by their late-delivery
key and the typed readout under the exclusion payoff, both obligations are
stated for the one-packet game (`Vegas.onePacket_keyedMemberRational`,
`Vegas.onePacket_keyedLocalComparisons`). A marked choice that fails surely
ranks last whatever the options are
(`GameTheory.Protocol.InformationModel.localFailure_le_of_sure_failure`): every
choice of an owner whose event is doomed, and every packet that spends the
event's one packet without the contract accepting it, such as a commitment at
a handle other than a fresh prepared slot of the owner.
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

section Obligations

variable [Fintype Player]
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (application setup leaks).State)
  (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
  [Fintype ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds initial horizon scheduler).InfoState who)]

local notation "onePacketN" => onePacketModel setup leaks bounds initial horizon scheduler

/-- The late-delivery agents of the one-packet game: the agents at late
deliveries (`Vegas.LateDelivery`). -/
def LateDeliveryAgent (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) :
    Prop :=
  LateDelivery setup leaks agent.1 agent.2.1

/-- The typed readout of a native history. -/
abbrev nativeReadout (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial
    horizon scheduler).History) : Option (State L setup.program.terminalCtx) :=
  sourceReadout setup leaks history.state

include bounds initial horizon scheduler in
open Classical in
/-- **Member rationality of the late pools under the exclusion payoff.** On
the one-packet game observed through its typed readout, pool the late-delivery
agents by their late-delivery key with the late options as parts, and every
other agent in one pool. Suppose, for every weights family the pooled
completion may choose, at every late-delivery decision site: the continuation
value is at least the player's least utility up to `error n` and exceeds its
exclusion payoff by at most `bound`; the successful part of each option's late
law is its success probability times that continuation value up to `error n`;
and each option's late law fails on the given failed histories, belief-averaged
over the site, with probability within `drift n` of one minus its score at the
site's late-delivery key. If the failed histories pay exactly the exclusion
payoff, the exclusion payoff is at most the least utility, and `error` and
`drift` vanish, the member-rationality obligation holds. -/
theorem onePacket_keyedMemberRational (fuel : Nat)
    (bounded : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).BoundedHorizon fuel)
    (targetRecall : (onePacketN).DecisionRecall)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff lower : Player → ℝ) (excluded_le_lower : ∀ who, excludedPayoff who ≤ lower who)
    (fallback : ∀ who, (onePacketN).Policy who) {slots : Nat}
    (prescribed : ℕ → ∀ agent : (onePacketN).InformationAgent (onePacketN).playedInformation,
      PMF ((onePacketN).Choice agent.1 agent.2.1))
    (lateLaw : ℕ → ∀ agent : (onePacketN).InformationAgent (onePacketN).playedInformation,
      LateOption slots → PMF ((onePacketN).Choice agent.1 agent.2.1))
    (failed : (onePacketN).InformationAgent (onePacketN).playedInformation →
      Set ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
        scheduler).History)
    (pays : ∀ agent, ∀ history ∈ failed agent, exclusionReadoutUtility setup parameter utility
      excludedPayoff (nativeReadout setup leaks bounds initial horizon scheduler history)
        agent.1 = excludedPayoff agent.1)
    (bound : ℝ) (bound_nonneg : 0 ≤ bound)
    (oneDimensional : ∀ (weights : ℕ → ∀ p, PMF (KeyedPart
          (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
          (agentLateKey setup leaks bounds initial horizon scheduler) (LateOption slots) p))
        (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior
        (onePacketN).playedInformation fallback
        fun agent => (weights n (keyedPool (LateDeliveryAgent setup leaks bounds initial horizon
          scheduler) (agentLateKey setup leaks bounds initial horizon scheduler) agent)).bind
          (keyedComponent (prescribed n) (lateLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent _ (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
        (score : ℕ → Option (LateKey setup leaks) → LateOption slots → ℝ) (error drift : ℕ → ℝ),
        Tendsto error atTop (nhds 0) ∧ Tendsto drift atTop (nhds 0) ∧ (∀ n, 0 ≤ drift n) ∧
        ∀ n agent, LateDeliveryAgent setup leaks bounds initial horizon scheduler agent →
          ∀ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
          lower agent.1 - error n ≤ continuation n agent ∧
          continuation n agent - excludedPayoff agent.1 ≤ bound ∧
          (∀ option, |localSuccessValue fuel
              (nativeReadout setup leaks bounds initial horizon scheduler)
              (exclusionReadoutUtility setup parameter utility excludedPayoff) (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩ (failed agent) (lateLaw n agent option) -
            (1 - localFailure fuel (targetSequence n) (who := agent.1) ⟨agent.2.1, decision⟩
              (failed agent) (lateLaw n agent option)) * continuation n agent| ≤ error n) ∧
          ∀ option, |localFailure fuel (targetSequence n) (who := agent.1) ⟨agent.2.1, decision⟩
              (failed agent) (lateLaw n agent option) -
            (1 - score n (agentLateKey setup leaks bounds initial horizon scheduler agent)
              option)| ≤ drift n) :
    ∀ (weights : ℕ → ∀ p, PMF (KeyedPart
        (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
        (agentLateKey setup leaks bounds initial horizon scheduler) (LateOption slots) p))
      (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior
        (onePacketN).playedInformation fallback
        fun agent => (weights n (keyedPool (LateDeliveryAgent setup leaks bounds initial horizon
          scheduler) (agentLateKey setup leaks bounds initial horizon scheduler) agent)).bind
          (keyedComponent (prescribed n) (lateLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent _ (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (KeyedPart
          (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
          (agentLateKey setup leaks bounds initial horizon scheduler) (LateOption slots) p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => keyedPool
            (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
            (agentLateKey setup leaks bounds initial horizon scheduler) agent = p),
          (if decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1 then
            have comparison := (onePacketN).assessmentComparisonWith
              ((onePacketN).truncatedRunner fuel)
              (nativeReadout setup leaks bounds initial horizon scheduler) (targetSequence n)
              agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (keyedPool (LateDeliveryAgent setup leaks bounds initial horizon
                  scheduler) (agentLateKey setup leaks bounds initial horizon scheduler)
                  agent)).bind (keyedComponent (prescribed n) (lateLaw n) agent)))
            expect comparison.alternative
                (exclusionReadoutUtility setup parameter utility excludedPayoff · agent.1) -
              expect comparison.prescribed
                (exclusionReadoutUtility setup parameter utility excludedPayoff · agent.1)
          else 0) ≤ 0) →
      ∃ memberError : ℕ → ℝ, Tendsto memberError atTop (nhds 0) ∧
        ∀ n who (site : (onePacketN).InformationSite who)
          (alternative : PMF (KeyedPart
            (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
            (agentLateKey setup leaks bounds initial horizon scheduler) (LateOption slots)
            (keyedPool (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
              (agentLateKey setup leaks bounds initial horizon scheduler)
              ((onePacketN).agentAt site)))),
          have comparison := (onePacketN).assessmentComparisonWith
            ((onePacketN).truncatedRunner fuel)
            (nativeReadout setup leaks bounds initial horizon scheduler) (targetSequence n) who
            (site, ((targetSequence n).strategy who).withLaw site.1
              (alternative.bind (keyedComponent (prescribed n) (lateLaw n)
                ((onePacketN).agentAt site))))
          expect comparison.alternative
              (exclusionReadoutUtility setup parameter utility excludedPayoff · who) -
            expect comparison.prescribed
              (exclusionReadoutUtility setup parameter utility excludedPayoff · who) ≤
            memberError n := by
  convert keyedMemberRational fuel bounded targetRecall _ _ fallback _ _ prescribed lateLaw failed
    excludedPayoff pays bound bound_nonneg
    (fun weights targetSequence played mixed bayes => by
      obtain ⟨continuation, score, error, drift, errorVanishes, driftVanishes, drift_nonneg,
        facts⟩ := oneDimensional weights targetSequence played mixed bayes
      refine ⟨continuation, score, error, drift, errorVanishes, driftVanishes, drift_nonneg,
        fun n agent late decision => ?_⟩
      obtain ⟨lower_le, gap_le, near, common⟩ := facts n agent late decision
      exact ⟨by linarith [excluded_le_lower agent.1], gap_le, near, common⟩)


include bounds initial horizon scheduler in
open Classical in
/-- **Local comparisons of the late pools under the exclusion payoff.** With the
pools of `Vegas.onePacket_keyedMemberRational`, mark the single choices to
compare with the best part of their pool. Suppose, for every weights family
the pooled completion may choose, at every marked choice of a compared site:
the continuation value is at least the player's least utility up to `error n`
and exceeds its exclusion payoff by at most `bound`; the successful part of the
choice is its success probability times that continuation value up to
`error n`; at a late delivery, the same holds for every option's late law,
each option's late law fails on the given failed histories, belief-averaged,
with probability within `drift n` of one minus its score at the site's
late-delivery key, and so does the choice for some option unless it fails
surely; at any other site, the same holds for the prescribed law, which fails
at most as often as the choice up to `slack n` unless the choice fails surely.
If the failed histories pay exactly the exclusion payoff, the exclusion payoff
is at most the least utility, `error`, `drift` and `slack` vanish, and the
unmarked choices meet the comparisons on their own, the local-comparison
obligation holds. -/
theorem onePacket_keyedLocalComparisons {E : ExecutionProtocol Player}
    {M : InformationModel E} (sourceObserve : E.History → Option (State L
      setup.program.terminalCtx)) (sourceFuel : Nat)
    (sourceSequence : ℕ → M.BehavioralAssessment) (fuel : Nat)
    (bounded : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).BoundedHorizon fuel)
    (targetRecall : (onePacketN).DecisionRecall)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff lower : Player → ℝ) (excluded_le_lower : ∀ who, excludedPayoff who ≤ lower who)
    (fallback : ∀ who, (onePacketN).Policy who) {slots : Nat}
    (prescribed : ℕ → ∀ agent : (onePacketN).InformationAgent (onePacketN).playedInformation,
      PMF ((onePacketN).Choice agent.1 agent.2.1))
    (lateLaw : ℕ → ∀ agent : (onePacketN).InformationAgent (onePacketN).playedInformation,
      LateOption slots → PMF ((onePacketN).Choice agent.1 agent.2.1))
    (free : Finset ((onePacketN).InformationAgent (onePacketN).playedInformation))
    (compared : ∀ who (site : (onePacketN).InformationSite who),
      (onePacketN).Choice who site.1 → Prop)
    (failed : (onePacketN).InformationAgent (onePacketN).playedInformation →
      Set ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
        scheduler).History)
    (pays : ∀ agent, ∀ history ∈ failed agent, exclusionReadoutUtility setup parameter utility
      excludedPayoff (nativeReadout setup leaks bounds initial horizon scheduler history)
        agent.1 = excludedPayoff agent.1)
    (bound : ℝ) (bound_nonneg : 0 ≤ bound)
    (ranking : ∀ (weights : ℕ → ∀ p, PMF (KeyedPart
          (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
          (agentLateKey setup leaks bounds initial horizon scheduler) (LateOption slots) p))
        (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior
        (onePacketN).playedInformation fallback
        fun agent => (weights n (keyedPool (LateDeliveryAgent setup leaks bounds initial horizon
          scheduler) (agentLateKey setup leaks bounds initial horizon scheduler) agent)).bind
          (keyedComponent (prescribed n) (lateLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent _ (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
        (score : ℕ → Option (LateKey setup leaks) → LateOption slots → ℝ)
        (error drift slack : ℕ → ℝ),
        Tendsto error atTop (nhds 0) ∧ Tendsto drift atTop (nhds 0) ∧
        Tendsto slack atTop (nhds 0) ∧ (∀ n, 0 ≤ drift n) ∧ (∀ n, 0 ≤ slack n) ∧
        ∀ n who (site : (onePacketN).InformationSite who) (choice : (onePacketN).Choice who site.1),
          (onePacketN).agentAt site ∉ free → compared who site choice →
          lower who - error n ≤ continuation n ((onePacketN).agentAt site) ∧
          continuation n ((onePacketN).agentAt site) - excludedPayoff who ≤ bound ∧
          |localSuccessValue fuel (nativeReadout setup leaks bounds initial horizon scheduler)
              (exclusionReadoutUtility setup parameter utility excludedPayoff) (targetSequence n)
              site (failed ((onePacketN).agentAt site)) (PMF.pure choice) -
            (1 - localFailure fuel (targetSequence n) site
              (failed ((onePacketN).agentAt site)) (PMF.pure choice)) *
              continuation n ((onePacketN).agentAt site)| ≤ error n ∧
          (LateDeliveryAgent setup leaks bounds initial horizon scheduler
              ((onePacketN).agentAt site) →
            (∀ option, |localSuccessValue fuel
                (nativeReadout setup leaks bounds initial horizon scheduler)
                (exclusionReadoutUtility setup parameter utility excludedPayoff)
                (targetSequence n) site (failed ((onePacketN).agentAt site))
                (lateLaw n ((onePacketN).agentAt site) option) -
              (1 - localFailure fuel (targetSequence n) site (failed ((onePacketN).agentAt site))
                (lateLaw n ((onePacketN).agentAt site) option)) *
                continuation n ((onePacketN).agentAt site)| ≤ error n) ∧
            (∀ option, |localFailure fuel (targetSequence n) site
              (failed ((onePacketN).agentAt site))
                (lateLaw n ((onePacketN).agentAt site) option) -
              (1 - score n (agentLateKey setup leaks bounds initial horizon scheduler
                ((onePacketN).agentAt site)) option)| ≤ drift n) ∧
            ((∃ option, |localFailure fuel (targetSequence n) site
              (failed ((onePacketN).agentAt site))
                (PMF.pure choice) - (1 - score n (agentLateKey setup leaks bounds initial horizon
                  scheduler ((onePacketN).agentAt site)) option)| ≤ drift n) ∨
              localFailure fuel (targetSequence n) site
                (failed ((onePacketN).agentAt site)) (PMF.pure choice) = 1)) ∧
          (¬ LateDeliveryAgent setup leaks bounds initial horizon scheduler
              ((onePacketN).agentAt site) →
            |localSuccessValue fuel (nativeReadout setup leaks bounds initial horizon scheduler)
                (exclusionReadoutUtility setup parameter utility excludedPayoff)
                (targetSequence n) site
                  (failed ((onePacketN).agentAt site)) (prescribed n ((onePacketN).agentAt site)) -
              (1 - localFailure fuel (targetSequence n) site (failed ((onePacketN).agentAt site))
                (prescribed n ((onePacketN).agentAt site))) *
                continuation n ((onePacketN).agentAt site)| ≤ error n ∧
            (localFailure fuel (targetSequence n) site (failed ((onePacketN).agentAt site))
                (prescribed n ((onePacketN).agentAt site)) ≤
              localFailure fuel (targetSequence n) site
                (failed ((onePacketN).agentAt site)) (PMF.pure choice) + slack n ∨
              localFailure fuel (targetSequence n) site
                (failed ((onePacketN).agentAt site)) (PMF.pure choice) = 1)))
    (otherComparisons : ∀ (weights : ℕ → ∀ p, PMF (KeyedPart
          (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
          (agentLateKey setup leaks bounds initial horizon scheduler) (LateOption slots) p))
        (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior
        (onePacketN).playedInformation fallback
        fun agent => (weights n (keyedPool (LateDeliveryAgent setup leaks bounds initial horizon
          scheduler) (agentLateKey setup leaks bounds initial horizon scheduler) agent)).bind
          (keyedComponent (prescribed n) (lateLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent _ (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (KeyedPart
          (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
          (agentLateKey setup leaks bounds initial horizon scheduler) (LateOption slots) p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => keyedPool
            (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
            (agentLateKey setup leaks bounds initial horizon scheduler) agent = p),
          (if decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1 then
            localGain fuel (nativeReadout setup leaks bounds initial horizon scheduler)
              (exclusionReadoutUtility setup parameter utility excludedPayoff) (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩
              ((alternative (keyedPool (LateDeliveryAgent setup leaks bounds initial horizon
                scheduler) (agentLateKey setup leaks bounds initial horizon scheduler)
                agent)).bind (keyedComponent (prescribed n) (lateLaw n) agent))
          else 0) ≤ 0) →
      ∃ otherError : ℕ → ℝ, Tendsto otherError atTop (nhds 0) ∧
        ∀ n who (site : (onePacketN).InformationSite who), (onePacketN).agentAt site ∉ free →
          ∀ choice : (onePacketN).Choice who site.1, ¬ compared who site choice →
          localGain fuel (nativeReadout setup leaks bounds initial horizon scheduler)
              (exclusionReadoutUtility setup parameter utility excludedPayoff) (targetSequence n)
              site (PMF.pure choice) ≤ otherError n ∨
            (∃ alternative : PMF (KeyedPart
                (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
                (agentLateKey setup leaks bounds initial horizon scheduler) (LateOption slots)
                (keyedPool (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
                  (agentLateKey setup leaks bounds initial horizon scheduler)
                  ((onePacketN).agentAt site))),
              localGain fuel (nativeReadout setup leaks bounds initial horizon scheduler)
                  (exclusionReadoutUtility setup parameter utility excludedPayoff)
                  (targetSequence n) site (PMF.pure choice) ≤
                localGain fuel (nativeReadout setup leaks bounds initial horizon scheduler)
                  (exclusionReadoutUtility setup parameter utility excludedPayoff)
                  (targetSequence n) site (alternative.bind (keyedComponent (prescribed n)
                    (lateLaw n) ((onePacketN).agentAt site))) + otherError n) ∨
            ∃ mixture : PMF (M.AssessmentDeviation who),
              localGain fuel (nativeReadout setup leaks bounds initial horizon scheduler)
                  (exclusionReadoutUtility setup parameter utility excludedPayoff)
                  (targetSequence n) site (PMF.pure choice) ≤
                expect mixture (fun deviation =>
                  let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                      sourceFuel) sourceObserve
                    (sourceSequence n) who deviation
                  expect sourceComparison.alternative
                      (exclusionReadoutUtility setup parameter utility excludedPayoff · who) -
                    expect sourceComparison.prescribed
                      (exclusionReadoutUtility setup parameter utility excludedPayoff · who)) +
                  otherError n) :
    ∀ (weights : ℕ → ∀ p, PMF (KeyedPart
        (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
        (agentLateKey setup leaks bounds initial horizon scheduler) (LateOption slots) p))
      (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior
        (onePacketN).playedInformation fallback
        fun agent => (weights n (keyedPool (LateDeliveryAgent setup leaks bounds initial horizon
          scheduler) (agentLateKey setup leaks bounds initial horizon scheduler) agent)).bind
          (keyedComponent (prescribed n) (lateLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent _ (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (KeyedPart
          (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
          (agentLateKey setup leaks bounds initial horizon scheduler) (LateOption slots) p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => keyedPool
            (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
            (agentLateKey setup leaks bounds initial horizon scheduler) agent = p),
          (if decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1 then
            localGain fuel (nativeReadout setup leaks bounds initial horizon scheduler)
              (exclusionReadoutUtility setup parameter utility excludedPayoff) (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩
              ((alternative (keyedPool (LateDeliveryAgent setup leaks bounds initial horizon
                scheduler) (agentLateKey setup leaks bounds initial horizon scheduler)
                agent)).bind (keyedComponent (prescribed n) (lateLaw n) agent))
          else 0) ≤ 0) →
      ∃ comparisonError : ℕ → ℝ, Tendsto comparisonError atTop (nhds 0) ∧
        ∀ n who (site : (onePacketN).InformationSite who), (onePacketN).agentAt site ∉ free →
          ∀ choice : (onePacketN).Choice who site.1,
          localGain fuel (nativeReadout setup leaks bounds initial horizon scheduler)
              (exclusionReadoutUtility setup parameter utility excludedPayoff) (targetSequence n)
              site (PMF.pure choice) ≤ comparisonError n ∨
            (∃ alternative : PMF (KeyedPart
                (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
                (agentLateKey setup leaks bounds initial horizon scheduler) (LateOption slots)
                (keyedPool (LateDeliveryAgent setup leaks bounds initial horizon scheduler)
                  (agentLateKey setup leaks bounds initial horizon scheduler)
                  ((onePacketN).agentAt site))),
              localGain fuel (nativeReadout setup leaks bounds initial horizon scheduler)
                  (exclusionReadoutUtility setup parameter utility excludedPayoff)
                  (targetSequence n) site (PMF.pure choice) ≤
                localGain fuel (nativeReadout setup leaks bounds initial horizon scheduler)
                  (exclusionReadoutUtility setup parameter utility excludedPayoff)
                  (targetSequence n) site (alternative.bind (keyedComponent (prescribed n)
                    (lateLaw n) ((onePacketN).agentAt site))) + comparisonError n) ∨
            ∃ mixture : PMF (M.AssessmentDeviation who),
              localGain fuel (nativeReadout setup leaks bounds initial horizon scheduler)
                  (exclusionReadoutUtility setup parameter utility excludedPayoff)
                  (targetSequence n) site (PMF.pure choice) ≤
                expect mixture (fun deviation =>
                  let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                      sourceFuel) sourceObserve
                    (sourceSequence n) who deviation
                  expect sourceComparison.alternative
                      (exclusionReadoutUtility setup parameter utility excludedPayoff · who) -
                    expect sourceComparison.prescribed
                      (exclusionReadoutUtility setup parameter utility excludedPayoff · who)) +
                  comparisonError n := by
  convert keyedLocalComparisons fuel bounded targetRecall _ _ fallback _ _ sourceObserve
    sourceFuel sourceSequence prescribed lateLaw free compared failed excludedPayoff pays bound
    bound_nonneg
    (fun weights targetSequence played mixed bayes => by
      obtain ⟨continuation, score, error, drift, slack, errorVanishes, driftVanishes,
        slackVanishes, drift_nonneg, slack_nonneg, facts⟩ :=
        ranking weights targetSequence played mixed bayes
      refine ⟨continuation, score, error, drift, slack, errorVanishes, driftVanishes,
        slackVanishes, drift_nonneg, slack_nonneg, fun n who site choice notFree marked => ?_⟩
      obtain ⟨lower_le, gap_le, rest⟩ := facts n who site choice notFree marked
      exact ⟨Or.inl ⟨by linarith [excluded_le_lower who], gap_le⟩, rest⟩)
    (fun weights targetSequence played mixed bayes pooled =>
      otherComparisons weights targetSequence played mixed bayes (by convert pooled; rfl))
  all_goals rfl

end Obligations

end Vegas
