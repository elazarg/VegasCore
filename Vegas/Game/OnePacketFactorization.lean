/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketTrembles
import GameTheory.Analysis.Protocol.CounterfactualReach
import GameTheoryExtensions.Analysis.Protocol.ReachBounds

/-! # The operational factorization of one-packet reach

**Three factors of a history.** Fix an observer `who`. The *source weight* of a
native history of the one-packet game multiplies Nature's initial draw, the
chance mass of every completed event (`Vegas.completionMass`), and, at every
response of another player, the *content factor*: the mass that the
as-if-honest law at the responder's projected source view gives the source
action its transmission decodes to, whatever handle slot carries it
(`Vegas.contentFactor`, `Vegas.othersSourceWeight`). The content factor is
taken when the packet is sent, not when its event completes: a pending
commitment already carries the law of its hidden value. The *operational
record* lists the operational states along the history, newest first: the
control position, the scheduler's recall and view (with the pending payloads),
the leaked packets, and every player's late-delivery key
(`Vegas.operationalRecord`). The *owner mass* is the product of the observer's
own choice masses read from its recall (`Vegas.ownerMass`).

**Regular histories.** A history is regular for `who` when every response of
another player is made at a forced agent of that player and has a positive
content factor (`Vegas.RegularTrace`). Bad bindings of other players, and
values outside the as-if-honest support, are the irregular remainder.

**Operational steps.** The factorization rests on two local hypotheses,
bundled in `Vegas.OperationalSteps`. *Value blindness*: the mass of a
scheduler round is the chance mass of the event it completes times a function
of the operational states before and after. The runtime's types do not give
this by themselves in the form needed downstream: the scheduler and the
observation rule read whole pending payloads, and only on forced histories do
those carry no hidden value other than the delivered one
(`Vegas.onePacket_pending_of_forced`). *Component steps*: at a
regular response of another player, the response mass is its content factor
times a function of the operational states, up to a relative error `error n`.

**The factorization.** Under these hypotheses, at every regular history the
reach is the source weight times a function of the operational record times
the owner mass of the observer's recall, within the relative error
`(1 + error n) ^ length - 1` (`Vegas.reach_near_factorization`). Histories have
at most `2 * horizon + 1` steps, so the relative error is uniform and vanishes
with `error n` (`Vegas.onePacketReachFactorization`).

**Late delivery at site level.** A late-delivery option's failure probability
from one history is not a function of the late-delivery key alone: a scheduler
may recall commands the owner never observed. A belief average of quantities
close, on the histories of a set, to a function of the operational record is
close to the average of that function, up to the mass outside the set
(`Vegas.expect_near_of_record`).

The factorization is approximate: tremble tiers put scale-dependent mass on the
as-if-honest action, and that mass depends on the private menu. It is consumed
in the form of `GameTheory.Math.Probability.NearProductWeights`, whose
`regular_close` field is this inequality;
`GameTheory.Protocol.InformationModel.FactoredHistoryLikelihood` needs an exact
identity.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

section Records

/-- The operational part of a native protocol state: the control position, the
scheduler's recall and view (with the pending payloads), every player's leaked
packets, and every player's late-delivery key, which carries the operational
part of its recall and the value an opening at its reveal turn delivers. -/
structure OperationalState where
  /-- Scheduler rounds left. -/
  remaining : Nat
  /-- The player being activated, if any. -/
  actor : Option Player
  /-- The scheduler's command recall. -/
  environmentRecall : List (application setup leaks).EnvironmentEntry
  /-- The scheduler's view: public network state, public contract view, receipts. -/
  environment : (application setup leaks).EnvironmentView
  /-- The pending packets leaked to each player. -/
  leaked : Player → List (Message Player (application setup leaks).Payload)
  /-- Each player's late-delivery key. -/
  keys : Player → Option (LateKey setup leaks)

/-- The operational part of a native protocol state. -/
def operationalState : (application setup leaks).ProtocolState →
    Option (OperationalState setup leaks)
  | none => none
  | some control => some
      { remaining := control.remaining
        actor := control.actor
        environmentRecall := control.execution.environmentRecall
        environment := control.execution.observeEnvironment (application setup leaks)
        leaked := control.execution.network.leaked
        keys := fun who => lateKey setup leaks who
          (some (control.execution.recall who,
            control.execution.observe (application setup leaks) who)) }

/-- The observer's own recall at a native protocol state. -/
def ownerRecall (who : Player) :
    (application setup leaks).ProtocolState → List (application setup leaks).PlayerEntry
  | none => []
  | some control => control.execution.recall who

/-- The chance mass of the event a configuration step completes: at an event
without an actor, a sample, the mass the graph step gives the reached
configuration, which is the draw's probability; one at a decision, and one when
no event completes. -/
def completionMass (before after : EventGraphRuntime.State (graph setup)) : ℝ :=
  match after.config.history.drop before.config.history.length with
  | [⟨event, action⟩] =>
      match (graph setup).actor? event with
      | none =>
          if ready : before.config.cut.Ready event then
            (before.config.step event ready action after.config).toReal
          else 0
      | some _ => 1
  | _ => 1

/-- The source action a transmission decodes to: at a binding event, the
commitment of the value the submitted handle binds after submission, at any
slot; at a resolve event, the disclosure. -/
def sentSourceAction (after : (application setup leaks).Execution)
    (action : (application setup leaks).Action) : Option (OwnAction Player L) :=
  match action.transmission with
  | none => none
  | some material =>
      match material.call.packet with
      | .commitment event handle =>
          match nodeView (graph setup) event with
          | .bind _ payload outputEq _ =>
              decodeEventAction setup.program event
                (cast (congrArg EventGraph.EventField.Action outputEq.symm)
                  (after.application.bindingResult handle payload))
          | _ => none
      | .opening event _ _ =>
          match nodeView (graph setup) event with
          | .resolve _ _ _ _ outputEq _ =>
              decodeEventAction setup.program event
                (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
          | _ => none
      | .malformed _ => none

/-- **The content factor of a response.** One for silence; for a transmission,
the mass the as-if-honest law at the responder's projected source view gives
the source action it decodes to. -/
def contentFactor (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (before after : (application setup leaks).Execution)
    (action : (application setup leaks).Action) : ℝ :=
  match action.transmission with
  | none => 1
  | some _ =>
      (((assessment.strategy who (sourceViewOf setup leaks who
        (before.observe (application setup leaks) who))).map Subtype.val)
          (sentSourceAction setup leaks after action)).toReal

/-- The source factor of one native transition for an observer `who`:
Nature's initial draw; at another player's response, its content factor; at a
scheduler round, the chance mass of the completed event; one at `who`'s own
responses. -/
def transitionSourceFactor (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) : (application setup leaks).ProtocolState →
      (Player → Option (application setup leaks).Action) →
        (application setup leaks).ProtocolState → ℝ
  | none, _, some after => (initialLaw setup after.execution.application).toReal
  | some before, joint, some after =>
      match before.actor with
      | some actor =>
          if actor = who then 1 else
            contentFactor setup leaks assessment actor before.execution after.execution
              ((joint actor).getD ⟨none⟩)
      | none => completionMass setup before.execution.application after.execution.application
  | _, _, _ => 1

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- The native protocol of the one-packet game from the default initial law. -/
abbrev onePacketProtocol :=
  (bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon scheduler

/-- The information model of the one-packet game from the default initial
law. -/
abbrev onePacketInformation :=
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

/-- **The source weight.** The product, along a native history, of the source
factors of its transitions for the observer `who`. -/
def othersSourceWeight (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) :
    ∀ {state}, (onePacketProtocol setup leaks bounds horizon scheduler).Trace state → ℝ
  | _, .start => 1
  | _, .extend (source := before) (target := after) prior joint _ _ =>
      othersSourceWeight assessment who prior *
        transitionSourceFactor setup leaks assessment who before joint after

/-- **The operational record.** The operational states along a native history,
newest first. -/
def operationalRecord :
    ∀ {state}, (onePacketProtocol setup leaks bounds horizon scheduler).Trace state →
      List (Option (OperationalState setup leaks))
  | _, .start => [operationalState setup leaks none]
  | _, .extend (target := after) prior _ _ _ =>
      operationalState setup leaks after :: operationalRecord prior

/-- A response of another player is regular when it is made at a forced agent
of the responder, from a forced state of the observer, and its content factor
is positive. Forcedness for the observer rules out other players' exclusion and
owed failures, so a regular responder holds no bad binding of its own. -/
def RegularStep (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) :
    (application setup leaks).ProtocolState →
      (Player → Option (application setup leaks).Action) →
        (application setup leaks).ProtocolState → Prop
  | some before, joint, some after => ∀ actor, before.actor = some actor → actor ≠ who →
      (forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
          scheduler actor ((application setup leaks).observe actor (some before)) ∧
        ForcedState setup leaks who (some before)) ∧
        0 < contentFactor setup leaks assessment actor before.execution after.execution
          ((joint actor).getD ⟨none⟩)
  | _, _, _ => True

/-- **A regular history.** Every response of another player is regular. -/
def RegularTrace (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) :
    ∀ {state}, (onePacketProtocol setup leaks bounds horizon scheduler).Trace state → Prop
  | _, .start => True
  | _, .extend (source := before) (target := after) prior joint _ _ =>
      RegularTrace assessment who prior ∧
        RegularStep setup leaks bounds horizon scheduler assessment who before joint after

end Records

section Owner

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler) {who : Player}
  (policy : (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy who)

/-- The mass a policy gives the action recorded in a recall entry, at the
information of that entry. -/
def ownerStepMass (past : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry) : ℝ :=
  (((policy (some (past, entry.beforeView))).map Subtype.val) (some entry.action)).toReal

/-- The product of the owner's step masses along recall entries, after a given
past. -/
def ownerMassFrom : List (application setup leaks).PlayerEntry →
    List (application setup leaks).PlayerEntry → ℝ
  | _, [] => 1
  | past, entry :: rest =>
      ownerStepMass setup leaks bounds horizon scheduler policy past entry *
        ownerMassFrom (past ++ [entry]) rest

/-- **The owner mass.** The product of the owner's choice masses read from its
recall. -/
def ownerMass (entries : List (application setup leaks).PlayerEntry) : ℝ :=
  ownerMassFrom setup leaks bounds horizon scheduler policy [] entries

theorem ownerMassFrom_append (past rest : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry) :
    ownerMassFrom setup leaks bounds horizon scheduler policy past (rest ++ [entry]) =
      ownerMassFrom setup leaks bounds horizon scheduler policy past rest *
        ownerStepMass setup leaks bounds horizon scheduler policy (past ++ rest) entry := by
  induction rest generalizing past with
  | nil => simp [ownerMassFrom]
  | cons head rest ih =>
      simp only [List.cons_append, ownerMassFrom, ih, List.append_assoc, List.nil_append]
      ring

theorem ownerMass_append (entries : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry) :
    ownerMass setup leaks bounds horizon scheduler policy (entries ++ [entry]) =
      ownerMass setup leaks bounds horizon scheduler policy entries *
        ownerStepMass setup leaks bounds horizon scheduler policy entries entry := by
  unfold ownerMass
  rw [ownerMassFrom_append, List.nil_append]

theorem ownerMassFrom_nonneg (past entries : List (application setup leaks).PlayerEntry) :
    0 ≤ ownerMassFrom setup leaks bounds horizon scheduler policy past entries := by
  induction entries generalizing past with
  | nil => exact zero_le_one
  | cons head rest ih =>
      exact mul_nonneg ENNReal.toReal_nonneg (ih _)

end Owner

section Operational

variable {who : Player}

/-- The operational factor of one transition: one at the initial draw and at
`who`'s own responses, and the given mass elsewhere. -/
def operationalFactor (who : Player)
    (mass : Option (OperationalState setup leaks) → Option (OperationalState setup leaks) → ℝ)
    (before after : Option (OperationalState setup leaks)) : ℝ :=
  match before with
  | none => 1
  | some state => if state.actor = some who then 1 else mass before after

theorem operationalFactor_operationalState
    (mass : Option (OperationalState setup leaks) → Option (OperationalState setup leaks) → ℝ)
    (control : (application setup leaks).Control) (after : Option (OperationalState setup leaks)) :
    operationalFactor setup leaks who mass (operationalState setup leaks (some control)) after =
      if control.actor = some who then 1 else mass (operationalState setup leaks (some control))
        after := rfl

/-- **The operational weight.** The product of the operational factors of
consecutive operational states of a record, newest first. -/
def operationalWeight (who : Player)
    (mass : Option (OperationalState setup leaks) → Option (OperationalState setup leaks) → ℝ) :
    List (Option (OperationalState setup leaks)) → ℝ
  | after :: before :: rest =>
      operationalFactor setup leaks who mass before after *
        operationalWeight who mass (before :: rest)
  | _ => 1

theorem operationalFactor_nonneg
    {mass : Option (OperationalState setup leaks) → Option (OperationalState setup leaks) → ℝ}
    (nonnegative : ∀ before after, 0 ≤ mass before after)
    (before after : Option (OperationalState setup leaks)) :
    0 ≤ operationalFactor setup leaks who mass before after := by
  unfold operationalFactor
  split
  · exact zero_le_one
  · split
    · exact zero_le_one
    · exact nonnegative _ _

theorem operationalWeight_nonneg
    {mass : Option (OperationalState setup leaks) → Option (OperationalState setup leaks) → ℝ}
    (nonnegative : ∀ before after, 0 ≤ mass before after) :
    ∀ record, 0 ≤ operationalWeight setup leaks who mass record
  | [] => zero_le_one
  | [_] => zero_le_one
  | _ :: before :: rest =>
      mul_nonneg (operationalFactor_nonneg setup leaks nonnegative _ _)
        (operationalWeight_nonneg nonnegative (before :: rest))

end Operational

section Factorization

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- **Operational steps.** The two local hypotheses of the factorization along a
sequence of intended assessments and native profiles.

* `environment` (value blindness): the mass of every scheduler round is the
  chance mass of the event it completes times a function of the operational
  states before and after.
* `component`: at a regular response of another player, the response mass is
  its content factor times the same function, up to the relative error
  `error n`. -/
structure OperationalSteps (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (profiles : ℕ → ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    (who : Player) where
  /-- The operational mass of a transition. -/
  mass : ℕ → Option (OperationalState setup leaks) → Option (OperationalState setup leaks) → ℝ
  /-- The relative error of the component steps. -/
  error : ℕ → ℝ
  mass_nonneg : ∀ n before after, 0 ≤ mass n before after
  error_nonneg : ∀ n, 0 ≤ error n
  error_tendsto : Tendsto error atTop (nhds 0)
  environment : ∀ n {before after}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before) joint legal
    (_ : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
      ⟨joint, legal⟩).support) (control : (application setup leaks).Control),
    before = some control → control.actor = none →
    ∀ next : (application setup leaks).Control, after = some next →
      InformationModel.stepProb (onePacketInformation setup leaks bounds horizon scheduler)
          (profiles n) prior ⟨joint, legal⟩ after =
        completionMass setup control.execution.application next.execution.application *
          mass n (operationalState setup leaks before) (operationalState setup leaks after)
  component : ∀ n {before after}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before) joint legal
    (_ : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
      ⟨joint, legal⟩).support) (control next : (application setup leaks).Control)
    (actor : Player), before = some control → after = some next →
    control.actor = some actor → actor ≠ who →
    forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler actor ((application setup leaks).observe actor (some control)) →
    ForcedState setup leaks who (some control) →
    0 < contentFactor setup leaks (sequence n) actor control.execution next.execution
      ((joint actor).getD ⟨none⟩) →
    |InformationModel.stepProb (onePacketInformation setup leaks bounds horizon scheduler)
        (profiles n) prior ⟨joint, legal⟩ after -
      contentFactor setup leaks (sequence n) actor control.execution next.execution
          ((joint actor).getD ⟨none⟩) *
        mass n (operationalState setup leaks before) (operationalState setup leaks after)| ≤
      error n * (contentFactor setup leaks (sequence n) actor control.execution next.execution
          ((joint actor).getD ⟨none⟩) *
        mass n (operationalState setup leaks before) (operationalState setup leaks after))

variable {setup leaks bounds horizon scheduler}

omit [Fintype Player] in
theorem completionMass_nonneg (before after : EventGraphRuntime.State (graph setup)) :
    0 ≤ completionMass setup before after := by
  unfold completionMass
  split
  · split
    · split
      · exact ENNReal.toReal_nonneg
      · exact le_rfl
    · exact zero_le_one
  · exact zero_le_one

omit [Fintype Player] in
theorem contentFactor_nonneg (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (before after : (application setup leaks).Execution)
    (action : (application setup leaks).Action) :
    0 ≤ contentFactor setup leaks assessment who before after action := by
  unfold contentFactor
  split
  · exact zero_le_one
  · exact ENNReal.toReal_nonneg

omit [Fintype Player] in
theorem transitionSourceFactor_nonneg (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (before : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (after : (application setup leaks).ProtocolState) :
    0 ≤ transitionSourceFactor setup leaks assessment who before joint after := by
  unfold transitionSourceFactor
  split
  · exact ENNReal.toReal_nonneg
  · split
    · split
      · exact zero_le_one
      · exact contentFactor_nonneg _ _ _ _ _
    · exact completionMass_nonneg _ _
  · exact zero_le_one

theorem othersSourceWeight_nonneg (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) : ∀ {state}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state),
    0 ≤ othersSourceWeight setup leaks bounds horizon scheduler assessment who trace
  | _, .start => zero_le_one
  | _, .extend prior _ _ _ =>
      mul_nonneg (othersSourceWeight_nonneg assessment who prior)
        (transitionSourceFactor_nonneg _ _ _ _ _)

/-- The newest entry of the operational record is the current operational
state. -/
theorem operationalRecord_head : ∀ {state : (application setup leaks).ProtocolState}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state),
    ∃ rest, operationalRecord setup leaks bounds horizon scheduler trace =
      operationalState setup leaks state :: rest
  | _, .start => ⟨[], rfl⟩
  | _, .extend _ _ _ _ => ⟨_, rfl⟩

/-- The one-packet information of a player is its native observation. -/
theorem onePacket_infoOf (player : Player) {state : (application setup leaks).ProtocolState}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state) :
    (onePacketInformation setup leaks bounds horizon scheduler).infoOf player trace =
      (application setup leaks).observe player state :=
  (bounds.onePacketMenu (runtime setup) leaks).info (initialLaw setup) horizon scheduler player
    trace

/-- An idle player's only choice has mass one. -/
theorem idle_choice_mass (player : Player)
    (policy : (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    {state : (application setup leaks).ProtocolState}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    (idle : (application setup leaks).actor state ≠ some player)
    (choice : (onePacketInformation setup leaks bounds horizon scheduler).Choice player
      ((onePacketInformation setup leaks bounds horizon scheduler).infoOf player trace)) :
    (policy _ choice).toReal = 1 := by
  have none_ : (onePacketInformation setup leaks bounds horizon scheduler).infoOf player trace =
      none := by
    rw [onePacket_infoOf]
    cases state with
    | none => rfl
    | some control =>
        have different : control.actor ≠ some player := idle
        simp only [ReactiveApplication.observe, different, ↓reduceIte]
  revert choice
  rw [none_]
  intro choice
  have single : ∀ other : (onePacketInformation setup leaks bounds horizon scheduler).Choice
      player none, other = choice := fun other => by
    apply Subtype.ext
    have left : other.1 = none := other.2
    have right : choice.1 = none := choice.2
    rw [left, right]
  have mass : policy none choice = 1 := by
    rw [PMF.apply_eq_one_iff]
    ext other
    simp only [Set.mem_singleton_iff]
    constructor
    · intro _
      exact single other
    · rintro rfl
      obtain ⟨member, supported⟩ := (policy none).support_nonempty
      rw [single member] at supported
      exact supported
  rw [mass, ENNReal.toReal_one]

/-- The mass of a step with no actor is its transition mass. -/
theorem stepProb_of_idle
    (profile : ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    {before after : (application setup leaks).ProtocolState}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before)
    (joint : Player → Option (application setup leaks).Action)
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
    (idle : (application setup leaks).actor before = none) :
    InformationModel.stepProb (onePacketInformation setup leaks bounds horizon scheduler)
        profile prior ⟨joint, legal⟩ after =
      ((application setup leaks).transition (initialLaw setup) horizon scheduler before joint
        after).toReal := by
  unfold InformationModel.stepProb
  rw [InformationModel.behavioralJoint_prob_eq_prod, Finset.prod_eq_one, one_mul]
  · rfl
  · intro player _
    exact idle_choice_mass player _ prior (by rw [idle]; exact (Option.some_ne_none _).symm) _

/-- The mass of a step with an actor is the actor's choice mass times the
transition mass. -/
theorem stepProb_of_actor
    (profile : ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    {before after : (application setup leaks).ProtocolState}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before)
    (joint : Player → Option (application setup leaks).Action)
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
    {actor : Player} (acting : (application setup leaks).actor before = some actor) :
    InformationModel.stepProb (onePacketInformation setup leaks bounds horizon scheduler)
        profile prior ⟨joint, legal⟩ after =
      (profile actor _ (InformationModel.choicesOfLegal
        (onePacketInformation setup leaks bounds horizon scheduler) prior ⟨joint, legal⟩
          actor)).toReal *
      ((application setup leaks).transition (initialLaw setup) horizon scheduler before joint
        after).toReal := by
  unfold InformationModel.stepProb
  rw [InformationModel.behavioralJoint_prob_eq_prod, Finset.prod_eq_single actor]
  · rfl
  · intro player _ different
    exact idle_choice_mass player _ prior (by
      rw [acting]
      exact fun same => different (Option.some.inj same).symm) _
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

omit [Fintype Player] in
/-- A response's transition is the point mass at the response. -/
theorem transition_respond (control : (application setup leaks).Control) {actor : Player}
    (acting : control.actor = some actor)
    (joint : Player → Option (application setup leaks).Action) :
    (application setup leaks).transition (initialLaw setup) horizon scheduler (some control)
        joint =
      PMF.pure (some { control with
        actor := none
        execution := control.execution.respond (application setup leaks) actor
          ((joint actor).getD ⟨none⟩) }) := by
  rcases control with ⟨remaining, current, execution⟩
  cases acting
  rfl

omit [Fintype Player] in
/-- A response appends one entry, with the responder's view and action, to its
own recall. -/
private theorem respond_recall_self (execution : (application setup leaks).Execution) (who : Player)
    (action : (application setup leaks).Action) :
    ∃ emitted, (execution.respond (application setup leaks) who action).recall who =
      execution.recall who ++
        [⟨execution.observe (application setup leaks) who, action, emitted⟩] := by
  rcases action with ⟨transmission⟩
  cases transmission <;>
    simp only [ReactiveApplication.Execution.respond, ↓reduceIte] <;> exact ⟨_, rfl⟩

omit [Fintype Player] in
/-- A scheduler round from an initialized state reaches an initialized state
with the same recalls. -/
theorem transition_environment (control : (application setup leaks).Control)
    (idle : control.actor = none) (joint : Player → Option (application setup leaks).Action)
    {after : (application setup leaks).ProtocolState}
    (reached : after ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler
      (some control) joint).support) :
    ∃ next : (application setup leaks).Control, after = some next ∧
      next.execution.recall = control.execution.recall := by
  rcases control with ⟨remaining, current, execution⟩
  cases idle
  cases remaining with
  | zero => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached, rfl⟩
  | succ remaining =>
      obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
      exact ⟨_, rfl, (application setup leaks).environmentStep_recall execution next command
        supported⟩

/-- **The factor of one step.** At a regular step, the step mass is within the
relative error of a nonnegative factor that carries the source factor, the
operational factor and the owner's step mass. -/
theorem step_factor {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {who : Player} (steps : OperationalSteps setup leaks bounds horizon scheduler sequence
      profiles who) (n : ℕ) {before after : (application setup leaks).ProtocolState}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before)
    (joint : Player → Option (application setup leaks).Action)
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
    (realized : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
      ⟨joint, legal⟩).support)
    (regular : RegularStep setup leaks bounds horizon scheduler (sequence n) who before joint
      after) :
    ∃ factor, 0 ≤ factor ∧
      |InformationModel.stepProb (onePacketInformation setup leaks bounds horizon scheduler)
          (profiles n) prior ⟨joint, legal⟩ after - factor| ≤ steps.error n * factor ∧
      transitionSourceFactor setup leaks (sequence n) who before joint after *
          operationalFactor setup leaks who (steps.mass n) (operationalState setup leaks before)
            (operationalState setup leaks after) *
          ownerMass setup leaks bounds horizon scheduler (profiles n who)
            (ownerRecall setup leaks who after) =
        ownerMass setup leaks bounds horizon scheduler (profiles n who)
          (ownerRecall setup leaks who before) * factor := by
  have stepNonneg : 0 ≤ InformationModel.stepProb
      (onePacketInformation setup leaks bounds horizon scheduler) (profiles n) prior
      ⟨joint, legal⟩ after := by
    unfold InformationModel.stepProb
    exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have exact_ : ∀ factor, factor = InformationModel.stepProb
      (onePacketInformation setup leaks bounds horizon scheduler) (profiles n) prior
      ⟨joint, legal⟩ after →
      |InformationModel.stepProb (onePacketInformation setup leaks bounds horizon scheduler)
          (profiles n) prior ⟨joint, legal⟩ after - factor| ≤ steps.error n * factor := by
    rintro _ rfl
    rw [sub_self, abs_zero]
    exact mul_nonneg (steps.error_nonneg n) stepNonneg
  change after ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler
    before joint).support at realized
  cases before with
  | none =>
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ realized
      have mass := stepProb_of_idle (profiles n) prior joint legal rfl (after := some
        ⟨horizon, none, ReactiveApplication.Execution.initial (application setup leaks) initial⟩)
      have transitionMass : ((application setup leaks).transition (initialLaw setup) horizon
          scheduler none joint (some ⟨horizon, none, ReactiveApplication.Execution.initial
            (application setup leaks) initial⟩)) = initialLaw setup initial := by
        rw [show (application setup leaks).transition (initialLaw setup) horizon scheduler none
            joint = (initialLaw setup).map (fun state => some
              (⟨horizon, none, ReactiveApplication.Execution.initial (application setup leaks)
                state⟩ : (application setup leaks).Control)) from rfl]
        apply pmf_map_apply_of_injective
        intro first second same
        have inner := Option.some.inj same
        have executions := congrArg ReactiveApplication.Control.execution inner
        exact congrArg ReactiveApplication.Execution.application executions
      rw [transitionMass] at mass
      refine ⟨_, stepNonneg, exact_ _ rfl, ?_⟩
      rw [mass]
      simp only [transitionSourceFactor, operationalState, operationalFactor, ownerRecall,
        ReactiveApplication.Execution.initial]
      ring
  | some control =>
      cases acting : control.actor with
      | none =>
          obtain ⟨next, rfl, recallEq⟩ := transition_environment control acting joint realized
          have mass := steps.environment n prior joint legal realized control rfl acting next rfl
          refine ⟨_, stepNonneg, exact_ _ rfl, ?_⟩
          rw [mass]
          have actorNe : ¬ control.actor = some who := by
            rw [acting]; exact (Option.some_ne_none _).symm
          simp only [operationalFactor_operationalState, actorNe, ↓reduceIte]
          simp only [transitionSourceFactor, acting, ownerRecall, recallEq]
          ring
      | some actor =>
          rw [transition_respond control acting joint, PMF.mem_support_pure_iff] at realized
          subst realized
          have transitionOne : ((application setup leaks).transition (initialLaw setup) horizon
              scheduler (some control) joint (some { control with
                actor := none
                execution := control.execution.respond (application setup leaks) actor
                  ((joint actor).getD ⟨none⟩) })).toReal = 1 := by
            rw [transition_respond control acting joint, PMF.pure_apply_self,
              ENNReal.toReal_one]
          have mass := stepProb_of_actor (profiles n) prior joint legal
            (after := some { control with
              actor := none
              execution := control.execution.respond (application setup leaks) actor
                ((joint actor).getD ⟨none⟩) }) (show (application setup leaks).actor
                (some control) = some actor from acting)
          rw [transitionOne, mul_one] at mass
          by_cases owner : actor = who
          · subst owner
            obtain ⟨emitted, recallEq⟩ := respond_recall_self control.execution actor
              ((joint actor).getD ⟨none⟩)
            have active : (application setup leaks).actor (some control) = some actor := acting
            have chosen : ∃ action, joint actor = some action := by
              have local_ := legal.2 actor
              cases picked : joint actor with
              | none =>
                  rw [picked] at local_
                  exact (local_ active).elim
              | some action => exact ⟨action, rfl⟩
            obtain ⟨action, picked⟩ := chosen
            have stepEq : InformationModel.stepProb
                (onePacketInformation setup leaks bounds horizon scheduler) (profiles n) prior
                ⟨joint, legal⟩ (some { control with
                  actor := none
                  execution := control.execution.respond (application setup leaks) actor
                    ((joint actor).getD ⟨none⟩) }) =
                ownerStepMass setup leaks bounds horizon scheduler (profiles n actor)
                  (control.execution.recall actor)
                  ⟨control.execution.observe (application setup leaks) actor,
                    (joint actor).getD ⟨none⟩, emitted⟩ := by
              rw [mass]
              unfold ownerStepMass
              have general : ∀ info (_ : info = some (control.execution.recall actor,
                  control.execution.observe (application setup leaks) actor))
                  (choice : (onePacketInformation setup leaks bounds horizon scheduler).Choice
                    actor info), choice.1 = some action →
                  (profiles n actor info choice).toReal =
                    (((profiles n actor (some (control.execution.recall actor,
                      control.execution.observe (application setup leaks) actor))).map
                        Subtype.val) (some action)).toReal := by
                rintro info rfl choice value
                rw [← value, pmf_map_apply_of_injective _ Subtype.val_injective]
              rw [picked, Option.getD_some]
              apply general
              · rw [onePacket_infoOf]
                simp only [ReactiveApplication.observe, acting, ↓reduceIte]
              · exact picked
            refine ⟨_, stepNonneg, exact_ _ rfl, ?_⟩
            simp only [operationalFactor_operationalState, acting, ↓reduceIte]
            simp only [transitionSourceFactor, acting, ↓reduceIte, ownerRecall]
            rw [recallEq, ownerMass_append, ← stepEq]
            ring
          · obtain ⟨⟨forced, observerForced⟩, positive⟩ := regular actor acting owner
            have bound := steps.component n prior joint legal (by
              change _ ∈ ((application setup leaks).transition (initialLaw setup) horizon
                scheduler (some control) joint).support
              rw [transition_respond control acting joint]
              exact (PMF.mem_support_pure_iff _ _).mpr rfl) control _ actor rfl rfl acting owner
              forced observerForced positive
            refine ⟨_, mul_nonneg (contentFactor_nonneg _ _ _ _ _) (steps.mass_nonneg _ _ _),
              bound, ?_⟩
            have actorNe : ¬ control.actor = some who := by
              rw [acting]
              exact fun same => owner (Option.some.inj same)
            simp only [operationalFactor_operationalState, actorNe, ↓reduceIte]
            simp only [transitionSourceFactor, acting, owner, ↓reduceIte, ownerRecall,
              (application setup leaks).respond_recall_other control.execution actor who
                (Ne.symm owner)]
            ring

/-- Products of weights within relative errors stay within the compounded
relative error. -/
theorem abs_mul_sub_mul_le {reach weight step factor error : ℝ} {length : ℕ}
    (weightNonneg : 0 ≤ weight) (factorNonneg : 0 ≤ factor) (errorNonneg : 0 ≤ error)
    (prior : |reach - weight| ≤ ((1 + error) ^ length - 1) * weight)
    (current : |step - factor| ≤ error * factor) :
    |reach * step - weight * factor| ≤ ((1 + error) ^ (length + 1) - 1) * (weight * factor) := by
  have stepAbs : |step| ≤ (1 + error) * factor := by
    have := abs_sub_abs_le_abs_sub step factor
    rw [abs_of_nonneg factorNonneg] at this
    linarith
  have split : reach * step - weight * factor =
      (reach - weight) * step + weight * (step - factor) := by
    ring
  have powerGe : 1 ≤ (1 + error) ^ length := one_le_pow₀ (by linarith)
  calc |reach * step - weight * factor|
      ≤ |reach - weight| * |step| + weight * |step - factor| := by
        rw [split]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg weightNonneg]
    _ ≤ ((1 + error) ^ length - 1) * weight * ((1 + error) * factor) +
          weight * (error * factor) := by
        gcongr
    _ = ((1 + error) ^ (length + 1) - 1) * (weight * factor) := by ring

/-- The weight of a native history for an observer: its source weight, times
the operational weight of its record, times the owner mass of the observer's
recall. -/
def factoredWeight (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (profiles : ℕ → ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    {who : Player} (steps : OperationalSteps setup leaks bounds horizon scheduler sequence
      profiles who) (n : ℕ) {state : (application setup leaks).ProtocolState}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state) : ℝ :=
  othersSourceWeight setup leaks bounds horizon scheduler (sequence n) who trace *
    operationalWeight setup leaks who (steps.mass n)
      (operationalRecord setup leaks bounds horizon scheduler trace) *
    ownerMass setup leaks bounds horizon scheduler (profiles n who)
      (ownerRecall setup leaks who state)

theorem factoredWeight_nonneg {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {who : Player} (steps : OperationalSteps setup leaks bounds horizon scheduler sequence
      profiles who) (n : ℕ) {state : (application setup leaks).ProtocolState}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state) :
    0 ≤ factoredWeight sequence profiles steps n trace :=
  mul_nonneg (mul_nonneg (othersSourceWeight_nonneg _ _ trace)
    (operationalWeight_nonneg setup leaks (steps.mass_nonneg n) _))
    (ownerMassFrom_nonneg setup leaks bounds horizon scheduler _ _ _)

/-- **The operational factorization of reach.** Under operational steps, at
every regular history the reach under the `n`-th profile is its factored
weight, within the relative error `(1 + error n) ^ length - 1`. -/
theorem reach_near_factorization {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {who : Player} (steps : OperationalSteps setup leaks bounds horizon scheduler sequence
      profiles who) (n : ℕ) :
    ∀ {state} (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state),
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who trace →
      |((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
          (profiles n) ⟨state, trace⟩).toReal - factoredWeight sequence profiles steps n trace| ≤
        ((1 + steps.error n) ^ trace.length - 1) * factoredWeight sequence profiles steps n trace
  | _, .start, _ => by
      have reach := (onePacketInformation setup leaks bounds horizon
        scheduler).historyReachWeight_initHistory (profiles n)
      change |((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
        (profiles n) (onePacketProtocol setup leaks bounds horizon scheduler).initHistory).toReal
          - _| ≤ _
      have weight : factoredWeight sequence profiles steps n
          (Trace.start : (onePacketProtocol setup leaks bounds horizon scheduler).Trace _) = 1 := by
        change 1 * 1 * ownerMassFrom setup leaks bounds horizon scheduler (profiles n who) [] [] = 1
        simp [ownerMassFrom]
      rw [reach, weight]
      simp [ExecutionProtocol.Trace.length]
  | _, .extend (source := before) (target := after) prior joint legal realized,
      ⟨regularPrior, regularStep⟩ => by
      have previous := reach_near_factorization steps n prior regularPrior
      obtain ⟨factor, factorNonneg, close, equation⟩ := step_factor steps n prior joint legal
        realized regularStep
      rw [InformationModel.historyReachProbability_extend]
      obtain ⟨rest, record⟩ := operationalRecord_head prior
      have weightEq : factoredWeight sequence profiles steps n
          (prior.extend joint legal realized) =
          factoredWeight sequence profiles steps n prior * factor := by
        unfold factoredWeight
        simp only [othersSourceWeight, operationalRecord, record, operationalWeight]
        linear_combination (othersSourceWeight setup leaks bounds horizon scheduler (sequence n)
          who prior * operationalWeight setup leaks who (steps.mass n)
            (operationalState setup leaks before :: rest)) * equation
      rw [weightEq]
      exact abs_mul_sub_mul_le (factoredWeight_nonneg steps n prior) factorNonneg
        (steps.error_nonneg n) previous close

/-- Every history of the one-packet game has at most `2 * horizon + 1` steps. -/
theorem trace_length_le : ∀ {state}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state),
    (application setup leaks).rank horizon state + trace.length ≤ 2 * horizon + 1
  | _, .start => le_of_eq (by
      change (application setup leaks).rank horizon none + 0 = 2 * horizon + 1
      simp [ReactiveApplication.rank])
  | _, .extend (source := before) (target := after) prior joint legal realized => by
      have previous := trace_length_le prior
      have lower := (application setup leaks).rank_step (initialLaw setup) horizon scheduler
        before after joint legal.1 realized
      simp only [ExecutionProtocol.Trace.length]
      omega

/-- **The uniform operational factorization.** Under operational steps, at
every regular history the reach under the `n`-th profile is its factored
weight within the relative error `(1 + error n) ^ (2 * horizon + 1) - 1`, which
vanishes. -/
theorem onePacketReachFactorization {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {who : Player} (steps : OperationalSteps setup leaks bounds horizon scheduler sequence
      profiles who) :
    Tendsto (fun n => (1 + steps.error n) ^ (2 * horizon + 1) - 1) atTop (nhds 0) ∧
      ∀ n {state} (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state),
        RegularTrace setup leaks bounds horizon scheduler (sequence n) who trace →
        |((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
            (profiles n) ⟨state, trace⟩).toReal -
          factoredWeight sequence profiles steps n trace| ≤
          ((1 + steps.error n) ^ (2 * horizon + 1) - 1) *
            factoredWeight sequence profiles steps n trace := by
  refine ⟨?_, fun n state trace regular => ?_⟩
  · have limit := ((tendsto_const_nhds (x := (1 : ℝ))).add steps.error_tendsto).pow
      (2 * horizon + 1)
    have shifted := limit.sub (tendsto_const_nhds (x := (1 : ℝ)))
    simpa using shifted
  · refine (reach_near_factorization steps n trace regular).trans ?_
    apply mul_le_mul_of_nonneg_right _ (factoredWeight_nonneg steps n trace)
    have length := trace_length_le trace
    have grows : (1 + steps.error n) ^ trace.length ≤ (1 + steps.error n) ^ (2 * horizon + 1) :=
      pow_le_pow_right₀ (by linarith [steps.error_nonneg n]) (by omega)
    linarith

end Factorization

section LateDelivery

open Classical in
/-- A belief average of unit quantities within `drift` of a unit function of a
record, at the points where a property holds, is within `drift` plus the
belief's mass off the property of the average of that function under the
belief's record law. -/
theorem expect_near_of_record {α R : Type*} [Finite α] (belief : PMF α) (record : α → R)
    (value : α → ℝ) (target : R → ℝ) (good : α → Prop) (drift : ℝ) (drift_nonneg : 0 ≤ drift)
    (valueUnit : ∀ a, 0 ≤ value a ∧ value a ≤ 1) (targetUnit : ∀ r, 0 ≤ target r ∧ target r ≤ 1)
    (near : ∀ point ∈ belief.support, good point →
      |value point - target (record point)| ≤ drift) :
    |expect belief value - expect (belief.map record) target| ≤
      drift + expect belief (fun point => if good point then 0 else 1) := by
  let := Fintype.ofFinite α
  rw [expect_map, expect_eq_sum, expect_eq_sum, expect_eq_sum, ← Finset.sum_sub_distrib]
  have total : ∑ a, (belief a).toReal = 1 := by
    have sum := PMF.tsum_coe belief
    rw [tsum_fintype] at sum
    rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top belief a), sum, ENNReal.toReal_one]
  calc _ ≤ ∑ a, |(belief a).toReal * value a - (belief a).toReal * (target ∘ record) a| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ((belief a).toReal * drift +
          (belief a).toReal * (if good a then 0 else 1)) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, ← mul_add]
        by_cases supported : a ∈ belief.support
        · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          by_cases holds : good a
          · simp only [holds, ↓reduceIte, add_zero]
            exact near a supported holds
          · simp only [holds, ↓reduceIte, Function.comp]
            have valueBound := valueUnit a
            have targetBound := targetUnit (record a)
            rw [abs_le]
            constructor <;> linarith
        · have zero : belief a = 0 := (PMF.apply_eq_zero_iff belief a).mpr supported
          simp [zero]
    _ = drift + ∑ a, (belief a).toReal * (if good a then 0 else 1) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, total, one_mul]

end LateDelivery

end Vegas
