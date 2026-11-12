module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ExclusionNativeFailure
public import GameTheory.Analysis.Protocol.SequentialOneShot
public import Interaction.ReactiveOwnPlay

@[expose] public section

/-! # Whole-policy completion after public default

The native configuration's public default set defines one persistent region
of the ordinary runtime. Local optimality throughout that region controls
arbitrary whole continuation policies there. The result uses the supplied
response menu and assessment without introducing another application or game.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The native control has recorded at least one public default. -/
def PublicDefault : ((reactiveApplication timeouts) leaks).ProtocolState → Prop
  | none => False
  | some control => control.execution.application.config.defaulted ≠ ∅

/-- A deciding player's actual input displays at least one public default. -/
def PublicDefaultInput (input : ((reactiveApplication timeouts) leaks).Info) : Prop :=
  ∃ past view, input = some (past, view) ∧
    view.application.publicView.observation.defaulted ≠ ∅

/-- The public flag is visible exactly to the current decision maker, and
agrees with the native configuration independently of pending observations. -/
theorem publicDefaultInput_observe_iff (who : Player)
    (state : ((reactiveApplication timeouts) leaks).ProtocolState) :
    (PublicDefaultInput timeouts) leaks (((reactiveApplication timeouts) leaks).observe who state) ↔
      ((reactiveApplication timeouts) leaks).actor state = some who ∧
        (PublicDefault timeouts) leaks state := by
  cases state with
  | none => simp [PublicDefaultInput, PublicDefault, ReactiveApplication.observe,
      ReactiveApplication.actor]
  | some control =>
      by_cases active : control.actor = some who
      · have defaults : (control.execution.observe ((reactiveApplication timeouts) leaks)
            who).application.publicView.observation.defaulted =
          control.execution.application.config.defaulted := rfl
        simp [PublicDefaultInput, PublicDefault, ReactiveApplication.observe,
          ReactiveApplication.actor, active, defaults]
      · simp [PublicDefaultInput, PublicDefault, ReactiveApplication.observe,
          ReactiveApplication.actor, active]

variable (menu : ((reactiveApplication timeouts) leaks).ResponseMenu)
  (initial : PMF ((reactiveApplication timeouts) leaks).State) (horizon : Nat)
  (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)

local notation "N" => menu.information initial horizon scheduler
local notation "E" => menu.protocol initial horizon scheduler

/-- Public default persists through every supported native protocol transition. -/
theorem publicDefault_transition
    (before after : ((reactiveApplication timeouts) leaks).ProtocolState)
    (joint : Player → Option ((reactiveApplication timeouts) leaks).Action)
    (defaulted : (PublicDefault timeouts) leaks before)
    (realized : after ∈ (((reactiveApplication timeouts) leaks).transition initial horizon
      scheduler before joint).support) : (PublicDefault timeouts) leaks after := by
  cases before with
  | none => exact defaulted.elim
  | some current =>
      obtain ⟨next, nextEq, _⟩ :=
        ((reactiveApplication timeouts) leaks).transition_recall_prefix initial horizon scheduler
          current after joint realized
      rw [nextEq]
      change next.execution.application.config.defaulted ≠ ∅
      obtain ⟨owner, member⟩ := Finset.nonempty_iff_ne_empty.mpr defaulted
      exact Finset.ne_empty_of_mem
        ((reactiveApplication_defaulted_monotone timeouts leaks).transition initial horizon
          scheduler current next joint (nextEq ▸ realized) member)

/-- Every later legal history remains in the native public-default region. -/
theorem publicDefault_of_reaches {first last : (E).History}
    (reached : (E).HistoryReaches first last)
    (defaulted : (PublicDefault timeouts) leaks first.state) :
    (PublicDefault timeouts) leaks last.state := by
  obtain ⟨fuel, path⟩ := reached
  induction path with
  | refl => exact defaulted
  | step joint legal realized rest ih =>
      exact ih ((publicDefault_transition timeouts) leaks initial horizon scheduler _ _ joint
        defaulted realized)

/-- The flag holds throughout every history of a publicly defaulted information site. -/
theorem publicDefault_of_information {who : Player} (site : (N).InformationSite who)
    (flagged : (PublicDefaultInput timeouts) leaks site.1)
    (history : (N).InformationHistory who site.1) :
    (PublicDefault timeouts) leaks history.1.state := by
  have observed := ((menu).info initial horizon scheduler who history.1.trace).symm.trans
    history.2
  have actual := observed ▸ flagged
  exact (((publicDefaultInput_observe_iff timeouts) leaks who history.1.state).mp actual).2

open Classical in
/-- Restrict a whole deviation to the public-default inputs of the same native game. -/
def afterDefaultPolicy {who : Player} (baseline alternative : (N).BehavioralPolicy who) :
    (N).BehavioralPolicy who := fun input =>
  if (PublicDefaultInput timeouts) leaks input then alternative input else baseline input

variable [Finite Player]

/-- After public default, restricting an arbitrary whole deviation to that
region retains its complete actual terminal continuation law. -/
theorem run_afterDefaultPolicy_eq (certificate : (E).WellFoundedHistories)
    (profile : ∀ player, (N).BehavioralPolicy player) {who : Player}
    (alternative : (N).BehavioralPolicy who) (history : (E).History)
    (defaulted : (PublicDefault timeouts) leaks history.state) :
    (N).runBehavioralTerminalFrom certificate
        (Profile.update (sig := (N).behavioralSignature) profile who alternative) history =
      (N).runBehavioralTerminalFrom certificate
        (Profile.update (sig := (N).behavioralSignature) profile who
          ((afterDefaultPolicy timeouts) leaks menu initial horizon scheduler (profile who)
            alternative)) history := by
  apply (N).runBehavioralTerminalFrom_congr certificate history
  intro later reached _nonterminal player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    by_cases active : (E).active later.state who
    · have persists := (publicDefault_of_reaches timeouts) leaks menu initial horizon scheduler
        reached defaulted
      have observed : (PublicDefaultInput timeouts) leaks ((N).infoOf who later.trace) := by
        have actual := ((publicDefaultInput_observe_iff timeouts) leaks who later.state).mpr
          ⟨active, persists⟩
        exact (menu.info initial horizon scheduler who later.trace).symm ▸ actual
      simp only [afterDefaultPolicy, observed, ↓reduceIte]
    · exact (N).behavioral_eq_of_not_active _ _ later.trace active
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

/-- The restriction retains the continuation value on the entire information
fiber, including histories the assessment assigns probability zero. -/
theorem value_afterDefaultPolicy_eq (certificate : (E).WellFoundedHistories)
    (assessment : (N).BehavioralAssessment) {who : Player} (site : (N).InformationSite who)
    (flagged : (PublicDefaultInput timeouts) leaks site.1) (payoff : (E).History → ℝ)
    (alternative : (N).BehavioralPolicy who) :
    (assessment.continuationContext certificate site payoff).value alternative =
      (assessment.continuationContext certificate site payoff).value
        ((afterDefaultPolicy timeouts) leaks menu initial horizon scheduler
          (assessment.strategy who) alternative) := by
  rw [BehavioralAssessment.continuationContext_value,
    BehavioralAssessment.continuationContext_value]
  apply congrArg (fun law : PMF (E).History => expect law payoff)
  apply bind_congr_on_support
  intro history _supported
  exact (run_afterDefaultPolicy_eq timeouts) leaks menu initial horizon scheduler certificate
    assessment.strategy alternative history.1
    ((publicDefault_of_information timeouts) leaks menu initial horizon scheduler site flagged
      history)

open Classical in
/-- A consistent assessment locally optimal at every public-default site is
rational against every whole continuation policy at those sites. Local
optimality is an explicit completion obligation, with no source or utility-range premise. -/
theorem wholePolicyOptimal_of_publicDefault
    [Finite (E).History]
    (certificate : (E).WellFoundedHistories) (payoff : Player → (E).History → ℝ)
    (assessment : (N).BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      (menu.decisionRecall initial horizon scheduler).decisionInformationAntichain)
    (localOptimal : ∀ player (site : (N).InformationSite player),
      (PublicDefaultInput timeouts) leaks site.1 → ∀ law : PMF ((N).Choice player site.1),
        (assessment.continuationContext certificate site (payoff player)).value
            ((assessment.strategy player).withLaw site.1 law) ≤
          (assessment.continuationContext certificate site (payoff player)).value
            (assessment.strategy player))
    (who : Player) (site : (N).InformationSite who)
    (flagged : (PublicDefaultInput timeouts) leaks site.1)
    (alternative : (N).BehavioralPolicy who) :
    (assessment.continuationContext certificate site (payoff who)).value alternative ≤
      (assessment.continuationContext certificate site (payoff who)).value
        (assessment.strategy who) := by
  classical
  let restricted := (afterDefaultPolicy timeouts) leaks menu initial horizon scheduler
    (assessment.strategy who) alternative
  rw [(value_afterDefaultPolicy_eq timeouts) leaks menu initial horizon scheduler certificate
    assessment site flagged (payoff who) alternative]
  apply consistent.continuation_value_le_of_locallyOptimal (N)
    (menu.decisionRecall initial horizon scheduler)
    (fun player input law => (PublicDefaultInput timeouts) leaks input ∨
      law = assessment.strategy player input)
    payoff certificate ?_ who site restricted ?_
  · intro player later law allowed
    rcases allowed with defaulted | same
    · exact localOptimal player later defaulted law
    · rw [same, BehavioralPolicy.withLaw_eq_self]
  · intro later
    by_cases defaulted : (PublicDefaultInput timeouts) leaks later.1
    · exact Or.inl defaulted
    · exact Or.inr (ite_eq_right defaulted)

end Vegas.EventGraphRuntime
