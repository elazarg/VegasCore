module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ConditionedLedgerReach
public import Vegas.Game.ConditionedLedgerAssessment
public import Vegas.Game.ConditionedSourceEquilibrium
public import Vegas.Game.ClientAssessmentFidelity

@[expose] public section

/-! # Replay and prescribed decisions across locally observed components -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {Signal : Type*}
  {signal : State L setup.context → Signal}
  {timeouts : EventTimeouts setup.informationGraph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
  {scheduler : (application setup timeouts leaks).Scheduler} {horizon : Nat}
  {bounds : MessageBounds setup.informationGraph}
  (supported : ∀ key, key ∈ (setup.initialLaw.map signal).support)
  (read : Player → (application setup timeouts leaks).Info → Signal)
  (observed : ∀ draw ∈ setup.initialLaw.support,
    ∀ execution : (application setup timeouts leaks).Execution,
    State.Invariant (graph := setup.informationGraph) (setup.eventInputs draw)
      execution.application → ∀ who,
      read who (some (execution.logs who, execution.observe (application setup timeouts leaks)
        who)) = signal draw)

local notation "raw" => bounds.rawMenu timeouts leaks
local notation "one" => bounds.onePacketMenu timeouts leaks
local notation "fullLaw" => Vegas.initialLaw setup
local notation "part" => fun k => setup.conditionInitial signal k
local notation "law" => fun k => Vegas.initialLaw (setup.conditionInitial signal k)

/-- At a genuine global site, every raw history has one component history with identical
controls, actions, and observations. -/
def ledger_componentHistoryEquiv {who : Player}
    (site : ((raw).information fullLaw horizon scheduler).InformationSite who) :
    ((raw).information (law (read who site.1)) horizon scheduler).InformationHistory who site.1 ≃
      ((raw).information fullLaw horizon scheduler).InformationHistory who site.1 :=
  Equiv.ofBijective ((raw).infoHistoryOfInitialSupportSubset
    (setup.conditionInitial_ledgerSupport signal _ (supported _)) who site.1)
    ⟨(raw).infoHistoryOfInitialSupportSubset_injective _ who site.1,
      ledgerInfoHistory_component_surjective (raw) supported read observed who site⟩

/-- Normalize and replay in the unique observed component, then retain the entire intended
history under the original joint prior. -/
def componentReplay {who : Player}
    (site : ((raw).information fullLaw horizon scheduler).InformationSite who)
    (history : ((raw).information fullLaw horizon scheduler).InformationHistory who site.1) :
    Option setup.intendedProtocol.History :=
  let key := read who site.1
  let localHistory := (ledger_componentHistoryEquiv supported read observed site).symm history
  (rawIntendedHistory? (part key) timeouts leaks bounds horizon scheduler localHistory.1).map
    (setup.conditionInitial_history signal key (supported key))

variable (inside : ∀ key who
    (site : (setup.conditionInitial signal key).intendedModel.InformationSite who)
    (h : setup.intendedModel.InformationHistory who site.1),
    setup.initialComponent signal key h.1.state)
  {Parameter : Type} {parameter : State L setup.context → Parameter}
  {utility : Parameter × PublicOutcome setup.program → Player → ℝ} {exit : Player → ℝ}
  {spec : ∀ k, ClientSpec (setup.conditionInitial signal k) timeouts leaks bounds horizon scheduler
    parameter utility exit}
  (intended : setup.intendedModel.BehavioralAssessment)
  (compiled : ∀ k, ClientCompilation (spec k)
    (setup.conditionInitial_assessment signal k (supported k) (inside k) intended))

/-- At every matching forced decision, including repeated turns and zero-probability
sites, replay of the glued raw assessment's belief gives the original intended posterior. -/
theorem componentAssessment_belief_replay {who : Player}
    (site : ((raw).information fullLaw horizon scheduler).InformationSite who)
    (source : (part (read who site.1)).intendedModel.InformationSite who)
    (native : ((one).information (law (read who site.1)) horizon scheduler).InformationSite who)
    (matched : ((reactiveNormalization timeouts) leaks).site (raw)
      (bounds.rawMenu_recall timeouts leaks) (law (read who site.1)) horizon scheduler who
      (ledger_componentSite (raw) supported read observed who site) =
        (bounds.onePacketRestriction timeouts leaks (law (read who site.1)) horizon scheduler).site
          who native)
    (projected : source.1 = projectView (part (read who site.1)) timeouts leaks who native.1)
    (forced : forcedAgent (setup := part (read who site.1)) (timeouts := timeouts)
      (one) (law (read who site.1)) horizon scheduler
      who native.1)
    {past view} (shown : native.1 = some (past, view))
    {event} (turn : view.application.publicView.ownTurn? who = some event) :
    ((ledger_componentAssessment (raw) supported read observed
      (fun k => (compiled k).assessment)).belief who site).map
        (componentReplay supported read observed site) =
      (intended.belief who
        (setup.conditionInitial_informationSite signal _ (supported _) source)).map
          (fun h => some h.1) := by
  let key := read who site.1
  let equiv := ledger_componentHistoryEquiv supported read observed site
  let localSite := ledger_componentSite (raw) supported read observed who site
  let replay := fun h : ((raw).information (law key) horizon scheduler).InformationHistory
      who site.1 => rawIntendedHistory? (part key) timeouts leaks bounds horizon scheduler h.1
  let embed := setup.conditionInitial_history signal key (supported key)
  have localLaw := (compiled key).raw_belief_replay source native localSite matched
    projected forced shown turn
  have sourceLaw := setup.conditionInitial_assessment_belief_map signal key (supported key)
    (inside key) intended who source
  calc
    _ = (((compiled key).assessment.belief who localSite).map replay).map (Option.map embed) := by
      change ((((compiled key).assessment.belief who localSite).map equiv).map
        (fun h => (replay (equiv.symm h)).map embed)) = _
      simp only [PMF.map_comp, Function.comp_def, Equiv.symm_apply_apply]
      rfl
    _ = _ := by
      rw [show ((compiled key).assessment.belief who localSite).map replay = _ from localLaw]
      rw [← sourceLaw, PMF.map_comp, PMF.map_comp]
      rfl

omit [Fintype Player] in
/-- Every original intended decision, including an unreached one, is the identical
view of a genuine decision under one supported component initializer. -/
theorem conditionInitial_sourceSite_covered {who : Player}
    (site : setup.intendedModel.InformationSite who) :
    ∃ (key : Signal) (localSite : (part key).intendedModel.InformationSite who),
      setup.conditionInitial_informationSite signal key (supported key) localSite = site := by
  obtain ⟨h, running, action, allowed⟩ := site.2
  cases atState : h.1.state with
  | none =>
    have active := InformationModel.InformationSite.active (M := setup.intendedModel) site h
    rw [atState] at active
    exact active.elim
  | some point =>
    let key := signal (ProtocolState.base setup.program point)
    have member : setup.initialComponent signal key h.1.state := by rw [atState]; rfl
    let t := setup.conditionInitial_historyOfComponent signal key (supported key) h.1 member
    have mapped : setup.conditionInitial_history signal key (supported key) t = h.1 :=
      setup.conditionInitial_history_historyOfComponent signal key (supported key) h.1 member
    have observedAt := setup.conditionInitial_history_observed signal key (supported key) t who
    rw [mapped] at observedAt
    let localSite : (part key).intendedModel.InformationSite who := ⟨site.1,
      ⟨⟨t, observedAt.symm.trans h.2⟩, running, action, by
        change some action ∈ (part key).intendedMenu who site.1
        rw [setup.conditionInitial_intendedMenu]
        exact allowed⟩⟩
    exact ⟨key, localSite, Subtype.ext rfl⟩

include compiled observed in
/-- Every intended site has a component one-packet realization and a genuine global raw
counterpart whose own information identifies that same component. -/
theorem componentAssessment_sourceSite_covered {who : Player}
    (source : setup.intendedModel.InformationSite who) :
    ∃ (key : Signal) (localSource : (part key).intendedModel.InformationSite who)
      (native : ((one).information (law key) horizon scheduler).InformationSite who)
      (localRaw : ((raw).information (law key) horizon scheduler).InformationSite who)
      (globalRaw : ((raw).information fullLaw horizon scheduler).InformationSite who),
      setup.conditionInitial_informationSite signal key (supported key) localSource = source ∧
      SourceDecisionRealization (part key) timeouts leaks bounds horizon scheduler localSource
        native ∧
      ((reactiveNormalization timeouts) leaks).site (raw) (bounds.rawMenu_recall timeouts leaks)
        (law key) horizon scheduler who localRaw =
          (bounds.onePacketRestriction timeouts leaks (law key) horizon scheduler).site who native ∧
      globalRaw.1 = localRaw.1 ∧ read who globalRaw.1 = key := by
  obtain ⟨key, localSource, same⟩ := conditionInitial_sourceSite_covered supported source
  obtain ⟨native, realized⟩ := (compiled key).refinement.fidelity.coverage localSource
  obtain ⟨localRaw, represented⟩ := (compiled key).refinement.rawSites who native
  obtain ⟨h, running, action, allowed⟩ := localRaw.2
  let lift := (raw).infoHistoryOfInitialSupportSubset (scheduler := scheduler) (horizon := horizon)
    (setup.conditionInitial_ledgerSupport signal key (supported key)) who localRaw.1
  let globalRaw : ((raw).information fullLaw horizon scheduler).InformationSite who :=
    ⟨localRaw.1, ⟨lift h, running, action, by
      rw [← (raw).information_menu_initial_eq (restricted := law key)]
      exact allowed⟩⟩
  refine ⟨key, localSource, native, localRaw, globalRaw, same, realized, represented, rfl, ?_⟩
  have active := InformationModel.InformationSite.active
    (M := (raw).information (law key) horizon scheduler) localRaw h
  have seen := ledger_component_active_read (raw) read observed (supported key) h.1.trace who active
  have viewEq := ((raw).info (law key) horizon scheduler who h.1.trace).symm.trans h.2
  exact (congrArg (read who) viewEq.symm).trans seen

/-- Every original intended information site, even if it has zero probability, has a
global raw counterpart whose actual posterior replays to the supplied intended posterior. -/
theorem componentAssessment_source_belief_covered {who : Player}
    (source : setup.intendedModel.InformationSite who) :
    ∃ site : ((raw).information fullLaw horizon scheduler).InformationSite who,
      ((ledger_componentAssessment (raw) supported read observed
        (fun k => (compiled k).assessment)).belief who site).map
          (componentReplay supported read observed site) =
        (intended.belief who source).map (fun h => some h.1) := by
  obtain ⟨key, localSource, native, localRaw, globalRaw, sourceEq, realization,
    normalized, rawEq, keyEq⟩ :=
    componentAssessment_sourceSite_covered supported read observed inside intended compiled source
  subst key
  have siteEq : ledger_componentSite (raw) supported read observed who globalRaw = localRaw :=
    Subtype.ext rawEq
  obtain ⟨past, view, event, shown, pending, _⟩ := realization.first
  rw [shown] at pending
  have turn := (pendingEvent_spec pending).1
  rw [← sourceEq]
  exact ⟨globalRaw, componentAssessment_belief_replay supported read observed inside intended
    compiled globalRaw localSource native (siteEq.symm ▸ normalized) realization.projected
      realization.forced shown turn⟩

private theorem conditionInitial_honestChoice (key : Signal) (who : Player)
    (info : (application setup timeouts leaks).Info) :
    honestChoice (part key) timeouts leaks bounds (law key) horizon scheduler
      (setup.conditionInitial_assessment signal key (supported key) (inside key) intended)
      who info =
      honestChoice setup timeouts leaks bounds (law key) horizon scheduler intended who info := by
  cases info with
  | none => rfl
  | some pair =>
    obtain ⟨past, view⟩ := pair
    cases turn : view.application.publicView.ownTurn? who with
    | none => simp only [honestChoice, honestResponse, turn]; rfl
    | some event =>
      have source := setup.conditionInitial_policy_map_val signal key who (intended.strategy who)
        (projectView setup timeouts leaks who (some (past, view)))
      have choices : asIfHonestProfile (part key) timeouts leaks
          (setup.conditionInitial_assessment signal key (supported key) (inside key) intended)
          who (some (past, view)) =
          asIfHonestProfile setup timeouts leaks intended who (some (past, view)) := source
      simp only [honestChoice, honestResponse, turn, choices]
      simp only [conditionInitial]
      congr 1
      apply map_congr_on_support
      intro choice _
      cases choice with
      | none => rfl
      | some action =>
        simp only [Option.bind_some]
        cases chosen : encodeEventAction? setup.program event action <;> rfl

/-- At a genuine first source decision, the glued raw client's normalized choice has
exactly the canonical action law of the original intended assessment. -/
theorem componentAssessment_first_decision (who : Player)
    (past : List (application setup timeouts leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView)
    (source : (part (read who (some (past, view)))).intendedModel.InformationSite who)
    (native : ((one).information (law (read who (some (past, view)))) horizon
      scheduler).InformationSite who)
    (realization : SourceDecisionRealization (part (read who (some (past, view)))) timeouts leaks
      bounds horizon scheduler source native)
    (matched : ((reactiveNormalization timeouts) leaks).info who (some (past, view)) =
      (bounds.onePacketRestriction timeouts leaks (law (read who (some (past, view)))) horizon
        scheduler).information who native.1) :
    let key := read who (some (past, view))
    let client := (raw).decodeProfile fullLaw horizon scheduler
      (ledger_componentAssessment (raw) supported read observed
        (fun k => (compiled k).assessment)).strategy who
    (((raw).restrictPolicy (law key) horizon scheduler who client) (some (past, view))).map
      (fun choice => Eq.mp (congrArg (((bounds.menu timeouts leaks).information (law key) horizon
        scheduler).Choice who) matched)
          (((reactiveNormalization timeouts) leaks).choice (raw) (bounds.rawMenu_recall timeouts
            leaks) (law key) horizon scheduler who (some (past, view)) choice)) =
      (honestChoice setup timeouts leaks bounds (law key) horizon scheduler intended who
        native.1).map
          ((bounds.onePacketRestriction timeouts leaks (law key) horizon scheduler).choice who
            native.1) := by
  dsimp only
  let key := read who (some (past, view))
  let global := ledger_componentAssessment (raw) supported read observed
    (fun k => (compiled k).assessment)
  have same : (raw).decodeProfile fullLaw horizon scheduler global.strategy who past view =
      (compiled key).clients who past view := rfl
  rw [(raw).restrictPolicy_congr_at _ _ _ _ _ _ past view same]
  exact ((compiled key).clients_strategy_at_sourceDecision source native realization
    _ matched).trans (congrArg (PMF.map _)
      (conditionInitial_honestChoice supported inside intended key who native.1))

end Vegas.SourceProgram.Setup
