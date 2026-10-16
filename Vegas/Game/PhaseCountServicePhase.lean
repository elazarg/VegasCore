/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServiceEpisode
import Vegas.Pending.PhaseAttemptReceiptSnapshot
import Interaction.ReactiveMenuLikelihood
import Interaction.ReactiveRecallEntries
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay

/-! # Original phase survival under quantified private service -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

section PhaseSurvival

variable
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (phaseApplication runtime leaks).PlayerEntry → (phaseApplication runtime
      leaks).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent (serviceGraph setup mode) → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (horizon : Nat) (tapes : PhaseSeedAddress (serviceGraph setup mode) → Fin horizon → Bool × Bool)
  (plan : RuntimePhasePlan (serviceGraph setup mode)) (ordered : (serviceGraph setup
      mode).RevealRelaxedOrdered)
  (inputs : PMF (serviceGraph setup mode).Inputs)
  {LocalSeed RestSeed : Type}
  (seedLaw : PMF (RestSeed × (PhaseSeedAddress (serviceGraph setup mode) → LocalSeed)))
  (family : (RestSeed × (PhaseSeedAddress (serviceGraph setup mode) → LocalSeed)) →
      (phaseApplication runtime leaks).Scheduler)
  (calendar : PhaseService.PrivateActivationCalendar runtime leaks bounds plan inputs horizon
    seedLaw family)
  (privateSuccess : PhaseService.PrivateBindingSuccess runtime leaks bounds plan inputs horizon
    seedLaw family)
  (capacity : horizon ≤ bounds.candidateCount)
  (catalogue : ∀ owner event payload (_binding : (serviceGraph setup mode).outputLayout event =
      .binding owner payload),
    ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "rawWeight" => (0 : ℝ)
local notation "rawNonnegative" => (le_refl (0 : ℝ))
local notation "rawBounded" => (zero_le_one (α := ℝ))
local notation "Q" => phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes

local notation "originalTapes" => independentProduct (fun _coordinate : PhaseSeedAddress graph =>
  independentProduct (fun index : Fin horizon => PhaseCount.bindingServiceCoinLaw failure timing
    firstNonnegative firstBounded timingNonnegative timingBounded rawWeight rawNonnegative
      rawBounded (Fin.val index)))

/-- Every original zero-RAW table draw has false RAW flags at every address
and ordinal; the original timing coordinates are retained unchanged. -/
private theorem original_tapes_no_raw (supported : tapes ∈ (originalTapes).support) :
    ∀ coordinate index, (tapes coordinate index).1 = false := by
  intro coordinate index
  have address := (independentProduct_support_iff _ tapes).mp supported coordinate
  have coin := (independentProduct_support_iff _ (tapes coordinate)).mp address index
  have marginal : (PhaseCount.bindingServiceCoinLaw failure timing firstNonnegative firstBounded
      timingNonnegative timingBounded rawWeight rawNonnegative rawBounded index.val).map Prod.fst =
        PMF.pure false := by
    simp only [PhaseCount.bindingServiceCoinLaw, mix_zero, PMF.pure_bind, PMF.map_comp,
      Function.comp_def]
    exact PMF.map_const _ _
  have observed : (tapes coordinate index).1 ∈ (PMF.pure false : PMF Bool).support := by
    rw [← marginal]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨tapes coordinate index, coin, rfl⟩
  exact (PMF.mem_support_pure_iff _ _).mp observed

include ordered in
/-- A true receipt in the actual immutable prescription recovers a genuine
old-coordinate request, even after immediate normalization and restoration. -/
private theorem receipt_request_origin
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (remaining : Nat) (execution : (app).Execution)
    (trace : ((menu).protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout coordinate.1.event = .binding owner payload)
    (consistent : (Q owner).Consistent (execution.recall owner))
    (accepted : PhaseService.BindingAccepted runtime leaks coordinate.1 owner execution) :
    ∃ (before : (app).Control)
      (prior : ((menu).protocol initial horizon (family seeds)).Trace (some before)),
      TracePrefix prior trace ∧ before.execution.application.SeedRequest owner coordinate.1 := by
  classical
  obtain ⟨message, input, sender, attempt, event, _receipt⟩ := accepted
  have recalled := (app).history_inputRecall initial horizon (family seeds)
    ((menu).toRawTrace initial horizon (family seeds) trace)
  have authored : message ∈ (app).outputs (execution.recall owner) := by
    rw [← recalled owner]
    exact List.mem_filter.mpr ⟨input, by simp only [sender, decide_true]⟩
  have named : PhaseCount.event? message.payload = some coordinate.1 := by
    simp only [PhaseCount.event?, event, Option.map_some, attempt]
  have localConsistent := phaseCountServiceTapePolicy_local_consistent setup mode runtime leaks
    bounds values choose failure timing firstNonnegative firstBounded timingNonnegative
    timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
    horizon tapes plan inputs (family seeds) ⟨remaining, none, execution⟩ trace coordinate
      owner
    payload binding consistent
  obtain ⟨before, prior, _action, retained, _active, request, _rest⟩ :=
    PhaseCount.bindingServiceTapeMember_emission_origin runtime leaks bounds plan ordered inputs
      horizon (family seeds) (Q owner) owner coordinate.1 payload
      (fun past view => (values owner coordinate.1.event payload binding past view).map
        PublicationResult.success)
      (choose owner coordinate.1) failure timing firstNonnegative firstBounded timingNonnegative
      timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
      (tapes coordinate) remaining execution trace localConsistent message authored named
  exact ⟨before, prior, retained, request⟩

/-- Actual supported continuation of the restricted complete prescription
preserves the original member's complete own recall. Old entry recall is
retained and only the genuinely new response suffix is checked. -/
private theorem continuation_consistent
    (scheduler : (app).Scheduler)
    (profile : ∀ who, ((menu).information initial horizon scheduler).BehavioralPolicy who)
    (start final : (app).Control)
    (entry : ((menu).protocol initial horizon scheduler).Trace (some start))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some final))
    (stopped : ((menu).protocol initial horizon scheduler).History → Prop)
    (supported : ⟨some final, trace⟩ ∈
      (((menu).information initial horizon scheduler).runBehavioralUntil
        ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
          ⟨some start, entry⟩).support)
    (owner : Player)
    (follows : profile owner = (menu).restrictPolicy initial horizon scheduler owner (Q owner))
    (atEntry : (Q owner).Consistent (start.execution.recall owner)) :
    (Q owner).Consistent (final.execution.recall owner) := by
  classical
  let E := (menu).protocol initial horizon scheduler
  let N := (menu).information initial horizon scheduler
  have kept := N.runBehavioralUntil_support_prefix
    ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
      ⟨some start, entry⟩ ⟨some final, trace⟩ supported
  have first := N.runBehavioralUntil_support_first
    ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
      ⟨some start, entry⟩ ⟨some final, trace⟩ supported
  have halted := N.mem_support_runBehavioralUntil
    ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
      ⟨some start, entry⟩ ⟨some final, trace⟩ supported
  have atom := N.runBehavioralUntil_apply_of_first_hit
    ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
      ⟨some start, entry⟩ ⟨some final, trace⟩ kept halted first
  have positive : 0 < (N.runBehavioralFrom profile (trace.length - entry.length)
      ⟨some start, entry⟩ ⟨some final, trace⟩).toReal := by
    rw [← atom]
    exact pmf_toReal_pos_iff.mpr supported
  obtain ⟨records, recordEq, _provenance, chance, nonnegative, _natureMass, factor⟩ :=
    N.exists_continuation_ownPlay_factor entry trace kept
  rw [factor profile] at positive
  have productPositive : 0 < ∏ who, N.ownPlayReachProbability (profile who) (records who) :=
    pos_of_mul_pos_right positive nonnegative
  have ownNonzero : N.ownPlayReachProbability (profile owner) (records owner) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (ne_of_gt productPositive) owner (Finset.mem_univ owner)
  have ownPositive : 0 < N.ownPlayReachProbability (profile owner) (records owner) :=
    lt_of_le_of_ne (N.ownPlayReachProbability_nonneg _ _) ownNonzero.symm
  have mapPrefix : ∀ {before after} (prior : E.Trace before) (later : E.Trace after),
      TracePrefix prior later → TracePrefix ((menu).toRawTrace initial horizon scheduler prior)
        ((menu).toRawTrace initial horizon scheduler later) := by
    intro before after prior later prefixProof
    induction prefixProof with
    | refl => exact .refl
    | extend prefixProof actions legal moved ih =>
        exact TracePrefix.extend ih actions ((menu).legal_raw initial horizon scheduler legal) moved
  obtain ⟨suffix, suffixEq⟩ := (app).reaches_recall_prefix initial horizon scheduler
    (mapPrefix entry trace kept).reachesWithin start final rfl rfl owner
  have ownRecall {state} (history : E.Trace state) :
      N.ownPlay owner history = (app).recallOwnPlay ((app).recallAt owner state) := by
    change ((menu).signals initial horizon scheduler).ownPlay owner history = _
    rw [← (menu).ownPlay_toRawTrace initial horizon scheduler owner history, (app).trace_ownPlay]
  have actualRecords : records owner =
      (app).ownPlayFrom (start.execution.recall owner) suffix := by
    have equal : (app).recallOwnPlay (final.execution.recall owner) =
        List.append (records owner) ((app).recallOwnPlay (start.execution.recall owner)) :=
      (ownRecall trace).symm.trans ((recordEq owner).trans
        (congrArg (List.append (records owner)) (ownRecall entry)))
    change (app).ownPlayFrom [] (final.execution.recall owner) =
      List.append (records owner) ((app).ownPlayFrom [] (start.execution.recall owner)) at equal
    rw [← suffixEq, (app).ownPlayFrom_concat] at equal
    exact (List.append_cancel_right equal).symm
  rw [actualRecords, follows] at ownPositive
  have covered : ∀ past view response, response ∈ (Q owner past view).support →
      response ∈ (menu).actions owner past view := by
    intro past view response member
    exact phaseCountServiceTapePolicy_covered setup mode runtime leaks bounds values choose failure
      timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
      slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes owner past view response
      member
  have extend (suffix : List (app).PlayerEntry) :
      0 < N.ownPlayReachProbability
        ((menu).restrictPolicy initial horizon scheduler owner (Q owner))
          ((app).ownPlayFrom (start.execution.recall owner) suffix) →
      (Q owner).Consistent (start.execution.recall owner ++ suffix) := by
    induction suffix using List.reverseRecOn with
    | nil => exact fun _ => by simpa only [List.append_nil] using atEntry
    | append_singleton suffix response ih =>
        intro positive
        rw [(app).ownPlayFrom_append, InformationModel.ownPlayReachProbability] at positive
        have earlier := pos_of_mul_pos_right positive ENNReal.toReal_nonneg
        have responsePositive := pos_of_mul_pos_left positive
          (N.ownPlayReachProbability_nonneg _ _)
        rw [(menu).restrictPolicy_atom initial horizon scheduler owner (Q owner)
          (start.execution.recall owner ++ suffix) response.beforeView response.action
            (covered _ _)] at responsePositive
        exact (by
          simpa only [List.append_assoc] using
            ReactiveApplication.Policy.Consistent.snoc response (ih earlier)
              (pmf_toReal_pos_iff.mp responsePositive))
  rw [← suffixEq]
  exact extend suffix ownPositive

include ordered calendar privateSuccess capacity catalogue in
/-- The actual normalized proper-domain prescription has the same entire
foreign survivor vector at the original phase boundary under any two focal
continuations with the same original foreign event seeds and timing tapes.
The quantified full calendar and packet success law supply the service facts.
The original zero-RAW prior support derives that every tape RAW flag is false;
no post-RAW claim is made. The boundary
includes focal-triggered retry and exhausted restoration, and actual immutable
member support is required only at the original entry and derived at the boundary. -/
theorem phaseCountServiceTapePolicy_foreign_survival_iff
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (firstSupport : firstSeeds ∈ seedLaw.support) (secondSupport : secondSeeds ∈ seedLaw.support)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (firstContract : PhaseService.AsyncContract runtime leaks initial horizon (family firstSeeds)
      delay bound)
    (secondContract : PhaseService.AsyncContract runtime leaks initial horizon (family secondSeeds)
      delay bound)
    (firstProfile : ∀ who, ((menu).information initial horizon
      (family firstSeeds)).BehavioralPolicy who)
    (secondProfile : ∀ who, ((menu).information initial horizon
      (family secondSeeds)).BehavioralPolicy who)
    (start first second : (app).Control)
    (firstStart : ((menu).protocol initial horizon (family firstSeeds)).Trace (some start))
    (secondStart : ((menu).protocol initial horizon (family secondSeeds)).Trace (some start))
    (firstTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace (some first))
    (secondTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace (some second))
    (phase : RuntimePhase graph) (installed : phase ∈ start.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (focal : Player)
    (firstRun : ⟨some first, firstTrace⟩ ∈
      (((menu).information initial horizon (family firstSeeds)).runBehavioralUntil
        ((menu).bounded initial horizon (family firstSeeds)).wellFoundedHistories firstProfile
        (fun history => match history.state with
          | none => False
          | some control => control.execution.application.attempt ≠
      start.execution.application.attempt)
        ⟨some start, firstStart⟩).support)
    (secondRun : ⟨some second, secondTrace⟩ ∈
      (((menu).information initial horizon (family secondSeeds)).runBehavioralUntil
        ((menu).bounded initial horizon (family secondSeeds)).wellFoundedHistories secondProfile
        (fun history => match history.state with
          | none => False
          | some control => control.execution.application.attempt ≠
      start.execution.application.attempt)
        ⟨some start, secondStart⟩).support)
    (atEntry : ∀ owner, owner ≠ focal →
      (Q owner).Consistent (start.execution.recall owner))
    (firstFollows : ∀ owner, owner ≠ focal → firstProfile owner =
      (menu).restrictPolicy initial horizon (family firstSeeds) owner (Q owner))
    (secondFollows : ∀ owner, owner ≠ focal → secondProfile owner =
      (menu).restrictPolicy initial horizon (family secondSeeds) owner (Q owner))
    (tapeSupport : tapes ∈ (originalTapes).support)
    (sameSeeds : ∀ owner, owner ≠ focal → ∀ event ∈ phase.events, (serviceGraph setup mode).actor?
      event = some owner →
      ∀ bounded, firstSeeds.2 (⟨⟨start.execution.application.attempt, event⟩, bounded⟩) =
        secondSeeds.2 (⟨⟨start.execution.application.attempt, event⟩, bounded⟩)) :
    (∀ coordinate index, (tapes coordinate index).1 = false) ∧
      ∀ owner, owner ≠ focal → owner ∉ start.execution.application.current.excluded →
      (owner ∉ first.execution.application.current.excluded ↔
        owner ∉ second.execution.application.current.excluded) := by
  classical
  refine ⟨original_tapes_no_raw setup mode failure timing firstNonnegative firstBounded
    timingNonnegative timingBounded horizon tapes tapeSupport, ?_⟩
  intro owner foreign active
  have firstConsistent := continuation_consistent setup mode runtime leaks bounds values choose
    failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded horizon tapes plan inputs (family firstSeeds) firstProfile start
    first firstStart firstTrace _ firstRun owner (firstFollows owner foreign) (atEntry owner
      foreign)
  have secondConsistent := continuation_consistent setup mode runtime leaks bounds values choose
    failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded horizon tapes plan inputs (family secondSeeds) secondProfile start
    second secondStart secondTrace _ secondRun owner (secondFollows owner foreign) (atEntry owner
      foreign)
  have sameSeeds := sameSeeds owner foreign
  obtain ⟨firstEnd, firstState, firstChanged, firstIdle, _snapshot⟩ :=
    phase_attempt_stopped_receipt_snapshot runtime leaks menu plan inputs horizon (family
      firstSeeds)
      delay bound firstContract firstProfile start firstStart phase installed ⟨some first,
      firstTrace⟩ (by
        convert firstRun using 1; congr 3; funext history;
          cases history.state <;> rfl)
  cases Option.some.inj firstState
  obtain ⟨secondEnd, secondState, secondChanged, secondIdle, _snapshot⟩ :=
    phase_attempt_stopped_receipt_snapshot runtime leaks menu plan inputs horizon (family
      secondSeeds)
      delay bound secondContract secondProfile start secondStart phase installed ⟨some second,
      secondTrace⟩ (by
        convert secondRun using 1; congr 3; funext history;
          cases history.state <;> rfl)
  cases Option.some.inj secondState
  rcases first with ⟨firstRemaining, firstActor, firstExecution⟩
  change firstActor = none at firstIdle
  subst firstActor
  let first : (app).Control := ⟨firstRemaining, none, firstExecution⟩
  rcases second with ⟨secondRemaining, secondActor, secondExecution⟩
  change secondActor = none at secondIdle
  subst secondActor
  let second : (app).Control := ⟨secondRemaining, none, secondExecution⟩
  let firstIdleTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace
      (some ⟨first.remaining, none, first.execution⟩) := firstTrace
  let secondIdleTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace
      (some ⟨second.remaining, none, second.execution⟩) := secondTrace
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered plan draw
  have firstOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    (family firstSeeds) initialized ((menu).toRawTrace initial horizon (family firstSeeds)
      firstStart)
  have secondOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    (family secondSeeds) initialized ((menu).toRawTrace initial horizon (family secondSeeds)
      secondStart)
  have firstPrefix := ((menu).information initial horizon (family
      firstSeeds)).runBehavioralUntil_support_prefix
    ((menu).bounded initial horizon (family firstSeeds)).wellFoundedHistories firstProfile _
    ⟨some start, firstStart⟩ ⟨some first, firstTrace⟩ firstRun
  have secondPrefix := ((menu).information initial horizon (family
      secondSeeds)).runBehavioralUntil_support_prefix
    ((menu).bounded initial horizon (family secondSeeds)).wellFoundedHistories secondProfile _
    ⟨some start, secondStart⟩ ⟨some second, secondTrace⟩ secondRun
  have firstProgress := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
      horizon
    (family firstSeeds) start first firstStart firstTrace firstPrefix firstOrdered
  have secondProgress := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
      horizon
    (family secondSeeds) start second secondStart secondTrace secondPrefix secondOrdered
  have firstResolved (event : (serviceGraph setup mode).EventId) :
      (⟨start.execution.application.attempt, event⟩ : CommitAttemptEvent graph).Resolved
        first.execution.application := CommitAttemptEvent.Resolved.of_step _ _ _ rfl
          ⟨firstProgress.1, firstProgress.2.1⟩ (Or.inl (Ne.symm firstChanged))
  have secondResolved (event : (serviceGraph setup mode).EventId) :
      (⟨start.execution.application.attempt, event⟩ : CommitAttemptEvent graph).Resolved
        second.execution.application := CommitAttemptEvent.Resolved.of_step _ _ _ rfl
          ⟨secondProgress.1, secondProgress.2.1⟩ (Or.inl (Ne.symm secondChanged))
  have boundFor (event : (serviceGraph setup mode).EventId) (before : (app).Control)
      (prior : ((menu).protocol initial horizon (family firstSeeds)).Trace (some before))
      (request : before.execution.application.SeedRequest owner
        ⟨start.execution.application.attempt, event⟩) :
      start.execution.application.attempt.phase < (serviceGraph setup mode).order.eventCount ∧
        start.execution.application.attempt.generation ≤ Fintype.card Player := by
    have budget := (phaseApplication_seedBudget runtime leaks).history initial horizon
      (family firstSeeds) (fun state member => by
        obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
        exact PhaseRuntimeState.initial_seedBudget plan draw)
      ((menu).toRawTrace initial horizon (family firstSeeds) prior)
    exact (request.coordinate budget).2
  obtain ⟨_first, firstEq, firstReceipt⟩ := phase_attempt_stopped_survivor_iff_receipts runtime
      leaks
    menu plan inputs horizon (family firstSeeds) delay bound firstContract firstProfile start
      firstStart
    phase installed commitment ⟨some first, firstTrace⟩ (by
        convert firstRun using 1; congr 3; funext history;
          cases history.state <;> rfl)
  cases Option.some.inj firstEq
  obtain ⟨_second, secondEq, secondReceipt⟩ := phase_attempt_stopped_survivor_iff_receipts runtime
      leaks
    menu plan inputs horizon (family secondSeeds) delay bound secondContract secondProfile start
      secondStart
    phase installed commitment ⟨some second, secondTrace⟩ (by
        convert secondRun using 1; congr 3; funext history;
          cases history.state <;> rfl)
  cases Option.some.inj secondEq
  constructor
  · intro survived failed
    obtain ⟨event, inside, before, prior, _fromStart, retained, _same, request, absent⟩ :=
      PhaseService.phase_attempt_stopped_exclusion_unaccepted runtime leaks menu plan inputs horizon
        (family secondSeeds) secondProfile start secondStart phase installed commitment owner active
        ⟨some second, secondTrace⟩ (by
        convert secondRun using 1; congr 3; funext history;
          cases history.state <;> rfl) second rfl failed
    have accepted := (firstReceipt owner active).mp survived event inside request.2.2.2.1
    have bounded : start.execution.application.attempt.phase < (serviceGraph setup
      mode).order.eventCount ∧
        start.execution.application.attempt.generation ≤ Fintype.card Player := by
      have budget := (phaseApplication_seedBudget runtime leaks).history initial horizon
        (family secondSeeds) (fun state member => by
          obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
          exact PhaseRuntimeState.initial_seedBudget plan draw)
        ((menu).toRawTrace initial horizon (family secondSeeds) prior)
      exact (request.coordinate budget).2
    let coordinate : PhaseSeedAddress graph := ⟨⟨start.execution.application.attempt, event⟩,
      bounded⟩
    have ranks := (phase.mem_events event).mp inside
    obtain ⟨who, payload, layout⟩ := commitment ▸ phase.fields event ranks.1 ranks.2
    have same : who = owner := Option.some.inj
      ((actor?_of_outputLayout_binding graph layout).symm.trans request.2.2.2.1)
    subst who
    have ready := receipt_request_origin setup mode runtime leaks bounds values choose failure
      timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
      slotNonnegative
      slotBounded horizon tapes plan ordered inputs family firstSeeds first.remaining
      first.execution firstIdleTrace owner coordinate payload layout firstConsistent accepted
    have success := phaseCountServiceTapePolicy_accepted_iff_of_resolved setup mode runtime leaks
      bounds values choose failure timing firstNonnegative firstBounded timingNonnegative
      timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
      horizon tapes plan ordered inputs seedLaw family calendar privateSuccess firstSeeds
      secondSeeds
      firstSupport secondSupport owner coordinate payload layout capacity
      (catalogue owner event payload layout) first.remaining second.remaining first.execution
      second.execution firstIdleTrace secondIdleTrace ready ⟨before, prior, retained, request⟩
      (firstResolved event) (secondResolved event) (sameSeeds event inside request.2.2.2.1 bounded)
      firstConsistent secondConsistent
    exact absent (success.mp accepted)
  · intro survived failed
    obtain ⟨event, inside, before, prior, _fromStart, retained, _same, request, absent⟩ :=
      PhaseService.phase_attempt_stopped_exclusion_unaccepted runtime leaks menu plan inputs horizon
        (family firstSeeds) firstProfile start firstStart phase installed commitment owner active
        ⟨some first, firstTrace⟩ (by
          convert firstRun using 1; congr 3; funext history;
            cases history.state <;> rfl) first rfl failed
    have accepted := (secondReceipt owner active).mp survived event inside request.2.2.2.1
    have bounded := boundFor event before prior request
    let coordinate : PhaseSeedAddress graph := ⟨⟨start.execution.application.attempt, event⟩,
      bounded⟩
    have ranks := (phase.mem_events event).mp inside
    obtain ⟨who, payload, layout⟩ := commitment ▸ phase.fields event ranks.1 ranks.2
    have same : who = owner := Option.some.inj
      ((actor?_of_outputLayout_binding graph layout).symm.trans request.2.2.2.1)
    subst who
    have ready := receipt_request_origin setup mode runtime leaks bounds values choose failure
      timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
      slotNonnegative
      slotBounded horizon tapes plan ordered inputs family secondSeeds second.remaining
      second.execution secondIdleTrace owner coordinate payload layout secondConsistent accepted
    have success := phaseCountServiceTapePolicy_accepted_iff_of_resolved setup mode runtime leaks
      bounds values choose failure timing firstNonnegative firstBounded timingNonnegative
      timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
      horizon tapes plan ordered inputs seedLaw family calendar privateSuccess firstSeeds
      secondSeeds
      firstSupport secondSupport owner coordinate payload layout capacity
      (catalogue owner event payload layout) first.remaining second.remaining first.execution
      second.execution firstIdleTrace secondIdleTrace ⟨before, prior, retained, request⟩ ready
      (firstResolved event) (secondResolved event) (sameSeeds event inside request.2.2.2.1 bounded)
      firstConsistent secondConsistent
    exact absent (success.mpr accepted)

end PhaseSurvival

end Vegas
