module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketOwnDisclosure
public import Vegas.Game.OnePacketBeliefWiring
public import Vegas.Game.OnePacketPooledMemberGains
public import Vegas.Game.OnePacketKeyedCommitmentComparisons
public import Vegas.Game.OnePacketStoppedValueComparison
public import Vegas.Game.OnePacketUnintendedValue
public import Vegas.Game.OnePacketIrregularBeliefBounds
public import GameTheoryExtensions.Analysis.Protocol.GainComparison
public import Vegas.Game.OnePacketOpeningUnique
public import Vegas.Game.OnePacketOpeningLaw
public import Vegas.Game.OnePacketPrescribedCompletion
public import Vegas.Game.OnePacketPooledGains

@[expose] public section

/-! # Native keyed local comparisons

Every pure keyed deviation is compared on the supplied native assessment.
The full terminal payoff and the debt-stopped payoff are related by the
checked vanishing native continuation error.
-/

noncomputable section

namespace Vegas.OnePacketComparison

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  {Public : Type*} {signal : State L setup.context → Public}

local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) (initialLaw setup) horizon scheduler
local notation "Menu" => bounds.onePacketMenu timeouts leaks
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup timeouts leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

open Classical in
private theorem late_main_value_sub_le
    [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (source : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) {who : Player}
    (site : (N).InformationSite who) (option : LateOption slots) (choice : (N).Choice who site.1)
    (main : lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler source who
      site.1 option = PMF.pure choice)
    (assessment : (N).BehavioralAssessment)
    {Outcome : Type*} (observe : (NP).History → Outcome) (utility : Outcome → Player → ℝ)
    {bound : ℝ} (bounded : ∀ final : (NP).History, |utility (observe final) who| ≤ bound) :
    |localValue (2 * horizon + 1) observe utility assessment site (PMF.pure choice) -
      localValue (2 * horizon + 1) observe utility assessment site
        (lateComponent setup timeouts leaks bounds (initialLaw setup) horizon scheduler source
          scale nonnegative le_one who site.1 option)| ≤ 6 * scale * bound := by
  let value := fun found : (N).Choice who site.1 =>
    localValue (2 * horizon + 1) observe utility assessment site (PMF.pure found)
  have valueBounded : ∀ found, |value found| ≤ bound := by
    intro found
    dsimp only [value]
    rw [localValue_eq_expect_localRun]
    exact expect_abs_le_of_bounded
      (by obtain ⟨final, _⟩ := (localRun (2 * horizon + 1) assessment site
        (PMF.pure found)).support_nonempty
          exact (abs_nonneg _).trans (bounded final)) bounded
  have affine : ∀ law : PMF ((N).Choice who site.1),
      localValue (2 * horizon + 1) observe utility assessment site law = expect law value := by
    intro law
    have linear := localValue_bind (2 * horizon + 1) observe utility assessment site
      ((Menu).bounded (initialLaw setup) horizon scheduler)
      ((Menu).decisionRecall (initialLaw setup) horizon scheduler).actsOnceWhereItMatters law
      PMF.pure
    simpa only [PMF.bind_pure] using linear
  have mainValue : expect (lateChoice setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler source who site.1 option) value = value choice := by rw [main, expect_pure]
  have near := abs_expect_slotTrembledChoice_sub_le (timeouts := timeouts) nonnegative le_one who
    site.1
    (lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler source who
      site.1 option)
    (PMF.pure (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      who site.1))
    (slotChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler source who site.1)
    value valueBounded (valueBounded choice) mainValue
  have component := affine (lateComponent setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler source scale nonnegative le_one who site.1 option)
  rw [component]
  exact (abs_sub_comm _ _).trans_le near

open Classical in
private theorem lateChoice_eq_pure_opening
    [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (source : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} {who : Player} (site : (N).InformationSite who)
    (notFree : ¬ Vegas.FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler ((N).agentAt
      site))
    (debtFree : SiteDebtFree setup timeouts leaks bounds horizon scheduler site)
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId}
    (pending : pendingEvent setup timeouts leaks who site.1 = some event)
    (choice : (N).Choice who site.1) {response : (application setup timeouts leaks).Action}
    (chosen : choice.1 = some response)
    (member : response ∈ bounds.onePacketActions timeouts leaks who past view)
    {material : (application setup timeouts leaks).Submission}
    (sends : response.transmission = some material)
    {handle : Handle (graph setup)} {raw : Raw L}
    (packet : material.call.packet = .opening event handle raw) (slot : Fin slots) :
    lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler source who
      site.1
      (some slot) = PMF.pure choice := by
  obtain ⟨native, seen, forced⟩ := forcedAgent_of_not_free setup timeouts leaks bounds
      (initialLaw setup) horizon
    scheduler notFree
  have owed := debtFree ⟨native, seen⟩
  obtain ⟨payload, binding, checks, outputEq, codeEq, node⟩ :=
    onePacket_opening_node (timeouts := timeouts) member sends packet
  obtain ⟨info, decision⟩ := site
  change info = some (past, view) at atSite
  subst atSite
  obtain ⟨state, trace⟩ := native
  change (onePacketInformation setup timeouts leaks bounds horizon scheduler).infoOf who
    trace =
    some (past, view) at seen
  rw [onePacket_infoOf] at seen
  cases state with
  | none => cases seen
  | some control =>
  rcases control with ⟨remaining, actor, execution⟩
  by_cases active : actor = some who
  swap
  · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
    cases seen
  subst active
  simp only [ReactiveApplication.observe, ↓reduceIte] at seen
  obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj seen)
  subst pastEq viewEq
  have turn := (pendingEvent_spec (timeouts := timeouts) (setup := setup) pending).1
  have resolves := disclosureResolves_of_debtFree (timeouts := timeouts) wellFormed trace who forced
    owed
  obtain ⟨disclosed, sendsDisclosure⟩ := Option.ne_none_iff_exists'.mp
    (resolves _ pending who payload binding checks outputEq codeEq node)
  have responseEq := onePacket_opening_eq_disclosure (timeouts := timeouts) trace who _ node
    disclosed sendsDisclosure
    response member material sends ((congrArg (Payload.event? (graph setup)) packet).trans rfl)
  have lateEq := lateChoice_reveal (timeouts := timeouts) source trace who _ turn node slot
  have choiceEq : choice = responseChoice setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler who _ ((canonicalServiceDecision timeouts) leaks who
        (execution.logs who) (execution.observe (application setup timeouts leaks) who) _
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)) := by
    rw [← responseEq]
    apply Subtype.ext
    rw [chosen]
    simp only [responseChoice, member, ↓reduceDIte]
  rw [choiceEq]
  exact lateEq



open Classical in
/-- Every pure keyed native deviation has vanishing gain or is bounded by an
original source deviation mixture under the same assessments. -/
theorem assembled_keyed_local_comparisons
    [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
    [Finite setup.intendedProtocol.History]
    [∀ player, DecidableEq ((N).InfoState player)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          bounds.candidateCount p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (targetSequence n)
      ((Menu).decisionRecall (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Opportunity timeouts leaks (initialLaw setup) horizon scheduler delay)
    (inclusion : ProtectedInclusion timeouts leaks (initialLaw setup) horizon scheduler bound)
    (timely : (AsyncTimely timeouts) delay bound)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (payoffBound : ℝ) (nonnegative : 0 ≤ payoffBound)
    (completes : CompletesPlay timeouts leaks (initialLaw setup) horizon scheduler)
    (payoffBounded : ∀ who (final : (NP).History),
      |exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state
        who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (upper : Player → ℝ) (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (pooled : ∀ n (alternative : ∀ p,
        PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          bounds.candidateCount p)) p,
      ∑ agent ∈ Finset.univ.filter
          (fun agent => onePacketPool setup timeouts leaks bounds (initialLaw setup) horizon
          scheduler agent = p),
        (if decision : (N).IsDecisionInfo agent.1 agent.2.1 then
          ((targetSequence n).continuationContext
              ((Menu).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
              ⟨agent.2.1, decision⟩
              (fun final => exclusionBase setup timeouts parameter utility excludedPayoff leaks
          final.state
                agent.1)).value
              (((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (onePacketPool setup timeouts leaks bounds (initialLaw setup)
          horizon scheduler
                  agent)).bind
                  (onePacketComponent setup timeouts leaks bounds (initialLaw setup) horizon
          scheduler (sequence n)
                    (scale n)
                    (positive n).le (le_one n) agent))) -
            ((targetSequence n).continuationContext
              ((Menu).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
              ⟨agent.2.1, decision⟩
              (fun final => exclusionBase setup timeouts parameter utility excludedPayoff leaks
          final.state
                agent.1)).value ((targetSequence n).strategy agent.1)
        else 0) ≤ 0) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ¬ OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ownedKeyed (FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler)
          (LateDeliveryAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler)
          ((N).agentAt site) →
        ∀ choice : (N).Choice who site.1,
          localGain (2 * horizon + 1) (fun final => final.state)
              (exclusionBase setup timeouts parameter utility excludedPayoff leaks)
                (targetSequence n) site
              (PMF.pure choice) ≤ error n ∨
          ∃ mixture : PMF (setup.intendedModel.AssessmentDeviation who),
            localGain (2 * horizon + 1) (fun final => final.state)
                (exclusionBase setup timeouts parameter utility excludedPayoff leaks)
                  (targetSequence n) site
                (PMF.pure choice) ≤
              expect mixture (intendedSiteGain setup parameter utility excludedPayoff (sequence
                n)) +
                error n := by
  let certificate := ((Menu).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  obtain ⟨memberError, memberLimit, members⟩ := assembled_pooled_member_gain_bounds setup timeouts
    leaks bounds horizon scheduler wellFormed independent observable sequence sourceMixed scale
    positive le_one scaleEq covers coversInputs capacity slots_pos weights targetSequence
          assembled mixed
    bayes opportunity inclusion timely completes parameter utility excludedPayoff payoffBound
    nonnegative payoffBounded excludedBounded readoutBounded upper le_upper below pooled
  obtain ⟨continuation, score, affineError, affineLimit, scoreUnit, affineValues⟩ :=
    assembled_keyed_component_value_bounds setup timeouts leaks bounds horizon scheduler
      wellFormed independent observable sequence sourceMixed scale positive le_one scaleEq covers
      coversInputs capacity slots_pos weights targetSequence assembled mixed bayes opportunity
          inclusion
      timely completes parameter utility excludedPayoff payoffBound nonnegative payoffBounded
      excludedBounded readoutBounded upper le_upper below
  obtain ⟨valueError, valueLimit, comparisonValues⟩ :=
    assembled_terminal_stopped_comparison_bounds setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff wellFormed independent observable sequence sourceMixed
      scale positive le_one scaleEq covers coversInputs capacity weights targetSequence assembled
      mixed bayes opportunity inclusion timely completes nonnegative payoffBounded excludedBounded
  obtain ⟨nativeError, nativeLimit, nativeCommitments⟩ :=
    assembled_keyed_commitment_comparisons setup timeouts leaks bounds horizon scheduler
      wellFormed independent observable covers coversInputs capacity slots_pos sequence sourceMixed
      sourceBayes scale positive le_one scaleEq weights targetSequence assembled mixed bayes
      (fun control trace _ => opportunity control
        ((Menu).toRawTrace (initialLaw setup) horizon scheduler trace))
      (fun control trace _ => inclusion control
        ((Menu).toRawTrace (initialLaw setup) horizon scheduler trace)) timely
      (fun control trace _ ended => completes control
        ((Menu).toRawTrace (initialLaw setup) horizon scheduler trace) ended)
      parameter utility excludedPayoff nonnegative readoutBounded excludedBounded
  obtain ⟨irregularError, irregularLimit, irregular⟩ := irregular_belief_bounds_of_assembled
    setup timeouts leaks bounds horizon scheduler wellFormed independent observable sequence
    sourceMixed scale positive le_one scaleEq covers coversInputs capacity weights targetSequence
    assembled mixed bayes
  have scaleLimit : Tendsto scale atTop (nhds 0) := by
    have identity : scale = fun n => trembleScale
        (combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n))
        (2 * horizon + 2) n := funext scaleEq
    rw [identity]
    exact tendsto_trembleScale _
      (fun n => combinedFloor_pos setup timeouts leaks bounds horizon scheduler (sequence n))
      (fun n => combinedFloor_le_one setup timeouts leaks bounds horizon scheduler (sequence
        n))
  let error := fun n => |nativeError n| + |memberError n| + 2 * |valueError n| +
    |affineError n| + 2 * payoffBound * |irregularError n| + 6 * scale n * payoffBound
  have errorLimit : Tendsto error atTop (nhds 0) := by
    simpa only [error, abs_zero, zero_mul, mul_zero, add_zero, zero_add] using
      (((((nativeLimit.abs.add memberLimit.abs).add (valueLimit.abs.const_mul 2)).add
        affineLimit.abs).add (irregularLimit.abs.const_mul (2 * payoffBound))).add
          ((scaleLimit.const_mul 6).mul_const payoffBound))
  refine ⟨error, errorLimit, ?_⟩
  intro n who site notFree notOwing keyed choice
  have positiveTerms : 0 ≤ 2 * payoffBound * |irregularError n| ∧
      0 ≤ 6 * scale n * payoffBound := by
    have := (positive n).le
    constructor <;> positivity
  obtain ⟨nativePast, nativeView, nativeEvent, nativeAt, nativePending, _old⟩ := keyed.1
  let nativeSite := site
  let nativeChoice := choice
  have nativeNotFree := notFree
  have nativeNotOwing := notOwing
  have nativeKeyed := keyed
  let decision := site.2
  let target := targetSequence n
  let common := target.strategy
  let stopped := fun final : (NP).History => ¬ Clear final.state ∨
    DecodedState setup timeouts leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure who setup.program) final.state
  let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
    exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state who
  let stoppedValue := fun law => expect (target.belief who nativeSite) (fun history =>
    expect ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) common who
        ((common who).withLaw nativeSite.1 law)) stopped history.1) payoff)
  let terminalValue := fun law => localValue (2 * horizon + 1) (fun final => final.state)
    (exclusionBase setup timeouts parameter utility excludedPayoff leaks) (targetSequence n)
      site law
  let optionLaw := fun option : LateOption bounds.candidateCount => lateComponent setup timeouts
    leaks bounds (initialLaw setup) horizon scheduler (sequence n) (scale n)
    (positive n).le (le_one n) who site.1 option
  have pendingAt := nativePending
  rw [nativeAt] at pendingAt
  have values := (comparisonValues n who site notFree notOwing nativeAt
    (pendingEvent_spec (timeouts := timeouts) pendingAt).1).1
  have pureNear := values (PMF.pure choice)
  change |terminalValue (PMF.pure choice) - stoppedValue (PMF.pure nativeChoice)| ≤ valueError n
    at pureNear
  have optionNear : ∀ option, |terminalValue (optionLaw option) -
      stoppedValue (optionLaw option)| ≤ valueError n := by
    intro option
    exact values (optionLaw option)
  have memberAt : ∀ option,
      localGain (2 * horizon + 1) (fun final => final.state)
        (exclusionBase setup timeouts parameter utility excludedPayoff leaks) (targetSequence n)
          site
        (optionLaw option) ≤ memberError n := by
    intro option
    exact lateComponent_gain_le_of_member_mixtures setup timeouts leaks bounds horizon scheduler
      parameter
      utility excludedPayoff (targetSequence n) (sequence n) (scale n) (positive n).le (le_one
          n) site
      keyed (members n who site) option
  have viaNative : ∀ option,
      localGain (2 * horizon + 1) (fun final => final.state)
          (exclusionBase setup timeouts parameter utility excludedPayoff leaks)
            (targetSequence n) site
          (PMF.pure choice) ≤ stoppedValue (PMF.pure nativeChoice) -
        stoppedValue (optionLaw option) + 2 * valueError n + memberError n := by
    intro option
    have nativeNear := optionNear option
    have member := memberAt option
    rw [localGain_eq_sub] at member ⊢
    change terminalValue (optionLaw option) - _ ≤ _ at member
    change terminalValue (PMF.pure choice) - _ ≤ _
    linarith [(abs_le.mp pureNear).2, (abs_le.mp nativeNear).1]
  have viaMain : ∀ (option : LateOption bounds.candidateCount),
      lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler (sequence
        n) who
        nativeSite.1 option = PMF.pure nativeChoice →
      localGain (2 * horizon + 1) (fun final => final.state)
          (exclusionBase setup timeouts parameter utility excludedPayoff leaks)
            (targetSequence n) site
          (PMF.pure choice) ≤ 6 * scale n * payoffBound + memberError n := by
    intro option main
    have near := late_main_value_sub_le setup timeouts leaks bounds horizon scheduler (sequence n)
      (scale n) (positive n).le (le_one n) site option choice main (targetSequence n)
      (fun final => final.state)
      (exclusionBase setup timeouts parameter utility excludedPayoff leaks) (payoffBounded who)
    change |terminalValue (PMF.pure choice) - terminalValue (optionLaw option)| ≤
      6 * scale n * payoffBound at near
    have member := memberAt option
    rw [localGain_eq_sub] at member ⊢
    change terminalValue (optionLaw option) - _ ≤ _ at member
    change terminalValue (PMF.pure choice) - _ ≤ _
    linarith [(abs_le.mp near).2]
  by_cases intendedChoice : IntendedCommitment setup timeouts leaks bounds horizon scheduler
    nativeSite
      nativeChoice
  · have metadata := intendedChoice
    obtain ⟨p, v, response, material, named, serial, payload, outputEq, value, atNative, selected,
      sends, packet, _after, _offered⟩ := metadata
    have submitted : (submittedEvent? timeouts) leaks response = some named := by
      unfold EventGraphRuntime.submittedEvent?
      simp only [sends, packet, Payload.event?]
    have atTurn := commitsAtTurn_of_notOwing (timeouts := timeouts) wellFormed nativeSite
      nativeNotOwing nativeChoice
      selected submitted
    obtain ⟨option, deviation, success, successNonneg, successLe, bounded⟩ := nativeCommitments
      n who
      nativeSite nativeChoice nativeNotFree nativeNotOwing nativeKeyed atTurn intendedChoice
    dsimp only at bounded
    rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)] at bounded
    change stoppedValue (PMF.pure nativeChoice) - stoppedValue (optionLaw option) ≤
      success * intendedSiteGain setup parameter utility excludedPayoff (sequence n) deviation +
        nativeError n at bounded
    let baseline : setup.intendedModel.AssessmentDeviation who :=
      ⟨deviation.1, (sequence n).strategy who⟩
    have zero : intendedSiteGain setup parameter utility excludedPayoff (sequence n) baseline = 0 :=
      by simp [intendedSiteGain, baseline, InformationModel.assessmentComparisonWith,
        InformationModel.assessmentLawWith, Profile.update_eq_self]
    refine GainComparison.of_weighted
      (intendedSiteGain setup parameter utility excludedPayoff (sequence n))
      ⟨success, successNonneg, successLe⟩ deviation baseline zero ?_
    have gain := viaNative option
    have covered : nativeError n + 2 * valueError n + memberError n ≤ error n := by
      dsimp only [error]
      linarith [le_abs_self (nativeError n), le_abs_self (valueError n), le_abs_self
        (memberError n),
        abs_nonneg (affineError n), positiveTerms.1, positiveTerms.2]
    linarith only [gain, bounded, covered]
  left
  obtain ⟨response, selected, member⟩ := choice_response setup timeouts leaks bounds horizon
    scheduler
    nativeSite nativeAt nativeChoice
  have simpleCovered : 6 * scale n * payoffBound + memberError n ≤ error n := by
    dsimp only [error]
    linarith [abs_nonneg (nativeError n), abs_nonneg (valueError n), abs_nonneg (affineError n),
      positiveTerms.1, le_abs_self (memberError n)]
  cases sends : response.transmission with
  | none =>
      have silent : nativeChoice = silenceChoice setup timeouts leaks bounds (initialLaw setup)
        horizon
          scheduler who nativeSite.1 := by
        apply Subtype.ext
        rw [selected, nativeAt]
        change some response = (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon
          scheduler who (some (nativePast, nativeView))).1
        have responseEq : response = ⟨none⟩ :=
          congrArg (fun transmission => (⟨transmission⟩ : (application setup timeouts
            leaks).Action)) sends
        rw [responseEq]
        simp only [silenceChoice, responseChoice]
        split <;> rfl
      have main : lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          (sequence n) who nativeSite.1 (none : LateOption bounds.candidateCount) =
            PMF.pure nativeChoice := by
        rw [silent, nativeAt, lateChoice_none]
      exact (viaMain none main).trans simpleCovered
  | some material =>
      obtain ⟨named, submitted⟩ := submittedEvent_of_transmits setup timeouts leaks bounds member
        sends
      have atTurn := commitsAtTurn_of_notOwing (timeouts := timeouts) wellFormed nativeSite
        nativeNotOwing nativeChoice
        selected submitted
      cases packet : material.call.packet with
      | malformed raw => exact (onePacket_not_malformed (timeouts := timeouts) bounds member sends
        raw packet).elim
      | commitment named candidate =>
          let nativeBelief := target.belief who nativeSite
          have debtFree := siteDebtFree_of_not_owing setup timeouts leaks bounds horizon
            scheduler
            nativeNotOwing
          have forced := forcedAgent_of_not_free setup timeouts leaks bounds (initialLaw setup)
            horizon scheduler
            nativeNotFree
          have unforcedMass : expect nativeBelief (fun history =>
              if ForcedState setup timeouts leaks who history.1.state then (0 : ℝ) else 1) ≤
                |irregularError n| := by
            have rows : ∀ history ∈ nativeBelief.support,
                (if ForcedState setup timeouts leaks who history.1.state then (0 : ℝ) else 1) ≤
                if RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
                    history.1.trace then 0 else 1 := by
              intro history _supported
              by_cases regular : RegularTrace setup timeouts leaks bounds horizon scheduler
                  (sequence n) who history.1.trace
              · have ownIntended :=
                  ownCompletionsIntended_of_siteNotOwes (timeouts := timeouts) wellFormed debtFree
                    history
                have forcing := forcedState_of_regular (timeouts := timeouts) wellFormed (sequence
                  n) nativeAt forced
                  history regular ownIntended
                simp only [forcing, regular, ↓reduceIte, le_refl]
              · simp only [regular, ↓reduceIte]
                split <;> norm_num
            have averaged := expect_mono rows (payoffIntegrable_of_finite _ _)
              (payoffIntegrable_of_finite _ _)
            have pendingHere := nativePending
            rw [nativeAt] at pendingHere
            have rare := irregular n who nativeSite nativeNotFree nativeNotOwing nativeAt
              (pendingEvent_spec (timeouts := timeouts) pendingHere).1
            exact averaged.trans (rare.trans (le_abs_self _))
          have bad := OnePacketComparison.unintendedCommitment_value_sub_le setup timeouts leaks
            bounds horizon scheduler wellFormed
            (fun control trace _ ended => completes control
              ((Menu).toRawTrace (initialLaw setup) horizon scheduler trace) ended)
            (targetSequence n) nativeSite nativeChoice nativeNotOwing atTurn intendedChoice
            nativeAt response selected material sends named candidate packet parameter utility
            excludedPayoff (readoutBounded who) (excludedBounded who) unforcedMass
          change |stoppedValue (PMF.pure nativeChoice) - excludedPayoff who| ≤
            2 * payoffBound * |irregularError n| at bad
          obtain ⟨lower, affine⟩ := affineValues n ((N).agentAt site) keyed notOwing decision
          have productNonneg := mul_nonneg
            (scoreUnit n (agentLateKey setup timeouts leaks bounds (initialLaw setup) horizon
          scheduler
              ((N).agentAt site))
              none).1 (sub_nonneg.mpr lower)
          have optionLower : excludedPayoff who - affineError n ≤ terminalValue (optionLaw none) :=
            by
            have near := affine none
            change |terminalValue (optionLaw none) -
              (excludedPayoff who + score n
                (agentLateKey setup timeouts leaks bounds (initialLaw setup) horizon scheduler
                  ((N).agentAt site)) none *
                (continuation n ((N).agentAt site) - excludedPayoff who))| ≤ affineError n at near
            linarith [(abs_le.mp near).1]
          have memberBound := memberAt none
          rw [localGain_eq_sub] at memberBound ⊢
          change terminalValue (optionLaw none) - _ ≤ _ at memberBound
          change terminalValue (PMF.pure choice) - _ ≤ _
          have covered : 2 * payoffBound * |irregularError n| + valueError n + affineError n +
              memberError n ≤ error n := by
            dsimp only [error]
            linarith [abs_nonneg (nativeError n), abs_nonneg (valueError n),
              le_abs_self (valueError n), le_abs_self (affineError n), le_abs_self (memberError n),
              positiveTerms.2]
          linarith [(abs_le.mp pureNear).2, (abs_le.mp bad).2]
      | opening named handle raw =>
          have packetSubmitted : (submittedEvent? timeouts) leaks response = some named := by
            unfold EventGraphRuntime.submittedEvent?
            simp only [sends, packet, Payload.event?]
          obtain ⟨p, v, turnResponse, turnEvent, seen, turnChosen, turnSubmitted, namedTurn⟩ :=
            atTurn
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (nativeAt.symm.trans seen))
          have responseEq := Option.some.inj (selected.symm.trans turnChosen)
          subst turnResponse
          have eventEq := Option.some.inj (packetSubmitted.symm.trans turnSubmitted)
          subst turnEvent
          have pendingHere := nativePending
          rw [nativeAt] at pendingHere
          have namedEq : named = nativeEvent :=
            Option.some.inj (namedTurn.symm.trans (pendingEvent_spec (timeouts := timeouts)
              pendingHere).1)
          subst named
          have main := lateChoice_eq_pure_opening setup timeouts leaks bounds horizon scheduler
            wellFormed
            (sequence n) nativeSite nativeNotFree
            (siteDebtFree_of_not_owing setup timeouts leaks bounds horizon scheduler
              nativeNotOwing)
            nativeAt nativePending nativeChoice selected member sends packet
            (⟨0, slots_pos⟩ : Fin bounds.candidateCount)
          exact (viaMain (some ⟨0, slots_pos⟩) main).trans simpleCovered


end Vegas.OnePacketComparison
