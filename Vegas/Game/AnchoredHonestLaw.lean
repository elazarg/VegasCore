/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AnchoredHonestAgreement
import Vegas.Game.OnePacketHonestForced
import Vegas.Game.OnePacketContinuation

/-! # The as-if-honest continuation law from reached boundaries

From a reached boundary decoding to a point of the intended game, rounds of
as-if-honest play in the one-packet game are rounds of the anchored first-turn
clients of the intended effective opening
(`Vegas.runRounds_honest_eq_anchoredClients`). So the as-if-honest continuation
from a history ending at such a boundary reads out the source continuation of
the intended effective opening at the boundary
(`Vegas.honestProfile_boundary_readout_law`).

That law records no failed reveal, while a decoded debt would record one on
every terminal continuation, so every history as-if-honest play reaches from
the boundary is forced (`Vegas.honest_boundary_forced`). A profile keeping a
fraction of every as-if-honest choice at those forced information states
dominates as-if-honest play from the boundary
(`Vegas.dominatesHonestFrom_of_boundary_forced`,
`Vegas.dominatesHonestFrom_of_boundary_prescribed`), and its expected exclusion
payoffs are within the transport error of the source continuation value at the
boundary's point (`Vegas.onePacket_boundary_expect_exclusion_sub_le`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **As-if-honest rounds are the anchored clients' rounds.** Under the
hypotheses of `Vegas.honestPolicy_eq_anchoredClients`, from every execution
the anchored first-turn clients reach from the boundary, rounds of as-if-honest
play read as native policies have, within the horizon, the law of the anchored
clients' rounds. -/
theorem runRounds_honest_eq_anchoredClients [Fintype Player]
    (bounds : MessageBounds (graph setup)) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound) (turns : Nat)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsOpeningCanonical setup leaks bounds bound horizon scheduler
      assessment.strategy) {rank : Nat}
    {anchor : (application setup leaks).Execution}
    (reached : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point) :
    ∀ (more count : Nat), anchor.environmentRecall.length + count + more ≤ horizon →
      ∀ execution ∈ ((application setup leaks).runRounds scheduler
          (ReactiveApplication.anchoredPolicy anchor
            (openingClients setup leaks bound turns assessment.strategy)) count anchor).support,
        (application setup leaks).runRounds scheduler
            ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon
              scheduler (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler
                assessment)) more execution =
          (application setup leaks).runRounds scheduler
            (ReactiveApplication.anchoredPolicy anchor
              (openingClients setup leaks bound turns assessment.strategy)) more execution := by
  let app := application setup leaks
  let players := ReactiveApplication.anchoredPolicy anchor
    (openingClients setup leaks bound turns assessment.strategy)
  let honest := (bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup)
    horizon scheduler (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler
      assessment)
  intro more
  induction more with
  | zero => intro _ _ _ _; rfl
  | succ more ih =>
      intro count within execution supported
      have roundEq :
          app.round scheduler honest execution = app.round scheduler players execution := by
        apply bind_congr_on_support _
        intro command selected
        apply bind_congr_on_support _
        intro middle moved
        cases active : command.actor? app with
        | none => rfl
        | some who =>
            have extends_ := (ContinuesAnchor.runRounds (bound := bound) (turns := turns)
              (profile := setup.intendedOpeningProfile assessment.strategy)
              (scheduler := scheduler) count anchor ⟨fun _ => List.prefix_refl _, reached.turns⟩
              execution supported).1
            have recallEq := app.environmentStep_recall execution middle command moved
            have agree := ReactiveApplication.anchoredPolicy_of_extends anchor
              (openingClients setup leaks bound turns assessment.strategy) who
              (middle.recall who) (middle.observe app who)
              (by rw [recallEq]; exact extends_ who)
            change (honest who (middle.recall who) (middle.observe app who)).map
                (middle.respond app who) =
              (players who (middle.recall who) (middle.observe app who)).map
                (middle.respond app who)
            rw [show players who (middle.recall who) (middle.observe app who) = _ from agree]
            exact congrArg (PMF.map (middle.respond app who))
              (honestPolicy_eq_anchoredClients bounds contract timely turns assessment retains
                reached point decoded intendedPoint (by omega) supported selected moved active)
      change (app.round scheduler honest execution).bind (app.runRounds scheduler honest more) =
        (app.round scheduler players execution).bind (app.runRounds scheduler players more)
      rw [roundEq]
      apply bind_congr_on_support _
      intro next nextReached
      apply ih (count + 1) (by omega) next
      rw [ReactiveApplication.runRounds_add]
      refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨execution, supported, ?_⟩
      change next ∈ ((app.round scheduler players execution).bind PMF.pure).support
      rwa [PMF.bind_pure]

/-- **The as-if-honest continuation law from a reached boundary.** For the
setup under the asynchronous contract with timely delays and retention of the
opening's canonical packets, from a one-packet history ending between rounds at
a reached boundary decoding to a point of the intended game, as-if-honest play
of an intended assessment reads out the source continuation of the intended
effective opening of its strategy at the boundary. -/
theorem honestProfile_boundary_readout_law [Fintype Player]
    (bounds : MessageBounds (graph setup)) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsOpeningCanonical setup leaks bounds bound horizon scheduler
      assessment.strategy) {rank : Nat}
    {anchor : (application setup leaks).Execution}
    (reached : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (fuel : Nat) (enough : 2 * (horizon - anchor.environmentRecall.length) ≤ fuel) :
    ((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).runBehavioralFrom
        (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment) fuel
        start).map (fun final => sourceReadout setup leaks final.state) =
      sourceContinuation setup (setup.intendedOpeningProfile assessment.strategy) rank
        anchor.application.config := by
  let app := application setup leaks
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let remaining := horizon - anchor.environmentRecall.length
  have finishLaw := menu.run_eq_finish (initialLaw setup) horizon scheduler
    (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment) fuel start
    (by
      rw [state]
      change 2 * remaining + 0 ≤ fuel
      omega)
  change ((menu.information (initialLaw setup) horizon scheduler).runBehavioralFrom _ fuel
    start).map (fun final => sourceReadout setup leaks final.state) = _
  rw [show (fun final : (menu.protocol (initialLaw setup) horizon scheduler).History =>
      sourceReadout setup leaks final.state) =
    (sourceReadout setup leaks) ∘ ExecutionProtocol.History.state from rfl,
    ← PMF.map_comp, finishLaw, state]
  change (((PMF.pure anchor).bind (app.runRounds scheduler _ remaining)).map
    app.finished).map (sourceReadout setup leaks) = _
  rw [PMF.pure_bind, runRounds_honest_eq_anchoredClients bounds contract timely 0 assessment
      retains reached point decoded intendedPoint remaining 0
      (by have := reached.bounded; omega) anchor
      ((PMF.mem_support_pure_iff _ _).mpr rfl),
    ReactiveApplication.runRounds_anchoredPolicy, PMF.map_comp,
    ← reachedBoundary_continuation contract timely 0 _
      (setup.intendedOpeningProfile_opensEffectively assessment.strategy) reached]
  rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Under a global horizon, terminal play from a history reached by play of
some length from `start` is reached by play from `start` of that length plus
the horizon. -/
private theorem mem_runBehavioralFrom_of_terminalFrom [Fintype Player]
    {E : ExecutionProtocol Player}
    (M : InformationModel E) (certificate : E.WellFoundedHistories) {bound : Nat}
    (bounded : E.BoundedHorizon bound) (profile : ∀ who, M.BehavioralPolicy who) {fuel : Nat}
    {start history final : E.History}
    (reached : history ∈ (M.runBehavioralFrom profile fuel start).support)
    (finished : final ∈ (M.runBehavioralTerminalFrom certificate profile history).support) :
    final ∈ (M.runBehavioralFrom profile (fuel + bound) start).support := by
  rw [M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded] at finished
  rw [M.runBehavioralFrom_add]
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨history, reached, finished⟩

/-- **As-if-honest play from a reached boundary stays forced.** For a
well-formed setup, under the asynchronous contract with timely delays and
retention of the opening's canonical packets, from a one-packet history ending
between rounds at a reached boundary decoding to a point of the intended game,
at every history as-if-honest play of an intended assessment reaches, the state
is forced for every player. -/
theorem honest_boundary_forced [Fintype Player] (bounds : MessageBounds (graph setup))
    (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsOpeningCanonical setup leaks bounds bound horizon scheduler
      assessment.strategy) {rank : Nat}
    {anchor : (application setup leaks).Execution}
    (reached : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (fuel : Nat)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (reachedHistory : history ∈ ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).runBehavioralFrom
        (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment) fuel
        start).support)
    (control : (application setup leaks).Control) (current : history.state = some control)
    (who : Player) :
    ForcedState setup leaks who history.state := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
  let honest := honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment
  let opening := setup.intendedOpeningProfile assessment.strategy
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  obtain ⟨historyRank, ⟨residual⟩, holds⟩ := decodedState_intended_or_owes wellFormed opening menu
    horizon scheduler history.trace control current
  -- The anchor's point carries the program's registry and publication status.
  have staticPoint : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context)
      point := by
    have boundary := reachedBoundary_completionBoundary reached
      (firstTurnClients setup leaks bound 0 opening)
    obtain ⟨staticRank, ⟨staticResidual⟩, staticHolds⟩ := roundsFrom_static scheduler
      (ReactiveApplication.anchoredPolicy anchor (firstTurnClients setup leaks bound 0 opening))
      opening anchor.environmentRecall.length anchor boundary.supported
    have sameRank := isPrefix_unique staticResidual.checkpoint.ordered reached.ordered
    subst sameRank
    exact staticHolds point decoded
  have noDebt : ∀ player, ¬ ProtocolState.OwesFailure player setup.program
      (residual.lift (ProtocolState.entry residual.program residual.source)) := by
    intro player owed
    have owing : DecodedState setup leaks opening (ProtocolState.OwesFailure player setup.program)
        history.state := by
      rw [current]
      refine ⟨historyRank, ⟨residual⟩, fun point decodedHistory => ?_⟩
      rw [residual.decode, Option.some.injEq] at decodedHistory
      rw [← decodedHistory]
      exact owed
    obtain ⟨final, finalMem⟩ := (model.runBehavioralTerminalFrom certificate honest
      history).support_nonempty
    obtain ⟨terminal, read, failed⟩ := decoded_owesFailure_failedReveals menu horizon scheduler
      contract.completes certificate honest player history owing final finalMem
    have inRun := mem_runBehavioralFrom_of_terminalFrom model certificate
      (menu.bounded (initialLaw setup) horizon scheduler) honest reachedHistory finalMem
    have inLaw : some terminal ∈ ((model.runBehavioralFrom honest (fuel + (2 * horizon + 1))
        start).map (fun final => sourceReadout setup leaks final.state)).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨final, inRun, read⟩
    rw [honestProfile_boundary_readout_law bounds contract timely assessment retains reached
      point decoded intendedPoint start state _ (by omega)] at inLaw
    change some terminal ∈ ((setup.continuationLaw opening
      (sourceServicePrefix? setup rank anchor.application.config)).map some).support at inLaw
    rw [decoded] at inLaw
    obtain ⟨source, sourceMem, sourceEq⟩ := (PMF.mem_support_map_iff _ _ _).mp inLaw
    cases Option.some.inj sourceEq
    have zero := setup.intendedOpening_continuation_failedReveals assessment.strategy _ point le_rfl
      staticPoint intendedPoint terminal sourceMem player
    omega
  rw [current]
  refine ⟨historyRank, _, residual.checkpoint.ordered, residual.decode, ?_⟩
  rcases holds _ residual.decode with intended | ⟨player, owed⟩
  · exact ⟨fun failed => ProtocolState.not_excluded_of_intended who setup.program _ intended
        (ProtocolState.RevealFailed.excluded setup.program _ failed),
      fun other _ => ⟨ProtocolState.not_excluded_of_intended other setup.program _ intended,
        noDebt other⟩⟩
  · exact (noDebt player owed).elim

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem apply_eq_one_of_subsingleton {α : Type} [Subsingleton α] (law : PMF α) (a : α) :
    law a = 1 := by
  rw [← law.tsum_coe, tsum_eq_single a (fun other different =>
    (different (Subsingleton.elim other a)).elim)]

variable (setup leaks) in
/-- An information state of `who` at some history as-if-honest play reaches
from `start` in the one-packet game. -/
def HonestReachedFrom [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) (who : Player) (info : (application setup leaks).Info) : Prop :=
  ∃ fuel, ∃ history ∈ ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).runBehavioralFrom
      (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment) fuel
      start).support,
    (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).infoOf who
      history.trace = info

/-- **Keeping the as-if-honest choice at forced states dominates as-if-honest
play from a reached boundary.** Under the hypotheses of
`Vegas.honest_boundary_forced`, a profile of the one-packet game that gives
every choice at every forced information state as-if-honest play reaches from
the boundary history at least `retention ≤ 1` times its as-if-honest mass
dominates as-if-honest play from that history with that retention, whatever it
plays elsewhere. -/
theorem dominatesHonestFrom_of_boundary_forced [Fintype Player]
    (bounds : MessageBounds (graph setup)) (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsOpeningCanonical setup leaks bounds bound horizon scheduler
      assessment.strategy) {rank : Nat}
    {anchor : (application setup leaks).Execution}
    (reached : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    {retention : ℝ} (le_one : retention ≤ 1)
    (profile : ∀ who,
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (kept : ∀ who info,
      HonestReachedFrom setup leaks bounds horizon scheduler assessment start who info →
      forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
        scheduler who info → ∀ choice,
      retention * ((honestProfile setup leaks bounds (initialLaw setup) horizon scheduler
          assessment who info) choice).toReal ≤ ((profile who info) choice).toReal) :
    DominatesHonestFrom setup leaks bounds (initialLaw setup) horizon scheduler assessment
      retention profile start := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
  intro fuel history reachedHistory who choice
  have observed : model.infoOf who history.trace =
      (application setup leaks).observe who history.state :=
    menu.info (initialLaw setup) horizon scheduler who history.trace
  by_cases forced : forcedAgent menu (initialLaw setup) horizon scheduler who
      (model.infoOf who history.trace)
  · exact kept who _ ⟨fuel, history, reachedHistory, rfl⟩ forced choice
  · have info : model.infoOf who history.trace = none := by
      rw [observed]
      cases current : history.state with
      | none => rfl
      | some control =>
          exact (forced (forcedAgent_of_history history
            (honest_boundary_forced bounds wellFormed contract timely assessment retains reached
              point decoded intendedPoint start state fuel history reachedHistory control current
              who))).elim
    revert choice
    rw [info]
    intro choice
    have : Subsingleton (model.Choice who none) :=
      InformationModel.subsingleton_choice_of_menu_subsingleton _ _ Set.subsingleton_singleton
    rw [apply_eq_one_of_subsingleton _ choice, apply_eq_one_of_subsingleton _ choice,
      ENNReal.toReal_one, mul_one]
    exact le_one

/-- **Prescribed play at forced states dominates as-if-honest play from a
reached boundary.** Under the hypotheses of `Vegas.honest_boundary_forced`, a
profile playing the prescribed component at every forced information state
as-if-honest play reaches from the boundary history dominates as-if-honest
play from that history with the retention of the tremble scale. -/
theorem dominatesHonestFrom_of_boundary_prescribed [Fintype Player]
    (bounds : MessageBounds (graph setup)) (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsOpeningCanonical setup leaks bounds bound horizon scheduler
      assessment.strategy) {rank : Nat}
    {anchor : (application setup leaks).Execution}
    (reached : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (profile : ∀ who,
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (prescribed : ∀ who info,
      HonestReachedFrom setup leaks bounds horizon scheduler assessment start who info →
      forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
        scheduler who info →
      profile who info = prescribedComponent setup leaks bounds (initialLaw setup) horizon
        scheduler assessment scale nonnegative le_one who info) :
    DominatesHonestFrom setup leaks bounds (initialLaw setup) horizon scheduler assessment
      (trembleRetention scale) profile start :=
  dominatesHonestFrom_of_boundary_forced bounds wellFormed contract timely assessment retains
    reached point decoded intendedPoint start state (trembleRetention_le_one nonnegative le_one)
    profile fun who info reachedInfo forced choice => by
      rw [prescribed who info reachedInfo forced]
      exact trembledChoice_ge_main setup leaks bounds (initialLaw setup) horizon scheduler
        nonnegative le_one who _ _ _ choice

/-- **The continuation value from a reached boundary.** For a well-formed
setup, under the asynchronous contract with timely delays and retention of the
opening's canonical packets, from a one-packet history ending between rounds at
a reached boundary decoding to a point of the intended game, every profile that
gives every choice at every forced information state as-if-honest play of an
intended assessment reaches from that history at least `retention ∈ [0, 1]`
times its as-if-honest mass, whatever it plays elsewhere, has an expected
exclusion payoff for each player within `|Player| * fuel * (1 - retention)`
times the payoff range of the source continuation value of the intended
effective opening at that point. -/
theorem onePacket_boundary_expect_exclusion_sub_le [Fintype Player]
    (bounds : MessageBounds (graph setup)) (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsOpeningCanonical setup leaks bounds bound horizon scheduler
      assessment.strategy) {rank : Nat}
    {anchor : (application setup leaks).Execution}
    (reached : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (fuel : Nat) (enough : 2 * (horizon - anchor.environmentRecall.length) ≤ fuel)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (profile : ∀ who,
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (kept : ∀ who info,
      HonestReachedFrom setup leaks bounds horizon scheduler assessment start who info →
      forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
        scheduler who info → ∀ choice,
      retention * ((honestProfile setup leaks bounds (initialLaw setup) horizon scheduler
          assessment who info) choice).toReal ≤ ((profile who info) choice).toReal)
    (who : Player) (low range : ℝ)
    (bounded : ∀ readout, low ≤ exclusionReadoutUtility setup parameter utility excludedPayoff
        readout who ∧
      exclusionReadoutUtility setup parameter utility excludedPayoff readout who ≤ low + range) :
    |expect ((onePacketModel setup leaks bounds (initialLaw setup) horizon
        scheduler).runBehavioralFrom profile fuel start)
        (fun final => exclusionBase setup parameter utility excludedPayoff leaks final.state who) -
      expect ((ProtocolState.continuationLaw setup.program
          (setup.intendedOpeningProfile assessment.strategy) point).map some)
        (fun readout => exclusionReadoutUtility setup parameter utility excludedPayoff readout
          who)| ≤
      ((Fintype.card Player * fuel : ℕ) * (1 - retention)) * range := by
  have honest := honestProfile_boundary_readout_law bounds contract timely assessment retains
    reached point decoded intendedPoint start state fuel enough
  change _ = (setup.continuationLaw (setup.intendedOpeningProfile assessment.strategy)
    (sourceServicePrefix? setup rank anchor.application.config)).map some at honest
  rw [decoded] at honest
  exact onePacket_continuation_expect_exclusion_sub_le setup leaks bounds (initialLaw setup)
    horizon scheduler parameter utility excludedPayoff assessment start fuel _ honest
    nonnegative le_one profile
    (dominatesHonestFrom_of_boundary_forced bounds wellFormed contract timely assessment retains
      reached point decoded intendedPoint start state le_one profile kept)
    who low range bounded

end Vegas
