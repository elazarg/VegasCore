/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketHonestAgreement

/-! # As-if-honest play stays in the forced region

Along every history of the one-packet game, under any profile and any
scheduler, the decoding of the configuration is a point of the intended game
or one at which some player owes a failed reveal
(`Vegas.decodedState_intended_or_owes`): every source step from the intended
game stays in it or leaves a debt, and debts persist.

For a well-formed setup under the asynchronous contract with timely delays and
retention of first canonical packets, as-if-honest play reads out the intended
law, which records no failed reveal, while a decoded debt would record one on
every terminal continuation. So at every history as-if-honest play reaches,
the decoding is an intended point at which nobody is excluded or owes a failed
reveal, and the state is forced for every player
(`Vegas.honest_reached_forced`). A profile that keeps a fraction of every
as-if-honest choice at every forced information state therefore dominates
as-if-honest play with that fraction (`Vegas.dominatesHonest_of_forced`),
whatever it plays elsewhere; the prescribed component keeps the retention of
its scale (`Vegas.dominatesHonest_of_prescribed_forced`).

**The law approximation.** Along retentions tending to one, profiles keeping
that fraction of the as-if-honest choice at forced information states have a
law of typed readouts, and of typed readouts with exclusion payoffs, within a
vanishing error of the intended law, uniformly over outcomes and over their
play at other information states (`Vegas.onePacket_readout_lawApproximation`,
`Vegas.onePacket_exclusion_lawApproximation`); prescribed trembled components
along vanishing scales are one instance
(`Vegas.onePacket_prescribed_lawApproximation`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup) in
/-- A point of the intended game, or one at which some player owes a failed
reveal. -/
def IntendedOrOwed (point : ProtocolState setup.program) : Prop :=
  ProtocolState.Intended setup.program point ∨
    ∃ who, ProtocolState.OwesFailure who setup.program point

theorem intendedOrOwed_stepClosed : StepClosed setup (IntendedOrOwed setup) := by
  intro state joint target holds reached
  rcases holds with intended | ⟨who, owed⟩
  · exact ProtocolState.intended_or_owesFailure_step setup.program state joint target intended
      reached
  · exact Or.inr ⟨who, ProtocolState.owesFailure_step who setup.program state joint target owed
      reached⟩

/-- **Intended or owed along every history.** For a well-formed setup, along
every history of a response menu of the default runtime from its initial law,
under any scheduler, the configuration decodes to a point of the intended game
or one at which some player owes a failed reveal. -/
theorem decodedState_intended_or_owes (wellFormed : setup.WellFormed)
    (profile : BehavioralProfile setup.program)
    (menu : (application setup leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) :
    ∀ {state} (_ : (menu.protocol (initialLaw setup) horizon scheduler).Trace state)
      (control : (application setup leaks).Control), state = some control →
      DecodedState setup leaks profile (IntendedOrOwed setup) (some control) := by
  intro state trace
  induction trace with
  | start => intro _ initialized; cases initialized
  | @extend before after prior joint _ realized ih =>
      intro control current
      subst current
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state =>
            some ⟨horizon, none, ReactiveApplication.Execution.initial
              (application setup leaks) state⟩).support at realized
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          obtain ⟨initial, initialMem, rfl⟩ := PMF.support_map .. ▸ supported
          let residual := SourceResidual.initial setup profile initial
          refine ⟨0, ⟨residual⟩, fun point decoded => ?_⟩
          change sourceServicePrefix? setup 0 (EventGraphRuntime.State.initial
            (graph := graph setup) (setup.eventInputs initial)).config = some point at decoded
          rw [residual.decode, Option.some.injEq] at decoded
          subst decoded
          exact Or.inl (ProtocolState.intended_entry setup.program _
            (setup.initialConfig_intended wellFormed initialMem)
            (wellFormed.guardsSatisfiable initial initialMem))
      | some previous =>
          exact decodedHolds_transition intendedOrOwed_stepClosed (initialLaw setup) horizon
            scheduler (some previous) (some control) joint (ih previous rfl) realized

section Forced

variable [Fintype Player] (bounds : MessageBounds (graph setup))

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Under a global horizon, terminal play from a history reached by play of
some length is reached by play to the horizon. -/
theorem mem_runBehavioral_of_terminalFrom {E : ExecutionProtocol Player}
    (M : InformationModel E) (certificate : E.WellFoundedHistories) {bound : Nat}
    (bounded : E.BoundedHorizon bound) (profile : ∀ who, M.BehavioralPolicy who) {fuel : Nat}
    {history final : E.History} (reached : history ∈ (M.runBehavioral profile fuel).support)
    (finished : final ∈ (M.runBehavioralTerminalFrom certificate profile history).support) :
    final ∈ (M.runBehavioral profile bound).support := by
  rw [M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded] at finished
  have longer : E.BoundedHorizon (fuel + bound) := fun state trace long =>
    bounded state trace (by omega)
  have same : M.runBehavioral profile (fuel + bound) = M.runBehavioral profile bound := by
    unfold InformationModel.runBehavioral
    rw [← M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate longer,
      M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded]
  rw [← same]
  unfold InformationModel.runBehavioral at reached ⊢
  rw [M.runBehavioralFrom_add]
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨history, reached, finished⟩

/-- **As-if-honest play stays forced.** For a well-formed setup, under the
asynchronous contract with timely delays and retention of first canonical
packets, at every history as-if-honest play of an intended assessment reaches
in the one-packet game, the state is forced for every player. -/
theorem honest_reached_forced (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsFirstCanonical setup leaks bounds bound) (fuel : Nat)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (reached : history ∈ ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).runBehavioral
        (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment)
        fuel).support)
    (control : (application setup leaks).Control) (current : history.state = some control)
    (who : Player) :
    ForcedState setup leaks who history.state := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
  let honest := honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment
  let profile := setup.intendedOpeningProfile assessment.strategy
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  obtain ⟨rank, ⟨residual⟩, holds⟩ := decodedState_intended_or_owes wellFormed profile menu
    horizon scheduler history.trace control current
  have noDebt : ∀ player, ¬ ProtocolState.OwesFailure player setup.program
      (residual.lift (ProtocolState.entry residual.program residual.source)) := by
    intro player owed
    have owing : DecodedState setup leaks profile (ProtocolState.OwesFailure player setup.program)
        history.state := by
      rw [current]
      refine ⟨rank, ⟨residual⟩, fun point decoded => ?_⟩
      rw [residual.decode, Option.some.injEq] at decoded
      rw [← decoded]
      exact owed
    obtain ⟨final, finalMem⟩ := (model.runBehavioralTerminalFrom certificate honest
      history).support_nonempty
    obtain ⟨terminal, read, failed⟩ := decoded_owesFailure_failedReveals menu horizon scheduler
      contract.completes certificate honest player history owing final finalMem
    have inRun := mem_runBehavioral_of_terminalFrom model certificate
      (menu.bounded (initialLaw setup) horizon scheduler) honest reached finalMem
    have inLaw : some terminal ∈ ((model.runBehavioral honest (2 * horizon + 1)).map
        (fun final => sourceReadout setup leaks final.state)).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨final, inRun, read⟩
    rw [honestProfile_readout_law bounds wellFormed contract timely assessment retains] at inLaw
    obtain ⟨intendedHistory, _, intendedRead⟩ := (PMF.mem_support_map_iff _ _ _).mp inLaw
    have zero := setup.failedReveals_eq_zero_of_intendedState
      (setup.intendedState_trace wellFormed intendedHistory.trace) player intendedRead
    omega
  rw [current]
  refine ⟨rank, _, residual.checkpoint.ordered, residual.decode, ?_⟩
  rcases holds _ residual.decode with intended | ⟨player, owed⟩
  · exact ⟨fun failed => ProtocolState.not_excluded_of_intended who setup.program _ intended
        (ProtocolState.RevealFailed.excluded setup.program _ failed),
      fun other _ => ⟨ProtocolState.not_excluded_of_intended other setup.program _ intended,
        noDebt other⟩⟩
  · exact (noDebt player owed).elim

end Forced

section Domination

variable [Fintype Player] (bounds : MessageBounds (graph setup))

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem apply_eq_one_of_subsingleton {α : Type} [Subsingleton α] (law : PMF α) (a : α) :
    law a = 1 := by
  rw [← law.tsum_coe, tsum_eq_single a (fun other different =>
    (different (Subsingleton.elim other a)).elim)]

variable (setup leaks) in
/-- An information state of `who` at some history as-if-honest play reaches
from initialization in the one-packet game. -/
def HonestReached (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (info : (application setup leaks).Info) : Prop :=
  ∃ fuel, ∃ history ∈ ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).runBehavioral
      (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment)
      fuel).support,
    (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).infoOf who
      history.trace = info

/-- **Keeping the as-if-honest choice at forced states dominates as-if-honest
play.** For a well-formed setup, under the asynchronous contract with timely
delays and retention of first canonical packets, a profile of the one-packet
game that gives every choice at every forced information state as-if-honest
play reaches at least `retention ∈ [0, 1]` times its as-if-honest mass
dominates as-if-honest play
from initialization with that retention, whatever it plays elsewhere. -/
theorem dominatesHonest_of_forced (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsFirstCanonical setup leaks bounds bound)
    {retention : ℝ} (le_one : retention ≤ 1)
    (profile : ∀ who,
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (kept : ∀ who info, HonestReached setup leaks bounds horizon scheduler assessment who info →
      forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
        scheduler who info → ∀ choice,
      retention * ((honestProfile setup leaks bounds (initialLaw setup) horizon scheduler
          assessment who info) choice).toReal ≤ ((profile who info) choice).toReal) :
    DominatesHonestFrom setup leaks bounds (initialLaw setup) horizon scheduler assessment
      retention profile ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
        horizon scheduler).initHistory := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
  intro fuel history reached who choice
  have observed : model.infoOf who history.trace =
      (application setup leaks).observe who history.state :=
    menu.info (initialLaw setup) horizon scheduler who history.trace
  by_cases forced : forcedAgent menu (initialLaw setup) horizon scheduler who
      (model.infoOf who history.trace)
  · exact kept who _ ⟨fuel, history, reached, rfl⟩ forced choice
  · have info : model.infoOf who history.trace = none := by
      rw [observed]
      cases state : history.state with
      | none => rfl
      | some control =>
          exact (forced (forcedAgent_of_history history
            (honest_reached_forced bounds wellFormed contract timely assessment retains fuel history
              reached control state who))).elim
    revert choice
    rw [info]
    intro choice
    have : Subsingleton (model.Choice who none) :=
      InformationModel.subsingleton_choice_of_menu_subsingleton _ _ Set.subsingleton_singleton
    rw [apply_eq_one_of_subsingleton _ choice, apply_eq_one_of_subsingleton _ choice,
      ENNReal.toReal_one, mul_one]
    exact le_one

/-- **Prescribed play at forced states dominates as-if-honest play.** Under the
hypotheses of `dominatesHonest_of_forced`, a profile playing the prescribed
component at every forced information state dominates as-if-honest play with
the retention of the tremble scale. -/
theorem dominatesHonest_of_prescribed_forced (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsFirstCanonical setup leaks bounds bound)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (profile : ∀ who,
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (prescribed : ∀ who info,
      HonestReached setup leaks bounds horizon scheduler assessment who info →
      forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
        scheduler who info →
      profile who info = prescribedComponent setup leaks bounds (initialLaw setup) horizon
        scheduler assessment scale nonnegative le_one who info) :
    DominatesHonestFrom setup leaks bounds (initialLaw setup) horizon scheduler assessment
      (trembleRetention scale) profile ((bounds.onePacketMenu (runtime setup) leaks).protocol
        (initialLaw setup) horizon scheduler).initHistory :=
  dominatesHonest_of_forced bounds wellFormed contract timely assessment retains
    (trembleRetention_le_one nonnegative le_one) profile
    fun who info reachedInfo forced choice => by
      rw [prescribed who info reachedInfo forced]
      exact trembledChoice_ge_main setup leaks bounds (initialLaw setup) horizon scheduler
        nonnegative le_one who _ _ _ choice

end Domination

section LawApproximation

open Filter

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- **The law approximation of the one-packet game under the contract.** For
a well-formed setup, under the asynchronous contract with timely delays and
retention of first canonical packets, along retentions `retentions n` in
`[0, 1]` tending to one, every sequence of one-packet profiles that at every
forced information state give every choice at least `retentions n` times its
as-if-honest mass under `assessments n`, whatever they play elsewhere, has a
law of typed readouts whose probabilities differ from the intended ones under
`(assessments n).strategy` by an error that vanishes, uniformly over outcomes;
the error depends only on the retentions. -/
theorem onePacket_readout_lawApproximation (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsFirstCanonical setup leaks bounds bound)
    (assessments : ℕ → setup.intendedModel.BehavioralAssessment)
    (retentions : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ retentions n) (le_one : ∀ n, retentions n ≤ 1)
    (converging : Tendsto retentions atTop (nhds 1))
    (profiles : ℕ → ∀ who,
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (kept : ∀ n who info,
      HonestReached setup leaks bounds horizon scheduler (assessments n) who info →
      forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
        scheduler who info → ∀ choice,
      retentions n * ((honestProfile setup leaks bounds (initialLaw setup) horizon scheduler
          (assessments n) who info) choice).toReal ≤ ((profiles n who info) choice).toReal) :
    ∃ lawError : ℕ → ℝ, Tendsto lawError atTop (nhds 0) ∧
      ∀ n outcome,
        |((((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).runBehavioral
            (profiles n) (2 * horizon + 1)).map
            (fun final => sourceReadout setup leaks final.state)) outcome).toReal -
          (((setup.intendedModel.runBehavioral (assessments n).strategy
            (instructionCount setup.program + 1)).map
            (fun final => setup.protocolReadout final.state)) outcome).toReal| ≤ lawError n := by
  refine ⟨fun n => (Fintype.card Player * (2 * horizon + 1) : ℕ) * (1 - retentions n),
    ?_, fun n outcome => ?_⟩
  · have limit := ((tendsto_const_nhds (x := (1 : ℝ))).sub converging).const_mul
      ((Fintype.card Player * (2 * horizon + 1) : ℕ) : ℝ)
    simpa using limit
  · have close := (onePacket_withinTV_honest setup leaks bounds (initialLaw setup) horizon
      scheduler (assessments n) (nonnegative n) (le_one n) (profiles n)
      (dominatesHonest_of_forced bounds wellFormed contract timely (assessments n) retains
        (le_one n) (profiles n) (kept n))
      (2 * horizon + 1)).map (fun final => sourceReadout setup leaks final.state)
    rw [honestProfile_readout_law bounds wellFormed contract timely (assessments n) retains]
      at close
    exact close.symm.apply outcome

/-- **The joint law approximation with exclusion payoffs.** Under the
hypotheses of `onePacket_readout_lawApproximation`, the joint law of typed
readout and native exclusion payoff is within a vanishing error of the
intended joint law of typed readout and exclusion payoff. -/
theorem onePacket_exclusion_lawApproximation (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsFirstCanonical setup leaks bounds bound)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (assessments : ℕ → setup.intendedModel.BehavioralAssessment)
    (retentions : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ retentions n) (le_one : ∀ n, retentions n ≤ 1)
    (converging : Tendsto retentions atTop (nhds 1))
    (profiles : ℕ → ∀ who,
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (kept : ∀ n who info,
      HonestReached setup leaks bounds horizon scheduler (assessments n) who info →
      forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
        scheduler who info → ∀ choice,
      retentions n * ((honestProfile setup leaks bounds (initialLaw setup) horizon scheduler
          (assessments n) who info) choice).toReal ≤ ((profiles n who info) choice).toReal) :
    ∃ lawError : ℕ → ℝ, Tendsto lawError atTop (nhds 0) ∧
      ∀ n outcome,
        |((((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).runBehavioral
            (profiles n) (2 * horizon + 1)).map
            (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
              utility excludedPayoff)) outcome).toReal -
          (((setup.intendedModel.runBehavioral (assessments n).strategy
            (instructionCount setup.program + 1)).map
            (intendedReadoutExclusion setup parameter utility excludedPayoff))
            outcome).toReal| ≤ lawError n :=
  onePacket_lawApproximation setup leaks bounds (initialLaw setup) horizon scheduler parameter
    utility excludedPayoff assessments (fun n => (assessments n).strategy)
    (instructionCount setup.program + 1) (2 * horizon + 1)
    (fun n => honestProfile_readout_law bounds wellFormed contract timely (assessments n) retains)
    retentions nonnegative le_one converging profiles
    (fun n => dominatesHonest_of_forced bounds wellFormed contract timely (assessments n)
      retains (le_one n) (profiles n) (kept n))

/-- **The law approximation for prescribed trembled components.** Under the
hypotheses of `onePacket_exclusion_lawApproximation`, along vanishing tremble
scales in `[0, 1]`, profiles playing the prescribed component at every forced
information state satisfy the law approximation with exclusion payoffs. -/
theorem onePacket_prescribed_lawApproximation (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsFirstCanonical setup leaks bounds bound)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (assessments : ℕ → setup.intendedModel.BehavioralAssessment)
    (scales : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ scales n) (le_one : ∀ n, scales n ≤ 1)
    (vanishing : Tendsto scales atTop (nhds 0))
    (profiles : ℕ → ∀ who,
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (prescribed : ∀ n who info,
      HonestReached setup leaks bounds horizon scheduler (assessments n) who info →
      forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
        scheduler who info →
      profiles n who info = prescribedComponent setup leaks bounds (initialLaw setup) horizon
        scheduler (assessments n) (scales n) (nonnegative n) (le_one n) who info) :
    ∃ lawError : ℕ → ℝ, Tendsto lawError atTop (nhds 0) ∧
      ∀ n outcome,
        |((((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).runBehavioral
            (profiles n) (2 * horizon + 1)).map
            (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
              utility excludedPayoff)) outcome).toReal -
          (((setup.intendedModel.runBehavioral (assessments n).strategy
            (instructionCount setup.program + 1)).map
            (intendedReadoutExclusion setup parameter utility excludedPayoff))
            outcome).toReal| ≤ lawError n :=
  onePacket_exclusion_lawApproximation bounds wellFormed contract timely retains parameter utility
    excludedPayoff assessments (fun n => trembleRetention (scales n))
    (fun n => trembleRetention_nonneg (nonnegative n) (le_one n))
    (fun n => trembleRetention_le_one (nonnegative n) (le_one n))
    (tendsto_trembleRetention vanishing) profiles fun n who info reachedInfo forced choice => by
      rw [prescribed n who info reachedInfo forced]
      exact trembledChoice_ge_main setup leaks bounds (initialLaw setup) horizon scheduler
        (nonnegative n) (le_one n) who _ _ _ choice

end LawApproximation

end Vegas
