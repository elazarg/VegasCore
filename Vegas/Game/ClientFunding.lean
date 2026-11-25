module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ClientSpecification

@[expose] public section

/-! # Funding a certified client specification

Observation rates are declared lower bounds and may be negative. Clamping that
bound to zero preserves coverage and makes deposit monotonicity unconditional.
Translating both ordinary and exit utilities preserves terminal payoff
differences and the certified deposit.
-/

noncomputable section

namespace Vegas.ClientSpec

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {timeouts : EventTimeouts setup.informationGraph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
  {bounds : MessageBounds setup.informationGraph} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  {Parameter : Type} {parameter : State L setup.context → Parameter}
  {utility : Parameter × PublicOutcome setup.program → Player → ℝ}
  {excludedPayoff : Player → ℝ}

/-- Any pointwise larger deposit gives another certified specification for the
same source, runtime and evidence service. No sign assumption on the old observation-rate
lower bound is needed. The resulting completion may differ off path. -/
def withDeposit (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
    parameter utility excludedPayoff) (deposit : Player → ℝ)
    (larger : ∀ who, spec.deposit who ≤ deposit who) :
    ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff where
  __ := spec
  observationRate := fun who => max 0 (spec.observationRate who)
  coverage := by
    intro actual who witnessed
    obtain ⟨observed, delivered⟩ := spec.coverage actual who witnessed
    exact ⟨max_le ENNReal.toReal_nonneg observed, delivered⟩
  deposit := deposit
  deposit_nonnegative := fun who => (spec.deposit_nonnegative who).trans (larger who)
  funded := by
    intro compliant deviating who
    refine (spec.funded compliant deviating who).trans ?_
    calc
      spec.observationRate who * spec.deliveryRate who * spec.deposit who ≤
          max 0 (spec.observationRate who) * spec.deliveryRate who * spec.deposit who :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (spec.delivery_nonnegative who))
          (spec.deposit_nonnegative who)
      _ ≤ max 0 (spec.observationRate who) * spec.deliveryRate who * deposit who :=
        mul_le_mul_of_nonneg_left (larger who)
          (mul_nonneg (le_max_left _ _) (spec.delivery_nonnegative who))

omit [Fintype Player] in
/-- An interval for the ordinary readout payoffs gives a sufficient bound on
the base-payoff gain after accounting for exit and unfinished play. -/
theorem basePayoffGap_le_of_readoutBounds
    (lower upper : Player → ℝ)
    (bounded : ∀ (source : Config Player L setup.program.terminalCtx) who,
      lower who ≤ utility (setup.parameterOutcome parameter source) who ∧
        utility (setup.parameterOutcome parameter source) who ≤ upper who)
    (compliant deviating : (application setup timeouts leaks).ProtocolState) (who : Player) :
    exclusionBase setup timeouts parameter utility excludedPayoff leaks deviating who -
      exclusionBase setup timeouts parameter utility excludedPayoff leaks compliant who ≤
      max 0 (max (excludedPayoff who) (upper who)) -
        min 0 (min (excludedPayoff who) (lower who)) := by
  have boundsAt (state : (application setup timeouts leaks).ProtocolState) :=
    exclusionBase_mem_Icc setup timeouts parameter utility excludedPayoff leaks lower upper
      state (fun source _ i => (bounded source i).1) (fun source _ i => (bounded source i).2) who
  exact sub_le_sub (boundsAt deviating).2 (boundsAt compliant).1

omit [Fintype Player] in
/-- Adding a player-specific constant to ordinary and exit utilities adds the
same constant to the base payoff of every legal terminal history. -/
theorem terminal_base_add_constant
    (completes : CompletesPlay timeouts leaks (initialDistribution setup) horizon scheduler)
    (constant : Player → ℝ)
    (menu : (application setup timeouts leaks).ResponseMenu)
    (history : (menu.protocol (initialDistribution setup) horizon scheduler).History)
    (terminal : (menu.protocol (initialDistribution setup) horizon scheduler).terminal
      history.state) (who : Player) :
    exclusionBase setup timeouts parameter (fun outcome i => utility outcome i + constant i)
      (fun i => excludedPayoff i + constant i) leaks history.state who =
    exclusionBase setup timeouts parameter utility excludedPayoff leaks history.state who +
      constant who := by
  cases state : history.state with
  | none =>
      rw [state] at terminal
      exact False.elim terminal
  | some control =>
      have trace := menu.toRawTrace (initialDistribution setup) horizon scheduler history.trace
      rw [state] at trace terminal
      obtain ⟨source, read⟩ := serviceSourceReadout_exists_of_terminal setup
        setup.informationDependencies timeouts.duration leaks control
        (completes control trace terminal)
      change sourceReadout setup timeouts leaks (some control) = some source at read
      rw [exclusionBase_eq_readout_of_readout setup timeouts parameter
        (fun outcome i => utility outcome i + constant i)
        (fun i => excludedPayoff i + constant i) leaks _ _ read who,
        exclusionBase_eq_readout_of_readout setup timeouts parameter utility excludedPayoff
          leaks _ _ read who, read]
      simp only [exclusionReadoutUtility, Option.elim_some, exclusionTerminalUtility,
        exclusionUtility]
      split <;> rfl

/-- A change of utility origin preserves the certified deposit and audit.
The ordinary utility and fixed exit utility receive the same shift, so their
differences across terminal histories are preserved. -/
def addUtilityConstant
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler parameter utility
      excludedPayoff) (constant : Player → ℝ) :
    ClientSpec setup timeouts leaks bounds horizon scheduler parameter
      (fun outcome who => utility outcome who + constant who)
      (fun who => excludedPayoff who + constant who) :=
  { spec with
    exitBelow := fun history source read who =>
      add_le_add_left (spec.exitBelow history source read who) _
    funded := by
      intro compliant deviating who
      rw [terminal_base_add_constant (parameter := parameter) (utility := utility)
          (excludedPayoff := excludedPayoff) spec.completes constant _ deviating.1 deviating.2 who,
        terminal_base_add_constant (parameter := parameter) (utility := utility)
          (excludedPayoff := excludedPayoff) spec.completes constant _ compliant.1 compliant.2 who,
        add_sub_add_right_eq_sub]
      exact spec.funded compliant deviating who }

end Vegas.ClientSpec
