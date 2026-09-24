/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationNative
import Vegas.Compile.EventGraphReadout

/-! # The selective-association utilities are the compiled settlement payoffs

The source returns the three signed integer payoff expressions. On every
completed native configuration, their compiled evaluation is exactly the
fixed utility used by the sequential-equilibrium obstruction. The equality
is pointwise, so it also covers histories reached only through deviations.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.SourceProgram Vegas.SourceProgram.EventLowering

/-- Evaluate the program's declared payoff on its public result carrier. -/
def returnedPayoff (result : Results) (who : Player) : ℝ :=
  (evalExpr (payoffExpr who)
    (Env.cons result.bob (Env.cons result.carol (Env.cons result.alice (Env.empty _)))) : ℝ)

theorem returnedPayoff_eq_utility (result : Results) (who : Player) :
    returnedPayoff result who = utility result who :=
  payoffExpr_eq_utility _ who

def terminalSourceState (config : nativeGraph.Config) :
    State simpleExpr sourceProgram.terminalCtx :=
  Env.cons (nativeResults config).bob <|
  Env.cons (nativeResults config).carol <|
  Env.cons (nativeResults config).alice <|
  Env.cons ((bobBindingRef.get? config.store).getD .failure) <|
  Env.cons ((carolBindingRef.get? config.store).getD .failure) <|
  Env.cons ((aliceBindingRef.get? config.store).getD .failure) <|
  Env.empty _

theorem terminal_reference_value (config : nativeGraph.Config)
    (terminal : config.cut.Terminal) {field : EventGraph.EventField Player simpleExpr}
    (reference : EventGraph.FieldRef nativeGraph.layout field)
    (fallback : field.Value) :
    reference.get? config.store = some ((reference.get? config.store).getD fallback) := by
  have available := reference.get?_isSome config.store
    (config.store_available_of_terminal terminal reference.field)
  cases read : reference.get? config.store with
  | none => simp [read] at available
  | some value => rfl

theorem terminal_source_agrees (config : nativeGraph.Config)
    (terminal : config.cut.Terminal) :
    (terminalRefs sourceProgram).Agrees (terminalSourceState config) config.store := by
  intro name cell source
  cases source with
  | here => exact terminal_reference_value config terminal bobPublicationRef .failure
  | there source => cases source with
    | here => exact terminal_reference_value config terminal carolPublicationRef .failure
    | there source => cases source with
      | here => exact terminal_reference_value config terminal alicePublicationRef .failure
      | there source => cases source with
        | here => exact terminal_reference_value config terminal bobBindingRef .failure
        | there source => cases source with
          | here => exact terminal_reference_value config terminal carolBindingRef .failure
          | there source => cases source with
            | here => exact terminal_reference_value config terminal aliceBindingRef .failure
            | there source => nomatch source

/-- Every terminal native settlement uses precisely the fixed public-result
utilities of the counterexample. No preference over private data or traffic
is needed. -/
theorem native_settlement_eq_utility (config : nativeGraph.Config)
    (terminal : config.cut.Terminal) :
    (config.terminalPayoffs terminal).map (fun payoff => (payoff.1, (payoff.2 : ℝ))) =
      [(alice, utility (nativeResults config) alice),
        (bob, utility (nativeResults config) bob),
        (carol, utility (nativeResults config) carol)] := by
  have sourceEq := terminalPayoffs_eq_source sourceProgram config terminal
    (terminalSourceState config) (terminal_source_agrees config terminal)
  have mapped := congrArg (List.map (fun payoff : Player × Int =>
    (payoff.1, (payoff.2 : ℝ)))) sourceEq
  exact mapped.trans (source_settlement_eq_utility (terminalSourceState config))

/-- Read Alice's entry from the actual compiled terminal settlement. The
default applies only to unfinished executions, excluded by the fixed service. -/
def nativeAlicePayout (config : nativeGraph.Config) : ℝ :=
  if terminal : config.cut.Terminal then
    (((config.terminalPayoffs terminal).map (fun payoff =>
      (payoff.1, (payoff.2 : ℝ)))).headD (alice, 0)).2
  else 0

theorem nativeAlicePayout_eq_utility (config : nativeGraph.Config)
    (terminal : config.cut.Terminal) :
    nativeAlicePayout config = utility (nativeResults config) alice := by
  have equality := congrArg (fun payouts : List (Player × ℝ) =>
    (payouts.headD (alice, 0)).2) (native_settlement_eq_utility config terminal)
  simpa [nativeAlicePayout, terminal] using equality

end VegasTests.SelectiveAssociation
