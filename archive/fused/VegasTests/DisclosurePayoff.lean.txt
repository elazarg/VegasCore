/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureCorrespondence
import VegasTests.DisclosureAccounting

/-! # Compiled public payoffs for the disclosure process

Changing the final payoff expressions leaves the information and execution
graph unchanged. The strategic correspondence therefore applies to every
payoff list in the terminal public context, without replacing the actual
machine utility by an unrelated abstract utility.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

abbrev Payouts := List (TestPlayer × Expr PayoffContext .int)

def sourceWithPayoffs (payouts : Payouts) : GraphProgram TestPlayer simpleExpr where
  Γ := []
  prog := coreWithPayoffs payouts
  env := VEnv.empty simpleExpr
  wctx := by simp
  fresh := by simp [coreWithPayoffs, FreshBindings, Fresh]

theorem legalWithPayoffs (payouts : Payouts) : Legal (sourceWithPayoffs payouts).prog := by
  unfold sourceWithPayoffs coreWithPayoffs
  constructor
  · intro _; exact ⟨false, rfl⟩
  · constructor
    · intro _; exact ⟨false, rfl⟩
    · constructor
      · intro _; exact ⟨none, rfl⟩
      · constructor
        · intro _; exact ⟨false, rfl⟩
        · trivial

/-- Checked admission uses the same conditional-publication plan for every
public payoff list; the source choices and their information are unchanged. -/
def checkedWithPayoffs (payouts : Payouts) : WFProgram TestPlayer simpleExpr where
  core := sourceWithPayoffs payouts
  accounted := DisclosureAccounting.optionalPlanWithPayoffs payouts
  legal := legalWithPayoffs payouts

instance finiteDomainsWithPayoffs (payouts : Payouts) :
    FiniteDomains (checkedWithPayoffs payouts) where
  context := inferInstanceAs (FiniteVCtx ([] : VCtx TestPlayer simpleExpr))
  program := {
    proof := .commit inferInstance (.commit inferInstance (.reveal inferInstance
      (.sample inferInstance (.commit inferInstance (.reveal inferInstance
        (.commit inferInstance (.reveal inferInstance .ret))))))) }

def finiteUtility (payouts : Payouts) (data : RunData) (who : TestPlayer) : ℝ :=
  (evalPayoffs payouts (terminalEnv data.secret data.signal data.opening data.response) who : ℝ)

def finiteGame (payouts : Payouts) : UtilityGame TestPlayer where
  form := finiteForm
  utility := finiteUtility payouts

theorem cfg_payoff (payouts : Payouts) (data : RunData) :
    evalPayoffs? (ToEventGraph.compile (sourceWithPayoffs payouts)).payoffs (cfg data 8).store =
      some (evalPayoffs payouts
        (terminalEnv data.secret data.signal data.opening data.response)) := by
  let compiled := ToEventGraph.compile (sourceWithPayoffs payouts)
  let env := terminalEnv data.secret data.signal data.opening data.response
  have hstore : ∀ {name ty} (binding : VHasVar compiled.terminalCtx name ty),
      Store.getAs (cfg data 8).store (compiled.terminalState.fieldOf binding) ty.base =
        some (env name ty binding) := by
    intro name ty binding
    cases binding with
    | here => rfl
    | there binding => cases binding with
      | here => rfl
      | there binding => cases binding with
        | here => rfl
        | there binding => cases binding with
          | here => rfl
          | there binding => cases binding with
            | here => rfl
            | there binding => cases binding with
              | here => rfl
              | there binding => cases binding with
                | here => rfl
                | there binding => cases binding with
                  | here => rfl
                  | there binding => cases binding
  let available : ∀ {name ty} (binding : VHasVar compiled.terminalCtx name ty),
      ∃ value, Store.getAs (cfg data 8).store
        (compiled.terminalState.fieldOf binding) ty.base = some value :=
    fun binding => ⟨env _ _ binding, hstore binding⟩
  have henv : ToEventGraph.sourceEnvOfStore compiled.terminalState
      (cfg data 8).store available = env := by
    funext name ty binding
    exact Option.some.inj
      ((ToEventGraph.sourceEnvOfStore_get compiled.terminalState
        (cfg data 8).store available binding).symm.trans (hstore binding))
  have heval := compiled.evalPayoffs_eq_sourceEnvOfStore (cfg data 8).store available
  rw [henv] at heval
  exact heval

end VegasTests.OptionalDisclosure
