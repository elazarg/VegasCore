/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureApplicationLaw
import VegasTests.DisclosureOwnerSettlement
import VegasTests.DisclosureResponderSettlement
import VegasTests.DisclosureSignalLaw
import GameTheory.Core.Approximate

/-! # Exact responder deviations under resolving public service

For the checked disclosure application, a fixed pure owner retains its binding
and signal-dependent publication against every raw responder policy. Reserved
inclusion service and a positive response window ensure completion; the public
chance law is unchanged. Conditioning on that public signal gives a legal
source responder policy with exactly the runtime's terminal-environment law.

The source comparison uses the written AST and replaces only the responder.
This is a result for this application specialization and fixed pure owner,
not a general compiler theorem or a result about owner deviations. Runtime
policies may depend on their full message views and histories. The outcome
projection retains completion and the source terminal environment, not runtime
traffic or clock values.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Vegas Interaction GameTheory GameTheory.Math.Probability

variable {window : Nat}

private def signalRead (next : (application window).PolicyExecution) : Bool :=
  next.native.application.signal.getD false

private def responseRead (next : (application window).PolicyExecution) : Bool :=
  next.native.application.response.getD false

private theorem sourceOutcome_of_owner (secret : Bool) (complete : Bool → Bool → Bool)
    (hwindow : 1 ≤ window)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete))
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : window + 3 ≤ cycles)
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window cycles selector).play players).support) :
    sourceOutcome? next = some (terminalEnv secret (signalRead next)
      (if complete secret (signalRead next) then some secret else none) (responseRead next)) := by
  obtain ⟨signal, haccepted, hstored, hsignal, hpublication⟩ :=
    owner_choices_preserved secret complete hwindow players howner selector hselector
      cycles (by omega) next hnext
  have hcomplete := owner_settles_by_cycle secret complete hwindow players howner
    selector hselector cycles hcycles next hnext
  simp [sourceOutcome?, policyData?, hcomplete, data, boundValue?, haccepted,
    DisclosureBinding.value?, hstored, hsignal, hpublication, signalRead, responseRead]

private theorem fibre_support {α : Type} (law : FinDist α) (read : α → Bool)
    (bit : Bool) (hbit : bit ∈ (law.map read).support)
    (value : α) (hvalue : value ∈ (law.condOnFibre read bit).support) :
    read value = bit ∧ value ∈ law.support := by
  classical
  rw [FinDist.support_map] at hbit
  obtain ⟨witness, hwitness, hread⟩ := hbit
  have hfibre : ∃ a ∈ read ⁻¹' {bit}, a ∈ law.support := ⟨witness, hread, hwitness⟩
  rw [FinDist.condOnFibre, dif_pos hfibre] at hvalue
  exact law.support_condOn _ hfibre hvalue

private theorem response_law_of_signal_law
    (payouts : List (TestPlayer × Expr PayoffContext .int))
    (secret : Bool) (complete : Bool → Bool → Bool) (original : Bool → Option Bool → Bool)
    (hwindow : 1 ≤ window)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete))
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : window + 3 ≤ cycles)
    (hsignal : (((serviceGame window cycles selector).play players).map signalRead) =
      fairCoin.denote) :
    ∃ replacement : SourceBehavioralPolicy (coreWithPayoffs payouts) (1 : TestPlayer),
      (((serviceGame window cycles selector).play players).map sourceOutcome?) =
        (denoteSource (coreWithPayoffs payouts)
          (Profile.update (sig := sourceGameSignature (coreWithPayoffs payouts))
            (SourcePolicies.pureProfile payouts secret complete original) 1 replacement)
          (VEnv.empty simpleExpr)).map some := by
  let law := (serviceGame window cycles selector).play players
  let response : Bool → Option Bool → FinDist Bool := fun bit _ =>
    (law.condOnFibre signalRead bit).map responseRead
  refine ⟨SourcePolicies.responseStrategy payouts response, ?_⟩
  rw [SourcePolicies.responseStrategy_law, FinDist.map_bind]
  calc
    law.map sourceOutcome? =
        (law.map signalRead).bind (fun bit =>
          (law.condOnFibre signalRead bit).map sourceOutcome?) := by
      conv_lhs => rw [law.eq_bind_condOnFibre signalRead]
      exact FinDist.map_bind _ _ _
    _ = fairCoin.denote.bind (fun bit =>
        ((response bit (if complete secret bit then some secret else none)).map
          (terminalEnv secret bit (if complete secret bit then some secret else none))).map
            some) := by
      rw [hsignal]
      apply FinDist.bind_congr
      intro bit hbit
      simp only [response, FinDist.map_comp, Function.comp_def]
      apply FinDist.map_congr_of_eq_on_support
      intro next hnext
      obtain ⟨hread, hsupport⟩ := fibre_support law signalRead bit
        (by simpa only [law, hsignal] using hbit) next hnext
      rw [sourceOutcome_of_owner secret complete hwindow players howner selector hselector
        cycles hcycles next hsupport, hread]

private theorem reference_law_of_signal_law (secret : Bool)
    (complete : Bool → Bool → Bool) (response : Bool → Option Bool → Bool)
    (hwindow : 1 ≤ window)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : window + 3 ≤ cycles)
    (hsignal : (((serviceGame window cycles selector).play
        (honestPlayers secret complete response)).map signalRead) = fairCoin.denote) :
    (((serviceGame window cycles selector).play
      (honestPlayers secret complete response)).map sourceOutcome?) =
        (denoteSource source.prog (SourcePolicies.pureProfile [(0, payoff)]
          secret complete response) source.env).map some := by
  change _ = (denoteSource (coreWithPayoffs [(0, payoff)])
    (SourcePolicies.pureProfile [(0, payoff)] secret complete response)
    (VEnv.empty simpleExpr)).map some
  rw [SourcePolicies.pure_law, FinDist.map_comp]
  rw [← hsignal, FinDist.map_comp]
  apply FinDist.map_congr_of_eq_on_support
  intro next hnext
  have howner := sourceOutcome_of_owner secret complete hwindow
    (honestPlayers secret complete response) rfl selector hselector cycles hcycles next hnext
  have hcomplete := owner_settles_by_cycle secret complete hwindow
    (honestPlayers secret complete response) rfl selector hselector cycles hcycles next hnext
  rcases responder_choice_preserved response hwindow (honestPlayers secret complete response)
      rfl selector hselector cycles next hnext with hnone | ⟨signal, opening, hs, hp, hr⟩
  · simp [outcome?, hnone] at hcomplete
  · obtain ⟨ownerSignal, _, _, hos, hop⟩ := owner_choices_preserved secret complete hwindow
      (honestPlayers secret complete response) rfl selector hselector cycles (by omega) next hnext
    have heq : signal = ownerSignal := Option.some.inj (hs.symm.trans hos)
    subst ownerSignal
    have hopening : opening = if complete secret signal then some secret else none :=
      Option.some.inj (hp.symm.trans hop)
    rw [howner]
    simp [Function.comp_def, signalRead, responseRead, hs, hr, hopening]

/-- Exact written-source law for compiled pure profiles under the resolving
service, with any admitted adaptive inclusion selector. -/
theorem resolving_compiled_source_law (secret : Bool)
    (complete : Bool → Bool → Bool) (response : Bool → Option Bool → Bool)
    (hwindow : 1 ≤ window)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : window + 3 ≤ cycles) :
    (((serviceGame window cycles selector).play
      (compiledPlayers (SourcePolicies.pureProfile [(0, payoff)]
        secret complete response))).map sourceOutcome?) =
      (denoteSource source.prog (SourcePolicies.pureProfile [(0, payoff)]
        secret complete response) source.env).map some := by
  rw [compiledPlayers_pure]
  exact reference_law_of_signal_law secret complete response hwindow selector hselector
    cycles hcycles (owner_service_signal_law secret complete hwindow
      (honestPlayers secret complete response) rfl selector hselector cycles hcycles)

/-- Every unilateral raw responder deviation has the law of one source
behavioral responder deviation. The compiled owner is unchanged. Settlement
is proved from the stated service and window, not assumed or conditioned on. -/
theorem resolving_responder_deviation_law (secret : Bool)
    (complete : Bool → Bool → Bool) (response : Bool → Option Bool → Bool)
    (hwindow : 1 ≤ window)
    (replacement : (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : window + 3 ≤ cycles) :
    ∃ sourceReplacement : SourceBehavioralPolicy source.prog (1 : TestPlayer),
      (((serviceGame window cycles selector).play
        (Profile.update (sig := (application window).policySignature)
          (compiledPlayers (SourcePolicies.pureProfile [(0, payoff)]
            secret complete response)) 1 replacement)).map sourceOutcome?) =
        (denoteSource source.prog
          (Profile.update (sig := sourceGameSignature source.prog)
            (SourcePolicies.pureProfile [(0, payoff)] secret complete response)
            1 sourceReplacement) source.env).map some := by
  let players := Profile.update (sig := (application window).policySignature)
    (compiledPlayers (SourcePolicies.pureProfile [(0, payoff)] secret complete response))
    1 replacement
  have howner : players 0 =
      ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete) := by
    dsimp only [players]
    rw [Profile.update_of_ne _ _ (by decide : (0 : TestPlayer) ≠ 1), compiledPlayers_pure]
    rfl
  exact response_law_of_signal_law [(0, payoff)] secret complete response hwindow
    players howner selector hselector cycles hcycles
    (owner_service_signal_law secret complete hwindow players howner selector hselector
      cycles hcycles)

/-- An arbitrary valuation of source terminal outcomes has the same worst-case
lower bound against raw runtime responder deviations. No assumption about the
responder's utility appears. -/
theorem resolving_owner_guarantee (secret : Bool)
    (complete : Bool → Bool → Bool) (response : Bool → Option Bool → Bool)
    (hwindow : 1 ≤ window)
    (replacement : (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : window + 3 ≤ cycles)
    (value : Option (VEnv simpleExpr TerminalContext) → ℝ) (bound : ℝ)
    (hbound : ∀ sourceReplacement : SourceBehavioralPolicy source.prog (1 : TestPlayer),
      bound ≤ ((denoteSource source.prog
        (Profile.update (sig := sourceGameSignature source.prog)
          (SourcePolicies.pureProfile [(0, payoff)] secret complete response)
          1 sourceReplacement) source.env).map some).expect value) :
    bound ≤ (((serviceGame window cycles selector).play
      (Profile.update (sig := (application window).policySignature)
        (compiledPlayers (SourcePolicies.pureProfile [(0, payoff)] secret complete response))
        1 replacement)).map sourceOutcome?).expect value := by
  obtain ⟨sourceReplacement, hlaw⟩ := resolving_responder_deviation_law secret complete
    response hwindow replacement selector hselector cycles hcycles
  rw [hlaw]
  exact hbound sourceReplacement

/-- The source responder's epsilon-best-response property survives every raw
runtime replacement with the same error. This is one player's incentive
guarantee, not a Nash theorem for both players. -/
theorem resolving_responder_bestResponse (secret : Bool)
    (complete : Bool → Bool → Bool) (response : Bool → Option Bool → Bool)
    (hwindow : 1 ≤ window)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : window + 3 ≤ cycles)
    (utility : Option (VEnv simpleExpr TerminalContext) → TestPlayer → ℝ) (epsilon : ℝ)
    (hsource : IsεBestResponse (sourceGameForm source.prog source.env)
      (fun terminal => utility (some terminal)) epsilon 1
      (SourcePolicies.pureProfile [(0, payoff)] secret complete response)
      (SourcePolicies.pureProfile [(0, payoff)] secret complete response 1)) :
    IsεBestResponse (serviceGame window cycles selector)
      (fun execution => utility (sourceOutcome? execution)) epsilon 1
      (compiledPlayers (SourcePolicies.pureProfile [(0, payoff)] secret complete response))
      (compiledPlayers (SourcePolicies.pureProfile [(0, payoff)] secret complete response) 1) := by
  intro replacement
  obtain ⟨sourceReplacement, hdeviation⟩ := resolving_responder_deviation_law secret complete
    response hwindow replacement selector hselector cycles hcycles
  have hreference := resolving_compiled_source_law secret complete response hwindow
    selector hselector cycles hcycles
  have hbound := hsource sourceReplacement
  simp only [euPreferenceWithin, expectedUtility, Profile.update_eq_self,
    sourceGameForm_play] at hbound ⊢
  have hdeviationUtility := congrArg
    (fun law : FinDist (Option (VEnv simpleExpr TerminalContext)) =>
      law.expect (fun outcome => utility outcome 1)) hdeviation
  have hreferenceUtility := congrArg
    (fun law : FinDist (Option (VEnv simpleExpr TerminalContext)) =>
      law.expect (fun outcome => utility outcome 1)) hreference
  simp only [FinDist.expect_map] at hdeviationUtility hreferenceUtility
  exact hdeviationUtility.le.trans
    (hbound.trans_eq (congrArg (fun value => value + epsilon) hreferenceUtility.symm))

end VegasTests.OptionalDisclosure.DisclosureState

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.resolving_compiled_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.resolving_compiled_source_law

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.resolving_responder_deviation_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.resolving_responder_deviation_law

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.resolving_owner_guarantee'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.resolving_owner_guarantee

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.resolving_responder_bestResponse'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.resolving_responder_bestResponse
