/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.Game
import Vegas.Pending.ReactiveFiniteResponses
import Vegas.Pending.ReactiveServiceSelection
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import Interaction.ReactiveReceipts
import GameTheoryExtensions.Math.Probability.Support

/-! # A monitored native service for the initialized guessing game

Alice has one ambient response before the ordinary two-event service. Watcher
independently receives all pending envelopes or none, each with probability one
half. A subsequent wire turn includes only an Alice envelope actually replayed
by Watcher. Bob sees pending envelopes before guessing. The source publications
then receive the usual grant, response, inclusion, and expiry service.

The liability below is an explicit extra utility charge on rejected Alice
receipts. Receipt persistence is implemented; collection of the charge is an
assumed utility interpretation, not an escrow implementation.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def nativeRuntime : EventGraphRuntime nativeGraph where
  deadline event := 2 ^ event.val

def pendingIds (pending : List (Message Player (WitnessedPacket nativeGraph))) :
    Finset (MessageId Player) := (pending.map Message.id).toFinset

def nativeLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph) :=
  fun who pending =>
    if who = watcher then
      mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure (pendingIds pending)) (PMF.pure ∅)
    else PMF.pure (if who = bob then pendingIds pending else ∅)

abbrev nativeApp := nativeRuntime.reactiveApplication nativeLeaks

def nativeInputs (bit : Bool) : nativeGraph.Inputs :=
  sourceSetup.eventInputs (initialState bit)

def nativeInitial (bit : Bool) : EventGraphRuntime.State nativeGraph := State.initial
    (nativeInputs bit)

def nativeInitialLaw : PMF (EventGraphRuntime.State nativeGraph) :=
  (PMF.uniformOfFintype Bool).map nativeInitial

/-- The complete bounded raw menu includes arbitrary event addresses, wrong
values and types, independently attached evidence, and replay. -/
def nativeBounds : MessageBounds nativeGraph where
  candidateCount := 1
  values := {⟨.bool, false⟩, ⟨.bool, true⟩, ⟨.int, 0⟩}

abbrev nativeMenu := nativeBounds.rawMenu nativeRuntime nativeLeaks

def nativeOwner (event : nativeGraph.EventId) : Player :=
  if event = bobPublication then bob else alice

theorem native_actor (event : nativeGraph.EventId) :
    nativeGraph.actor? event = some (nativeOwner event) := by
  fin_cases event <;> rfl

def nativeVisit (event : nativeGraph.EventId) : List (ServiceInstruction nativeGraph) :=
  [.grant event, .player (nativeOwner event), .includeLatest event (nativeOwner event)] ++
    List.replicate (nativeRuntime.deadline event) .tick ++ [.expire event]

def nativePlan : List (ServiceInstruction nativeGraph) :=
  [.player alice, .player watcher, .wire] ++
    [bobPublication, alicePublication].flatMap nativeVisit

/-- The scheduler checks a public rebroadcast. It never sees which packets
Watcher privately sampled, and a fresh Watcher-authored packet is not a report. -/
def nativeNetwork : nativeRuntime.NetworkPolicy nativeLeaks := fun _ view =>
  PMF.pure <| match view.network.inputs.getLast? with
  | none => .wait
  | some input =>
      if input.broadcaster = watcher ∧ input.envelope.sender = alice then
        .include input.envelope.id
      else .wait

def nativeScheduler : nativeApp.Scheduler := fun history view =>
  match nativePlan[history.length]? with
  | none => PMF.pure .wait
  | some instruction => nativeRuntime.interactionInstruction nativeLeaks
      nativeNetwork history view instruction

instance : nativeLeaks.FiniteSupport where
  support_finite who pending := by
    unfold nativeLeaks
    split_ifs
    · refine ((Set.finite_singleton (pendingIds pending)).union (Set.finite_singleton ∅)).subset ?_
      simpa only [PMF.support_pure] using support_mix_subset (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure (pendingIds pending)) (PMF.pure ∅)
    all_goals simp

instance : nativeNetwork.FiniteSupport := ⟨fun _ _ => by simp [nativeNetwork]⟩

instance : nativeApp.FiniteNature nativeInitialLaw nativeScheduler where
  initial_finite := by
    rw [nativeInitialLaw, PMF.support_map]
    exact (Set.toFinite _).image _
  scheduler_finite history view := by
    unfold nativeScheduler
    split
    · simp
    · exact nativeRuntime.interactionInstruction_support_finite nativeLeaks nativeNetwork
        history view _

abbrev nativeHorizon : Nat := nativePlan.length

abbrev nativeArena := nativeMenu.protocol nativeInitialLaw nativeHorizon nativeScheduler
abbrev nativeModel := nativeMenu.information nativeInitialLaw nativeHorizon nativeScheduler

theorem native_horizon : nativeHorizon = 14 := by decide

def aliceInput : nativeGraph.InputId := ⟨0, by decide⟩
def bobInput : nativeGraph.InputId := ⟨1, by decide⟩

def aliceHandle : Handle nativeGraph := (alice, .initial aliceInput)
def bobHandle : Handle nativeGraph := (bob, .initial bobInput)

def alicePublicationRef : EventGraph.FieldRef nativeGraph.layout (.publication .bool) :=
  ⟨.inr alicePublication, rfl⟩
def bobPublicationRef : EventGraph.FieldRef nativeGraph.layout (.publication .bool) :=
  ⟨.inr bobPublication, rfl⟩

def nativeResults (config : nativeGraph.Config) : Results where
  alice := (alicePublicationRef.get? config.store).getD .failure
  bob := (bobPublicationRef.get? config.store).getD .failure

def rejectedAlice (receipts : List (MessageId Player × Bool)) : Bool :=
  receipts.any (fun receipt => receipt.1.1 = alice && !receipt.2)

def nativeExecutionUtility (deposit : ℝ) (who : Player)
    (execution : nativeApp.Execution) : ℝ :=
  utility (nativeResults execution.application.config) who -
    if who = alice ∧ rejectedAlice execution.receipts then deposit else 0

def nativeUtility (deposit : ℝ) (who : Player) (state : nativeApp.ProtocolState) : ℝ :=
  state.elim 0 (fun control => nativeExecutionUtility deposit who control.execution)

/-- Native payoffs are bounded by the source payoffs plus the deposit, so every
continuation law has an integrable payoff. -/
theorem nativeExecutionUtility_abs_le (deposit : ℝ) (who : Player)
    (execution : nativeApp.Execution) :
    |nativeExecutionUtility deposit who execution| ≤ 5 + |deposit| := by
  have correct (a b : PublicationResult Bool) : 0 ≤ correctness a b ∧ correctness a b ≤ 1 := by
    cases a <;> simp only [correctness] <;> (try split_ifs) <;> norm_num
  have penalty (a : PublicationResult Bool) : 0 ≤ openingPenalty a ∧ openingPenalty a ≤ 4 := by
    cases a <;> simp only [openingPenalty] <;> norm_num
  have base (result : Results) : |utility result who| ≤ 5 := by
    unfold utility
    have := correct result.alice result.bob
    have := penalty result.alice
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  unfold nativeExecutionUtility
  refine (abs_sub _ _).trans (add_le_add (base _) ?_)
  split_ifs <;> simp

theorem nativeUtility_abs_le (deposit : ℝ) (who : Player) (state : nativeApp.ProtocolState) :
    |nativeUtility deposit who state| ≤ 5 + |deposit| := by
  cases state with
  | none => simp only [nativeUtility, Option.elim_none, abs_zero]; positivity
  | some control => exact nativeExecutionUtility_abs_le deposit who control.execution

theorem nativeExecutionUtility_integrable (deposit : ℝ) (who : Player)
    (law : PMF nativeApp.Execution) : PayoffIntegrable law (nativeExecutionUtility deposit who) :=
  payoffIntegrable_of_bounded _ _ (nativeExecutionUtility_abs_le deposit who)

theorem nativeExecutionValue_integrable {α : Type*} (deposit : ℝ) (who : Player) (μ : PMF α)
    (law : α → PMF nativeApp.Execution) :
    PayoffIntegrable μ (fun a => expect (law a) (nativeExecutionUtility deposit who)) :=
  payoffIntegrable_expect_of_bounded _ _ _ (by positivity)
    (nativeExecutionUtility_abs_le deposit who)

@[simp] theorem native_execution_utility_watcher (deposit : ℝ)
    (execution : nativeApp.Execution) :
    nativeExecutionUtility deposit watcher execution = 0 := by
  simp [nativeExecutionUtility, watcher, alice]

theorem initial_alice_handle (bit : Bool) :
    (nativeInitial bit).accepted (.inl aliceInput) = some aliceHandle := rfl

theorem initial_bob_handle (bit : Bool) :
    (nativeInitial bit).accepted (.inl bobInput) = some bobHandle := rfl

theorem initial_alice_candidate (bit : Bool) :
    (nativeInitial bit).candidates.lookup aliceHandle = .openable ⟨.bool, bit⟩ := by
  cases bit <;> rfl

theorem initial_bob_candidate (bit : Bool) :
    (nativeInitial bit).candidates.lookup bobHandle = .openable ⟨.bool, true⟩ := by
  cases bit <;> rfl

theorem initial_bob_ready (bit : Bool) :
    (nativeInitial bit).config.cut.Ready bobPublication := by
  cases bit <;> decide

theorem initial_alice_not_ready (bit : Bool) :
    ¬ (nativeInitial bit).config.cut.Ready alicePublication := by
  cases bit <;> decide

end Vegas.Examples.MonitoredGuessing
