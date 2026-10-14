/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRosterAsync
import Vegas.Game.OnePacketCertificateAssembly
import Vegas.Expr.Simple

/-! # The structural hypotheses of one-packet preservation for committed matching pennies

Alice and Bob each commit a hidden Boolean in the game, then Alice and Bob
reveal theirs. Alice wins when the revealed bits match and Bob wins otherwise;
a failed reveal leaves the game drawn. On the default sequential runtime under
the fixed roster calendar with an empty leak rule, the program satisfies the
structural hypotheses of the one-packet preservation theorem
(`Vegas.onePacket_intended_sequentialEquilibrium_of_blindInputs`): the setup is
well formed, the calendar is an asynchronous service with timely bounds
(`Vegas.rosterScheduler_asyncContract`, `Vegas.rosterScheduler_asyncTimely`),
the canonical menu retains first covered canonical packets, the message bounds
cover every output value with spare candidate capacity, the late options cover
the bounded slots, and the utility is bounded with an exclusion payoff below
every intended outcome.
-/

noncomputable section

namespace Vegas.Examples.OnePacketCommitRevealHypotheses

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol

abbrev Player := Fin 2
abbrev alice : Player := 0
abbrev bob : Player := 1

/-- Every Boolean may be committed. -/
def acceptGuard {Γ : SourceCtx Player simpleExpr} (who : Player) (name : VarId) :
    SourceGuard simpleExpr Γ who name .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by simp
  code := .constBool true
  reads := fun h => nomatch h

/-- Both bits are bound before Alice and then Bob reveal them. -/
def program : SourceProgram Player simpleExpr [] ∅ :=
  .commit 0 alice (by decide) (acceptGuard alice 0) <|
  .commit 1 bob (by decide) (acceptGuard bob 1) <|
  .reveal 2 alice 0 (by decide) (.there .here) (by decide) <|
  .reveal 3 bob 1 (by decide) (.there .here) (by decide) <|
  .ret []

def setup : Setup (Player := Player) (L := simpleExpr) where
  context := []
  namesNodup := by decide
  initialLaw := PMF.pure (Env.empty (CellVal simpleExpr))
  obligations := ∅
  program := program
  accounts := rfl

instance finiteInitial : setup.FiniteInitialLaw where
  support_finite := by
    change (PMF.pure (Env.empty (CellVal simpleExpr))).support.Finite
    rw [PMF.support_pure]
    exact Set.finite_singleton _

theorem wellFormed : setup.WellFormed where
  initialValues := by
    intro initial _ name owner payload cell
    cases cell
  guardsSatisfiable := by
    intro initial _
    refine ⟨⟨true, rfl⟩, fun _ _ => ⟨⟨true, rfl⟩, fun _ _ => trivial⟩⟩

abbrev nativeGraph := graph setup

/-- Nothing leaks. -/
def leaks : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph) :=
  fun _ _ => PMF.pure ∅

instance finiteLeaks : leaks.FiniteSupport where
  support_finite := by intro who pending; simp [leaks]

/-- Both players are activated at every event. -/
def rosters (_ : nativeGraph.EventId) : List Player := [alice, bob]

/-- The calendar never consults its network policy. -/
def network : (runtime setup).NetworkPolicy leaks := fun _ _ => PMF.pure .wait

theorem opportunities : ActorOpportunities setup rosters := by
  intro event owner _
  fin_cases owner <;> simp [rosters]

abbrev horizon : Nat := (rosterPlan setup rosters).length

abbrev scheduler : (application setup leaks).Scheduler :=
  rosterScheduler setup leaks rosters network

abbrev delay (event : nativeGraph.EventId) : Nat := event.val

abbrev bound (_ : nativeGraph.EventId) : Nat := 0

theorem contract :
    AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay bound :=
  rosterScheduler_asyncContract setup leaks rosters network opportunities

theorem timely : AsyncTimely (runtime setup) delay bound :=
  rosterScheduler_asyncTimely setup

open Classical in
/-- Message bounds with two prepared slots and every Boolean value. -/
def bounds : MessageBounds nativeGraph where
  candidateCount := 2
  values := Finset.univ.image fun bit : Bool => (⟨.bool, bit⟩ : Raw simpleExpr)

theorem covers : bounds.CoversOutputValues := by
  intro event
  change Fin 4 at event
  fin_cases event <;>
    (intro value
     exact Finset.mem_image.mpr ⟨value, Finset.mem_univ _, rfl⟩)

theorem capacity : ∀ who, bindingEventCount nativeGraph who < bounds.candidateCount := by
  intro who
  change (Finset.univ.filter fun event => bindingOwnedBy nativeGraph who event = true).card < 2
  fin_cases who <;> decide

/-- Each player binds once in the game: the bindings are in-game events. -/
theorem binding_events : bindingEventCount nativeGraph alice = 1 ∧
    bindingEventCount nativeGraph bob = 1 := by
  constructor <;> decide

theorem retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound :=
  retainsCoveredCanonical_of_adequate bounds covers capacity horizon scheduler bound

/-- As many late slots as bounded prepared slots. -/
abbrev slots : Nat := 2

theorem slots_pos : 0 < slots := by decide

theorem slotsCover : bounds.candidateCount ≤ slots := le_rfl

theorem slotsLe : slots ≤ bounds.candidateCount := le_rfl

theorem oneSlot : 1 ≤ bounds.candidateCount := by decide

/-- Matching pennies on the revealed bits: Alice wins a match and Bob a mismatch;
a failed reveal draws. -/
def pennies (aliceBit bobBit : PublicationResult Bool) (who : Player) : ℝ :=
  match aliceBit, bobBit with
  | .success first, .success second =>
      if (first = second) = (who = alice) then 1 else -1
  | _, _ => 0

def utility : Unit × PublicOutcome program → Player → ℝ := fun pair who =>
  pennies (pair.2.get (.there .here)) (pair.2.get .here) who

/-- A failed delivery costs more than losing. -/
def excludedPayoff : Player → ℝ := fun _ => -2

theorem lower_le : ∀ outcome who, (fun _ => (-1 : ℝ)) who ≤ utility outcome who := by
  intro outcome who
  simp only [utility, pennies]
  split
  · split <;> norm_num
  · norm_num

theorem le_upper : ∀ outcome who, utility outcome who ≤ (fun _ => (1 : ℝ)) who := by
  intro outcome who
  simp only [utility, pennies]
  split
  · split <;> norm_num
  · norm_num

theorem below (parameter : State simpleExpr setup.context → Unit) :
    ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who := by
  intro _ terminal _ who
  have := lower_le (setup.parameterOutcome parameter terminal) who
  simp only [excludedPayoff] at this ⊢
  linarith

/-- **The structural hypotheses hold together.** -/
theorem structural (parameter : State simpleExpr setup.context → Unit) :
    setup.WellFormed ∧
      AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay bound ∧
      AsyncTimely (runtime setup) delay bound ∧
      RetainsCoveredCanonical setup leaks bounds horizon scheduler bound ∧
      bounds.CoversOutputValues ∧
      (∀ who, bindingEventCount nativeGraph who < bounds.candidateCount) ∧
      0 < slots ∧ bounds.candidateCount ≤ slots ∧ slots ≤ bounds.candidateCount ∧
      1 ≤ bounds.candidateCount ∧
      (∀ (final : setup.intendedProtocol.History) terminal,
        setup.protocolReadout final.state = some terminal →
          ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who) :=
  ⟨wellFormed, contract, timely, retains, covers, capacity, slots_pos, slotsCover, slotsLe,
    oneSlot, below parameter⟩

open Classical in
/-- The one-packet preservation theorem applies to committed matching pennies:
its structural hypotheses and instance requirements are met, leaving the
intended sequential equilibrium and the inputs by value blindness. -/
example (parameter : State simpleExpr setup.context → Unit) :=
  have : Finite setup.intendedProtocol.History := setup.intended_finite_history
    ⟨inferInstance, inferInstance, trivial⟩
  onePacket_intended_sequentialEquilibrium_of_blindInputs setup leaks bounds horizon scheduler
    parameter utility excludedPayoff wellFormed contract timely retains (fun _ => -1)
    (fun _ => 1) lower_le le_upper (below parameter)

end Vegas.Examples.OnePacketCommitRevealHypotheses
