/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSource
import Vegas.Pending.ReactiveServiceProgress
import Vegas.Pending.ReactiveFiniteResponses
import Vegas.Pending.ReactiveAsyncContract
import Interaction.PendingErasureSelection
import Interaction.ReactiveObservation

/-! # A public two-late service for the initialized three-instruction source

The compiled graph is unchanged. This example sets relative deadlines, samples
foreign pending identifiers through independent fair disclosure, and uses a
public padded schedule. Its late inclusion lottery competes over every pending
identifier, including malformed packets. The service-contract proof is separate
from constructing this scheduler and proving finite branching.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeService

open SourceProgram EventGraph EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource

def deadline (event : nativeGraph.EventId) : Nat :=
  if event = bobRevealEvent then 4 else 3

def runtime : EventGraphRuntime nativeGraph := serviceRuntime setup .sequential deadline

def delay (event : nativeGraph.EventId) : Nat :=
  if event = aliceEvent then 0 else if event = bobBindEvent then 2 else 3

def bound (event : nativeGraph.EventId) : Nat := if event = aliceEvent then 2 else 0

theorem timely : runtime.AsyncTimely delay bound := by
  intro event _
  change Fin 3 at event
  fin_cases event
  · change 0 + 2 < 3
    decide
  · change 2 + 0 < 3
    decide
  · change 3 + 0 < 4
    decide

def foreignPending (who : Player) (pending : List (Message Player (WitnessedPacket nativeGraph))) :
    Finset (MessageId Player) := (MessageNetwork.pendingIds pending).filter (fun id => id.1 ≠ who)

/-- Uniform subsets of the foreign pending pool make each identifier's sample
an independent fair coin. Sampling keeps already learned packets in recall. -/
def leaks : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph) :=
  fun who pending => PMF.uniformOfFinset (foreignPending who pending).powerset
    (by exact ⟨∅, Finset.empty_mem_powerset _⟩)

theorem leaks_supported (who : Player)
    (pending : List (Message Player (WitnessedPacket nativeGraph)))
    (selected : Finset (MessageId Player)) :
    selected ∈ (leaks who pending).support ↔ selected ⊆ foreignPending who pending := by
  rw [leaks, PMF.mem_support_uniformOfFinset_iff, Finset.mem_powerset]

instance finiteLeaks : leaks.FiniteSupport where
  support_finite who pending := by
    rw [leaks, PMF.support_uniformOfFinset]
    exact Finset.finite_toSet _

abbrev app := runtime.reactiveApplication leaks

abbrev initial : PMF app.State := serviceInitialLaw setup .sequential

/-- Protected author service issues a receipt even for an invalid call. -/
def latestAuthor (who : Player) (view : app.EnvironmentView) : app.Command :=
  match view.network.pending.reverse.find? (fun message =>
      message.sender = who ∧ view.Unpublished app message.id) with
  | none => .wait
  | some message => .include message.id

def stageChoice (weight : ℝ) (nonnegative : 0 ≤ weight)
    (position : Nat) (view : app.EnvironmentView) : PMF app.Command :=
  match position with
  | 0 | 3 | 7 => PMF.pure (.activate alice)
  | 1 => PMF.pure (latestAuthor alice view)
  | 4 | 11 | 19 => PMF.pure (.activate bob)
  | 5 | 12 | 20 => PMF.pure (latestAuthor bob view)
  | 8 => app.pendingLotteryScheduler weight nonnegative [] view
  | 10 => PMF.pure (.application (.expire aliceEvent))
  | 13 => PMF.pure (if bobBindEvent ∈ view.application.observation.completionOrder
      then .activate bob else .wait)
  | 14 => PMF.pure (if bobBindEvent ∈ view.application.observation.completionOrder
      then latestAuthor bob view else .wait)
  | 18 => PMF.pure (.application (.expire bobBindEvent))
  | 25 => PMF.pure (.application (.expire bobRevealEvent))
  | 2 | 6 | 9 | 15 | 16 | 17 | 21 | 22 | 23 | 24 => PMF.pure (.application .advanceClock)
  | _ => PMF.pure .wait

def scheduler (weight : ℝ) (nonnegative : 0 ≤ weight) : app.Scheduler :=
  fun past view => stageChoice weight nonnegative past.length view

abbrev horizon : Nat := 26

private theorem lottery_support_finite (weight : ℝ) (nonnegative : 0 ≤ weight)
    (view : app.EnvironmentView) :
    (app.pendingLotteryScheduler weight nonnegative [] view).support.Finite := by
  rw [ReactiveApplication.pendingLotteryScheduler, PMF.support_map]
  apply Set.Finite.image
  apply ((MessageNetwork.chooseUniform_support_finite
    (MessageNetwork.pendingIds view.network.pending)).union (Set.finite_singleton none)).subset
  intro selected supported
  have choices := support_mix_subset _ _ _ _ _ supported
  rcases choices with chosen | idle
  · exact Or.inl chosen
  · exact Or.inr ((PMF.mem_support_pure_iff _ _).mp idle)

theorem stageChoice_support_finite (weight : ℝ) (nonnegative : 0 ≤ weight)
    (position : Nat) (view : app.EnvironmentView) :
    (stageChoice weight nonnegative position view).support.Finite := by
  unfold stageChoice
  split <;> try simp only [PMF.support_pure, Set.finite_singleton]
  exact lottery_support_finite weight nonnegative view

instance finiteNature (weight : ℝ) (nonnegative : 0 ≤ weight) :
    app.FiniteNature initial (scheduler weight nonnegative) where
  initial_finite := serviceInitialLaw_support_finite setup .sequential
  scheduler_finite past view := stageChoice_support_finite weight nonnegative past.length view

def rawValues : Finset (Raw simpleExpr) := by
  classical
  exact (Finset.univ.image (fun bit : Bool => (⟨.bool, bit⟩ : Raw simpleExpr))) ∪
    (Finset.univ.image (fun label : Fin 3 => (⟨.range 0 2, labelValue label⟩ : Raw simpleExpr))) ∪
    (Finset.univ.image (fun answer : Fin 6 => (⟨.range 0 5, answerValue answer⟩ : Raw simpleExpr)))

def bounds : MessageBounds nativeGraph where
  candidateCount := horizon
  values := rawValues

abbrev rawMenu := bounds.rawMenu runtime leaks

instance finiteRawHistory (weight : ℝ) (nonnegative : 0 ≤ weight) :
    Finite (rawMenu.protocol initial horizon (scheduler weight nonnegative)).History :=
  inferInstance

theorem bool_covered (bit : Bool) : (⟨.bool, bit⟩ : Raw simpleExpr) ∈ bounds.values := by
  classical
  change _ ∈ rawValues
  unfold rawValues
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨bit, Finset.mem_univ bit, rfl⟩

theorem label_covered (label : Fin 3) :
    (⟨.range 0 2, labelValue label⟩ : Raw simpleExpr) ∈ bounds.values := by
  classical
  change _ ∈ rawValues
  unfold rawValues
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨label, Finset.mem_univ label, rfl⟩

theorem answer_covered (answer : Fin 6) :
    (⟨.range 0 5, answerValue answer⟩ : Raw simpleExpr) ∈ bounds.values := by
  classical
  change _ ∈ rawValues
  unfold rawValues
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨answer, Finset.mem_univ answer, rfl⟩

end Vegas.Examples.LateOpeningRuntimeService
