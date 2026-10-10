/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.PendingOutsideSelection
import Interaction.ReactiveErasure
import Interaction.ReactiveSchedulerObservation

/-! # Public pending lotteries commute with envelope erasure

The lottery gives every distinct pending identifier one common weight and
gives waiting weight one. It inspects no payload, application state, or command
recall. Its law is exactly a mixture of including any selected pending envelope
and its law with that envelope erased, restoring the remaining identifiers.

These are operational selection results. This scheduler alone supplies no
protected receipt, activation, deadline, or completion promise.
-/

noncomputable section

namespace Interaction

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal]

namespace MessageId

/-- Erasing a restored identifier recovers every identifier in the erased world. -/
theorem erase_restore (removed id : MessageId Principal) :
    erase removed (restore removed id) = id := by
  rcases removed with ⟨who, gone⟩
  rcases id with ⟨author, serial⟩
  unfold restore erase
  by_cases shifted : author = who ∧ gone ≤ serial
  · obtain ⟨rfl, below⟩ := shifted
    simp [below, Nat.lt_succ_of_le below]
  · have notLater : ¬ (author = who ∧ gone < serial) :=
      fun both => shifted ⟨both.1, both.2.le⟩
    simp only [shifted, ↓reduceIte, notLater]

/-- Restoring identifiers is injective even without finite carrier assumptions. -/
theorem restore_injective (removed : MessageId Principal) :
    Function.Injective (restore removed) := by
  intro first second same
  have erased := congrArg (erase removed) same
  simpa only [erase_restore] using erased

end MessageId

namespace MessageNetwork

variable {Payload : Type}

/-- Every distinct pending identifier competes, including malformed packets. -/
def pendingIds (pending : List (Message Principal Payload)) : Finset (MessageId Principal) :=
  (pending.map Message.id).toFinset

/-- Payload changes preserving identifiers cannot affect the inclusion law. -/
theorem pendingIds_eq_of_map_id_eq
    (first second : List (Message Principal Payload))
    (same : first.map Message.id = second.map Message.id) :
    pendingIds first = pendingIds second := congrArg List.toFinset same

/-- Erasing a pending envelope removes its identifier and renames later ones. -/
theorem pendingIds_eraseList (removed : MessageId Principal)
    (pending : List (Message Principal Payload)) :
    pendingIds (Message.eraseList removed pending) =
      ((pendingIds pending).erase removed).image (MessageId.erase removed) := by
  classical
  ext id
  simp only [pendingIds, Message.eraseList, List.mem_toFinset, List.mem_map,
    List.mem_filter, Finset.mem_image, Finset.mem_erase, decide_eq_true_eq]
  constructor
  · rintro ⟨message, ⟨original, ⟨member, kept⟩, rfl⟩, rfl⟩
    exact ⟨original.id, ⟨kept, original, member, rfl⟩, rfl⟩
  · rintro ⟨oldId, ⟨kept, original, member, rfl⟩, rfl⟩
    exact ⟨⟨MessageId.erase removed original.id, original.payload⟩,
      ⟨original, ⟨member, kept⟩, rfl⟩, rfl⟩

/-- Restoring all surviving identifiers recovers the original remaining pool. -/
theorem pendingIds_restore_erased (removed : MessageId Principal)
    (pending : List (Message Principal Payload)) :
    (pendingIds (Message.eraseList removed pending)).image (MessageId.restore removed) =
      (pendingIds pending).erase removed := by
  classical
  rw [pendingIds_eraseList, Finset.image_image]
  have same : ((pendingIds pending).erase removed).image
      (MessageId.restore removed ∘ MessageId.erase removed) =
      ((pendingIds pending).erase removed).image id := by
    apply Finset.image_congr
    intro identifier member
    exact MessageId.restore_erase removed identifier (Finset.mem_erase.mp member).1
  rw [same, Finset.image_id]

/-- Injective identifier renaming transports the entire outside-option lottery. -/
theorem chooseWithOutside_image (weight : ℝ) (nonnegative : 0 ≤ weight)
    (candidates : Finset (MessageId Principal)) (rename : MessageId Principal → MessageId Principal)
    (injective : Function.Injective rename) :
    (chooseWithOutside weight nonnegative candidates).map (Option.map rename) =
      chooseWithOutside weight nonnegative (candidates.image rename) := by
  classical
  have optionInjective : Function.Injective (Option.map rename) := by
    intro first second same
    cases first <;> cases second <;> simp_all [injective.eq_iff]
  have cardinal := Finset.card_image_of_injective candidates injective
  ext choice
  rw [← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  cases choice with
  | none =>
      rw [show (none : Option (MessageId Principal)) = Option.map rename none from rfl,
        pmf_map_apply_of_injective _ optionInjective, Option.map_none,
        chooseWithOutside_none_toReal,
        chooseWithOutside_none_toReal, cardinal]
  | some identifier =>
      by_cases preimage : ∃ original, rename original = identifier
      · obtain ⟨original, rfl⟩ := preimage
        rw [show some (rename original) = Option.map rename (some original) from rfl,
          pmf_map_apply_of_injective _ optionInjective, Option.map_some,
          chooseWithOutside_some_toReal,
          chooseWithOutside_some_toReal, cardinal]
        have member : rename original ∈ candidates.image rename ↔ original ∈ candidates := by
          rw [Finset.mem_image]
          exact ⟨fun ⟨other, present, same⟩ => injective same ▸ present,
            fun present => ⟨original, present, rfl⟩⟩
        simp only [member]
      · have mappedZero : ((chooseWithOutside weight nonnegative candidates).map
            (Option.map rename)) (some identifier) = 0 := by
          rw [PMF.map_apply]
          apply ENNReal.tsum_eq_zero.mpr
          intro value
          cases value with
          | none => simp
          | some original =>
              have different : identifier ≠ rename original :=
                fun same => preimage ⟨original, same.symm⟩
              simp [different]
        have absent : identifier ∉ candidates.image rename := by
          rintro member
          obtain ⟨original, _, same⟩ := Finset.mem_image.mp member
          exact preimage ⟨original, same⟩
        rw [mappedZero, ENNReal.toReal_zero, chooseWithOutside_some_toReal,
          ite_eq_right absent]

/-- Deleting and restoring an envelope yields precisely the residual lottery. -/
theorem chooseWithOutside_erased_restore (weight : ℝ) (nonnegative : 0 ≤ weight)
    (removed : MessageId Principal) (pending : List (Message Principal Payload)) :
    (chooseWithOutside weight nonnegative (pendingIds (Message.eraseList removed pending))).map
        (Option.map (MessageId.restore removed)) =
      chooseWithOutside weight nonnegative ((pendingIds pending).erase removed) := by
  rw [chooseWithOutside_image weight nonnegative _ _ (MessageId.restore_injective removed),
    pendingIds_restore_erased]

/-- Two distinct public identifiers receive equal competing inclusion chances. -/
theorem chooseWithOutside_pair_toReal (weight : ℝ) (nonnegative : 0 ≤ weight)
    (first second : MessageId Principal) (different : first ≠ second) :
    ((chooseWithOutside weight nonnegative {first, second}) (some first)).toReal =
      weight / (1 + 2 * weight) := by
  classical
  simp [chooseWithOutside_some_toReal, different]

/-- At any pending identifier, the public lottery is include-or-erased-law. -/
theorem chooseWithOutside_include_or_erased (weight : ℝ) (nonnegative : 0 ≤ weight)
    (pending : List (Message Principal Payload)) (removed : MessageId Principal)
    (present : removed ∈ pendingIds pending) :
    ∃ (probability : ℝ) (nonnegativeProbability : 0 ≤ probability)
      (atMost : probability ≤ 1),
      chooseWithOutside weight nonnegative (pendingIds pending) =
        mix probability nonnegativeProbability atMost (PMF.pure (some removed))
          ((chooseWithOutside weight nonnegative
            (pendingIds (Message.eraseList removed pending))).map
              (Option.map (MessageId.restore removed))) := by
  have decomposition := chooseWithOutside_insert weight nonnegative
    ((pendingIds pending).erase removed) removed (Finset.notMem_erase _ _)
  rw [Finset.insert_erase present] at decomposition
  let probability := weight / (1 + (((pendingIds pending).erase removed).card + 1 : ℝ) * weight)
  have probabilityNonnegative : 0 ≤ probability := by unfold probability; positivity
  have probabilityAtMost : probability ≤ 1 := by
    have denominator : 0 < 1 +
        (((pendingIds pending).erase removed).card + 1 : ℝ) * weight := by positivity
    change weight / (1 + (((pendingIds pending).erase removed).card + 1 : ℝ) * weight) ≤ 1
    rw [div_le_one denominator]
    nlinarith [Nat.cast_nonneg (α := ℝ) ((pendingIds pending).erase removed).card]
  refine ⟨probability, probabilityNonnegative, probabilityAtMost, ?_⟩
  rw [chooseWithOutside_erased_restore]
  exact decomposition

end MessageNetwork

namespace ReactiveApplication

variable (app : ReactiveApplication Principal)

/-- Interpret the public lottery's outside option as waiting. -/
def pendingLotteryCommand (selection : Option (MessageId Principal)) : app.Command :=
  selection.elim .wait .include

/-- Select any pending identifier using only public identifier metadata. -/
def pendingLotteryScheduler (weight : ℝ) (nonnegative : 0 ≤ weight) : app.Scheduler :=
  Scheduler.ofObservation app
    (fun _ view => MessageNetwork.pendingIds view.network.pending)
    (fun identifiers => (MessageNetwork.chooseWithOutside weight nonnegative identifiers).map
      app.pendingLotteryCommand)

/-- Only pending identifiers influence selection; payloads, application
observations, receipts, and earlier scheduler commands have no further effect. -/
theorem pendingLotteryScheduler_eq_of_identifiers (weight : ℝ) (nonnegative : 0 ≤ weight)
    (firstRecall secondRecall : List app.EnvironmentEntry)
    (firstView secondView : app.EnvironmentView)
    (same : MessageNetwork.pendingIds firstView.network.pending =
      MessageNetwork.pendingIds secondView.network.pending) :
    app.pendingLotteryScheduler weight nonnegative firstRecall firstView =
      app.pendingLotteryScheduler weight nonnegative secondRecall secondView := by
  exact Scheduler.ofObservation_eq_of_observation_eq app _ _ same

/-- The scheduler's law with one envelope removed differs only by that
envelope's inclusion branch and restoration of the remaining identifiers. -/
theorem pendingLotteryScheduler_include_or_erased (weight : ℝ) (nonnegative : 0 ≤ weight)
    (recall : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (message : Message Principal app.Payload) (present : message ∈ view.network.pending) :
    ∃ (probability : ℝ) (nonnegativeProbability : 0 ≤ probability)
      (atMost : probability ≤ 1),
      app.pendingLotteryScheduler weight nonnegative recall view =
        mix probability nonnegativeProbability atMost (PMF.pure (.include message.id))
          ((app.pendingLotteryScheduler weight nonnegative
            (app.eraseEnvironmentRecall message.id recall) (view.erase app message.id)).map
              (Command.restore app message.id)) := by
  have identifier : message.id ∈ MessageNetwork.pendingIds view.network.pending :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨message, present, rfl⟩)
  obtain ⟨probability, p0, p1, decomposition⟩ :=
    MessageNetwork.chooseWithOutside_include_or_erased weight nonnegative
      view.network.pending message.id identifier
  refine ⟨probability, p0, p1, ?_⟩
  dsimp only [pendingLotteryScheduler, Scheduler.ofObservation]
  rw [decomposition, mix_map, PMF.pure_map]
  congr 1
  rw [PMF.map_comp, PMF.map_comp]
  congr 1
  funext selection
  cases selection <;> rfl

end ReactiveApplication

end Interaction
