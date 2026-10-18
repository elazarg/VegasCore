/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialQuiet
import Vegas.Pending.PhaseCountProjection
import Interaction.ReactiveRoundTrace

/-! # All three actual initial raw response kernels and their immutable snapshot -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def initialAliceCallback : app.Execution := completeActivation initialExecution alice

def initialBobCallback (first : app.Action) : app.Execution :=
  completeActivation (initialAliceCallback.respond app alice first) bob

def initialCarolCallback (first second : app.Action) : app.Execution :=
  completeActivation ((initialBobCallback first).respond app bob second) carol

def afterInitialResponses (first second third : app.Action) : app.Execution :=
  (initialCarolCallback first second).respond app carol third

private theorem response_public (execution : app.Execution) (owner : Player)
    (response : app.Action) :
    (execution.respond app owner response).application.publicView =
      execution.application.publicView := by
  rcases response with ⟨material⟩
  cases material with
  | none => rfl
  | some material => exact PhaseCount.submit_publicView execution.application owner material

private theorem initial_position_choice (seed : Seeds) (execution : app.Execution)
    (owner : Player) (position : execution.environmentRecall.length = owner.val)
    (samePublic : execution.application.publicView = initialState.publicView) :
    family seed execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.activate owner) := by
  classical
  have sameAttempt : execution.application.attempt = initialState.attempt :=
    congrArg PhasePublicView.attempt samePublic
  have original : execution.application.attempt = originalAttempt :=
    sameAttempt.trans initialState_attempt
  have available : ready owner (bindingEvent owner) (execution.observeEnvironment app) = true := by
    change decide (PhaseRuntimeState.requests execution.application.publicView owner
      ⟨execution.application.attempt, bindingEvent owner⟩) = true
    rw [samePublic, original]
    exact decide_eq_true (initial_bindings_ready owner)
  have activated : activateReady owner (bindingEvent owner)
      (execution.observeEnvironment app) = .activate owner := by
    rw [activateReady, available]
    rfl
  change PMF.pure (choose seed _ _) = _
  rw [choose_original seed _ _ original, position]
  fin_cases owner <;> exact congrArg PMF.pure activated

theorem initial_alice_choice (seed : Seeds) :
    family seed initialExecution.environmentRecall (initialExecution.observeEnvironment app) =
      PMF.pure (.activate alice) :=
  initial_position_choice seed initialExecution alice rfl rfl

theorem initial_bob_choice (seed : Seeds) (first : app.Action) :
    family seed (initialAliceCallback.respond app alice first).environmentRecall
      ((initialAliceCallback.respond app alice first).observeEnvironment app) =
        PMF.pure (.activate bob) := by
  apply initial_position_choice seed _ bob rfl
  exact response_public initialAliceCallback alice first

theorem initial_carol_choice (seed : Seeds) (first second : app.Action) :
    family seed ((initialBobCallback first).respond app bob second).environmentRecall
      (((initialBobCallback first).respond app bob second).observeEnvironment app) =
        PMF.pure (.activate carol) := by
  apply initial_position_choice seed _ carol rfl
  exact (response_public (initialBobCallback first) bob second).trans
    (response_public initialAliceCallback alice first)

private theorem initial_bob_recall (first : app.Action) :
    (initialBobCallback first).recall bob = [] := by
  change (initialAliceCallback.respond app alice first).recall bob = []
  rw [app.respond_recall_other _ alice bob (by decide)]
  rfl

private theorem initial_carol_recall (first second : app.Action) :
    (initialCarolCallback first second).recall carol = [] := by
  change ((initialBobCallback first).respond app bob second).recall carol = []
  rw [app.respond_recall_other _ bob carol (by decide)]
  change (initialAliceCallback.respond app alice first).recall carol = []
  rw [app.respond_recall_other _ alice carol (by decide)]
  rfl

/-- The literal initialized native law retains every arbitrary raw response. -/
theorem first_three_rounds (seed : Seeds) (players : Player → app.Policy) :
    app.runRounds (family seed) players 3 initialExecution =
      (players alice [] (initialAliceCallback.observe app alice)).bind fun first =>
        (players bob [] ((initialBobCallback first).observe app bob)).bind fun second =>
          (players carol [] ((initialCarolCallback first second).observe app carol)).map
            (afterInitialResponses first second) := by
  have firstRound : app.round (family seed) players initialExecution =
      (players alice [] (initialAliceCallback.observe app alice)).map
        (initialAliceCallback.respond app alice) := by
    rw [ReactiveApplication.round, initial_alice_choice, PMF.pure_bind,
      ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
    rfl
  have secondRound (first : app.Action) :
      app.round (family seed) players (initialAliceCallback.respond app alice first) =
        (players bob [] ((initialBobCallback first).observe app bob)).map
          ((initialBobCallback first).respond app bob) := by
    rw [ReactiveApplication.round, initial_bob_choice, PMF.pure_bind,
      ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
    change (players bob ((initialBobCallback first).recall bob)
      ((initialBobCallback first).observe app bob)).map _ = _
    rw [initial_bob_recall]
    rfl
  have thirdRound (first second : app.Action) :
      app.round (family seed) players ((initialBobCallback first).respond app bob second) =
        (players carol [] ((initialCarolCallback first second).observe app carol)).map
          (afterInitialResponses first second) := by
    rw [ReactiveApplication.round, initial_carol_choice, PMF.pure_bind,
      ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
    change (players carol ((initialCarolCallback first second).recall carol)
      ((initialCarolCallback first second).observe app carol)).map _ = _
    rw [initial_carol_recall]
    rfl
  rw [ReactiveApplication.runRounds, firstRound, PMF.bind_map]
  congr 1
  funext first
  change (app.round (family seed) players (initialAliceCallback.respond app alice first)).bind
    (app.runRounds (family seed) players 1) = _
  rw [secondRound, PMF.bind_map]
  congr 1
  funext second
  change (app.round (family seed) players ((initialBobCallback first).respond app bob second)).bind
    (app.runRounds (family seed) players 0) = _
  rw [thirdRound]
  exact PMF.bind_pure _

private theorem response_inputs (execution : app.Execution) (owner : Player)
    (response : app.Action) :
    ∃ emitted : Option (Message Player app.Payload),
      (execution.respond app owner response).network.inputs =
        execution.network.inputs ++ emitted.toList ∧
      ∀ message ∈ emitted.toList, message.sender = owner := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      refine ⟨none, ?_, ?_⟩
      · exact (List.append_nil _).symm
      · intro message impossible
        cases impossible
  | some submission =>
      refine ⟨some ⟨(owner, execution.network.nextSerial owner),
        app.packet (app.submit execution.application owner submission) owner
          (execution.network.known owner) submission⟩, rfl, ?_⟩
      intro message member
      cases (List.mem_singleton.mp member).symm
      rfl

private theorem option_input_unique (emitted : Option (Message Player app.Payload))
    (left right : Message Player app.Payload)
    (leftInput : left ∈ emitted.toList) (rightInput : right ∈ emitted.toList) : left = right := by
  cases emitted with
  | none => cases leftInput
  | some message =>
      exact (List.mem_singleton.mp leftInput).trans (List.mem_singleton.mp rightInput).symm

/-- One initial response per owner gives at most one initial packet per owner. -/
theorem afterInitialResponses_unique_owner (first second third : app.Action) (owner : Player)
    (left right : Message Player app.Payload)
    (leftInput : left ∈ (afterInitialResponses first second third).network.inputs)
    (rightInput : right ∈ (afterInitialResponses first second third).network.inputs)
    (leftOwner : left.sender = owner) (rightOwner : right.sender = owner) : left = right := by
  obtain ⟨outA, inputsA, senderA⟩ := response_inputs initialAliceCallback alice first
  obtain ⟨outB, inputsB, senderB⟩ := response_inputs (initialBobCallback first) bob second
  obtain ⟨outC, inputsC, senderC⟩ := response_inputs (initialCarolCallback first second) carol third
  have initialInputs : initialAliceCallback.network.inputs = [] := rfl
  change (initialBobCallback first).network.inputs = _ at inputsA
  change (initialCarolCallback first second).network.inputs = _ at inputsB
  change (afterInitialResponses first second third).network.inputs = _ at inputsC
  rw [inputsC, inputsB, inputsA, initialInputs, List.nil_append] at leftInput rightInput
  have own (message : Message Player app.Payload)
      (member : message ∈ outA.toList ++ outB.toList ++ outC.toList)
      (same : message.sender = owner) :
      message ∈ (if owner = alice then outA else if owner = bob then outB else outC).toList := by
    rcases List.mem_append.mp member with pair | third
    · rcases List.mem_append.mp pair with first | second
      · have named := (senderA message first).symm.trans same
        rw [← named, ite_eq_left rfl]
        exact first
      · have named := (senderB message second).symm.trans same
        rw [← named, ite_eq_right (by decide : bob ≠ alice), ite_eq_left rfl]
        exact second
    · have named := (senderC message third).symm.trans same
      rw [← named, ite_eq_right (by decide : carol ≠ alice),
        ite_eq_right (by decide : carol ≠ bob)]
      exact third
  exact option_input_unique _ left right (own left leftInput leftOwner)
    (own right rightInput rightOwner)

/-- The immutable pre-advance snapshot has at most one packet from each
owner, even under arbitrary raw submissions and off-path player policies. -/
theorem first_snapshot_unique_owner (seed : Seeds) (players : Player → app.Policy)
    (extra : Nat) (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed) players (4 + extra)
      initialExecution).support)
    (snapshot : app.EnvironmentEntry) (selected : execution.environmentRecall[3]? = some snapshot)
    (owner : Player) (left right : Message Player app.Payload)
    (leftInput : left ∈ snapshot.beforeView.network.inputs)
    (rightInput : right ∈ snapshot.beforeView.network.inputs)
    (leftOwner : left.sender = owner) (rightOwner : right.sender = owner) : left = right := by
  rw [show 4 + extra = 3 + (extra + 1) by omega, app.runRounds_add,
    first_three_rounds, PMF.bind_bind] at reached
  obtain ⟨first, _firstSupport, afterFirst⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  rw [PMF.bind_bind] at afterFirst
  obtain ⟨second, _secondSupport, afterSecond⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterFirst)
  rw [PMF.bind_map] at afterSecond
  obtain ⟨third, _thirdSupport, remaining⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterSecond)
  change execution ∈ (app.runRounds (family seed) players (extra + 1)
    (afterInitialResponses first second third)).support at remaining
  rw [ReactiveApplication.runRounds.eq_def] at remaining
  obtain ⟨middle, moved, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ remaining)
  obtain ⟨command, _chosen, dispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  obtain ⟨later, recalled, _length⟩ :=
    app.runRounds_environmentRecall_append (family seed) players extra middle execution tail
  have complete : execution.environmentRecall =
      (afterInitialResponses first second third).environmentRecall ++
        [⟨(afterInitialResponses first second third).observeEnvironment app, command⟩] ++
          later := by
    rw [recalled, app.dispatch_environmentRecall players command _ middle dispatched]
  have snapshotEq : snapshot =
      ⟨(afterInitialResponses first second third).observeEnvironment app, command⟩ := by
    apply Option.some.inj
    rw [← selected, complete]
    rfl
  subst snapshot
  exact afterInitialResponses_unique_owner first second third owner left right leftInput rightInput
    leftOwner rightOwner

end Vegas.Examples.CommitSeedBroadcast
