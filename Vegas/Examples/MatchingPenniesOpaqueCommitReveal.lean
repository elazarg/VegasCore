import Vegas.Machine.MessageInFlight
import Vegas.Machine.MessageSecurity
import Vegas.Machine.RefinementKernelGame
import Vegas.Machine.Audited
import Vegas.Examples.MatchingPennies

/-!
# Matching Pennies with opaque commit/reveal messages

Property boundary: this file proves no plaintext in the visible runtime
buffers by construction at lock checkpoints, not cryptographic hiding or a
general no-profitable-front-running theorem.

This fixture is the positive counterpart to
`FrontrunningMessageInFlight`.  Players may inspect the message buffers before
choosing, but the lock phase emits only opaque commitments.  Plaintext moves
appear only after both moves are locked in the hidden source state.

The checked claim is protocol faithfulness plus no plaintext in the runtime
buffers at the lock checkpoints.  It is not a cryptographic hiding theorem or a
general theorem that all front-running deviations are unprofitable.
-/

namespace Vegas

open GameTheory
open Math.Probability

namespace Examples
namespace Refinement

@[simp] theorem player_alice_ne_bob : Player.alice ≠ Player.bob := by
  decide

@[simp] theorem player_bob_ne_alice : Player.bob ≠ Player.alice := by
  decide

structure LockedMPState where
  aliceMove : Option Bool
  bobMove : Option Bool
  aliceRevealed : Bool
  bobRevealed : Bool
deriving DecidableEq, Repr

def LockedMPState.init : LockedMPState where
  aliceMove := none
  bobMove := none
  aliceRevealed := false
  bobRevealed := false

def LockedMPState.move? :
    LockedMPState → Player → Option Bool
  | state, Player.alice => state.aliceMove
  | state, Player.bob => state.bobMove

def LockedMPState.revealed :
    LockedMPState → Player → Bool
  | state, Player.alice => state.aliceRevealed
  | state, Player.bob => state.bobRevealed

def LockedMPState.setMove
    (player : Player) (move : Bool)
    (state : LockedMPState) : LockedMPState :=
  match player with
  | Player.alice =>
      match state.aliceMove with
      | none => { state with aliceMove := some move }
      | some _ => state
  | Player.bob =>
      match state.bobMove with
      | none => { state with bobMove := some move }
      | some _ => state

def LockedMPState.markRevealed
    (player : Player) (state : LockedMPState) : LockedMPState :=
  match player with
  | Player.alice => { state with aliceRevealed := true }
  | Player.bob => { state with bobRevealed := true }

def LockedMPState.outcome? (state : LockedMPState) :
    Option (Bool × Bool) :=
  match state.aliceMove, state.bobMove with
  | some alice, some bob =>
      if state.aliceRevealed && state.bobRevealed then
        some (alice, bob)
      else
        none
  | _, _ => none

inductive LockRevealAction (_player : Player) where
  | lock (move : Bool)
  | ackReveal

def matchingPenniesRuntimeUtility
    (outcome : Bool × Bool) : Player → ℝ
  | Player.alice => if outcome.1 = outcome.2 then 1 else -1
  | Player.bob => if outcome.1 = outcome.2 then -1 else 1

/-- Hidden-lock source machine.  The source state records committed moves, but
public and player observations reveal no source-state data. -/
noncomputable def lockedMPMachine : Machine Player where
  State := LockedMPState
  Action := LockRevealAction
  Internal := PEmpty
  Public := PUnit
  Obs := fun _ => PUnit
  Outcome := Bool × Bool
  init := LockedMPState.init
  available := fun state player =>
    { action |
      match action with
      | .lock _ => state.move? player = none
      | .ackReveal =>
          (state.move? player).isSome = true ∧
            state.revealed player = false }
  availableInternal := fun _ => ∅
  stepPlay := fun player action state =>
    match action with
    | .lock move => PMF.pure (state.setMove player move)
    | .ackReveal => PMF.pure (state.markRevealed player)
  stepInternal := fun event _ => nomatch event
  terminal := fun state => state.outcome?.isSome = true
  publicView := fun _ => PUnit.unit
  observe := fun _ _ => PUnit.unit
  outcome := LockedMPState.outcome?
  utility := matchingPenniesRuntimeUtility

set_option linter.flexible false in
theorem lockedMPMachine_relock_unavailable
    (state : lockedMPMachine.State) (player : Player)
    (move existing : Bool)
    (hlocked : LockedMPState.move? state player = some existing) :
    LockRevealAction.lock move ∉ lockedMPMachine.available state player := by
  cases player <;> rcases state with
    ⟨aliceMove, bobMove, aliceRevealed, bobRevealed⟩ <;>
    cases aliceMove <;> cases bobMove <;>
    simp [lockedMPMachine, LockedMPState.move?] at hlocked ⊢
  all_goals
    intro h
    exact h

inductive CommitRevealMessage where
  | commit
  | reveal (move : Bool)
deriving DecidableEq, Repr

abbrev CommitRevealMessageOf (_player : Player) := CommitRevealMessage

def commitRevealPlaintextPolicy :
    Machine.PlaintextPolicy Player CommitRevealMessageOf Bool where
  plaintext?
    | _, .commit => none
    | _, .reveal move => some move

def commitMessage (player : Player) :
    Sigma CommitRevealMessageOf :=
  ⟨player, CommitRevealMessage.commit⟩

def revealMessage (player : Player) (move : Bool) :
    Sigma CommitRevealMessageOf :=
  ⟨player, CommitRevealMessage.reveal move⟩

def aliceCommitView : List (Sigma CommitRevealMessageOf) :=
  [commitMessage Player.alice]

def aliceBobCommitView : List (Sigma CommitRevealMessageOf) :=
  [commitMessage Player.alice, commitMessage Player.bob]

example :
    commitRevealPlaintextPolicy.noPlaintext aliceCommitView := by
  rfl

example :
    commitRevealPlaintextPolicy.noPlaintext aliceBobCommitView := by
  rfl

example (move : Bool) :
    ¬ commitRevealPlaintextPolicy.noPlaintext
        [revealMessage Player.alice move] := by
  cases move <;> simp [Machine.PlaintextPolicy.noPlaintext,
    Machine.PlaintextPolicy.plaintexts, revealMessage,
    commitRevealPlaintextPolicy]

/-- Strategies are allowed to inspect the public message buffer before
choosing a lock move.  The safety proof comes from what the protocol puts in
that buffer before the lock point. -/
abbrev CommitRevealStrategy (_player : Player) :=
  List (Sigma CommitRevealMessageOf) → Bool

def commitRevealActionProfile
    (profile : ∀ player : Player, CommitRevealStrategy player) :
    Player → Bool
  | Player.alice => profile Player.alice []
  | Player.bob => profile Player.bob aliceCommitView

/-- This is a projection fact about `commitRevealActionProfile`: Bob's action is
read from the fixed opaque commit view by definition. It is not a separate
cryptographic or incentive-hiding theorem. -/
theorem commitRevealActionProfile_bob_ignores_aliceSlot_byDefinition
    (alice₁ alice₂ : CommitRevealStrategy Player.alice)
    (bob : CommitRevealStrategy Player.bob) :
    commitRevealActionProfile
        (fun
          | Player.alice => alice₁
          | Player.bob => bob) Player.bob =
      commitRevealActionProfile
        (fun
          | Player.alice => alice₂
          | Player.bob => bob) Player.bob := by
  rfl

noncomputable def matchingPenniesBoolGame : KernelGame Player where
  Strategy := fun _ => Bool
  Outcome := Bool × Bool
  outcomeKernel := fun profile =>
    PMF.pure (profile Player.alice, profile Player.bob)
  utility := matchingPenniesRuntimeUtility

theorem matchingPenniesBoolGame_eu
    (profile : Player → Bool) (player : Player) :
    matchingPenniesBoolGame.eu profile player =
      match player with
      | Player.alice =>
          if profile Player.alice = profile Player.bob then 1 else -1
      | Player.bob =>
          if profile Player.alice = profile Player.bob then -1 else 1 := by
  cases player <;>
    simp [matchingPenniesBoolGame, KernelGame.eu, expect_pure,
      matchingPenniesRuntimeUtility]

theorem matchingPenniesBoolGame_no_pure_nash
    (profile : Player → Bool) :
    ¬ matchingPenniesBoolGame.IsNash profile := by
  intro hNash
  cases halice : profile Player.alice <;>
    cases hbob : profile Player.bob
  · have hdev := hNash Player.bob true
    norm_num [matchingPenniesBoolGame_eu, halice, hbob,
      Function.update] at hdev
  · have hdev := hNash Player.alice true
    norm_num [matchingPenniesBoolGame_eu, halice, hbob,
      Function.update] at hdev
  · have hdev := hNash Player.alice false
    norm_num [matchingPenniesBoolGame_eu, halice, hbob,
      Function.update] at hdev
  · have hdev := hNash Player.bob false
    norm_num [matchingPenniesBoolGame_eu, halice, hbob,
      Function.update] at hdev

def commitRevealSourceBatch
    (profile : ∀ player : Player, CommitRevealStrategy player)
    (state : lockedMPMachine.State) :
    List lockedMPMachine.Event :=
  match state.aliceMove, state.bobMove,
      state.aliceRevealed, state.bobRevealed with
    | none, none, false, false =>
        [.play Player.alice
          (.lock (commitRevealActionProfile profile Player.alice))]
    | some _, none, false, false =>
        [.play Player.bob
          (.lock (commitRevealActionProfile profile Player.bob))]
    | some _, some _, false, false =>
        [.play Player.alice .ackReveal]
    | some _, some _, true, false =>
        [.play Player.bob .ackReveal]
    | _, _, _, _ => []

set_option linter.flexible false in
theorem commitRevealSourceBatch_available
    (profile : ∀ player : Player, CommitRevealStrategy player)
    (state : lockedMPMachine.State) :
    ∃ dst, lockedMPMachine.AvailableRunFrom state
      (commitRevealSourceBatch profile state) dst := by
  rcases state with
    ⟨aliceMove, bobMove, aliceRevealed, bobRevealed⟩
  cases aliceMove with
  | none =>
      cases bobMove with
      | none =>
          cases aliceRevealed <;> cases bobRevealed
          · let move := commitRevealActionProfile profile Player.alice
            let src : lockedMPMachine.State :=
              { aliceMove := none, bobMove := none,
                aliceRevealed := false, bobRevealed := false }
            let dst : lockedMPMachine.State :=
              { aliceMove := some move, bobMove := none,
                aliceRevealed := false, bobRevealed := false }
            refine ⟨dst, ?_⟩
            change lockedMPMachine.AvailableRunFrom src
              [.play Player.alice (.lock move)] dst
            refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
              (Machine.AvailableRunFrom.nil _)
            · change LockRevealAction.lock move ∈
                lockedMPMachine.available src Player.alice
              change (lockedMPMachine.available src Player.alice)
                (LockRevealAction.lock move)
              simp [lockedMPMachine, LockedMPState.move?, src]
              trivial
            · change dst ∈ (PMF.pure dst).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
          all_goals exact ⟨_, Machine.AvailableRunFrom.nil _⟩
      | some bobMove =>
          exact ⟨_, Machine.AvailableRunFrom.nil _⟩
  | some aliceMove =>
      cases bobMove with
      | none =>
          cases aliceRevealed <;> cases bobRevealed
          · let move := commitRevealActionProfile profile Player.bob
            let src : lockedMPMachine.State :=
              { aliceMove := some aliceMove, bobMove := none,
                aliceRevealed := false, bobRevealed := false }
            let dst : lockedMPMachine.State :=
              { aliceMove := some aliceMove, bobMove := some move,
                aliceRevealed := false, bobRevealed := false }
            refine ⟨dst, ?_⟩
            change lockedMPMachine.AvailableRunFrom src
              [.play Player.bob (.lock move)] dst
            refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
              (Machine.AvailableRunFrom.nil _)
            · change LockRevealAction.lock move ∈
                lockedMPMachine.available src Player.bob
              change (lockedMPMachine.available src Player.bob)
                (LockRevealAction.lock move)
              simp [lockedMPMachine, LockedMPState.move?, src]
              trivial
            · change dst ∈ (PMF.pure dst).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
          all_goals exact ⟨_, Machine.AvailableRunFrom.nil _⟩
      | some bobMove =>
          cases aliceRevealed <;> cases bobRevealed
          · let src : lockedMPMachine.State :=
              { aliceMove := some aliceMove, bobMove := some bobMove,
                aliceRevealed := false, bobRevealed := false }
            let dst : lockedMPMachine.State :=
              { aliceMove := some aliceMove, bobMove := some bobMove,
                aliceRevealed := true, bobRevealed := false }
            refine ⟨dst, ?_⟩
            change lockedMPMachine.AvailableRunFrom src
              [.play Player.alice .ackReveal] dst
            refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
              (Machine.AvailableRunFrom.nil _)
            · change LockRevealAction.ackReveal ∈
                lockedMPMachine.available src Player.alice
              change
                (LockedMPState.move? src Player.alice).isSome = true ∧
                  LockedMPState.revealed src Player.alice = false
              constructor <;> rfl
            · change dst ∈ (PMF.pure dst).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
          · exact ⟨_, Machine.AvailableRunFrom.nil _⟩
          · let src : lockedMPMachine.State :=
              { aliceMove := some aliceMove, bobMove := some bobMove,
                aliceRevealed := true, bobRevealed := false }
            let dst : lockedMPMachine.State :=
              { aliceMove := some aliceMove, bobMove := some bobMove,
                aliceRevealed := true, bobRevealed := true }
            refine ⟨dst, ?_⟩
            change lockedMPMachine.AvailableRunFrom src
              [.play Player.bob .ackReveal] dst
            refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
              (Machine.AvailableRunFrom.nil _)
            · change LockRevealAction.ackReveal ∈
                lockedMPMachine.available src Player.bob
              change
                (LockedMPState.move? src Player.bob).isSome = true ∧
                  LockedMPState.revealed src Player.bob = false
              constructor <;> rfl
            · change dst ∈ (PMF.pure dst).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
          · exact ⟨_, Machine.AvailableRunFrom.nil _⟩

noncomputable def commitRevealSourceLaw
    (profile : ∀ player : Player, CommitRevealStrategy player) :
    lockedMPMachine.EventBatchLaw :=
  fun trace => PMF.pure (commitRevealSourceBatch profile trace.2)

noncomputable def commitRevealSourceLawFamily :
    lockedMPMachine.EventBatchLawFamily CommitRevealStrategy where
  law := commitRevealSourceLaw
  legal := by
    intro profile trace hnonterminal batch hbatch
    change batch ∈ (PMF.pure
      (commitRevealSourceBatch profile trace.2)).support at hbatch
    rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
    subst batch
    exact commitRevealSourceBatch_available profile trace.2

noncomputable def commitRevealMessageMachine : Machine Player :=
  Machine.messageInFlight lockedMPMachine CommitRevealMessageOf

noncomputable def commitRevealMessageRefinement :
    Machine.StochasticRefinement commitRevealMessageMachine
      lockedMPMachine :=
  Machine.messageInFlight.refinement lockedMPMachine CommitRevealMessageOf

def commitRevealMessageBatch
    (profile : ∀ player : Player, CommitRevealStrategy player)
    (source : lockedMPMachine.State) :
    List commitRevealMessageMachine.Event :=
  match source.aliceMove, source.bobMove,
      source.aliceRevealed, source.bobRevealed with
    | none, none, false, false =>
        [.play Player.alice (.send .commit),
          .play Player.alice
            (.spec (.lock
              (commitRevealActionProfile profile Player.alice)))]
    | some _, none, false, false =>
        [.play Player.bob (.send .commit),
          .play Player.bob
            (.spec (.lock
              (commitRevealActionProfile profile Player.bob)))]
    | some aliceMove, some _, false, false =>
        [.play Player.alice (.send (.reveal aliceMove)),
          .play Player.alice (.spec .ackReveal)]
    | some _, some bobMove, true, false =>
        [.play Player.bob (.send (.reveal bobMove)),
          .play Player.bob (.spec .ackReveal)]
    | _, _, _, _ => []

noncomputable def commitRevealMessageLaw
    (profile : ∀ player : Player, CommitRevealStrategy player) :
    commitRevealMessageMachine.EventBatchLaw :=
  fun trace => PMF.pure (commitRevealMessageBatch profile trace.2.source)

set_option linter.flexible false in
theorem commitRevealMessageBatch_available
    (profile : ∀ player : Player, CommitRevealStrategy player)
    (state : commitRevealMessageMachine.State)
    (hnonterminal : ¬ commitRevealMessageMachine.terminal state) :
    ∃ dst, commitRevealMessageMachine.AvailableRunFrom state
      (commitRevealMessageBatch profile state.source) dst := by
  rcases state with ⟨source, pending, delivered⟩
  rcases source with
    ⟨aliceMove, bobMove, aliceRevealed, bobRevealed⟩
  cases aliceMove with
  | none =>
      cases bobMove with
      | none =>
          cases aliceRevealed <;> cases bobRevealed
          · let move := commitRevealActionProfile profile Player.alice
            let sent := commitMessage Player.alice
            let src : commitRevealMessageMachine.State :=
              { source :=
                  { aliceMove := none, bobMove := none,
                    aliceRevealed := false, bobRevealed := false },
                pending := pending,
                delivered := delivered }
            let afterSend : commitRevealMessageMachine.State :=
              { source := src.source,
                pending := pending ++ [sent],
                delivered := delivered }
            let dst : commitRevealMessageMachine.State :=
              { source :=
                  { aliceMove := some move, bobMove := none,
                    aliceRevealed := false, bobRevealed := false },
                pending := pending ++ [sent],
                delivered := delivered }
            let restore (sourceValue : LockedMPState) :
                commitRevealMessageMachine.State :=
              { source := sourceValue,
                pending := pending ++ [sent],
                delivered := delivered }
            refine ⟨dst, ?_⟩
            change commitRevealMessageMachine.AvailableRunFrom src
              [.play Player.alice (.send .commit),
                .play Player.alice (.spec (.lock move))] dst
            refine Machine.AvailableRunFrom.cons (mid := afterSend) ?_ ?_ ?_
            · change Machine.MessageInFlightAction.send
                CommitRevealMessage.commit ∈
                commitRevealMessageMachine.available src Player.alice
              exact hnonterminal
            · change afterSend ∈ (PMF.pure afterSend).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
            · refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                (Machine.AvailableRunFrom.nil _)
              · change Machine.MessageInFlightAction.spec
                  (LockRevealAction.lock move) ∈
                  commitRevealMessageMachine.available afterSend Player.alice
                change LockRevealAction.lock move ∈
                  lockedMPMachine.available afterSend.source Player.alice
                change (lockedMPMachine.available afterSend.source Player.alice)
                  (LockRevealAction.lock move)
                simp [lockedMPMachine, LockedMPState.move?, afterSend, src]
                trivial
              · change dst ∈
                  (PMF.map restore
                    (PMF.pure
                      { aliceMove := some move, bobMove := none,
                        aliceRevealed := false,
                        bobRevealed := false })).support
                rw [PMF.pure_map, PMF.support_pure]
                exact Set.mem_singleton _
          all_goals
            exact ⟨_, Machine.AvailableRunFrom.nil _⟩
      | some bobMove =>
          exact
            ⟨{ source :=
                  { aliceMove := none, bobMove := some bobMove,
                    aliceRevealed := aliceRevealed,
                    bobRevealed := bobRevealed },
                pending := pending,
                delivered := delivered },
              Machine.AvailableRunFrom.nil _⟩
  | some aliceMove =>
      cases bobMove with
      | none =>
          cases aliceRevealed <;> cases bobRevealed
          · let move := commitRevealActionProfile profile Player.bob
            let sent := commitMessage Player.bob
            let src : commitRevealMessageMachine.State :=
              { source :=
                  { aliceMove := some aliceMove, bobMove := none,
                    aliceRevealed := false, bobRevealed := false },
                pending := pending,
                delivered := delivered }
            let afterSend : commitRevealMessageMachine.State :=
              { source := src.source,
                pending := pending ++ [sent],
                delivered := delivered }
            let dst : commitRevealMessageMachine.State :=
              { source :=
                  { aliceMove := some aliceMove, bobMove := some move,
                    aliceRevealed := false, bobRevealed := false },
                pending := pending ++ [sent],
                delivered := delivered }
            let restore (sourceValue : LockedMPState) :
                commitRevealMessageMachine.State :=
              { source := sourceValue,
                pending := pending ++ [sent],
                delivered := delivered }
            refine ⟨dst, ?_⟩
            change commitRevealMessageMachine.AvailableRunFrom src
              [.play Player.bob (.send .commit),
                .play Player.bob (.spec (.lock move))] dst
            refine Machine.AvailableRunFrom.cons (mid := afterSend) ?_ ?_ ?_
            · change Machine.MessageInFlightAction.send
                CommitRevealMessage.commit ∈
                commitRevealMessageMachine.available src Player.bob
              exact hnonterminal
            · change afterSend ∈ (PMF.pure afterSend).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
            · refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                (Machine.AvailableRunFrom.nil _)
              · change Machine.MessageInFlightAction.spec
                  (LockRevealAction.lock move) ∈
                  commitRevealMessageMachine.available afterSend Player.bob
                change LockRevealAction.lock move ∈
                  lockedMPMachine.available afterSend.source Player.bob
                change (lockedMPMachine.available afterSend.source Player.bob)
                  (LockRevealAction.lock move)
                simp [lockedMPMachine, LockedMPState.move?, afterSend, src]
                trivial
              · change dst ∈
                  (PMF.map restore
                    (PMF.pure
                      { aliceMove := some aliceMove, bobMove := some move,
                        aliceRevealed := false,
                        bobRevealed := false })).support
                rw [PMF.pure_map, PMF.support_pure]
                exact Set.mem_singleton _
          all_goals
            exact ⟨_, Machine.AvailableRunFrom.nil _⟩
      | some bobMove =>
          cases aliceRevealed <;> cases bobRevealed
          · let sent := revealMessage Player.alice aliceMove
            let src : commitRevealMessageMachine.State :=
              { source :=
                  { aliceMove := some aliceMove, bobMove := some bobMove,
                    aliceRevealed := false, bobRevealed := false },
                pending := pending,
                delivered := delivered }
            let afterSend : commitRevealMessageMachine.State :=
              { source := src.source,
                pending := pending ++ [sent],
                delivered := delivered }
            let dst : commitRevealMessageMachine.State :=
              { source :=
                  { aliceMove := some aliceMove, bobMove := some bobMove,
                    aliceRevealed := true, bobRevealed := false },
                pending := pending ++ [sent],
                delivered := delivered }
            let restore (sourceValue : LockedMPState) :
                commitRevealMessageMachine.State :=
              { source := sourceValue,
                pending := pending ++ [sent],
                delivered := delivered }
            refine ⟨dst, ?_⟩
            change commitRevealMessageMachine.AvailableRunFrom src
              [.play Player.alice (.send (.reveal aliceMove)),
                .play Player.alice (.spec .ackReveal)] dst
            refine Machine.AvailableRunFrom.cons (mid := afterSend) ?_ ?_ ?_
            · change Machine.MessageInFlightAction.send
                (CommitRevealMessage.reveal aliceMove) ∈
                commitRevealMessageMachine.available src Player.alice
              exact hnonterminal
            · change afterSend ∈ (PMF.pure afterSend).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
            · refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                (Machine.AvailableRunFrom.nil _)
              · change Machine.MessageInFlightAction.spec
                  LockRevealAction.ackReveal ∈
                  commitRevealMessageMachine.available afterSend Player.alice
                change LockRevealAction.ackReveal ∈
                  lockedMPMachine.available afterSend.source Player.alice
                change
                  (LockedMPState.move? afterSend.source Player.alice).isSome =
                      true ∧
                    LockedMPState.revealed afterSend.source Player.alice =
                      false
                constructor <;> rfl
              · change dst ∈
                  (PMF.map restore
                    (PMF.pure
                      { aliceMove := some aliceMove,
                        bobMove := some bobMove,
                        aliceRevealed := true,
                        bobRevealed := false })).support
                rw [PMF.pure_map, PMF.support_pure]
                exact Set.mem_singleton _
          · exact
              ⟨{ source :=
                    { aliceMove := some aliceMove, bobMove := some bobMove,
                      aliceRevealed := false, bobRevealed := true },
                  pending := pending,
                  delivered := delivered },
                Machine.AvailableRunFrom.nil _⟩
          · let sent := revealMessage Player.bob bobMove
            let src : commitRevealMessageMachine.State :=
              { source :=
                  { aliceMove := some aliceMove, bobMove := some bobMove,
                    aliceRevealed := true, bobRevealed := false },
                pending := pending,
                delivered := delivered }
            let afterSend : commitRevealMessageMachine.State :=
              { source := src.source,
                pending := pending ++ [sent],
                delivered := delivered }
            let dst : commitRevealMessageMachine.State :=
              { source :=
                  { aliceMove := some aliceMove, bobMove := some bobMove,
                    aliceRevealed := true, bobRevealed := true },
                pending := pending ++ [sent],
                delivered := delivered }
            let restore (sourceValue : LockedMPState) :
                commitRevealMessageMachine.State :=
              { source := sourceValue,
                pending := pending ++ [sent],
                delivered := delivered }
            refine ⟨dst, ?_⟩
            change commitRevealMessageMachine.AvailableRunFrom src
              [.play Player.bob (.send (.reveal bobMove)),
                .play Player.bob (.spec .ackReveal)] dst
            refine Machine.AvailableRunFrom.cons (mid := afterSend) ?_ ?_ ?_
            · change Machine.MessageInFlightAction.send
                (CommitRevealMessage.reveal bobMove) ∈
                commitRevealMessageMachine.available src Player.bob
              exact hnonterminal
            · change afterSend ∈ (PMF.pure afterSend).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
            · refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                (Machine.AvailableRunFrom.nil _)
              · change Machine.MessageInFlightAction.spec
                  LockRevealAction.ackReveal ∈
                  commitRevealMessageMachine.available afterSend Player.bob
                change LockRevealAction.ackReveal ∈
                  lockedMPMachine.available afterSend.source Player.bob
                change
                  (LockedMPState.move? afterSend.source Player.bob).isSome =
                      true ∧
                    LockedMPState.revealed afterSend.source Player.bob =
                      false
                constructor <;> rfl
              · change dst ∈
                  (PMF.map restore
                    (PMF.pure
                      { aliceMove := some aliceMove,
                        bobMove := some bobMove,
                        aliceRevealed := true,
                        bobRevealed := true })).support
                rw [PMF.pure_map, PMF.support_pure]
                exact Set.mem_singleton _
          · exact
              ⟨{ source :=
                    { aliceMove := some aliceMove, bobMove := some bobMove,
                      aliceRevealed := true, bobRevealed := true },
                  pending := pending,
                  delivered := delivered },
                Machine.AvailableRunFrom.nil _⟩

noncomputable def commitRevealMessageLawFamily :
    commitRevealMessageMachine.EventBatchLawFamily CommitRevealStrategy where
  law := commitRevealMessageLaw
  legal := by
    intro profile trace hnonterminal batch hbatch
    change batch ∈ (PMF.pure
      (commitRevealMessageBatch profile trace.2.source)).support at hbatch
    rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
    subst batch
    exact commitRevealMessageBatch_available profile trace.2 hnonterminal

noncomputable def commitRevealMessageLawLift :
    commitRevealMessageRefinement.EventBatchLawFamilyLift
      CommitRevealStrategy commitRevealSourceLawFamily where
  impl := commitRevealMessageLawFamily
  compatible := by
    intro profile
    change commitRevealMessageRefinement.EventBatchLawCompatible
      (fun trace =>
        PMF.pure (commitRevealMessageBatch profile trace.2.source))
      (fun trace => PMF.pure (commitRevealSourceBatch profile trace.2))
    apply Machine.StochasticRefinement.EventBatchLawCompatible.of_pure
    intro trace
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨source, pending, delivered⟩
    rcases source with
      ⟨aliceMove, bobMove, aliceRevealed, bobRevealed⟩
    cases aliceMove <;> cases bobMove <;>
      cases aliceRevealed <;> cases bobRevealed <;>
      rfl

noncomputable abbrev commitRevealSourceTraceGame : KernelGame Player :=
  Machine.eventBatchTraceKernelGame
    lockedMPMachine CommitRevealStrategy commitRevealSourceLawFamily
    (fun _ => 0) 4

noncomputable abbrev commitRevealMessageTraceGame : KernelGame Player :=
  Machine.eventBatchTraceKernelGame
    commitRevealMessageMachine CommitRevealStrategy
    commitRevealMessageLawFamily (fun _ => 0) 4

/-- Under the concrete commit/reveal scheduler, the first checkpoint has only
Alice's opaque commit in the visible buffers, so plaintext extraction is empty.
-/
theorem commitRevealLaw_before_bob_lock_buffers_plaintexts_empty
    (profile : ∀ player : Player, CommitRevealStrategy player) :
    PMF.map
        (fun trace =>
          (trace.2.pending,
            trace.2.delivered,
            commitRevealPlaintextPolicy.plaintexts
              (trace.2.pending ++ trace.2.delivered),
            trace.2.source.aliceMove,
            trace.2.source.bobMove))
        (commitRevealMessageMachine.eventBatchTraceDist
          (commitRevealMessageLaw profile) 1) =
      PMF.pure
        (aliceCommitView, [], [], some (commitRevealActionProfile profile
          Player.alice), none) := by
  simp [Machine.eventBatchTraceDist, Machine.eventBatchTraceDistFrom,
    commitRevealMessageLaw, commitRevealMessageBatch,
    commitRevealMessageMachine,
    Machine.messageInFlight, lockedMPMachine, Machine.runEventBatchesFrom,
    Machine.runEventsFrom, Machine.step, LockedMPState.init,
    LockedMPState.setMove, LockedMPState.outcome?,
    commitRevealActionProfile, aliceCommitView, commitMessage,
    commitRevealPlaintextPolicy, Machine.PlaintextPolicy.plaintexts,
    PMF.pure_map]

/-- Under the concrete commit/reveal scheduler, the second checkpoint has both
opaque commits in the visible buffers, no extracted plaintext, and both hidden
moves locked. -/
theorem commitRevealLaw_after_two_buffers_plaintexts_empty_and_locked
    (profile : ∀ player : Player, CommitRevealStrategy player) :
    PMF.map
        (fun trace =>
          (trace.2.pending,
            trace.2.delivered,
            commitRevealPlaintextPolicy.plaintexts
              (trace.2.pending ++ trace.2.delivered),
            trace.2.source.aliceMove,
            trace.2.source.bobMove,
            trace.2.source.aliceRevealed,
            trace.2.source.bobRevealed))
        (commitRevealMessageMachine.eventBatchTraceDist
          (commitRevealMessageLaw profile) 2) =
      PMF.pure
        (aliceBobCommitView, [], [],
          some (commitRevealActionProfile profile Player.alice),
          some (commitRevealActionProfile profile Player.bob),
          false, false) := by
  simp [Machine.eventBatchTraceDist, Machine.eventBatchTraceDistFrom,
    commitRevealMessageLaw, commitRevealMessageBatch,
    commitRevealMessageMachine,
    Machine.messageInFlight, lockedMPMachine, Machine.runEventBatchesFrom,
    Machine.runEventsFrom, Machine.step, LockedMPState.init,
    LockedMPState.setMove, LockedMPState.outcome?,
    commitRevealActionProfile, aliceCommitView, aliceBobCommitView,
    commitMessage, commitRevealPlaintextPolicy,
    Machine.PlaintextPolicy.plaintexts, PMF.pure_map]

theorem commitRevealMessage_projectTrace_eq
    (profile : ∀ player : Player, CommitRevealStrategy player) :
    PMF.map commitRevealMessageRefinement.projectEventBatchTrace
        (commitRevealMessageTraceGame.outcomeKernel profile) =
      commitRevealSourceTraceGame.outcomeKernel profile := by
  exact
    commitRevealMessageRefinement.eventBatchTraceKernelGame_projectTrace_eq
      commitRevealMessageLawLift (fun _ => 0) 4 profile

theorem commitRevealSourceTraceGame_eu_eq_matchingPennies
    (profile : ∀ player : Player, CommitRevealStrategy player)
    (player : Player) :
    commitRevealSourceTraceGame.eu profile player =
      matchingPenniesBoolGame.eu (commitRevealActionProfile profile)
        player := by
  cases player <;>
    simp [Machine.eventBatchTraceKernelGame,
      Machine.eventBatchTraceDist, Machine.eventBatchTraceDistFrom,
      commitRevealSourceLawFamily, commitRevealSourceLaw,
      commitRevealSourceBatch,
      lockedMPMachine, Machine.runEventBatchesFrom, Machine.runEventsFrom,
      Machine.step, KernelGame.eu, Machine.eventBatchTraceUtility,
      Machine.RoundView.optionOutcomeUtility, LockedMPState.init,
      LockedMPState.setMove, LockedMPState.markRevealed,
      LockedMPState.outcome?, matchingPenniesBoolGame,
      matchingPenniesRuntimeUtility, commitRevealActionProfile]

theorem commitRevealMessageTraceGame_eu_eq_matchingPennies
    (profile : ∀ player : Player, CommitRevealStrategy player)
    (player : Player) :
    commitRevealMessageTraceGame.eu profile player =
      matchingPenniesBoolGame.eu (commitRevealActionProfile profile)
        player := by
  cases player <;>
    simp [Machine.eventBatchTraceKernelGame,
      Machine.eventBatchTraceDist, Machine.eventBatchTraceDistFrom,
      commitRevealMessageLawFamily, commitRevealMessageLaw,
      commitRevealMessageBatch,
      commitRevealMessageMachine, Machine.messageInFlight,
      lockedMPMachine, Machine.runEventBatchesFrom, Machine.runEventsFrom,
      Machine.step, KernelGame.eu, Machine.eventBatchTraceUtility,
      Machine.RoundView.optionOutcomeUtility, LockedMPState.init,
      LockedMPState.setMove, LockedMPState.markRevealed,
      LockedMPState.outcome?, matchingPenniesBoolGame,
      matchingPenniesRuntimeUtility, commitRevealActionProfile,
      commitMessage, aliceCommitView, expect_pure]

theorem commitRevealActionProfile_update_const
    (profile : ∀ player : Player, CommitRevealStrategy player)
    (player : Player) (alternative : Bool) :
    commitRevealActionProfile
        (Function.update profile player (fun _ => alternative)) =
      Function.update (commitRevealActionProfile profile) player
        alternative := by
  funext who
  cases player <;> cases who <;>
    simp [commitRevealActionProfile, Function.update]

theorem commitRevealMessageTraceGame_no_pure_nash
    (profile : ∀ player : Player, CommitRevealStrategy player) :
    ¬ commitRevealMessageTraceGame.IsNash profile := by
  intro hNash
  apply matchingPenniesBoolGame_no_pure_nash
    (commitRevealActionProfile profile)
  intro player alternative
  let backendAlternative : CommitRevealStrategy player :=
    fun _ => alternative
  calc
    matchingPenniesBoolGame.eu (commitRevealActionProfile profile) player =
        commitRevealMessageTraceGame.eu profile player :=
      (commitRevealMessageTraceGame_eu_eq_matchingPennies
        profile player).symm
    _ ≥
        commitRevealMessageTraceGame.eu
          (Function.update profile player backendAlternative) player :=
      hNash player backendAlternative
    _ =
        matchingPenniesBoolGame.eu
          (Function.update (commitRevealActionProfile profile) player
            alternative) player := by
      rw [commitRevealMessageTraceGame_eu_eq_matchingPennies]
      change matchingPenniesBoolGame.eu
          (commitRevealActionProfile
            (Function.update profile player (fun _ => alternative)))
          player =
        matchingPenniesBoolGame.eu
          (Function.update (commitRevealActionProfile profile) player
            alternative) player
      rw [commitRevealActionProfile_update_const]
      rfl

/-! ## Audited backend preserves opaque commit/reveal payoff and Nash facts -/

noncomputable def auditedCommitRevealMessageMachine : Machine Player :=
  Machine.audited commitRevealMessageMachine

noncomputable def auditedCommitRevealMessageLawLift :
    (Machine.audited.refinement commitRevealMessageMachine)
      |>.EventBatchLawFamilyLift CommitRevealStrategy
        commitRevealMessageLawFamily :=
  Machine.audited.liftEventBatchLawFamily commitRevealMessageMachine
    commitRevealMessageLawFamily

theorem commitRevealMessageTraceUtility_bound
    (player : Player)
    (trace : commitRevealMessageMachine.EventBatchTrace) :
    |Machine.eventBatchTraceUtility commitRevealMessageMachine (fun _ => 0)
        trace player| ≤ 1 := by
  rcases trace with ⟨batches, state⟩
  rcases state with ⟨source, pending, delivered⟩
  rcases source with
    ⟨aliceMove, bobMove, aliceRevealed, bobRevealed⟩
  cases aliceMove <;> cases bobMove <;>
    cases aliceRevealed <;> cases bobRevealed <;>
    cases player <;>
    simp [Machine.eventBatchTraceUtility, commitRevealMessageMachine,
      Machine.messageInFlight, lockedMPMachine,
      Machine.RoundView.optionOutcomeUtility, LockedMPState.outcome?,
      matchingPenniesRuntimeUtility]
  all_goals split <;> norm_num

theorem auditedCommitRevealMessageTraceUtility_bound
    (player : Player)
    (trace : auditedCommitRevealMessageMachine.EventBatchTrace) :
    |Machine.eventBatchTraceUtility auditedCommitRevealMessageMachine
        (fun _ => 0) trace player| ≤ 1 := by
  simpa [auditedCommitRevealMessageMachine] using
    (Machine.audited.refinement commitRevealMessageMachine)
      |>.eventBatchTraceUtility_bound_project (fun _ => 0)
        commitRevealMessageTraceUtility_bound player trace

theorem auditedCommitRevealMessage_eu_eq_matchingPennies
    (profile : ∀ player : Player, CommitRevealStrategy player)
    (player : Player) :
    (Machine.eventBatchTraceKernelGame
        auditedCommitRevealMessageMachine CommitRevealStrategy
        auditedCommitRevealMessageLawLift.impl (fun _ => 0) 4).eu
      profile player =
      matchingPenniesBoolGame.eu (commitRevealActionProfile profile)
        player := by
  have h :=
    ((Machine.audited.refinement commitRevealMessageMachine)
      |>.eventBatchTraceEUMorphismOfBounded
        auditedCommitRevealMessageLawLift (fun _ => 0) 4
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        auditedCommitRevealMessageTraceUtility_bound
        commitRevealMessageTraceUtility_bound).eu_preserved profile player
  simpa [auditedCommitRevealMessageMachine,
    commitRevealMessageTraceGame] using
    h.symm.trans
      (commitRevealMessageTraceGame_eu_eq_matchingPennies profile player)

theorem auditedCommitRevealMessage_no_pure_nash
    (profile : ∀ player : Player, CommitRevealStrategy player) :
    ¬ (Machine.eventBatchTraceKernelGame
        auditedCommitRevealMessageMachine CommitRevealStrategy
        auditedCommitRevealMessageLawLift.impl (fun _ => 0) 4).IsNash
      profile := by
  intro hNash
  apply matchingPenniesBoolGame_no_pure_nash
    (commitRevealActionProfile profile)
  intro player alternative
  let backendAlternative : CommitRevealStrategy player :=
    fun _ => alternative
  calc
    matchingPenniesBoolGame.eu (commitRevealActionProfile profile) player =
        (Machine.eventBatchTraceKernelGame
          auditedCommitRevealMessageMachine CommitRevealStrategy
          auditedCommitRevealMessageLawLift.impl (fun _ => 0) 4).eu
          profile player :=
      (auditedCommitRevealMessage_eu_eq_matchingPennies
        profile player).symm
    _ ≥
        (Machine.eventBatchTraceKernelGame
          auditedCommitRevealMessageMachine CommitRevealStrategy
          auditedCommitRevealMessageLawLift.impl (fun _ => 0) 4).eu
          (Function.update profile player backendAlternative) player :=
      hNash player backendAlternative
    _ =
        matchingPenniesBoolGame.eu
          (Function.update (commitRevealActionProfile profile) player
            alternative) player := by
      rw [auditedCommitRevealMessage_eu_eq_matchingPennies]
      change matchingPenniesBoolGame.eu
          (commitRevealActionProfile
            (Function.update profile player (fun _ => alternative)))
          player =
        matchingPenniesBoolGame.eu
          (Function.update (commitRevealActionProfile profile) player
            alternative) player
      rw [commitRevealActionProfile_update_const]
      rfl

end Refinement
end Examples
end Vegas
