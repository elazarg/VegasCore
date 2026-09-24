/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceService
import Interaction.ReactiveMenuPolicy
import Interaction.ReactiveFiniteAssessment
import Interaction.ReactiveRounds

/-! # The fixed pending-message calendar for the named-evidence source fixture

There are two ambient responses, followed by six protected source visits.
Each visit grants its stage, activates its owner, records the latest matching
envelope, advances the declared clock, and settles any omitted source action.
No Alice activation occurs between Carol's and Bob's guesses. The scheduler
depends on public pending traffic and its own position, not on private leaks.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Vegas.SourceProgram Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

inductive Instruction where
  | player (who : Player)
  | application (command : Command)
  | record (event : Event)
  deriving DecidableEq

def visit (event : Event) : List Instruction :=
  [.application (.grant event), .player (eventOwner event), .record event] ++
    List.replicate (2 ^ event.val) (.application .tick) ++ [.application (.settle event)]

def calendar : List Instruction :=
  [.player alice, .player bob] ++ (List.finRange 6).flatMap visit

def before (count : Nat) : List Instruction :=
  [.player alice, .player bob] ++ ((List.finRange 6).take count).flatMap visit

theorem before_succ (event : Event) : before (event.val + 1) = before event.val ++ visit event := by
  fin_cases event <;> rfl

theorem calendar_length : calendar.length = 89 := by decide

open Classical in
def latest {Claim : Type} (view : (application Claim).EnvironmentView) (event : Event) :
    (application Claim).Command :=
  match view.network.pending.reverse.find? fun message =>
    message.sender = eventOwner event ∧ message.payload.address = some event ∧
      ¬ view.network.ledger.any (fun recorded => recorded.id = message.id) with
  | none => .wait
  | some message => .include message.id

def instruction {Claim : Type} (view : (application Claim).EnvironmentView) :
    Instruction → (application Claim).Command
  | .player who => .activate who
  | .application command => .application command
  | .record event => latest view event

def scheduler (Claim : Type) : (application Claim).Scheduler := fun past view =>
  FinDist.pure ((calendar[past.length]?).elim .wait (instruction view))

abbrev horizon : Nat := calendar.length
abbrev arena (Claim : Type) [Fintype Claim] :=
  (menu Claim).protocol (FinDist.pure initial) horizon (scheduler Claim)
abbrev model (Claim : Type) [Fintype Claim] :=
  (menu Claim).information (FinDist.pure initial) horizon (scheduler Claim)

def root (Claim : Type) : (application Claim).Execution :=
  .initial (application Claim) initial

def results (state : State) : Results :=
  ⟨(publications state.core alice).getD .failure,
    (publications state.core bob).getD .failure,
    (publications state.core carol).getD .failure⟩

def payoff {Claim : Type} [Fintype Claim] (who : Player) (history : (arena Claim).History) : ℝ :=
  utility (history.state.elim ⟨.failure, .failure, .failure⟩
    (fun control => results control.execution.application)) who

/-- Only a publicly recorded Alice certificate directs the prescribed guess.
Private claims, including request-shaped messages, remain observations. -/
def publicGuess {Claim : Type} (view : (application Claim).PlayerView) : Bool :=
  ((view.messages.ledger.flatMap fun message => message.payload.evidence.toList).find?
    (fun fact => fact.1 = 0)).map Prod.snd |>.getD false

def playing (Claim : Type) (defaultClaim : Claim) (event : Event)
    (binding : PublicationResult Bool) : (application Claim).Action :=
  ⟨some (.submit ⟨some event, if event.val < 3 then .bind else .open,
    defaultClaim, binding, none⟩)⟩

def policy (Claim : Type) (defaultClaim : Claim) (who : Player) :
    (application Claim).Policy := fun _ view =>
  match view.application.visit with
  | none => FinDist.pure ⟨none⟩
  | some event =>
      if who = eventOwner event then
        if event.val = 0 then
          (FinDist.uniformOfFintype (α := Bool)).map fun bit =>
            playing Claim defaultClaim event (.success bit)
        else FinDist.pure (playing Claim defaultClaim event (.success (publicGuess view)))
      else FinDist.pure ⟨none⟩

theorem playing_available (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (who : Player) (past : List (application Claim).PlayerEntry)
    (view : (application Claim).PlayerView) (event : Event) (binding : PublicationResult Bool) :
    playing Claim defaultClaim event binding ∈ (menu Claim).actions who past view :=
  every_submission Claim who past view _

theorem silence_available (Claim : Type) [Fintype Claim] (who : Player)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView) :
    (⟨none⟩ : (application Claim).Action) ∈ (menu Claim).actions who past view := by
  classical
  apply (baseMenu Claim).base_available
  exact Finset.mem_union_left _ (Finset.mem_singleton_self _)

theorem policy_covered (Claim : Type) [Fintype Claim] (defaultClaim : Claim) (who : Player)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (action : (application Claim).Action)
    (supported : action ∈ (policy Claim defaultClaim who past view).support) :
    action ∈ (menu Claim).actions who past view := by
  unfold policy at supported
  split at supported
  · cases FinDist.mem_support_pure.mp supported
    exact silence_available Claim who past view
  · split at supported
    · split at supported
      · obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ supported
        exact playing_available Claim defaultClaim who past view _ _
      · cases FinDist.mem_support_pure.mp supported
        exact playing_available Claim defaultClaim who past view _ _
    · cases FinDist.mem_support_pure.mp supported
      exact silence_available Claim who past view

def profile (Claim : Type) [Fintype Claim] (defaultClaim : Claim) :
    Profile (model Claim).behavioralSignature := fun who =>
  (menu Claim).restrictPolicy (FinDist.pure initial) horizon (scheduler Claim) who
    (policy Claim defaultClaim who)
    (fun _ _ _ => policy_covered Claim defaultClaim who _ _)

/-- One positive mixture weight applies at every player and information site;
the reference is uniform on the entire declared menu, including every replay. -/
def tremble (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1) :
    (model Claim).BehavioralAssessment :=
  (menu Claim).perturbedAssessment (FinDist.pure initial) horizon (scheduler Claim)
    (profile Claim defaultClaim) weight positive atMostOne

theorem tremble_fullyMixed (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1) :
    (tremble Claim defaultClaim weight positive atMostOne).IsFullyMixed :=
  (menu Claim).perturbedAssessment_fullyMixed (FinDist.pure initial) horizon (scheduler Claim)
    (profile Claim defaultClaim) weight positive atMostOne

theorem tremble_bayes (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1) :
    InformationModel.BehavioralAssessment.IsBayesConsistent (model Claim)
      (tremble Claim defaultClaim weight positive atMostOne)
      ((menu Claim).decisionInformationAntichain (FinDist.pure initial)
        horizon (scheduler Claim)) :=
  (menu Claim).perturbedAssessment_bayes (FinDist.pure initial) horizon (scheduler Claim)
    (profile Claim defaultClaim) weight positive atMostOne

end VegasTests.SelectiveAssociation.NamedSource
