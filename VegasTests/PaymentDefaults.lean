/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProgramPaymentAsyncNash
import Vegas.Examples.ProgramPaymentsRuntimeService

/-! # Declared exit receipts override an unconditional payment instruction -/

noncomputable section

namespace VegasTests.PaymentDefaults

open Vegas Vegas.SourceProgram Vegas.EventGraphRuntime Interaction
  GameTheory GameTheory.Protocol GameTheory.Math.Probability
open Vegas.Examples.ProgramPayments

private def guard : SourceGuard simpleExpr [] Player.alice 0 .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by simp
  code := .constBool true
  reads := fun h => nomatch h

private def cashProgram : SourceProgram Player simpleExpr [] ∅ :=
  .commit 0 .alice (by decide) guard <|
  .reveal 1 .alice 0 (by decide) .here (by decide) <|
  .ret [(.alice, .constInt 5)]

private abbrev cashSetup (exit : Int) : Setup (Player := Player) (L := simpleExpr) :=
  { setup 5 with program := cashProgram, exitTransfers := fun _ => exit }

private abbrev cashLeaks (exit : Int) :
    MessageNetwork.ObservationRule Player (WitnessedPacket (graph (cashSetup exit))) :=
  fun _ _ => PMF.pure ∅

private abbrev cashBounds (exit : Int) : MessageBounds (graph (cashSetup exit)) where
  candidateCount := 2
  values := Vegas.Examples.ProgramPaymentsRuntime.rawValues

private abbrev cashRosterService (exit : Int) : SourceServiceSpec Player simpleExpr where
  setup := cashSetup exit
  leaks := cashLeaks exit
  bounds := cashBounds exit
  rosters := fun _ => [.alice]
  network := (runtime (cashSetup exit)).idleNetwork (cashLeaks exit)
  values := Vegas.Examples.ProgramPaymentsRuntime.binding_values_covered 5
  initialValues := by
    intro state supported
    change state ∈ ((cashSetup exit).initialLaw.map
      (fun initial => EventGraphRuntime.State.initial (graph := graph (cashSetup exit))
        ((cashSetup exit).eventInputs initial))).support at supported
    obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
    intro candidate raw opened
    rcases candidate with ⟨owner, slot⟩
    rw [EventGraphRuntime.State.initial_candidate] at opened
    cases slot with
    | initial input => exact Fin.elim0 input
    | prepared serial => cases opened
  capacity := by change 2 ≤ 2; decide
  opportunities := by
    intro event owner _
    cases owner
    exact List.mem_singleton_self Player.alice
  initialFinite := ⟨by
    change (PMF.pure initial).support.Finite
    rw [PMF.support_pure]
    exact Set.finite_singleton initial⟩
  leaksFinite := ⟨fun _ _ => by
    rw [PMF.support_pure]
    exact Set.finite_singleton ∅⟩

private abbrev cashService (exit : Int) := (cashRosterService exit).toAsync

private def profile (binding : Option (PublicationResult Bool)) (disclose : Bool) :
    BehavioralProfile cashProgram
  | .alice => (fun _ _ _ => PMF.pure binding, (fun _ _ _ => PMF.pure disclose, PUnit.unit))

private def finished (binding : Option (PublicationResult Bool)) (disclose : Bool) :
    Config Player simpleExpr cashProgram.terminalCtx :=
  revealSuccessor 1 .here (commitSuccessor 0 guard (Config.initial initial) binding) disclose

private theorem run_profile (binding : Option (PublicationResult Bool)) (disclose : Bool) :
    cashProgram.run (profile binding disclose) initial = PMF.pure (finished binding disclose) := by
  change (PMF.pure binding).bind _ = _
  rw [PMF.pure_bind]
  cases binding with
  | none =>
      change (PMF.pure false).bind _ = _
      rw [PMF.pure_bind]
      cases disclose <;> rfl
  | some result =>
      change (PMF.pure disclose).bind _ = _
      rw [PMF.pure_bind]
      rfl

private def admission : CommitmentInterface cashProgram :=
  CommitmentInterface.forfeiture cashProgram

private theorem permitted (binding : Option (PublicationResult Bool)) (disclose : Bool)
    (who : Player) : (profile binding disclose who).Admitted cashProgram admission := by
  cases who
  constructor
  · intro _ _ _ choice _
    cases choice with
    | none => trivial
    | some result => cases result <;> trivial
  · trivial

private def auditSample (exit : Int)
    (_actual : List (SettledEvidence (cashSetup exit) .sequential)) :
    PMF (List (SettledEvidence (cashSetup exit) .sequential)) := PMF.pure []

private theorem authentic (exit : Int) :
    ∀ actual observed, observed ∈ (auditSample exit actual).support → observed ⊆ actual := by
  intro actual observed supported
  have same := (PMF.mem_support_pure_iff _ _).mp supported
  subst observed
  exact List.nil_subset actual

private theorem omission_defaulted : Player.alice ∈ (finished none false).defaulted := by
  decide

private theorem success_not_defaulted :
    Player.alice ∉ (finished (some (.success true)) true).defaulted := by
  decide

private theorem omission_transfers (exit : Int) : (cashSetup exit).transfers
    (cashProgram.publicOutcome (finished none false)) .alice = (exit : ℝ) := by
  change (if Player.alice ∈ (finished none false).defaulted then (exit : ℝ)
    else cashProgram.publicTransfers (cashProgram.publicOutcome (finished none false)) .alice) = _
  exact ite_eq_left omission_defaulted

private theorem literal_transfers (outcome : PublicOutcome cashProgram) :
    cashProgram.publicTransfers outcome .alice = 5 := by
  change ((transferAmount [(Player.alice, 5)] Player.alice : Int) : ℝ) = 5
  norm_num [transferAmount]

private def omissionSource (exit : Int) :
    Profile ((cashSetup exit).informationModel admission).behavioralSignature :=
  (cashSetup exit).encodeBehavioralProfile admission (profile none false) (permitted none false)

/-- The source omission is a real execution, whose instruction still evaluates to five. -/
example : (cashSetup 0).program.publicTransfers
    (cashProgram.publicOutcome (finished none false)) .alice = 5 :=
  literal_transfers _

/-- Omission pays the declared exit amount, not the unconditional instruction. -/
example (exit : Int) : (cashSetup exit).transfers
    (cashProgram.publicOutcome (finished none false)) .alice = (exit : ℝ) :=
  omission_transfers exit

/-- The parameterized monetary source utility includes the six-unit exit override. -/
example : (cashSetup 6).parameterPaymentUtility
    (fun (_ : Unit × PublicOutcome cashProgram) (_ : Player) => 0)
    ((), cashProgram.publicOutcome (finished none false)) .alice = 6 := by
  rw [Setup.parameterPaymentUtility_eq, zero_add]
  exact omission_transfers 6

/-- Actual compiled graph receipts pay six on omission even though `ret` pays five. -/
example :
    (((cashSetup 6).eventGame (cashSetup 6).eventGraph.canonicalScheduler).play
        (compileEventProfile cashProgram (profile none false))).map
        (fun outcome => (cashSetup 6).eventTransfers outcome .alice) = PMF.pure 6 := by
  simp_rw [Setup.eventTransfers_eq_transfers]
  change (((cashSetup 6).eventGraph.canonicalGame
      ((cashSetup 6).initialLaw.map (cashSetup 6).eventInputs)).play
        (compileEventProfile cashProgram (profile none false))).map
      ((fun terminal => (cashSetup 6).transfers (cashProgram.publicOutcome terminal) .alice) ∘
        terminalConfig cashProgram) = _
  rw [← PMF.map_comp]
  erw [canonical_setup_law (cashSetup 6) (profile none false)]
  change ((PMF.pure initial).bind _).map _ = _
  erw [PMF.pure_bind, run_profile, PMF.pure_map]
  exact congrArg PMF.pure (omission_transfers 6)

/-- The same contract retains the ordinary five-unit receipt on successful play. -/
example : (cashSetup 0).transfers
    (cashProgram.publicOutcome (finished (some (.success true)) true)) .alice = 5 := by
  change (if Player.alice ∈ (finished (some (.success true)) true).defaulted
    then ((0 : Int) : ℝ) else cashProgram.publicTransfers
      (cashProgram.publicOutcome (finished (some (.success true)) true)) .alice) = 5
  rw [ite_eq_right success_not_defaulted]
  exact literal_transfers _

/-- The ordinary compiler realizes that exact exit receipt on the actual bounded ledger. -/
example (exit : Int) :
    ((((cashService exit).rawMenu.information (serviceInitialLaw (cashSetup exit) .sequential)
        (cashService exit).horizon (cashService exit).scheduler).runBehavioral
      ((cashService exit).clientProfile admission (cashService exit).rawMenu
        (firstTurnTiming (cashSetup exit) 1 .sequential) (omissionSource exit))
      (2 * (cashService exit).horizon + 1)).bind fun final =>
        ((cashService exit).paymentSettlement (auditSample exit) (fun _ => 0) final.state).map
          (fun receipts => receipts .alice)) = PMF.pure (exit : ℝ) := by
  have law := (cashService exit).payment_firstTurnClientProfile_settlement_law admission
    (cashSetup exit).eventGraph.sequentialize_barrierOrdered (auditSample exit) (authentic exit)
    (fun _ => 0) 1 (omissionSource exit)
  have cash := congrArg (PMF.map (fun realized => realized.2 Player.alice)) law
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at cash
  erw [cash]
  unfold omissionSource
  erw [(cashSetup exit).decodeBehavioralProfile_encodeBehavioralProfile admission
    (profile none false) (permitted none false)]
  change ((PMF.pure initial).bind _).map _ = _
  erw [PMF.pure_bind, run_profile, PMF.pure_map]
  congr 1

end VegasTests.PaymentDefaults
