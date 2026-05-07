import Vegas.Examples.Prisoners
import Vegas.Examples.MatchingPennies
import Vegas.Examples.BattleOfTheSexes
import Vegas.Examples.MontyHall
import Vegas.ProtocolSemantics
import Vegas.Corollaries.PureStrategic
import Vegas.Corollaries.Equilibrium

/-!
# Strategic semantics examples

Examples showing how checked Vegas programs enter the generated strategic and
trace games. These statements are deliberately phrased over `WFProgram`s,
`pureKernelGame`, `pmfBehavioralKernelGame`, and blocked-trace games rather
than over hand-written normal-form games.
-/

namespace Vegas
namespace Examples
namespace StrategicSemantics

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- A concrete legal generated pure strategy for any player in any checked
program.

This is intentionally generic: it demonstrates how the generated strategy
carrier is inhabited. Source-specific examples can replace the choice step by
a hand-written policy such as “commit `false` at my first commit node.”
-/
noncomputable def defaultPureStrategy
    (g : WFProgram P L) [FiniteDomains g] (who : P) :
    (pureKernelGame g).Strategy who := by
  classical
  let horizon := syntaxSteps g.prog
  let G := (eventGraphFOSGView g).toBoundedFOSG horizon
  let hLeg : G.LegalObservable := by
    simpa [G, horizon] using
      eventGraphFOSGView_toBoundedFOSG_legalObservable g horizon
  let chooseMove : G.ReachablePureStrategy who := fun s =>
    Classical.choose (G.availableMoves_nonempty (Classical.choose s.2) who)
  refine ⟨chooseMove, ?_⟩
  intro h
  dsimp [chooseMove]
  let s : G.ReachableInfoState who := G.reachableInfoStateOfHistory who h
  let witness : G.History := Classical.choose s.2
  have hwitness : witness.playerView who = s.1 := by
    simpa [witness] using Classical.choose_spec s.2
  have hchosen :
      Classical.choose (G.availableMoves_nonempty witness who) ∈
        G.availableMoves witness who :=
    Classical.choose_spec (G.availableMoves_nonempty witness who)
  have hview : witness.playerView who = h.playerView who := by
    simpa [s] using hwitness
  have hEq := G.availableMoves_eq_of_playerView_eq hLeg who hview
  exact hEq ▸ hchosen

/-- A concrete generated pure profile for any checked program. -/
noncomputable def defaultPureProfile
    (g : WFProgram P L) [FiniteDomains g] :
    (pureKernelGame g).Profile :=
  fun who => defaultPureStrategy g who

/-- For any checked program, public pure-strategic play and pure blocked-trace
play have the same expected utility. -/
theorem pure_eu_eq_blockedTrace
    (g : WFProgram P L) [FiniteDomains g]
    (π : (pureKernelGame g).Profile) (who : P) :
    (pureBlockedTraceKernelGameAt g).eu π who =
      (pureKernelGame g).eu π who :=
  pureBlockedTraceKernelGameAt_eu_eq g π who

/-- For any checked program, pure Nash is invariant under replacing public
outcomes by full blocked traces. -/
theorem pure_nash_iff_blockedTrace
    (g : WFProgram P L) [FiniteDomains g]
    (π : (pureKernelGame g).Profile) :
    (pureKernelGame g).IsNash π ↔
      (pureBlockedTraceKernelGameAt g).IsNash π := by
  constructor
  · intro h who s'
    have hpure := h who s'
    calc
      (pureBlockedTraceKernelGameAt g).eu π who =
          (pureKernelGame g).eu π who :=
            pure_eu_eq_blockedTrace g π who
      _ ≥ (pureKernelGame g).eu (Function.update π who s') who := hpure
      _ = (pureBlockedTraceKernelGameAt g).eu
          (Function.update π who s') who :=
            (pure_eu_eq_blockedTrace g (Function.update π who s') who).symm
  · intro h who s'
    have htrace := h who s'
    calc
      (pureKernelGame g).eu π who =
          (pureBlockedTraceKernelGameAt g).eu π who :=
            (pure_eu_eq_blockedTrace g π who).symm
      _ ≥ (pureBlockedTraceKernelGameAt g).eu
          (Function.update π who s') who := htrace
      _ = (pureKernelGame g).eu (Function.update π who s') who :=
            pure_eu_eq_blockedTrace g (Function.update π who s') who

/-- Dominant pure strategies are invariant under the same public/trace
presentation change. -/
theorem pure_dominant_iff_blockedTrace
    (g : WFProgram P L) [FiniteDomains g]
    (who : P) (s : (pureKernelGame g).Strategy who) :
    (pureKernelGame g).IsDominant who s ↔
      (pureBlockedTraceKernelGameAt g).IsDominant who s := by
  constructor
  · intro h σ s'
    have hpure := h σ s'
    calc
      (pureBlockedTraceKernelGameAt g).eu (Function.update σ who s) who =
          (pureKernelGame g).eu (Function.update σ who s) who :=
            pure_eu_eq_blockedTrace g (Function.update σ who s) who
      _ ≥ (pureKernelGame g).eu (Function.update σ who s') who := hpure
      _ = (pureBlockedTraceKernelGameAt g).eu
          (Function.update σ who s') who :=
            (pure_eu_eq_blockedTrace g (Function.update σ who s') who).symm
  · intro h σ s'
    have htrace := h σ s'
    calc
      (pureKernelGame g).eu (Function.update σ who s) who =
          (pureBlockedTraceKernelGameAt g).eu
            (Function.update σ who s) who :=
            (pure_eu_eq_blockedTrace g (Function.update σ who s) who).symm
      _ ≥ (pureBlockedTraceKernelGameAt g).eu
          (Function.update σ who s') who := htrace
      _ = (pureKernelGame g).eu (Function.update σ who s') who :=
            pure_eu_eq_blockedTrace g (Function.update σ who s') who

/-- For any checked program, PMF-behavioral public play and PMF-behavioral
blocked-trace play have the same expected utility. -/
theorem behavioral_eu_eq_blockedTrace
    (g : WFProgram P L) [FiniteDomains g]
    (β : (pmfBehavioralKernelGame g).Profile) (who : P) :
    (pmfBehavioralBlockedTraceKernelGameAt g).eu β who =
      (pmfBehavioralKernelGame g).eu β who :=
  pmfBehavioralBlockedTraceKernelGameAt_eu_eq g β who

/-- PMF-behavioral Nash is invariant under replacing public outcomes by full
blocked traces. -/
theorem behavioral_nash_iff_blockedTrace
    (g : WFProgram P L) [FiniteDomains g]
    (β : (pmfBehavioralKernelGame g).Profile) :
    (pmfBehavioralKernelGame g).IsNash β ↔
      (pmfBehavioralBlockedTraceKernelGameAt g).IsNash β := by
  constructor
  · intro h who s'
    have hbehavioral := h who s'
    calc
      (pmfBehavioralBlockedTraceKernelGameAt g).eu β who =
          (pmfBehavioralKernelGame g).eu β who :=
            behavioral_eu_eq_blockedTrace g β who
      _ ≥ (pmfBehavioralKernelGame g).eu
          (Function.update β who s') who := hbehavioral
      _ = (pmfBehavioralBlockedTraceKernelGameAt g).eu
          (Function.update β who s') who :=
            (behavioral_eu_eq_blockedTrace g
              (Function.update β who s') who).symm
  · intro h who s'
    have htrace := h who s'
    calc
      (pmfBehavioralKernelGame g).eu β who =
          (pmfBehavioralBlockedTraceKernelGameAt g).eu β who :=
            (behavioral_eu_eq_blockedTrace g β who).symm
      _ ≥ (pmfBehavioralBlockedTraceKernelGameAt g).eu
          (Function.update β who s') who := htrace
      _ = (pmfBehavioralKernelGame g).eu
          (Function.update β who s') who :=
            behavioral_eu_eq_blockedTrace g
              (Function.update β who s') who

/-- Every finite checked Vegas program satisfies the PMF behavioral
realization theorem for mixed profiles over pure strategies. -/
theorem kuhnPMF (g : WFProgram P L) [FiniteDomains g] : KuhnPMF g :=
  kuhnPMF_finite g

namespace Prisoners

noncomputable def defaultProfile :
    (pureKernelGame Prisoners.game).Profile :=
  StrategicSemantics.defaultPureProfile Prisoners.game

/-- The source node for Row's first commitment in the Prisoner's Dilemma
program. -/
noncomputable def rowCommitNode : ProgramNode Prisoners.program :=
  .commitHere

/-- Row's concrete compiled write slice for committing to `false`
(`false` means defect in `Prisoners.lean`). -/
noncomputable def rowDefectSlice : ProgramField.WriteSlice Prisoners.program :=
  ProgramField.singleSlice (ProgramField.writtenBy rowCommitNode)
    (EventGraph.StoredValue.hidden false)

/-- The generated protocol-graph player action corresponding to Row's
source-level choice to defect at the first commitment. -/
noncomputable def rowDefectAction :
    EventGraph.PlayerAction
      (programEventGraph Prisoners.game) Prisoners.Player.row where
  node := rowCommitNode
  slice := rowDefectSlice

theorem rowDefectSlice_legal :
    (programEventGraph Prisoners.game).sliceLegal
      rowCommitNode rowDefectSlice := by
  change ProgramNode.sliceLegal Prisoners.game.obligations
    rowCommitNode rowDefectSlice
  unfold ProgramNode.sliceLegal
  unfold ProgramNode.sem
  dsimp [rowCommitNode, rowDefectSlice]
  exact ⟨false, rfl⟩

theorem rowDefectAction_legal_initial :
    (programEventGraph Prisoners.game).actionLegal
      (EventGraph.Configuration.initial
        (programEventGraph Prisoners.game)).result
      rowCommitNode rowDefectSlice := by
  change ProgramNode.actionLegal Prisoners.game.env Prisoners.game.obligations
    (EventGraph.Configuration.initial
      (programEventGraph Prisoners.game)).result
    rowCommitNode rowDefectSlice
  unfold ProgramNode.actionLegal
  unfold ProgramNode.sem
  dsimp [rowCommitNode, rowDefectSlice]
  refine ⟨?_, false, ?_, ?_⟩
  · intro read hread
    have hread_empty := hread
    simp only [Prisoners.game, Prisoners.Γ0, eraseVCtx_nil, eraseVCtx_cons,
      erasePubVCtx_cons_pub, erasePubVCtx_cons_hidden, erasePubVCtx_nil,
      ProgramField.commitEventGuard, ProgramField.currentFields,
      VCtxField.enumerate, List.map_nil, List.toFinset_nil] at hread_empty
    cases hread_empty
  · rfl
  · rfl

theorem rowCommitNode_prereqs_eq_empty :
    ProgramNode.prereqs Prisoners.game.obligations rowCommitNode = ∅ := by
  classical
  apply Finset.ext
  intro prereq
  constructor
  · intro hpre
    unfold ProgramNode.prereqs at hpre
    exact False.elim
      (Nat.not_lt_zero prereq.rank (Finset.mem_filter.mp hpre).2.1)
  · intro hpre
    cases hpre

theorem rowCommitNode_initial_frontier :
    rowCommitNode ∈
      (EventGraph.Configuration.initial
        (programEventGraph Prisoners.game)).frontier := by
  apply (EventGraph.Configuration.mem_frontier_iff
    (cfg := EventGraph.Configuration.initial
      (programEventGraph Prisoners.game)) rowCommitNode).mpr
  rw [EventGraph.Configuration.Enabled]
  refine ⟨?_, ?_, ?_⟩
  · exact ProgramNode.mem_finset Prisoners.program rowCommitNode
  · rfl
  · intro prereq hpre
    exfalso
    change prereq ∈ ProgramNode.prereqs Prisoners.game.obligations
      rowCommitNode at hpre
    rw [rowCommitNode_prereqs_eq_empty] at hpre
    cases hpre

theorem rowCommitNode_actor :
    (ProgramNode.sem Prisoners.game.obligations rowCommitNode).actor =
      some Prisoners.Player.row := by
  have hsem : ∃ field guard,
      ProgramNode.sem Prisoners.game.obligations rowCommitNode =
          EventGraph.NodeSem.commit Prisoners.Player.row field guard := by
    unfold ProgramNode.sem
    dsimp [rowCommitNode, Prisoners.game, Prisoners.program]
    refine ⟨_, _, rfl⟩
  rcases hsem with ⟨_field, _guard, hsem⟩
  rw [hsem]
  rfl

theorem rowDefectAction_available_initial :
    rowDefectAction ∈ EventGraph.available
      (programEventGraph Prisoners.game)
      (EventGraph.Configuration.initial (programEventGraph Prisoners.game))
      Prisoners.Player.row := by
  refine ⟨rowCommitNode_initial_frontier, ?_,
    rowDefectSlice_legal, rowDefectAction_legal_initial⟩
  change (ProgramNode.sem Prisoners.game.obligations rowCommitNode).actor =
    some Prisoners.Player.row
  exact rowCommitNode_actor

theorem defaultProfile_eu_eq_blockedTrace
    (who : Prisoners.Player) :
    (pureBlockedTraceKernelGameAt Prisoners.game).eu defaultProfile who =
      (pureKernelGame Prisoners.game).eu defaultProfile who :=
  StrategicSemantics.pure_eu_eq_blockedTrace
    Prisoners.game defaultProfile who

theorem pure_eu_eq_blockedTrace
    (π : (pureKernelGame Prisoners.game).Profile)
    (who : Prisoners.Player) :
    (pureBlockedTraceKernelGameAt Prisoners.game).eu π who =
      (pureKernelGame Prisoners.game).eu π who :=
  StrategicSemantics.pure_eu_eq_blockedTrace Prisoners.game π who

theorem pure_nash_iff_blockedTrace
    (π : (pureKernelGame Prisoners.game).Profile) :
    (pureKernelGame Prisoners.game).IsNash π ↔
      (pureBlockedTraceKernelGameAt Prisoners.game).IsNash π :=
  StrategicSemantics.pure_nash_iff_blockedTrace Prisoners.game π

theorem behavioral_nash_iff_blockedTrace
    (β : (pmfBehavioralKernelGame Prisoners.game).Profile) :
    (pmfBehavioralKernelGame Prisoners.game).IsNash β ↔
      (pmfBehavioralBlockedTraceKernelGameAt Prisoners.game).IsNash β :=
  StrategicSemantics.behavioral_nash_iff_blockedTrace Prisoners.game β

theorem kuhnPMF : KuhnPMF Prisoners.game :=
  StrategicSemantics.kuhnPMF Prisoners.game

end Prisoners

namespace MatchingPennies

noncomputable def defaultProfile :
    (pureKernelGame MatchingPennies.game).Profile :=
  StrategicSemantics.defaultPureProfile MatchingPennies.game

theorem defaultProfile_nash_iff_blockedTrace :
    (pureKernelGame MatchingPennies.game).IsNash defaultProfile ↔
      (pureBlockedTraceKernelGameAt MatchingPennies.game).IsNash
        defaultProfile :=
  StrategicSemantics.pure_nash_iff_blockedTrace
    MatchingPennies.game defaultProfile

theorem pure_eu_eq_blockedTrace
    (π : (pureKernelGame MatchingPennies.game).Profile)
    (who : MatchingPennies.Player) :
    (pureBlockedTraceKernelGameAt MatchingPennies.game).eu π who =
      (pureKernelGame MatchingPennies.game).eu π who :=
  StrategicSemantics.pure_eu_eq_blockedTrace MatchingPennies.game π who

theorem pure_nash_iff_blockedTrace
    (π : (pureKernelGame MatchingPennies.game).Profile) :
    (pureKernelGame MatchingPennies.game).IsNash π ↔
      (pureBlockedTraceKernelGameAt MatchingPennies.game).IsNash π :=
  StrategicSemantics.pure_nash_iff_blockedTrace MatchingPennies.game π

theorem behavioral_nash_iff_blockedTrace
    (β : (pmfBehavioralKernelGame MatchingPennies.game).Profile) :
    (pmfBehavioralKernelGame MatchingPennies.game).IsNash β ↔
      (pmfBehavioralBlockedTraceKernelGameAt MatchingPennies.game).IsNash β :=
  StrategicSemantics.behavioral_nash_iff_blockedTrace MatchingPennies.game β

theorem kuhnPMF : KuhnPMF MatchingPennies.game :=
  StrategicSemantics.kuhnPMF MatchingPennies.game

end MatchingPennies

namespace BattleOfTheSexes

noncomputable def defaultProfile :
    (pureKernelGame BattleOfTheSexes.game).Profile :=
  StrategicSemantics.defaultPureProfile BattleOfTheSexes.game

theorem pure_eu_eq_blockedTrace
    (π : (pureKernelGame BattleOfTheSexes.game).Profile)
    (who : BattleOfTheSexes.Player) :
    (pureBlockedTraceKernelGameAt BattleOfTheSexes.game).eu π who =
      (pureKernelGame BattleOfTheSexes.game).eu π who :=
  StrategicSemantics.pure_eu_eq_blockedTrace BattleOfTheSexes.game π who

theorem pure_nash_iff_blockedTrace
    (π : (pureKernelGame BattleOfTheSexes.game).Profile) :
    (pureKernelGame BattleOfTheSexes.game).IsNash π ↔
      (pureBlockedTraceKernelGameAt BattleOfTheSexes.game).IsNash π :=
  StrategicSemantics.pure_nash_iff_blockedTrace BattleOfTheSexes.game π

theorem behavioral_nash_iff_blockedTrace
    (β : (pmfBehavioralKernelGame BattleOfTheSexes.game).Profile) :
    (pmfBehavioralKernelGame BattleOfTheSexes.game).IsNash β ↔
      (pmfBehavioralBlockedTraceKernelGameAt BattleOfTheSexes.game).IsNash β :=
  StrategicSemantics.behavioral_nash_iff_blockedTrace BattleOfTheSexes.game β

theorem kuhnPMF : KuhnPMF BattleOfTheSexes.game :=
  StrategicSemantics.kuhnPMF BattleOfTheSexes.game

end BattleOfTheSexes

namespace MontyHall

noncomputable def defaultProfile :
    (pureKernelGame MontyHall.game).Profile :=
  StrategicSemantics.defaultPureProfile MontyHall.game

theorem defaultProfile_eu_eq_blockedTrace
    (who : MontyHall.Player) :
    (pureBlockedTraceKernelGameAt MontyHall.game).eu defaultProfile who =
      (pureKernelGame MontyHall.game).eu defaultProfile who :=
  StrategicSemantics.pure_eu_eq_blockedTrace
    MontyHall.game defaultProfile who

theorem pure_eu_eq_blockedTrace
    (π : (pureKernelGame MontyHall.game).Profile)
    (who : MontyHall.Player) :
    (pureBlockedTraceKernelGameAt MontyHall.game).eu π who =
      (pureKernelGame MontyHall.game).eu π who :=
  StrategicSemantics.pure_eu_eq_blockedTrace MontyHall.game π who

theorem pure_nash_iff_blockedTrace
    (π : (pureKernelGame MontyHall.game).Profile) :
    (pureKernelGame MontyHall.game).IsNash π ↔
      (pureBlockedTraceKernelGameAt MontyHall.game).IsNash π :=
  StrategicSemantics.pure_nash_iff_blockedTrace MontyHall.game π

theorem behavioral_nash_iff_blockedTrace
    (β : (pmfBehavioralKernelGame MontyHall.game).Profile) :
    (pmfBehavioralKernelGame MontyHall.game).IsNash β ↔
      (pmfBehavioralBlockedTraceKernelGameAt MontyHall.game).IsNash β :=
  StrategicSemantics.behavioral_nash_iff_blockedTrace MontyHall.game β

theorem kuhnPMF : KuhnPMF MontyHall.game :=
  StrategicSemantics.kuhnPMF MontyHall.game

end MontyHall

end StrategicSemantics
end Examples
end Vegas
