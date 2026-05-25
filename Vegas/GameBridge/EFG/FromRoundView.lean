import GameTheory.Languages.Expressiveness.EFG_FOSG
import Vegas.GameBridge.FOSG.RoundViewEquiv

/-!
# Round-view EFG presentation

Finite bounded round views can be serialized through the shared
`GameTheory.FOSG` bridge into extensive-form games.  The adapter is deliberately
generic over `Machine.RoundView`; compiled event graphs need an additional
finite-state presentation before they can use this export.
-/

namespace Vegas

open GameTheory

namespace EFGBridge

/-- A generated EFG subtree presents a simultaneous FOSG step as a spine of
serialized player decisions followed by the original stochastic transition. -/
inductive DecisionSpineThenChance {S : _root_.EFG.InfoStructure}
    {Outcome : Type} :
    Nat → _root_.EFG.GameTree S Outcome → Prop where
  | chance {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
      {next : Fin k → _root_.EFG.GameTree S Outcome} :
      DecisionSpineThenChance 0 (_root_.EFG.GameTree.chance k μ hk next)
  | decision {n : Nat} {p : S.Player} {I : S.Infoset p}
      {next : S.Act I → _root_.EFG.GameTree S Outcome}
      (tail : ∀ action, DecisionSpineThenChance n (next action)) :
      DecisionSpineThenChance (n + 1) (_root_.EFG.GameTree.decision I next)

namespace DecisionSpineThenChance

open FOSG.AugmentedEFGBridge

/-- The serialized-player inner loop of the FOSG-to-EFG bridge has exactly
one decision node for each remaining player, then reaches the continuation. -/
theorem choosePlayersFrom
    {ι W : Type} [DecidableEq ι] [Fintype ι]
    {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}
    (G : FOSG ι W Act PrivObs PubObs)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (k : Nat) (h : G.History) (pVal : Nat) (chosen : JointAction Act)
    (cont : JointAction Act → _root_.EFG.GameTree (infoStructure (G := G) k)
      (SerialExec.State G))
    (hcont : ∀ chosen,
      DecisionSpineThenChance 0 (cont chosen)) :
    DecisionSpineThenChance (Fintype.card ι - pVal)
      (Tree.choosePlayersFrom (G := G) k h pVal chosen cont) := by
  classical
  unfold Tree.choosePlayersFrom
  by_cases hp : pVal < Fintype.card ι
  · rw [dif_pos hp]
    have hsub : Fintype.card ι - pVal =
        (Fintype.card ι - (pVal + 1)) + 1 := by
      omega
    rw [hsub]
    apply DecisionSpineThenChance.decision
    intro action
    exact choosePlayersFrom (G := G) k h (pVal + 1)
      (Tree.recordOption (Act := Act) chosen
        (origPlayer (ι := ι) ⟨pVal, hp⟩)
        (actionOfIndex (G := G)
          (encodePlayerView (G := G) h
            (origPlayer (ι := ι) ⟨pVal, hp⟩)) action))
      cont hcont
  · rw [dif_neg hp]
    have hzero : Fintype.card ι - pVal = 0 := by
      omega
    rw [hzero]
    exact hcont chosen
termination_by Fintype.card ι - pVal
decreasing_by omega

/-- Every nonterminal original FOSG step becomes a full decision spine, one
decision opportunity per player, followed by a chance node for the transition. -/
theorem fromHistory_succ_nonterminal
    {ι W : Type} [DecidableEq ι] [Fintype ι]
    {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}
    (G : FOSG ι W Act PrivObs PubObs)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [Fintype W] [DecidablePred G.terminal]
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (k n : Nat) (h : G.History) (hnot : ¬ G.terminal h.lastState) :
    DecisionSpineThenChance (Fintype.card ι)
      (Tree.fromHistory (G := G) k (n + 1) h) := by
  classical
  rw [tree_fromHistory_succ_nonterminal (G := G) k n h hnot]
  simpa using
    choosePlayersFrom (G := G) k h 0 (noopAction Act)
      (fun chosen =>
        let a := Tree.legalize (G := G) h hnot chosen
        let μ := G.transition h.lastState a
        _root_.EFG.GameTree.chance (Fintype.card W)
          (PMF.map (Fintype.equivFin W) μ)
          (fintype_card_pos_of_pmf μ)
          (fun b =>
            let dst := (Fintype.equivFin W).symm b
            let h' := h.extendByOutcome a dst
            Tree.fromHistory (G := G) k n h'))
      (fun _ => DecisionSpineThenChance.chance)

end DecisionSpineThenChance

mutual

/-- Whole-tree structural certificate for the generated FOSG-to-EFG bridge.
A certified tree is either terminal or begins with a full serialized player
decision spine followed by the original chance transition, whose successors
are recursively certified. -/
inductive FullTreeShape {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (players : Nat) : _root_.EFG.GameTree S Outcome → Prop where
  | terminal {outcome : Outcome} :
      FullTreeShape players (_root_.EFG.GameTree.terminal outcome)
  | round {tree : _root_.EFG.GameTree S Outcome}
      (spine : RoundSpineShape players players tree) :
      FullTreeShape players tree

/-- Inner serialized-player spine used by `FullTreeShape`. At depth zero the
spine must be the chance transition of the original FOSG step, and every
successor subtree must satisfy `FullTreeShape`. -/
inductive RoundSpineShape {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (players : Nat) : Nat → _root_.EFG.GameTree S Outcome → Prop where
  | chance {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
      {next : Fin k → _root_.EFG.GameTree S Outcome}
      (tail : ∀ outcome, FullTreeShape players (next outcome)) :
      RoundSpineShape players 0 (_root_.EFG.GameTree.chance k μ hk next)
  | decision {n : Nat} {p : S.Player} {I : S.Infoset p}
      {next : S.Act I → _root_.EFG.GameTree S Outcome}
      (tail : ∀ action, RoundSpineShape players n (next action)) :
      RoundSpineShape players (n + 1) (_root_.EFG.GameTree.decision I next)

end

namespace RoundSpineShape

open FOSG.AugmentedEFGBridge

/-- The serialized-player inner loop preserves the recursive whole-tree shape:
one decision node for each remaining player, then a shape-certified
continuation. -/
theorem choosePlayersFrom
    {ι W : Type} [DecidableEq ι] [Fintype ι]
    {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}
    (G : FOSG ι W Act PrivObs PubObs)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (k : Nat) (h : G.History) (pVal : Nat) (chosen : JointAction Act)
    (cont : JointAction Act → _root_.EFG.GameTree (infoStructure (G := G) k)
      (SerialExec.State G))
    (hcont : ∀ chosen,
      RoundSpineShape (Fintype.card ι) 0 (cont chosen)) :
    RoundSpineShape (Fintype.card ι) (Fintype.card ι - pVal)
      (Tree.choosePlayersFrom (G := G) k h pVal chosen cont) := by
  classical
  unfold Tree.choosePlayersFrom
  by_cases hp : pVal < Fintype.card ι
  · rw [dif_pos hp]
    have hsub : Fintype.card ι - pVal =
        (Fintype.card ι - (pVal + 1)) + 1 := by
      omega
    rw [hsub]
    apply RoundSpineShape.decision
    intro action
    exact choosePlayersFrom (G := G) k h (pVal + 1)
      (Tree.recordOption (Act := Act) chosen
        (origPlayer (ι := ι) ⟨pVal, hp⟩)
        (actionOfIndex (G := G)
          (encodePlayerView (G := G) h
            (origPlayer (ι := ι) ⟨pVal, hp⟩)) action))
      cont hcont
  · rw [dif_neg hp]
    have hzero : Fintype.card ι - pVal = 0 := by
      omega
    rw [hzero]
    exact hcont chosen
termination_by Fintype.card ι - pVal
decreasing_by omega

end RoundSpineShape

namespace FullTreeShape

open FOSG.AugmentedEFGBridge

/-- Every FOSG-to-EFG bridge subtree produced by `Tree.fromHistory` has the
whole-tree serialized-round shape. -/
theorem fromHistory
    {ι W : Type} [DecidableEq ι] [Fintype ι]
    {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}
    (G : FOSG ι W Act PrivObs PubObs)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [Fintype W] [DecidablePred G.terminal]
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (k remaining : Nat) (h : G.History) :
    FullTreeShape (Fintype.card ι)
      (Tree.fromHistory (G := G) k remaining h) := by
  classical
  induction remaining generalizing h with
  | zero =>
      rw [tree_fromHistory_zero]
      exact FullTreeShape.terminal
  | succ remaining ih =>
      by_cases hterm : G.terminal h.lastState
      · rw [tree_fromHistory_succ_terminal (G := G) k remaining h hterm]
        exact FullTreeShape.terminal
      · rw [tree_fromHistory_succ_nonterminal (G := G) k remaining h hterm]
        apply FullTreeShape.round
        simpa using
          RoundSpineShape.choosePlayersFrom (G := G) k h 0 (noopAction Act)
            (fun chosen =>
              let a := Tree.legalize (G := G) h hterm chosen
              let μ := G.transition h.lastState a
              _root_.EFG.GameTree.chance (Fintype.card W)
                (PMF.map (Fintype.equivFin W) μ)
                (fintype_card_pos_of_pmf μ)
                (fun b =>
                  let dst := (Fintype.equivFin W).symm b
                  let h' := h.extendByOutcome a dst
                  Tree.fromHistory (G := G) k remaining h'))
            (by
              intro chosen
              apply RoundSpineShape.chance
              intro b
              exact ih _)

end FullTreeShape

end EFGBridge

namespace Machine
namespace RoundView

variable {Player : Type} [DecidableEq Player] [Fintype Player]
variable {M : Machine Player}

/-- Bounded FOSG presentation package for a finite-state round view. -/
noncomputable def boundedFOSGPresentation
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public] :
    Languages.Expressiveness.BoundedFOSGPresentation Player := by
  classical
  exact
    { W := M.BoundedState horizon
      Act := view.Act
      PrivObs := M.Obs
      PubObs := M.Public
      game := view.toFOSG horizon cutoff
      horizon := horizon
      bounded := view.toFOSG_boundedHorizon horizon cutoff }

/-- Serialized plain EFG presentation of a finite-state bounded round view. -/
noncomputable def toPlainEFG
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public] :
    EFG.EFGGame :=
  (view.boundedFOSGPresentation horizon cutoff).toPlainEFG

/-- Reindexed kernel game induced by serializing a finite-state bounded round
view as an EFG. -/
noncomputable def toPlainEFGKernelGame
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public] :
    KernelGame Player :=
  (view.boundedFOSGPresentation horizon cutoff).toPlainEFGKernelGame

/-- Serialized plain EFG presentation with utility read from the final native
machine state instead of cumulative FOSG transition rewards. -/
noncomputable def toPlainEFGMachinePayoff
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public] :
    EFG.EFGGame := by
  classical
  let base := view.toPlainEFG horizon cutoff
  exact
    { base with
      utility := fun h playerIx =>
        optionOutcomeUtility M cutoff (M.outcome h.lastState.state)
          (FOSG.AugmentedEFGBridge.origPlayer (ι := Player) playerIx) }

/-- Reindexed EFG kernel game with final native machine payoff utility. -/
noncomputable def toPlainEFGMachinePayoffKernelGame
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public] :
    KernelGame Player where
  Strategy := (view.toPlainEFGKernelGame horizon cutoff).Strategy
  Outcome := (view.toPlainEFGKernelGame horizon cutoff).Outcome
  utility := fun h player =>
    optionOutcomeUtility M cutoff (M.outcome h.lastState.state) player
  outcomeKernel :=
    (view.toPlainEFGKernelGame horizon cutoff).outcomeKernel

/-- Native bounded FOSG kernel induced by the finite-state round view. -/
noncomputable def toFOSGKernelGame
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public] :
    KernelGame Player :=
  (view.boundedFOSGPresentation horizon cutoff).toKernelGame

/-- The serialized EFG has the same outcome law as the bounded FOSG
presentation under the bridge's behavioral-profile translation. -/
theorem toPlainEFGKernelGame_outcomeKernel_eq_fosg
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public]
    (profile : (view.toFOSGKernelGame horizon cutoff).Profile) :
    (view.toPlainEFGKernelGame horizon cutoff).outcomeKernel
        ((view.boundedFOSGPresentation horizon cutoff).translateProfile profile) =
      (view.toFOSGKernelGame horizon cutoff).outcomeKernel profile :=
  (view.boundedFOSGPresentation horizon cutoff).toPlainEFGKernelGame_outcomeKernel_eq_native
    profile

/-- The final-payoff EFG kernel has the same outcome law as the final-payoff
FOSG history kernel under the bridge's behavioral-profile translation. -/
theorem toPlainEFGMachinePayoffKernelGame_outcomeKernel_eq_fosg
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public]
    (profile :
      (Machine.RoundView.ToFOSG.machinePayoffHistoryKernelGame
        view horizon cutoff).Profile) :
    (view.toPlainEFGMachinePayoffKernelGame horizon cutoff).outcomeKernel
        ((view.boundedFOSGPresentation horizon cutoff).translateProfile profile) =
      (Machine.RoundView.ToFOSG.machinePayoffHistoryKernelGame
        view horizon cutoff).outcomeKernel profile := by
  classical
  have hEFG :
      (view.toPlainEFGMachinePayoffKernelGame horizon cutoff).outcomeKernel
        ((view.boundedFOSGPresentation horizon cutoff).translateProfile profile) =
        (view.toFOSGKernelGame horizon cutoff).outcomeKernel profile := by
    simpa [toPlainEFGMachinePayoffKernelGame] using
      view.toPlainEFGKernelGame_outcomeKernel_eq_fosg
        horizon cutoff profile
  have hFOSG :
      (view.toFOSGKernelGame horizon cutoff).outcomeKernel profile =
      (Machine.RoundView.ToFOSG.machinePayoffHistoryKernelGame
        view horizon cutoff).outcomeKernel profile := by
    letI : Fintype (view.toFOSG horizon cutoff).History :=
      (view.boundedFOSGPresentation horizon cutoff).historyFintype
    change
      ((view.toFOSG horizon cutoff).toKernelGameOfBoundedHorizon
          (view.toFOSG_boundedHorizon horizon cutoff)).outcomeKernel profile =
        (view.toFOSG horizon cutoff).runDist horizon profile
    exact FOSG.toKernelGameOfBoundedHorizon_outcomeKernel
      (G := view.toFOSG horizon cutoff)
      (hBound := view.toFOSG_boundedHorizon horizon cutoff) profile
  exact hEFG.trans hFOSG

end RoundView
end Machine

end Vegas
