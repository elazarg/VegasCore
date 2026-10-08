/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Intended
import GameTheory.Protocol.OwnPlayRecall
import GameTheory.Protocol.DecisionRecall
import GameTheory.Protocol.FiniteInformation
import GameTheory.Analysis.Protocol.AssessmentCompactness
import GameTheory.Analysis.Protocol.BehavioralBayes

/-! # Late openings with complete public observation

This comparison model reuses the existing opening game and its terminal
payoffs. The public signal retains the logical turn and resolution, and every
emitted opening reveals its bit even after failed inclusion. The label remains
private. Own action recall is retained using the foundation's existing adapter.

This is an information refinement of a finite comparison game, not an adapter
from a Vegas source program or from its unrestricted raw packet interface.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter

/-- The public transcript records the logical turn and every resolved
transmission. Never sending leaves the committed bit unobserved. -/
def lateOpeningPublicTranscript : LateLeakState →
    ℕ × Option (LateLeakResolution × Option Bool)
  | .answering secret resolution | .finished secret resolution _ =>
      (lateLeakDepth (.answering secret resolution),
        some (resolution, if resolution = .withheld then none else some secret.1))
  | state => (lateLeakDepth state, none)

/-- Public traffic augments the existing owner-private view. -/
def lateOpeningPublicSignals (G : LateLeakParameters) :
    InfoSignals (lateLeakExecution G true) where
  PublicSignal := ℕ × Option (LateLeakResolution × Option Bool)
  PrivateSignal _ := LateLeakView
  initialPublic := lateOpeningPublicTranscript .initial
  initialPrivate who := lateLeakView who .initial
  publicSignal event := lateOpeningPublicTranscript event.target
  privateSignal who event := lateLeakView who event.target
  InfoState _ := LateLeakView × (ℕ × Option (LateLeakResolution × Option Bool))
  initInfo _ privateView publicView := (privateView, publicView)
  pushInfo _ _ _ privateView publicView := (privateView, publicView)

theorem lateOpeningPublicSignals_infoOf (G : LateLeakParameters) (who : LateLeakRole) :
    ∀ {state} (trace : (lateLeakExecution G true).Trace state),
      (lateOpeningPublicSignals G).infoOf who trace =
        (lateLeakView who state, lateOpeningPublicTranscript state)
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

/-- Complete public traffic with ordinary own-action recall. The legal action
menus and execution transitions are the existing late-opening game's menus. -/
def lateOpeningPublicModel (G : LateLeakParameters) :
    InformationModel (lateLeakExecution G true) where
  toInfoSignals := (lateOpeningPublicSignals G).withOwnPlayRecall
  menu _ info := lateLeakMenu true info.1.1
  menu_adequate who state trace choice := by
    rw [InfoSignals.withOwnPlayRecall_infoOf, lateOpeningPublicSignals_infoOf]
    simpa only [lateLeak_infoOf] using
      (lateLeakModel G true).menu_adequate who trace choice

theorem lateOpeningPublicModel_infoOf (G : LateLeakParameters) (who : LateLeakRole)
    {state} (trace : (lateLeakExecution G true).Trace state) :
    (lateOpeningPublicModel G).infoOf who trace =
      ((lateLeakView who state, lateOpeningPublicTranscript state),
        (lateOpeningPublicSignals G).ownPlay who trace) := by
  change (lateOpeningPublicSignals G).withOwnPlayRecall.infoOf who trace = _
  rw [InfoSignals.withOwnPlayRecall_infoOf, lateOpeningPublicSignals_infoOf]

/-- The old information is a projection of the complete public information. -/
theorem lateOpeningPublic_old_info_projection (G : LateLeakParameters) (who : LateLeakRole)
    {state} (trace : (lateLeakExecution G true).Trace state) :
    ((lateOpeningPublicModel G).infoOf who trace).1.1 =
      (lateLeakModel G true).infoOf who trace := by
  rw [lateOpeningPublicModel_infoOf, lateLeak_infoOf]

/-- The listener has made no prior move before its unique final answer. -/
theorem lateOpeningPublic_listener_ownPlay_empty (G : LateLeakParameters) :
    ∀ {state} (trace : (lateLeakExecution G true).Trace state),
      ¬ state.IsFinished → (lateOpeningPublicSignals G).ownPlay .listener trace = []
  | _, .start, _ => rfl
  | _, .extend (source := source) (target := target) prior joint legal realized, running => by
      have inactive : source.actor ≠ some .listener := by
        change target ∈ (lateLeakAdvance G source (joint source.mover)).support at realized
        cases source with
        | answering secret resolution =>
            simp only [lateLeakAdvance, PMF.mem_support_pure_iff] at realized
            subst realized
            exact (running trivial).elim
        | _ => simp [LateLeakState.actor]
      have silent := LegalOption.eq_none_of_inactive (E := lateLeakExecution G true)
        (joint .listener) ((lateLeakExecution G true).legalOption_of_legal legal .listener) inactive
      rw [InfoSignals.ownPlay_extend, silent]
      exact lateOpeningPublic_listener_ownPlay_empty G prior legal.1

/-- The final listener information is exactly its public transcript and empty
own recall; it contains no hidden label or private sender alias. -/
theorem lateOpeningPublic_listener_info_answering (G : LateLeakParameters)
    (secret : LateLeakType) (resolution : LateLeakResolution)
    (trace : (lateLeakExecution G true).Trace (.answering secret resolution)) :
    (lateOpeningPublicModel G).infoOf .listener trace =
      ((.asked (lateLeakSignal secret resolution),
        lateOpeningPublicTranscript (.answering secret resolution)), []) := by
  rw [lateOpeningPublicModel_infoOf,
    lateOpeningPublic_listener_ownPlay_empty G trace (by simp [LateLeakState.IsFinished])]
  rfl

theorem lateOpeningPublicModel_decisionRecall (G : LateLeakParameters) :
    (lateOpeningPublicModel G).DecisionRecall :=
  (lateOpeningPublicModel G).decisionRecall_of_perfectRecall
    ((lateOpeningPublicSignals G).withOwnPlayRecall_perfectRecall)

instance (G : LateLeakParameters) (who : LateLeakRole) :
    DecidableEq ((lateOpeningPublicModel G).InfoState who) :=
  Classical.decEq _

instance (G : LateLeakParameters) (who : LateLeakRole)
    (info : (lateOpeningPublicModel G).InfoState who) :
    Finite ((lateOpeningPublicModel G).Choice who info) :=
  inferInstanceAs (Finite ((lateLeakModel G true).Choice who info.1.1))

instance (G : LateLeakParameters) (who : LateLeakRole)
    (info : (lateOpeningPublicModel G).InfoState who) :
    Nonempty ((lateOpeningPublicModel G).Choice who info) :=
  inferInstanceAs (Nonempty ((lateLeakModel G true).Choice who info.1.1))

/-- Uniform reference play has full support at every information value. -/
def lateOpeningPublicUniform (G : LateLeakParameters) :
    (who : LateLeakRole) → (lateOpeningPublicModel G).BehavioralPolicy who :=
  fun who info => lateLeakUniformProfile G true who info.1.1

theorem lateOpeningPublicUniform_full (G : LateLeakParameters) (who : LateLeakRole)
    (info : (lateOpeningPublicModel G).InfoState who)
    (choice : (lateOpeningPublicModel G).Choice who info) :
    choice ∈ (lateOpeningPublicUniform G who info).support := by
  change (choice : (lateLeakModel G true).Choice who info.1.1) ∈
    (lateLeakUniformProfile G true who info.1.1).support
  let _ := Fintype.ofFinite ((lateLeakModel G true).Choice who info.1.1)
  exact @PMF.mem_support_uniformOfFintype ((lateLeakModel G true).Choice who info.1.1)
    (Fintype.ofFinite _) inferInstance choice

/-- The sender's canonical policy depends only on its original full view. -/
def lateOpeningPublicSenderPolicy (G : LateLeakParameters) :
    (lateLeakModel G true).BehavioralPolicy .sender
  | .full (.protectedTurn _) => PMF.pure ⟨some (.opening true), ⟨true, rfl, rfl⟩⟩
  | .full (.secondLate _) => PMF.pure ⟨some (.opening true), ⟨true, rfl⟩⟩
  | info => lateLeakUniformProfile G true .sender info

/-- Protected and final late openings are sent; the first late timing choice
is uniform. Successful replies are safe. Failed emitted openings are answered
truthfully, and never sending is answered by guessing zero. -/
def lateOpeningPublicCanonical (G : LateLeakParameters) :
    (who : LateLeakRole) → (lateOpeningPublicModel G).BehavioralPolicy who
  | .sender => fun info => lateOpeningPublicSenderPolicy G info.1.1
  | .listener => fun info =>
      match equal : info.1.1 with
      | .asked signal =>
          if success : signal.success then
            PMF.pure ⟨some (.reply .safe), by
              change some (.reply .safe) ∈ lateLeakMenu true info.1.1
              rw [equal]
              exact ⟨.safe, rfl, lateLeak_safe_fits success⟩⟩
          else
            let bit := ((info.1.2.2.bind Prod.snd).getD false)
            PMF.pure ⟨some (.reply (.failure bit)), by
              change some (.reply (.failure bit)) ∈ lateLeakMenu true info.1.1
              rw [equal]
              exact ⟨.failure bit, rfl, by
                simpa [LateLeakAnswer.fits] using success⟩⟩
      | _ => lateOpeningPublicUniform G .listener info

/-- Positive perturbations vanish along the ordinary sequence of naturals. -/
def lateOpeningPublicTrembleWeight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem lateOpeningPublicTrembleWeight_pos (n : ℕ) :
    0 < lateOpeningPublicTrembleWeight n :=
    one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))

theorem lateOpeningPublicTrembleWeight_le_one (n : ℕ) :
    lateOpeningPublicTrembleWeight n ≤ 1 := by
    apply (div_le_one (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))).mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

theorem lateOpeningPublicTrembleWeight_tendsto :
    Tendsto lateOpeningPublicTrembleWeight atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    convert h using 1
    funext n
    simp [lateOpeningPublicTrembleWeight, Nat.cast_add]
    ring

/-- The same perturbation weight is used at every type and information value. -/
def lateOpeningPublicTrembleProfile (G : LateLeakParameters) (n : ℕ) :
    (who : LateLeakRole) → (lateOpeningPublicModel G).BehavioralPolicy who :=
    fun who info => mix (lateOpeningPublicTrembleWeight n)
      (lateOpeningPublicTrembleWeight_pos n).le (lateOpeningPublicTrembleWeight_le_one n)
      (lateOpeningPublicUniform G who info) (lateOpeningPublicCanonical G who info)

/-- The reference old-information profile has exactly the new sender laws;
its listener is uniform, which is immaterial before that listener answers. -/
def lateOpeningPublicPrefixReference (G : LateLeakParameters) (n : ℕ) :
    LateLeakProfile G true
  | .sender => fun info => mix (lateOpeningPublicTrembleWeight n)
      (lateOpeningPublicTrembleWeight_pos n).le (lateOpeningPublicTrembleWeight_le_one n)
      (lateLeakUniformProfile G true .sender info) (lateOpeningPublicSenderPolicy G info)
  | .listener => lateLeakUniformProfile G true .listener

theorem lateOpeningPublic_sender_tremble_eq (G : LateLeakParameters) (n : ℕ)
    (info : (lateOpeningPublicModel G).InfoState .sender) :
    lateOpeningPublicTrembleProfile G n .sender info =
      lateOpeningPublicPrefixReference G n .sender info.1.1 := rfl

theorem lateOpeningPublicTrembleProfile_full (G : LateLeakParameters) (n : ℕ) :
    (InformationModel.BehavioralAssessment.ofStrategy
      (lateOpeningPublicTrembleProfile G n)).IsFullyMixed := by
    intro who site choice
    exact mem_support_mix_left (lateOpeningPublicTrembleWeight n)
      (lateOpeningPublicTrembleWeight_pos n).le (lateOpeningPublicTrembleWeight_le_one n)
      (lateOpeningPublicTrembleWeight_pos n) (lateOpeningPublicUniform_full G who site.1 choice)

/-- Native history-fiber Bayes assessments for the explicit public trembles. -/
def lateOpeningPublicTrembleAssessment (G : LateLeakParameters) (n : ℕ) :
    (lateOpeningPublicModel G).BehavioralAssessment :=
  (lateOpeningPublicModel G).bayesAssessment (lateOpeningPublicTrembleProfile G n)
    (lateOpeningPublicTrembleProfile_full G n)
    (lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain

/-- The explicit uniform trembles have a common assessment subsequence whose
strategy agrees with canonical play at every genuine decision site. -/
theorem lateOpeningPublicCanonical_consistent_witness (G : LateLeakParameters) :
    ∃ (A : (lateOpeningPublicModel G).BehavioralAssessment) (index : ℕ → ℕ),
      StrictMono index ∧
      (lateOpeningPublicModel G).BehavioralAssessmentConvergesPointwise
        (fun n => lateOpeningPublicTrembleAssessment G (index n)) A ∧
      ∀ who (site : (lateOpeningPublicModel G).InformationSite who),
        A.strategy who site.1 = lateOpeningPublicCanonical G who site.1 := by
  classical
  let M := lateOpeningPublicModel G
  let sequence := lateOpeningPublicTrembleAssessment G
  obtain ⟨A, index, increasing, converges⟩ :=
    M.exists_subseq_behavioralAssessmentConvergesPointwise_atSites_of_uniformlyTight sequence
      (fun _ _ => uniformlyTight_of_finite _) (fun _ _ => uniformlyTight_of_finite _)
  refine ⟨A, index, increasing, converges, ?_⟩
  intro who site
  apply (converges.strategy who site).unique
  change PMFConvergesPointwise
    (fun n => mix (lateOpeningPublicTrembleWeight (index n))
      (lateOpeningPublicTrembleWeight_pos (index n)).le
      (lateOpeningPublicTrembleWeight_le_one (index n))
      (lateOpeningPublicUniform G who site.1) (lateOpeningPublicCanonical G who site.1)) _
  exact pmfConvergesPointwise_mix_zero (fun n => lateOpeningPublicTrembleWeight (index n))
    (fun n => (lateOpeningPublicTrembleWeight_pos (index n)).le)
    (fun n => lateOpeningPublicTrembleWeight_le_one (index n))
    (lateOpeningPublicTrembleWeight_tendsto.comp increasing.tendsto_atTop) _ _

/-- Canonical public play admits a Kreps-Wilson consistent assessment.
Sequential rationality requires the payoff margins and listener posteriors. -/
theorem lateOpeningPublicCanonical_consistent (G : LateLeakParameters) :
    ∃ A : (lateOpeningPublicModel G).BehavioralAssessment,
      A.IsSequentiallyConsistent
        (lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain ∧
      ∀ who (site : (lateOpeningPublicModel G).InformationSite who),
        A.strategy who site.1 = lateOpeningPublicCanonical G who site.1 := by
  obtain ⟨A, index, _increasing, converges, agrees⟩ :=
    lateOpeningPublicCanonical_consistent_witness G
  let M := lateOpeningPublicModel G
  let anti := (lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain
  exact ⟨A, converges.isSequentiallyConsistent anti
    (fun n => lateOpeningPublicTrembleProfile_full G (index n))
    (fun n => M.bayesAssessment_isBayesConsistent (lateOpeningPublicTrembleProfile G (index n))
      (lateOpeningPublicTrembleProfile_full G (index n)) anti), agrees⟩

/-- The first and second late attempts have the same payoff when both failed
transmissions reveal the bit and both successful transmissions receive safe. -/
theorem lateOpeningPublic_attempt_payoff_eq (G : LateLeakParameters) (secret : LateLeakType) :
    lateLeakInclusionProb G * lateLeakSenderPayoff G secret .firstIncluded .safe +
        (1 - lateLeakInclusionProb G) *
          lateLeakSenderPayoff G secret .firstDropped (.failure secret.1) =
      lateLeakInclusionProb G * lateLeakSenderPayoff G secret .secondIncluded .safe +
        (1 - lateLeakInclusionProb G) *
          lateLeakSenderPayoff G secret .secondDropped (.failure secret.1) := by
  rfl

/-- A direct margin making the last late send better than never sending,
including the change from an uninformed to a truthful failed-opening reply. -/
theorem lateOpeningPublic_last_send_better (G : LateLeakParameters)
    (reward : 0 ≤ G.reward)
    (margin : 0 < lateLeakInclusionProb G * (G.forfeit + G.reward / 2) -
      G.reward - (1 - lateLeakInclusionProb G) * G.dropCharge)
    (secret : LateLeakType) :
    lateLeakSenderPayoff G secret .withheld (.failure false) <
      lateLeakInclusionProb G * lateLeakSenderPayoff G secret .secondIncluded .safe +
        (1 - lateLeakInclusionProb G) *
          lateLeakSenderPayoff G secret .secondDropped (.failure secret.1) := by
  have q0 := lateLeakInclusionProb_pos G
  have q1 := lateLeakInclusionProb_lt_one G
  rcases secret with ⟨bit, label⟩
  cases bit <;> cases label <;>
    simp [lateLeakSenderPayoff, lateLeakSenderBase, LateLeakResolution.succeeded,
      LateLeakResolution.droppedLate] <;>
    nlinarith [mul_nonneg (sub_nonneg.mpr q1.le) reward,
      mul_nonneg q0.le reward]

/-- Protected opening strictly dominates either late attempt under safe
success replies and truthful failed-opening replies. -/
theorem lateOpeningPublic_protected_better (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (cost : G.reward / 2 < G.forfeit + G.dropCharge)
    (secret : LateLeakType) :
    lateLeakInclusionProb G * lateLeakSenderPayoff G secret .secondIncluded .safe +
        (1 - lateLeakInclusionProb G) *
          lateLeakSenderPayoff G secret .secondDropped (.failure secret.1) <
      lateLeakSenderPayoff G secret .protectedOpen .safe := by
  have q1 := lateLeakInclusionProb_lt_one G
  have positive : 0 < (1 - lateLeakInclusionProb G) *
      (G.forfeit + G.dropCharge - G.reward / 2) := by
    apply mul_pos (sub_pos.mpr q1)
    exact sub_pos.mpr cost
  rcases secret with ⟨bit, label⟩
  cases bit <;> cases label <;>
    simp [lateLeakSenderPayoff, lateLeakSenderBase, LateLeakResolution.succeeded,
      LateLeakResolution.droppedLate] <;>
    nlinarith [mul_nonneg (sub_nonneg.mpr q1.le) reward]

/-- The parameter regime of the selective-observation impossibility result
also satisfies the direct send and protected margins for complete observation. -/
theorem lateOpeningPublic_margins_of_deferral_pays (G : LateLeakParameters)
    (pays : G.DeferralPays) (charge : 0 ≤ G.dropCharge) :
    G.reward / 2 < G.forfeit + G.dropCharge ∧
      0 < lateLeakInclusionProb G * (G.forfeit + G.reward / 2) -
        G.reward - (1 - lateLeakInclusionProb G) * G.dropCharge := by
  have q0 := lateLeakInclusionProb_pos G
  have q1 := lateLeakInclusionProb_lt_one G
  have d : G.reward < G.forfeit := by
    have nonneg := mul_nonneg (sub_nonneg.mpr q1.le) charge
    have strict : 0 < lateLeakInclusionProb G * (G.forfeit - G.reward) :=
      nonneg.trans_lt pays.send_beats_withhold
    by_contra failed
    have product := mul_nonpos_of_nonneg_of_nonpos q0.le
      (sub_nonpos.mpr (not_lt.mp failed))
    linarith
  refine ⟨by linarith [pays.reward_pos], ?_⟩
  have product := mul_pos (sub_pos.mpr q1) pays.reward_pos
  nlinarith [pays.guess_beats_safe]

end Vegas
