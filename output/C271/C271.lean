import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C271 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.indepNum : ℤ) ≤ 2) :
    (G.chromaticNumber.toNat : ℤ) ≥ -2 * (G.edgeFinset.card : ℤ) + 3 * (G.minDegree : ℤ) + 3 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (Fintype.card V : ℤ) ≥ 3 := by
        have hw := three_le_card_of_cycle_int G hp1
        try push_cast at hw
        linarith [hw]
      have s5 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s6 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s4]) (by linarith [s5])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s7 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s2, s3, s6]
      linarith [s7]
    · -- 1*chi <= 2
      have s8 : (Fintype.card V : ℤ) ≥ 3 := by
        have hw := three_le_card_of_cycle_int G hp1
        try push_cast at hw
        linarith [hw]
      have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s10 : -(G.indepNum : ℤ) ≥ -2 := by linarith [hn1]
      have s11 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s12 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s10]) (by linarith [s11])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s8, s9, s10, s12]
      have s14 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s13; omega
      have s15 : (G.edgeFinset.card : ℤ) ≥ 3 := by
        have hw := three_le_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s16 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s17 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s18 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s16, s17]
      have s19 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := turan_r2_int G (by linarith [s18])
        try push_cast at hw
        linarith [hw]
      have s20 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s9, s10, s17, s12]
      have s21 : 7 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 12 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (4 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s8]) (by linarith [s20])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s22 : 7 * (Fintype.card V : ℤ) ≥ 24 := by linarith [s15, s19, s21]
      have s23 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s22; omega
      have s24 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s25 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s26 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s27 : -(G.minDegree : ℤ) ≥ -3 := by linarith [s25, s26, s9, s10, s17, s12]
      have s28 : -3 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
        have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * (3 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s20]) (by linarith [s27])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s29 : 4 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 7 := by linarith [s14, s23, s15, s24, s28]
      have s30 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 4 := by have hr := s29; omega
      linarith [s30]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
