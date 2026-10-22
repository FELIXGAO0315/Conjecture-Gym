import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C115 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 5) (hn2 : (G.minDegree : ℤ) ≥ (G.maxDegree : ℤ)) :
    2 * (G.cliqueNum : ℤ) ≤ -3 * (G.maxDegree : ℤ) + 12 := by
  have s1 : -3 * (G.maxDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -12 := by
    by_cases hc1 : (6 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 6
      have s2 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s3 : -(G.maxDegree : ℤ) + (G.minDegree : ℤ) ≥ 0 := by linarith [hn2]
      have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
      have s6 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s7 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc1; omega
      have s8 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s7]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : -3 * (G.minDegree : ℤ) ≥ -5 := by linarith [s4, s5, s8]
      have s10 : -(G.minDegree : ℤ) ≥ -1 := by have hr := s9; omega
      have s11 : -3 * (G.maxDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -7 := by linarith [s2, s3, s10]
      linarith [s11]
    · -- 1*n <= 5
      have s12 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s13 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s14 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
      have s15 : -(G.maxDegree : ℤ) + (G.minDegree : ℤ) ≥ 0 := by linarith [hn2]
      have s16 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc1; omega
      have s17 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s18 : -(G.minDegree : ℤ) ≥ -4 := by linarith [s17, s12, s16]
      have s19 : -4 * (Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -20 := by
        have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * (4 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s16]) (by linarith [s18])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s20 : -9 * (G.maxDegree : ℤ) ≥ -26 := by linarith [s12, s13, s14, s15, s19]
      have s21 : -(G.maxDegree : ℤ) ≥ -2 := by have hr := s20; omega
      have s22 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_card_int G
        try push_cast at hw
        linarith [hw]
      have s23 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s24 : -9 * (G.cliqueNum : ℤ) ≥ -35 := by linarith [s22, s23, s13, s14, s15, s19]
      have s25 : -(G.cliqueNum : ℤ) ≥ -3 := by have hr := s24; omega
      have s26 : -3 * (G.maxDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -12 := by linarith [s21, s25]
      linarith [s26]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
