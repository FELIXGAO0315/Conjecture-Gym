import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C81 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 2 * (G.cliqueNum : ℤ)) (hn2 : (G.cliqueNum : ℤ) ≤ 6) :
    (G.cliqueNum : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 3 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -3 := by
    by_cases hc1 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 4
      have s2 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.cliqueNum : ℤ) ≥ -6 := by linarith [hn2]
      have s6 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s7 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc1; omega
      have s8 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s7]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : 4 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -7 := by linarith [s2, s3, s4, s5, s8]
      have s10 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -3 := by have hr := s9; omega
      linarith [s10]
    · -- 1*n <= 3
      have s11 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s12 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s13 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s14 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s15 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s16 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s17 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc1; omega
      have s18 : -(G.minDegree : ℤ) ≥ -2 := by linarith [s13, s14, s17]
      have s19 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
        have hmul : (0 : ℤ) ≤ (3 - (Fintype.card V : ℤ)) * (2 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s17]) (by linarith [s18])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s20 : 6 * (G.edgeFinset.card : ℤ) - 9 * (G.minDegree : ℤ) - 3 * (G.cliqueNum : ℤ) ≥ -11 := by linarith [s11, s12, s13, s14, s15, s16, s19]
      have s21 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -3 := by have hr := s20; omega
      linarith [s21]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
