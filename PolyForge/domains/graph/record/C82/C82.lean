import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C82 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≤ 4) (hn2 : (G.cliqueNum : ℤ) ≥ 2 * (G.indepNum : ℤ)) :
    (G.chromaticNumber.toNat : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 1 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -1 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s5 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s7 : (G.cliqueNum : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn2]
      have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s9 : 3 * (G.edgeFinset.card : ℤ) ≥ 5 := by linarith [s2, s3, s6, s4, s5, s7, s8]
      have s10 : (G.edgeFinset.card : ℤ) ≥ 2 := by have hr := s9; omega
      have s11 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s12 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s13 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s6]
      have s14 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s13]) (by linarith [s12])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s15 : 18 * (G.edgeFinset.card : ℤ) - 12 * (G.minDegree : ℤ) - 6 * (G.chromaticNumber.toNat : ℤ) ≥ -1 := by linarith [s2, s3, s4, s5, s10, s11, s7, s14, s8]
      have s16 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by have hr := s15; omega
      linarith [s16]
    · -- 1*chi <= 2
      have s17 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s18 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s19 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s20 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s21 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s22 : (G.cliqueNum : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn2]
      have s23 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s24 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s25 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -1 := by linarith [s17, s18, s19, s20, s21, s22, s23, s24]
      linarith [s25]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
