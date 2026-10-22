import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C245 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≤ (G.cliqueNum : ℤ)) (hn2 : (G.indepNum : ℤ) ≤ 3) :
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
      have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s7 : (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
      have s8 : -(G.indepNum : ℤ) ≥ -3 := by linarith [hn2]
      have s9 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s10 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s11 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s10]
      have s12 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s11]) (by linarith [s9])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s14 : 9 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [s2, s3, s4, s5, s6, s7, s8, s12, s13]
      have s15 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hr := s14; omega
      linarith [s15]
    · -- 1*chi <= 2
      have s16 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s17 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s18 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s19 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s20 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s21 : (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
      have s22 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s23 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s24 : 6 * (G.edgeFinset.card : ℤ) - 4 * (G.minDegree : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ -3 := by linarith [s16, s17, s18, s19, s20, s21, s22, s23]
      have s25 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hr := s24; omega
      linarith [s25]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
