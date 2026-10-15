import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C173 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.minDegree : ℤ) ≥ (G.maxDegree : ℤ)) (hn2 : (G.vertexCoverNum.toNat : ℤ) ≤ 2) :
    2 * (G.edgeFinset.card : ℤ) ≥ 2 * (G.cliqueNum : ℤ) + 3 * (G.vertexCoverNum.toNat : ℤ) - 6 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.cliqueNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
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
      have s5 : -(G.maxDegree : ℤ) + (G.minDegree : ℤ) ≥ 0 := by linarith [hn1]
      have s6 : -(G.vertexCoverNum.toNat : ℤ) ≥ -2 := by linarith [hn2]
      have s7 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s8 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s9 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s10 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s8, s9]
      have s11 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s10]) (by linarith [s7])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s12 : 6 * (G.edgeFinset.card : ℤ) - 6 * (G.cliqueNum : ℤ) - 9 * (G.vertexCoverNum.toNat : ℤ) ≥ -20 := by linarith [s2, s3, s4, s5, s6, s11]
      have s13 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.cliqueNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -6 := by have hr := s12; omega
      linarith [s13]
    · -- 1*chi <= 2
      have s14 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s15 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s16 : -(G.vertexCoverNum.toNat : ℤ) ≥ -2 := by linarith [hn2]
      have s17 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s18 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.cliqueNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -6 := by linarith [s14, s15, s16, s17]
      linarith [s18]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
