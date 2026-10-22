import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C228 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≤ (G.cliqueNum : ℤ)) (hn2 : (Fintype.card V : ℤ) ≤ 2 * (G.indepNum : ℤ)) :
    (G.cliqueNum : ℤ) ≥ -3 * (G.maxDegree : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) + 1 := by
  have s1 : 3 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
      have s6 : -(Fintype.card V : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn2]
      have s7 : 2 * (G.maxDegree : ℤ) ≥ 1 := by linarith [s3, s4, s2, s5, s6]
      have s8 : (G.maxDegree : ℤ) ≥ 1 := by have hr := s7; omega
      have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s10 : 3 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s2, s8, s5, s6, s9]
      linarith [s10]
    · -- 1*chi <= 2
      have s11 : (G.cliqueNum : ℤ) ≥ 1 := by
        have hw := omega_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s12 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s13 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s14 : (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
      have s15 : -(Fintype.card V : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn2]
      have s16 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s17 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s18 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s19 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s17, s14, s15, s18]
      have s20 : 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s19]) (by linarith [s16])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s21 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s22 : 6 * (G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) - 4 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s11, s12, s13, s14, s15, s20, s21]
      have s23 : 3 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s22; omega
      linarith [s23]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
