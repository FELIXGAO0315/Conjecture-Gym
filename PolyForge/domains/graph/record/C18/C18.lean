import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C18 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.minDegree : ℤ) ≤ 4) (hn2 : (G.cliqueNum : ℤ) ≥ 2 * (G.edgeFinset.card : ℤ)) :
    2 * (G.indepNum : ℤ) ≥ (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) + 2 := by
  have s1 : -(G.edgeFinset.card : ℤ) + 2 * (G.maxDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s7 : -2 * (G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn2]
      have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s9 : -2 * (G.edgeFinset.card : ℤ) + 4 * (G.maxDegree : ℤ) + 4 * (G.indepNum : ℤ) ≥ 3 := by linarith [s2, s3, s4, s5, s6, s7, s8]
      have s10 : -(G.edgeFinset.card : ℤ) + 2 * (G.maxDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 2 := by have hr := s9; omega
      linarith [s10]
    · -- 1*chi <= 2
      have s11 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s12 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s13 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s14 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s15 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s16 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s17 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s18 : -2 * (G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn2]
      have s19 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s20 : -(G.maxDegree : ℤ) ≥ -1 := by linarith [s16, s17, s18, s19]
      have s21 : (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (1 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s15]) (by linarith [s20])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s22 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s23 : -(G.edgeFinset.card : ℤ) + 2 * (G.maxDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 2 := by linarith [s11, s12, s13, s14, s21, s22]
      linarith [s23]
  linarith [s1]
