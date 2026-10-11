import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C63 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≥ (G.edgeFinset.card : ℤ)) :
    2 * (G.indepNum : ℤ) ≥ (G.edgeFinset.card : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) + 2 := by
  have s1 : -(G.edgeFinset.card : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by
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
      have s5 : -(G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s7 : -(G.edgeFinset.card : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s2, s3, s4, s5, s6]
      linarith [s7]
    · -- 1*chi <= 2
      have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s9 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s10 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
      have s11 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s12 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s13 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s14 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s15 : -(G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s16 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s17 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s13, s14, s15, s16]
      have s18 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s12]) (by linarith [s17])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s20 : -(G.edgeFinset.card : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [s8, s9, s10, s11, s18, s19]
      linarith [s20]
  linarith [s1]
