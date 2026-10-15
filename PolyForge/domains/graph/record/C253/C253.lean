import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C253 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 2) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 2) (hn2 : (G.cliqueNum : ℤ) ≥ (G.indepNum : ℤ)) :
    (Fintype.card V : ℤ) ≥ -(G.cliqueNum : ℤ) + 6 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) + (G.minDegree : ℤ) + 3 * (G.cliqueNum : ℤ) ≥ 20 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (G.maxDegree : ℤ) = 2 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s5 : (G.minDegree : ℤ) = 2 := by
        have hw := regular_min_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s6 : -2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s7 : 3 * (G.edgeFinset.card : ℤ) + (G.minDegree : ℤ) + 3 * (G.cliqueNum : ℤ) ≥ 20 := by linarith [s2, s3, s4, s5, s6]
      linarith [s7]
    · -- 1*omega <= 2
      have s8 : -(G.vertexCoverNum.toNat : ℤ) ≥ -2 := by linarith [hn1]
      have s9 : (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn2]
      have s10 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s11 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := turan_r2_int G (by linarith [s10])
        try push_cast at hw
        linarith [hw]
      have s12 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s13 : (G.maxDegree : ℤ) = 2 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s14 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s12, s13]
      have s15 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s16 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s8, s9, s10, s15]
      have s17 : 7 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 12 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (4 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s14]) (by linarith [s16])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s18 : (G.minDegree : ℤ) = 2 := by
        have hw := regular_min_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s19 : -2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s20 : 3 * (G.edgeFinset.card : ℤ) + (G.minDegree : ℤ) + 3 * (G.cliqueNum : ℤ) ≥ 20 := by linarith [s8, s9, s11, s17, s15, s18, s19]
      linarith [s20]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s1, heq_gallai, heq_rege, heq_regx, heq_regn]
