import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C43 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (Fintype.card V : ℤ) ≤ 6) :
    (Fintype.card V : ℤ) ≥ (G.edgeFinset.card : ℤ) - 2 * (G.indepNum : ℤ) + 3 := by
  have s1 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 2 * (G.indepNum : ℤ) ≥ 3 := by
    by_cases hc1 : (1 : ℤ) ≤ (G.maxDegree : ℤ)
    · -- 1*max_deg >= 1
      have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := bipartite_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s4 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := bipartite_four_mul_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s7 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s8 : -(Fintype.card V : ℤ) ≥ -6 := by linarith [hn1]
      have s9 : 7 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (6 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s7]) (by linarith [s8])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s10 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s11 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s10]) (by linarith [s3])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s12 : (G.maxDegree : ℤ) ≥ 1 := by have hcc := hc1; omega
      have s13 : (Fintype.card V : ℤ) + 6 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ (6 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s8]) (by linarith [s12])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s14 : 7 * (Fintype.card V : ℤ) - 7 * (G.edgeFinset.card : ℤ) + 14 * (G.indepNum : ℤ) ≥ 15 := by linarith [s2, s3, s4, s5, s6, s9, s11, s13]
      have s15 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 2 * (G.indepNum : ℤ) ≥ 3 := by have hr := s14; omega
      linarith [s15]
    · -- 1*max_deg <= 0
      have s16 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s17 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s18 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s19 : -(G.maxDegree : ℤ) ≥ 0 := by have hcc := hc1; omega
      have s20 : (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (0 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s16]) (by linarith [s19])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s21 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s22 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s16, s17, s18, s19, s20, s21]
      linarith [s22]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
