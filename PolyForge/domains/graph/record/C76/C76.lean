import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C76 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsEdgeConnected 1) (hp2 : 2 ≤ Fintype.card V) (hn1 : (Fintype.card V : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ)) :
    (G.edgeFinset.card : ℤ) ≥ 2 * (G.minDegree : ℤ) - 1 := by
  have s1 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ -1 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s5 : (G.minDegree : ℤ) ≥ 1 := by
        have hw := edge_conn_min_deg_int G hp1 hp2
        try push_cast at hw
        linarith [hw]
      have s6 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s7 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s8 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s6, s7]
      have s9 : -(Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -3 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s8]) (by linarith [s5])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s10 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ -1 := by linarith [s2, s3, s4, s9]
      linarith [s10]
    · -- 1*chi <= 2
      have s11 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s12 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s13 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s14 : (G.minDegree : ℤ) ≥ 1 := by
        have hw := edge_conn_min_deg_int G hp1 hp2
        try push_cast at hw
        linarith [hw]
      have s15 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s11, s12, s14]
      have s16 : -(Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * ((G.minDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s15]) (by linarith [s14])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : -(Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s18 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s19 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s17, s18]
      have s20 : -(G.minDegree : ℤ) ≥ -3 := by linarith [s11, s12, s17, s18]
      have s21 : -3 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
        have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * (3 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s19]) (by linarith [s20])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s22 : 2 * (G.edgeFinset.card : ℤ) - 4 * (G.minDegree : ℤ) ≥ -3 := by linarith [s11, s12, s13, s16, s21]
      have s23 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ -1 := by have hr := s22; omega
      linarith [s23]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
