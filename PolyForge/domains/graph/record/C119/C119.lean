import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C119 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : 2 ≤ Fintype.card V) (hn1 : (G.edgeFinset.card : ℤ) ≥ 6) :
    (G.diam : ℤ) ≥ -3 * (G.edgeFinset.card : ℤ) + 3 * (G.minDegree : ℤ) + 10 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.diam : ℤ) ≥ 10 := by
    by_cases hc1 : (6 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 6
      have s2 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := radius_le_diam_int G hp1
        try push_cast at hw
        linarith [hw]
      have s3 : (G.radius.toNat : ℤ) ≥ 1 := by
        have hw := radius_ge_one_int G hp1 hp2
        try push_cast at hw
        linarith [hw]
      have s4 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc1; omega
      have s5 : (G.edgeFinset.card : ℤ) ≥ 6 := by linarith [hn1]
      have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s7 : (G.minDegree : ℤ) ≥ 1 := by
        have hw := connected_min_deg_int G hp1 hp2
        try push_cast at hw
        linarith [hw]
      have s8 : -(Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s4]) (by linarith [s7])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.diam : ℤ) ≥ 13 := by linarith [s2, s3, s4, s5, s6, s8]
      linarith [s9]
    · -- 1*n <= 5
      have s10 : (G.diam : ℤ) ≥ 1 := by
        have hw := diam_ge_one_int G hp1 hp2
        try push_cast at hw
        linarith [hw]
      have s11 : (G.edgeFinset.card : ℤ) ≥ 6 := by linarith [hn1]
      have s12 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := two_mul_edges_le_card_sq_sub_card_int G
        try push_cast at hw
        linarith [hw]
      have s13 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s14 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc1; omega
      have s15 : 6 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 5 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (5 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s13]) (by linarith [s14])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s16 : 5 * (Fintype.card V : ℤ) ≥ 17 := by linarith [s11, s12, s15]
      have s17 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s16; omega
      have s18 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s19 : (G.minDegree : ℤ) ≥ 1 := by
        have hw := connected_min_deg_int G hp1 hp2
        try push_cast at hw
        linarith [hw]
      have s20 : -(Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -4 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s17]) (by linarith [s19])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s21 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.diam : ℤ) ≥ 10 := by linarith [s10, s17, s11, s18, s20]
      linarith [s21]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
