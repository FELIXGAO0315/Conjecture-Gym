import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C204 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.diam : ℤ) ≥ 3) :
    (G.diam : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 3 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.diam : ℤ) ≥ 3 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.diam : ℤ) ≥ 3 := by
        by_cases hc2 : (2 : ℤ) ≤ (G.minDegree : ℤ)
        · -- 1*min_deg >= 2
          have s3 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp1
            try push_cast at hw
            linarith [hw]
          have s4 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc2; omega
          have s5 : (G.diam : ℤ) ≥ 3 := by linarith [hn1]
          have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s7 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s8 : -2 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 2) :=
              mul_nonneg (by linarith [s7]) (by linarith [s4])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s9 : (G.edgeFinset.card : ℤ) ≥ 4 := by linarith [s3, s4, s5, s6, s8]
          have s10 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s3, s5]
          have s11 : -2 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -8 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 2) :=
              mul_nonneg (by linarith [s10]) (by linarith [s4])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s12 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.diam : ℤ) ≥ 3 := by linarith [s3, s9, s5, s6, s11]
          linarith [s12]
        · -- 1*min_deg <= 1
          have s13 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
            have hw := connected_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s14 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp1
            try push_cast at hw
            linarith [hw]
          have s15 : (G.diam : ℤ) ≥ 3 := by linarith [hn1]
          have s16 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc2; omega
          have s17 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.diam : ℤ) ≥ 3 := by linarith [s13, s14, s15, s16]
          linarith [s17]
      linarith [s2]
    · -- 1*omega <= 2
      have s18 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.diam : ℤ) ≥ 3 := by
        by_cases hc18 : (2 : ℤ) ≤ (G.minDegree : ℤ)
        · -- 1*min_deg >= 2
          have s19 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp1
            try push_cast at hw
            linarith [hw]
          have s20 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc18; omega
          have s21 : (G.diam : ℤ) ≥ 3 := by linarith [hn1]
          have s22 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s23 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s24 : -2 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 2) :=
              mul_nonneg (by linarith [s23]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s25 : (G.edgeFinset.card : ℤ) ≥ 4 := by linarith [s19, s20, s21, s22, s24]
          have s26 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s19, s21]
          have s27 : -2 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -8 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 2) :=
              mul_nonneg (by linarith [s26]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s28 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.diam : ℤ) ≥ 3 := by linarith [s19, s25, s21, s22, s27]
          linarith [s28]
        · -- 1*min_deg <= 1
          have s29 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
            have hw := connected_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s30 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp1
            try push_cast at hw
            linarith [hw]
          have s31 : (G.diam : ℤ) ≥ 3 := by linarith [hn1]
          have s32 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc18; omega
          have s33 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.diam : ℤ) ≥ 3 := by linarith [s29, s30, s31, s32]
          linarith [s33]
      linarith [s18]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
