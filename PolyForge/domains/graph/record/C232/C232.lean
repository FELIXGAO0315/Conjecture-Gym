import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C232 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.Connected) (hn1 : (G.radius.toNat : ℤ) ≤ 6) :
    (G.radius.toNat : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.radius.toNat : ℤ) ≥ -2 := by
    by_cases hc1 : (9 : ℤ) ≤ (G.edgeFinset.card : ℤ)
    · -- 1*m >= 9
      have s2 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.radius.toNat : ℤ) ≥ 3 := by
        by_cases hc2 : (8 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 8
          have s3 : (Fintype.card V : ℤ) ≥ 8 := by have hcc := hc2; omega
          have s4 : (G.edgeFinset.card : ℤ) ≥ 9 := by have hcc := hc1; omega
          have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s6 : -(G.radius.toNat : ℤ) ≥ -6 := by linarith [hn1]
          have s7 : (G.minDegree : ℤ) ≥ 1 := by
            have hw := connected_min_deg_int G hp2 hp1
            try push_cast at hw
            linarith [hw]
          have s8 : -(Fintype.card V : ℤ) - 8 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -8 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 8) * ((G.minDegree : ℤ) - 1) :=
              mul_nonneg (by linarith [s3]) (by linarith [s7])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s9 : 8 * (G.edgeFinset.card : ℤ) - 12 * (G.minDegree : ℤ) - 4 * (G.radius.toNat : ℤ) ≥ 21 := by linarith [s3, s4, s5, s6, s8]
          have s10 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.radius.toNat : ℤ) ≥ 6 := by have hr := s9; omega
          linarith [s10]
        · -- 1*n <= 7
          have s11 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
            have hw := radius_le_diam_int G hp2
            try push_cast at hw
            linarith [hw]
          have s12 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp2
            try push_cast at hw
            linarith [hw]
          have s13 : (G.edgeFinset.card : ℤ) ≥ 9 := by have hcc := hc1; omega
          have s14 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s15 : -(Fintype.card V : ℤ) ≥ -7 := by have hcc := hc2; omega
          have s16 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s17 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s18 : -(G.minDegree : ℤ) ≥ -6 := by linarith [s16, s17, s15]
          have s19 : -6 * (Fintype.card V : ℤ) - 7 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -42 := by
            have hmul : (0 : ℤ) ≤ (7 - (Fintype.card V : ℤ)) * (6 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s15]) (by linarith [s18])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s20 : (G.minDegree : ℤ) ≥ 1 := by
            have hw := connected_min_deg_int G hp2 hp1
            try push_cast at hw
            linarith [hw]
          have s21 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := two_mul_edges_le_card_sq_sub_card_int G
            try push_cast at hw
            linarith [hw]
          have s22 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s23 : (G.maxDegree : ℤ) ≥ 0 := by positivity
          have s24 : 7 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ (7 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s15]) (by linarith [s23])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s25 : 7 * (Fintype.card V : ℤ) ≥ 25 := by linarith [s17, s13, s22, s24]
          have s26 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s25; omega
          have s27 : 11 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 28 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (7 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s26]) (by linarith [s15])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s28 : 5 * (Fintype.card V : ℤ) ≥ 23 := by linarith [s13, s21, s27]
          have s29 : (Fintype.card V : ℤ) ≥ 5 := by have hr := s28; omega
          have s30 : -(Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -5 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 1) :=
              mul_nonneg (by linarith [s29]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s31 : 46 * (G.edgeFinset.card : ℤ) - 69 * (G.minDegree : ℤ) - 23 * (G.radius.toNat : ℤ) ≥ 64 := by linarith [s11, s12, s13, s14, s19, s30]
          have s32 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.radius.toNat : ℤ) ≥ 3 := by have hr := s31; omega
          linarith [s32]
      linarith [s2]
    · -- 1*m <= 8
      have s33 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.radius.toNat : ℤ) ≥ -2 := by
        by_cases hc33 : (3 : ℤ) ≤ (G.edgeFinset.card : ℤ)
        · -- 1*m >= 3
          have s34 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
            have hw := radius_le_diam_int G hp2
            try push_cast at hw
            linarith [hw]
          have s35 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp2
            try push_cast at hw
            linarith [hw]
          have s36 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s37 : (G.minDegree : ℤ) ≥ 1 := by
            have hw := connected_min_deg_int G hp2 hp1
            try push_cast at hw
            linarith [hw]
          have s38 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s39 : (G.edgeFinset.card : ℤ) ≥ 3 := by have hcc := hc33; omega
          have s40 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s41 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s42 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s41, s38, s37]
          have s43 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
            have hw := connected_edges_int G hp2
            try push_cast at hw
            linarith [hw]
          have s44 : -(G.edgeFinset.card : ℤ) ≥ -8 := by have hcc := hc33; omega
          have s45 : -(G.maxDegree : ℤ) ≥ -8 := by linarith [s38, s43, s44]
          have s46 : 8 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 16 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * (8 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s42]) (by linarith [s45])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s47 : 5 * (Fintype.card V : ℤ) ≥ 12 := by linarith [s38, s39, s40, s46]
          have s48 : (Fintype.card V : ℤ) ≥ 3 := by have hr := s47; omega
          have s49 : -(Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -3 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 1) :=
              mul_nonneg (by linarith [s48]) (by linarith [s37])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s50 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.radius.toNat : ℤ) ≥ -2 := by linarith [s34, s35, s36, s49]
          linarith [s50]
        · -- 1*m <= 2
          have s51 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s52 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s53 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
            have hw := radius_le_diam_int G hp2
            try push_cast at hw
            linarith [hw]
          have s54 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp2
            try push_cast at hw
            linarith [hw]
          have s55 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s56 : (G.minDegree : ℤ) ≥ 1 := by
            have hw := connected_min_deg_int G hp2 hp1
            try push_cast at hw
            linarith [hw]
          have s57 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s51, s52, s56]
          have s58 : -(Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * ((G.minDegree : ℤ) - 1) :=
              mul_nonneg (by linarith [s57]) (by linarith [s56])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s59 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
            have hw := connected_edges_int G hp2
            try push_cast at hw
            linarith [hw]
          have s60 : -(G.edgeFinset.card : ℤ) ≥ -2 := by have hcc := hc33; omega
          have s61 : -(Fintype.card V : ℤ) ≥ -3 := by linarith [s59, s60]
          have s62 : -(G.minDegree : ℤ) ≥ -2 := by linarith [s51, s52, s59, s60]
          have s63 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
            have hmul : (0 : ℤ) ≤ (3 - (Fintype.card V : ℤ)) * (2 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s61]) (by linarith [s62])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s64 : 4 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ -5 := by linarith [s51, s52, s53, s54, s55, s58, s63]
          have s65 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.radius.toNat : ℤ) ≥ -2 := by have hr := s64; omega
          linarith [s65]
      linarith [s33]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
