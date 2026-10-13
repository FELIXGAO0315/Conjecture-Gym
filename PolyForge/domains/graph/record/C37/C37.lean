import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C37 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≥ 2) (hn2 : (G.vertexCoverNum.toNat : ℤ) ≥ (G.indepNum : ℤ)) :
    2 * (G.edgeFinset.card : ℤ) ≥ 2 * (G.minDegree : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) + 8 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 8 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [hn1]
      have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : -(G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s7 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s3, s4, s5, s6]
      have s8 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by have hr := s7; omega
      have s9 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s10 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s11 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s3, s4]
      have s12 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s11]) (by linarith [s10])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : 6 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) + 9 * (G.vertexCoverNum.toNat : ℤ) ≥ 22 := by linarith [s2, s8, s9, s12]
      have s14 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 8 := by have hr := s13; omega
      linarith [s14]
    · -- 1*chi <= 2
      have s15 : (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [hn1]
      have s16 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by
        by_cases hc16 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 4
          have s34 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc16; omega
          have s18 : -(G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
          have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s20 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [s34, s18, s19]
          linarith [s20]
        · -- 1*n <= 3
          have s35 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s36 : (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [hn1]
          have s37 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s24 : -(G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
          have s38 : (G.maxDegree : ℤ) ≥ 0 := by positivity
          have s39 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc16; omega
          have s40 : 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ (3 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s39]) (by linarith [s38])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s28 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s29 : 6 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by linarith [s35, s36, s37, s24, s40, s28]
          have s30 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by have hr := s29; omega
          linarith [s30]
      have s31 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s32 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s33 : (Fintype.card V : ℤ) ≥ 3 := by
        by_cases hc33 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 4
          have s34 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc33; omega
          linarith [s34]
        · -- 1*n <= 3
          have s35 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s36 : (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [hn1]
          have s37 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s38 : (G.maxDegree : ℤ) ≥ 0 := by positivity
          have s39 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc33; omega
          have s40 : 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ (3 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s39]) (by linarith [s38])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s41 : 3 * (Fintype.card V : ℤ) ≥ 7 := by linarith [s35, s36, s37, s40]
          have s42 : (Fintype.card V : ℤ) ≥ 3 := by have hr := s41; omega
          linarith [s42]
      have s43 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s33]) (by linarith [s32])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s44 : 6 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) + 9 * (G.vertexCoverNum.toNat : ℤ) ≥ 22 := by linarith [s15, s16, s31, s43]
      have s45 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 8 := by have hr := s44; omega
      linarith [s45]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
