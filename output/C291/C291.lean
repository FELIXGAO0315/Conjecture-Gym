import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C291 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≤ 3) (hn2 : (G.indepNum : ℤ) ≤ (G.cliqueNum : ℤ)) :
    (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) + 1 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -1 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : 2 * (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -1 := by
        by_cases hc2 : (5 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 5
          have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s4 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc2; omega
          have s5 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s7 : -(G.cliqueNum : ℤ) ≥ -3 := by linarith [hn1]
          have s8 : (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn2]
          have s9 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s10 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s4]) (by linarith [s9])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s12 : 10 * (G.edgeFinset.card : ℤ) - 5 * (G.minDegree : ℤ) - 5 * (G.chromaticNumber.toNat : ℤ) ≥ -9 := by linarith [s3, s4, s5, s6, s7, s8, s10, s11]
          have s13 : 2 * (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hr := s12; omega
          linarith [s13]
        · -- 1*n <= 4
          have s14 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s15 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s16 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s17 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s18 : (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [s15, s16, s17]
          have s19 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s20 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc2; omega
          have s21 : -(G.chromaticNumber.toNat : ℤ) ≥ -4 := by linarith [s14, s20]
          have s22 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s23 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s24 : -(G.minDegree : ℤ) ≥ -3 := by linarith [s22, s23, s20]
          have s25 : -3 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
            have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * (3 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s20]) (by linarith [s24])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s26 : 2 * (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -1 := by linarith [s14, s18, s19, s21, s25]
          linarith [s26]
      linarith [s2]
    · -- 1*omega <= 2
      have s27 : 2 * (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -1 := by
        by_cases hc27 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s28 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s29 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s30 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc27; omega
          have s31 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s32 : (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn2]
          have s33 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s34 : (G.edgeFinset.card : ℤ) ≥ 1 := by linarith [s28, s30, s29, s31, s32, s33]
          have s35 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s36 : -(G.indepNum : ℤ) ≥ -2 := by linarith [s31, s32]
          have s37 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s38 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s28, s30]
          have s39 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s38]) (by linarith [s37])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s40 : 6 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [s28, s29, s34, s35, s36, s39, s33]
          have s41 : 2 * (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hr := s40; omega
          linarith [s41]
        · -- 1*chi <= 2
          have s42 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s43 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s44 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s45 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s46 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s47 : (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn2]
          have s48 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc27; omega
          have s49 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s50 : 4 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ -3 := by linarith [s42, s43, s44, s45, s46, s47, s48, s49]
          have s51 : 2 * (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hr := s50; omega
          linarith [s51]
      linarith [s27]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
