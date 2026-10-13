import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C54 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≥ 2 * (G.indepNum : ℤ)) (hn2 : (G.indepNum : ℤ) ≤ 6) :
    2 * (G.edgeFinset.card : ℤ) ≥ 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) - 3 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 3 * (G.indepNum : ℤ) ≥ -3 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 3 * (G.indepNum : ℤ) ≥ -3 := by
        by_cases hc2 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 4
          have s3 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 3 * (G.indepNum : ℤ) ≥ -3 := by
            by_cases hc3 : (3 : ℤ) ≤ (G.minDegree : ℤ)
            · -- 1*min_deg >= 3
              have s4 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                try push_cast at hw
                linarith [hw]
              have s5 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s6 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc2; omega
              have s7 : (G.minDegree : ℤ) ≥ 3 := by have hcc := hc3; omega
              have s8 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s9 : (G.cliqueNum : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
              have s10 : -3 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 3) :=
                  mul_nonneg (by linarith [s6]) (by linarith [s7])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s11 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 3 * (G.indepNum : ℤ) ≥ 0 := by linarith [s4, s5, s6, s7, s8, s9, s10]
              linarith [s11]
            · -- 1*min_deg <= 2
              have s12 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s13 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
                have hw := omega_le_maxdeg_add_one_int G
                try push_cast at hw
                linarith [hw]
              have s14 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s15 : (G.cliqueNum : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
              have s16 : -(G.minDegree : ℤ) ≥ -2 := by have hcc := hc3; omega
              have s17 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s18 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc2; omega
              have s19 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s18]) (by linarith [s17])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s20 : 4 * (G.edgeFinset.card : ℤ) - 4 * (G.minDegree : ℤ) - 6 * (G.indepNum : ℤ) ≥ -7 := by linarith [s12, s13, s14, s15, s16, s19]
              have s21 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 3 * (G.indepNum : ℤ) ≥ -3 := by have hr := s20; omega
              linarith [s21]
          linarith [s3]
        · -- 1*n <= 3
          have s22 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s23 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s24 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s25 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s26 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s27 : (G.cliqueNum : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
          have s28 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s29 : 3 * (G.edgeFinset.card : ℤ) ≥ 5 := by linarith [s22, s23, s24, s25, s26, s27, s28]
          have s30 : (G.edgeFinset.card : ℤ) ≥ 2 := by have hr := s29; omega
          have s31 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s32 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s33 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc2; omega
          have s34 : -2 * (G.indepNum : ℤ) ≥ -3 := by linarith [s32, s26, s27, s33]
          have s35 : -(G.indepNum : ℤ) ≥ -1 := by have hr := s34; omega
          have s36 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s37 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s22, s24]
          have s38 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s37]) (by linarith [s36])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s39 : 6 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) - 9 * (G.indepNum : ℤ) ≥ -5 := by linarith [s30, s31, s35, s38]
          have s40 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 3 * (G.indepNum : ℤ) ≥ -1 := by have hr := s39; omega
          linarith [s40]
      linarith [s2]
    · -- 1*chi <= 2
      have s41 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s42 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s43 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s44 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s45 : (G.cliqueNum : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
      have s46 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s47 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s48 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 3 * (G.indepNum : ℤ) ≥ -3 := by linarith [s41, s42, s43, s44, s45, s46, s47]
      linarith [s48]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
