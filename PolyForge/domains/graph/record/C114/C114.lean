import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C114 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≤ 2 * (G.vertexCoverNum.toNat : ℤ)) :
    2 * (G.edgeFinset.card : ℤ) ≥ -3 * (G.chromaticNumber.toNat : ℤ) + 8 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 8 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s6 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 13 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*omega <= 2
      have s7 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 8 := by
        by_cases hc7 : (2 : ℤ) ≤ (G.edgeFinset.card : ℤ)
        · -- 1*m >= 2
          have s8 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 9 := by
            by_cases hc8 : (3 : ℤ) ≤ (G.edgeFinset.card : ℤ)
            · -- 1*m >= 3
              have s9 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s10 : (G.edgeFinset.card : ℤ) ≥ 3 := by have hcc := hc8; omega
              have s11 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 9 := by linarith [s9, s10]
              linarith [s11]
            · -- 1*m <= 2
              have s12 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s13 : -(G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
              have s14 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s12, s13]
              have s15 : (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s14; omega
              have s16 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s17 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s18 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
                have hw := tau_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s19 : -(G.edgeFinset.card : ℤ) ≥ -2 := by have hcc := hc8; omega
              have s20 : -(G.indepNum : ℤ) ≥ -4 := by linarith [s18, s13, s19]
              have s21 : 4 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
                have hmul : (0 : ℤ) ≤ (4 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s20]) (by linarith [s17])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s22 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s23 : 4 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s15, s16, s21, s22]
              have s24 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s23; omega
              have s25 : (G.edgeFinset.card : ℤ) ≥ 2 := by have hcc := hc8; omega
              have s26 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 10 := by linarith [s24, s25]
              linarith [s26]
          linarith [s8]
        · -- 1*m <= 1
          have s27 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s28 : -(G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
          have s29 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s27, s28]
          have s30 : (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s29; omega
          have s31 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s32 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s33 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s34 : -(G.edgeFinset.card : ℤ) ≥ -1 := by have hcc := hc7; omega
          have s35 : -(G.indepNum : ℤ) ≥ -2 := by linarith [s33, s28, s34]
          have s36 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s35]) (by linarith [s32])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s37 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s38 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s30, s31, s36, s37]
          have s39 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s38; omega
          have s40 : 2 * (G.edgeFinset.card : ℤ) ≥ 1 := by linarith [s27, s33, s28]
          have s41 : (G.edgeFinset.card : ℤ) ≥ 1 := by have hr := s40; omega
          have s42 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 8 := by linarith [s39, s41]
          linarith [s42]
      linarith [s7]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
