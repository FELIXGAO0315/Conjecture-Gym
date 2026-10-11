import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C47 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 4) (hn2 : (G.indepNum : ℤ) ≥ (G.vertexCoverNum.toNat : ℤ)) :
    2 * (G.edgeFinset.card : ℤ) ≤ 3 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) - 3 := by
  have s1 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 4 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s3 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 4 := by
            by_cases hc3 : (1 : ℤ) ≤ (G.maxDegree : ℤ)
            · -- 1*max_deg >= 1
              have s4 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s5 : (G.maxDegree : ℤ) ≥ 1 := by have hcc := hc3; omega
              have s6 : -(G.edgeFinset.card : ℤ) ≥ -4 := by linarith [hn1]
              have s7 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 4 := by linarith [s4, s5, s6]
              linarith [s7]
            · -- 1*max_deg <= 0
              have s8 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s9 : (G.maxDegree : ℤ) ≥ 0 := by positivity
              have s10 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s11 : (Fintype.card V : ℤ) ≥ 1 := by
                have hw := card_ge_one_int (V := V)
                try push_cast at hw
                linarith [hw]
              have s12 : -(G.maxDegree : ℤ) ≥ 0 := by have hcc := hc3; omega
              have s13 : (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (0 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s11]) (by linarith [s12])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s14 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 9 := by linarith [s8, s9, s10, s13]
              linarith [s14]
          linarith [s3]
        · -- 1*alpha <= 2
          have s15 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s16 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s17 : (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
          have s18 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s19 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s15, s16, s17, s18]
          have s20 : (G.indepNum : ℤ) ≥ 2 := by have hr := s19; omega
          have s21 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s22 : -(G.edgeFinset.card : ℤ) ≥ -4 := by linarith [hn1]
          have s23 : (G.maxDegree : ℤ) ≥ 0 := by positivity
          have s24 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s25 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s17, s24, s18]
          have s26 : 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s25]) (by linarith [s23])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s27 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 4 := by linarith [s20, s21, s22, s26]
          linarith [s27]
      linarith [s2]
    · -- 1*chi <= 2
      have s28 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by
        by_cases hc28 : (3 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 3
          have s29 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 4 := by
            by_cases hc29 : (2 : ℤ) ≤ (G.maxDegree : ℤ)
            · -- 1*max_deg >= 2
              have s30 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc28; omega
              have s31 : (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
              have s32 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s33 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s30, s31, s32]
              have s34 : (G.indepNum : ℤ) ≥ 2 := by have hr := s33; omega
              have s35 : (G.maxDegree : ℤ) ≥ 2 := by have hcc := hc29; omega
              have s36 : -(G.edgeFinset.card : ℤ) ≥ -4 := by linarith [hn1]
              have s37 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 4 := by linarith [s34, s35, s36]
              linarith [s37]
            · -- 1*max_deg <= 1
              have s38 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc28; omega
              have s39 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s40 : (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
              have s41 : -(G.maxDegree : ℤ) ≥ -1 := by have hcc := hc29; omega
              have s42 : (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (1 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s38]) (by linarith [s41])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s43 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s44 : -4 * (G.edgeFinset.card : ℤ) + 6 * (G.maxDegree : ℤ) + 6 * (G.indepNum : ℤ) ≥ 9 := by linarith [s38, s39, s40, s42, s43]
              have s45 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by have hr := s44; omega
              linarith [s45]
          linarith [s29]
        · -- 1*n <= 2
          have s46 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s47 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
          have s48 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s49 : (G.maxDegree : ℤ) ≥ 0 := by positivity
          have s50 : -(Fintype.card V : ℤ) ≥ -2 := by have hcc := hc28; omega
          have s51 : 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ (2 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s50]) (by linarith [s49])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s52 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by linarith [s46, s47, s48, s51]
          linarith [s52]
      linarith [s28]
  linarith [s1]
