import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C222 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 6) :
    2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 * (Fintype.card V : ℤ) - 6 * (G.indepNum : ℤ) := by
  have s1 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.maxDegree : ℤ)
    · -- 1*max_deg >= 2
      have s2 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        by_cases hc2 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 2
          have s3 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            by_cases hc3 : (2 : ℤ) ≤ (G.indepNum : ℤ)
            · -- 1*alpha >= 2
              have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s5 : -(Fintype.card V : ℤ) ≥ -6 := by linarith [hn1]
              have s6 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc3; omega
              have s7 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s8 : -(G.chromaticNumber.toNat : ℤ) ≥ -6 := by linarith [s7, s5]
              have s9 : 2 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 12 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (6 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s6]) (by linarith [s8])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s11 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [s4, s5, s9, s10]
              linarith [s11]
            · -- 1*alpha <= 1
              have s12 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s13 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s14 : -(Fintype.card V : ℤ) ≥ -6 := by linarith [hn1]
              have s15 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc2; omega
              have s16 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc3; omega
              have s17 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 2) :=
                  mul_nonneg (by linarith [s16]) (by linarith [s15])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s18 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s19 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [s12, s13, s14, s17, s18]
              linarith [s19]
          linarith [s3]
        · -- 1*chi <= 1
          have s20 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s21 : (G.maxDegree : ℤ) ≥ 2 := by have hcc := hc1; omega
          have s22 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s23 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc2; omega
          have s24 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s25 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s24]) (by linarith [s23])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s26 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s27 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 11 := by linarith [s20, s21, s22, s23, s25, s26]
          linarith [s27]
      linarith [s2]
    · -- 1*max_deg <= 1
      have s28 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by
        by_cases hc28 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s29 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc28; omega
          have s30 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s31 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s32 : -(G.maxDegree : ℤ) ≥ -1 := by have hcc := hc1; omega
          have s33 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s34 : (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 1 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (1 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s33]) (by linarith [s32])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s35 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s36 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 6 := by linarith [s29, s30, s31, s32, s34, s35]
          linarith [s36]
        · -- 1*chi <= 2
          have s37 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s38 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc28; omega
          have s39 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s40 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s39]) (by linarith [s38])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s41 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s42 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [s37, s38, s40, s41]
          linarith [s42]
      linarith [s28]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
