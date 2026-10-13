import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C77 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.maxDegree : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)) :
    (G.minDegree : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 10 := by
  have s1 : -(G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 3
      have s2 : -(G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s5 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s6 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
          have s7 : -(G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 15 := by linarith [s3, s4, s5, s6]
          linarith [s7]
        · -- 1*chi <= 2
          have s8 : -(G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by
            by_cases hc8 : (2 : ℤ) ≤ (G.maxDegree : ℤ)
            · -- 1*max_deg >= 2
              have s9 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s10 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s11 : (G.maxDegree : ℤ) ≥ 2 := by have hcc := hc8; omega
              have s12 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
              have s13 : -(G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by linarith [s9, s10, s11, s12]
              linarith [s13]
            · -- 1*max_deg <= 1
              have s14 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s15 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s16 : (G.edgeFinset.card : ℤ) ≥ 3 := by
                have hw := three_le_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s17 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s18 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s19 : -(G.maxDegree : ℤ) ≥ -1 := by have hcc := hc8; omega
              have s20 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
              have s21 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s15]) (by linarith [s20])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s22 : (Fintype.card V : ℤ) ≥ 3 := by
                have hw := three_le_card_of_cycle_int G hp1
                try push_cast at hw
                linarith [hw]
              have s23 : (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (1 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s22]) (by linarith [s19])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s24 : -(G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 14 := by linarith [s14, s15, s16, s17, s18, s19, s21, s23]
              linarith [s24]
          linarith [s8]
      linarith [s2]
    · -- 1*alpha <= 2
      have s25 : -(G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by
        by_cases hc25 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s26 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s27 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s28 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc25; omega
          have s29 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s30 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s31 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
              mul_nonneg (by linarith [s30]) (by linarith [s28])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s32 : -(G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by linarith [s26, s27, s28, s29, s31]
          linarith [s32]
        · -- 1*chi <= 2
          have s33 : (Fintype.card V : ℤ) ≥ 3 := by
            have hw := three_le_card_of_cycle_int G hp1
            try push_cast at hw
            linarith [hw]
          have s34 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s35 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s36 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s37 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s35]) (by linarith [s36])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s38 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s33, s34, s35, s37]
          have s39 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s38; omega
          have s40 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc25; omega
          have s41 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s42 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s41]) (by linarith [s40])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s43 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s33, s34, s40, s42]
          have s44 : (G.indepNum : ℤ) ≥ 2 := by have hr := s43; omega
          have s45 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s46 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
          have s47 : -(G.minDegree : ℤ) ≥ -2 := by linarith [s45, s46, s40]
          have s48 : -(G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by linarith [s39, s44, s47]
          linarith [s48]
      linarith [s25]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
