import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C197 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 5) (hn2 : (Fintype.card V : ℤ) ≥ 2 * (G.chromaticNumber.toNat : ℤ)) :
    2 * (G.chromaticNumber.toNat : ℤ) ≥ -2 * (Fintype.card V : ℤ) - 3 * (G.indepNum : ℤ) + 23 := by
  have s1 : 2 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 23 := by
    by_cases hc1 : (4 : ℤ) ≤ (G.edgeFinset.card : ℤ)
    · -- 1*m >= 4
      have s2 : 2 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 23 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s3 : 2 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 23 := by
            by_cases hc3 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc3; omega
              have s5 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s6 : (Fintype.card V : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
              have s7 : 2 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 27 := by linarith [s4, s5, s6]
              linarith [s7]
            · -- 1*chi <= 2
              have s8 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s9 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
              have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc3; omega
              have s12 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s8]) (by linarith [s11])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s13 : 6 * (Fintype.card V : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) + 9 * (G.indepNum : ℤ) ≥ 67 := by linarith [s8, s9, s10, s12]
              have s14 : 2 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 23 := by have hr := s13; omega
              linarith [s14]
          linarith [s3]
        · -- 1*alpha <= 2
          have s15 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
          have s16 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s17 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s18 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s19 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s17]) (by linarith [s18])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s20 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s15, s16, s17, s19]
          have s21 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hr := s20; omega
          have s22 : (Fintype.card V : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
          have s23 : (G.indepNum : ℤ) ≥ 2 := by linarith [s16, s22, s19]
          have s24 : 2 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 24 := by linarith [s21, s23, s22]
          linarith [s24]
      linarith [s2]
    · -- 1*m <= 3
      have s25 : 2 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 23 := by
        by_cases hc25 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s26 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc25; omega
          have s27 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s28 : (Fintype.card V : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
          have s29 : -(G.edgeFinset.card : ℤ) ≥ -3 := by have hcc := hc1; omega
          have s30 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s31 : 2 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 27 := by linarith [s26, s27, s28, s29, s30]
          linarith [s31]
        · -- 1*chi <= 2
          have s32 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
          have s33 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s34 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc25; omega
          have s35 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s36 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s35]) (by linarith [s34])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s37 : 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s32, s33, s34, s36]
          have s38 : (G.indepNum : ℤ) ≥ 3 := by have hr := s37; omega
          have s39 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s38]) (by linarith [s34])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s40 : 6 * (Fintype.card V : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) + 9 * (G.indepNum : ℤ) ≥ 67 := by linarith [s38, s32, s33, s39]
          have s41 : 2 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 23 := by have hr := s40; omega
          linarith [s41]
      linarith [s25]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
