import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C299 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 5) (hn2 : (G.chromaticNumber.toNat : ℤ) ≥ (G.maxDegree : ℤ)) :
    (G.maxDegree : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - 10 := by
  have s1 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.edgeFinset.card : ℤ)
    · -- 1*m >= 3
      have s2 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s3 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by
            by_cases hc3 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc3; omega
              have s5 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s6 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
              have s7 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 12 := by linarith [s4, s5, s6]
              linarith [s7]
            · -- 1*chi <= 2
              have s8 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s9 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
              have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s11 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
              have s12 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc3; omega
              have s13 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s8]) (by linarith [s12])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s14 : -3 * (G.maxDegree : ℤ) + 9 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) ≥ 28 := by linarith [s8, s9, s10, s11, s13]
              have s15 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by have hr := s14; omega
              linarith [s15]
          linarith [s3]
        · -- 1*alpha <= 2
          have s16 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
          have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s18 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s19 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s20 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s18]) (by linarith [s19])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s21 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s16, s17, s18, s20]
          have s22 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hr := s21; omega
          have s23 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
          have s24 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
              mul_nonneg (by linarith [s18]) (by linarith [s22])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s25 : -3 * (G.maxDegree : ℤ) + 9 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) ≥ 28 := by linarith [s22, s16, s17, s23, s24]
          have s26 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by have hr := s25; omega
          linarith [s26]
      linarith [s2]
    · -- 1*m <= 2
      have s27 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by
        by_cases hc27 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s28 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s29 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc27; omega
          have s30 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
          have s31 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s32 : -(G.edgeFinset.card : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s33 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s34 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 13 := by linarith [s28, s29, s30, s31, s32, s33]
          linarith [s34]
        · -- 1*chi <= 2
          have s35 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
          have s36 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s37 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
          have s38 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s39 : -(G.edgeFinset.card : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s40 : -(G.vertexCoverNum.toNat : ℤ) ≥ -2 := by linarith [s38, s39]
          have s41 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc27; omega
          have s42 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s43 : (G.indepNum : ℤ) ≥ 3 := by linarith [s35, s38, s39, s42]
          have s44 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s43]) (by linarith [s41])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s45 : -3 * (G.maxDegree : ℤ) + 9 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) ≥ 28 := by linarith [s35, s36, s37, s40, s44, s42]
          have s46 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by have hr := s45; omega
          linarith [s46]
      linarith [s27]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
