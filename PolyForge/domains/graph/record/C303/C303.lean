import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C303 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.cliqueNum : ℤ) ≤ 6) :
    2 * (G.cliqueNum : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 6 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -6 := by
        by_cases hc2 : (6 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 6
          have s3 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -6 := by
            by_cases hc3 : (2 : ℤ) ≤ (G.minDegree : ℤ)
            · -- 1*min_deg >= 2
              have s4 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc2; omega
              have s5 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc3; omega
              have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s7 : -(G.cliqueNum : ℤ) ≥ -6 := by linarith [hn1]
              have s8 : -2 * (Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 2) :=
                  mul_nonneg (by linarith [s4]) (by linarith [s5])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s9 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -6 := by linarith [s4, s5, s6, s7, s8]
              linarith [s9]
            · -- 1*min_deg <= 1
              have s10 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s11 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
                have hw := omega_le_maxdeg_add_one_int G
                try push_cast at hw
                linarith [hw]
              have s12 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc3; omega
              have s13 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -5 := by linarith [s10, s11, s12]
              linarith [s13]
          linarith [s3]
        · -- 1*n <= 5
          have s14 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -6 := by
            by_cases hc14 : (5 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 5
              have s15 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s16 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s17 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
                have hw := omega_le_maxdeg_add_one_int G
                try push_cast at hw
                linarith [hw]
              have s18 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s19 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc14; omega
              have s20 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s21 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc14; omega
              have s22 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s21]) (by linarith [s20])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s23 : 10 * (G.edgeFinset.card : ℤ) - 15 * (G.minDegree : ℤ) - 10 * (G.cliqueNum : ℤ) ≥ -34 := by linarith [s15, s16, s17, s18, s19, s22]
              have s24 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -6 := by have hr := s23; omega
              linarith [s24]
            · -- 1*n <= 4
              have s25 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_card_int G
                try push_cast at hw
                linarith [hw]
              have s26 : (G.edgeFinset.card : ℤ) ≥ 3 := by
                have hw := three_le_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s27 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s28 : (Fintype.card V : ℤ) ≥ 3 := by
                have hw := three_le_card_of_cycle_int G hp1
                try push_cast at hw
                linarith [hw]
              have s29 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s30 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s28]) (by linarith [s29])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s31 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc14; omega
              have s32 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s33 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s34 : -(G.minDegree : ℤ) ≥ -3 := by linarith [s32, s33, s31]
              have s35 : -3 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
                have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * (3 - (G.minDegree : ℤ)) :=
                  mul_nonneg (by linarith [s31]) (by linarith [s34])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s36 : 6 * (G.edgeFinset.card : ℤ) - 9 * (G.minDegree : ℤ) - 6 * (G.cliqueNum : ℤ) ≥ -20 := by linarith [s25, s26, s27, s30, s35]
              have s37 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -6 := by have hr := s36; omega
              linarith [s37]
          linarith [s14]
      linarith [s2]
    · -- 1*chi <= 2
      have s38 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s39 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s40 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s41 : (Fintype.card V : ℤ) ≥ 3 := by
        have hw := three_le_card_of_cycle_int G hp1
        try push_cast at hw
        linarith [hw]
      have s42 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s43 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s41]) (by linarith [s42])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s44 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -4 := by linarith [s38, s39, s40, s43]
      linarith [s44]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
