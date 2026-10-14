import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C75 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≤ 2 * (G.vertexCoverNum.toNat : ℤ)) (hn2 : (G.edgeFinset.card : ℤ) ≥ 5) :
    2 * (G.edgeFinset.card : ℤ) ≥ -3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) + 25 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 25 := by
    by_cases hc1 : (9 : ℤ) ≤ (G.edgeFinset.card : ℤ)
    · -- 1*m >= 9
      have s2 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 31 := by
        by_cases hc2 : (11 : ℤ) ≤ (G.edgeFinset.card : ℤ)
        · -- 1*m >= 11
          have s3 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 32 := by
            by_cases hc3 : (13 : ℤ) ≤ (G.edgeFinset.card : ℤ)
            · -- 1*m >= 13
              have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s5 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s6 : (G.edgeFinset.card : ℤ) ≥ 13 := by have hcc := hc3; omega
              have s7 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 32 := by linarith [s4, s5, s6]
              linarith [s7]
            · -- 1*m <= 12
              have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s9 : (G.edgeFinset.card : ℤ) ≥ 11 := by have hcc := hc3; omega
              have s10 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s12 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s13 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s14 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
                have hw := tau_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s15 : -(G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
              have s16 : -(G.edgeFinset.card : ℤ) ≥ -12 := by have hcc := hc3; omega
              have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s18 : -(G.chromaticNumber.toNat : ℤ) ≥ -36 := by linarith [s13, s14, s15, s16, s17]
              have s19 : (G.chromaticNumber.toNat : ℤ) + 36 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 36 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (36 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s12]) (by linarith [s18])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s20 : -(G.indepNum : ℤ) ≥ -24 := by linarith [s14, s15, s16]
              have s21 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s22 : 24 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 24 := by
                have hmul : (0 : ℤ) ≤ (24 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s20]) (by linarith [s21])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s23 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s24 : -(G.maxDegree : ℤ) ≥ -12 := by linarith [s23, s16]
              have s25 : 2 * (Fintype.card V : ℤ) ≥ 3 := by linarith [s12, s15, s17]
              have s26 : (Fintype.card V : ℤ) ≥ 2 := by have hr := s25; omega
              have s27 : 12 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 24 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * (12 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s26]) (by linarith [s24])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s28 : 21 * (G.chromaticNumber.toNat : ℤ) ≥ 22 := by linarith [s8, s9, s10, s11, s15, s22, s27, s17]
              have s29 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s28; omega
              have s30 : 24 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 48 := by
                have hmul : (0 : ℤ) ≤ (24 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 2) :=
                  mul_nonneg (by linarith [s20]) (by linarith [s29])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s31 : 7 * (Fintype.card V : ℤ) ≥ 24 := by linarith [s8, s9, s10, s27]
              have s32 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s31; omega
              have s33 : 12 * (Fintype.card V : ℤ) + 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 48 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (12 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s32]) (by linarith [s24])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s34 : 13792 * (G.edgeFinset.card : ℤ) + 20688 * (G.chromaticNumber.toNat : ℤ) + 20688 * (G.indepNum : ℤ) ≥ 217367 := by linarith [s8, s9, s10, s11, s19, s30, s33]
              have s35 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 32 := by have hr := s34; omega
              linarith [s35]
          linarith [s3]
        · -- 1*m <= 10
          have s36 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 31 := by
            by_cases hc36 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s37 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s38 : (G.edgeFinset.card : ℤ) ≥ 9 := by have hcc := hc2; omega
              have s39 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s40 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s41 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s42 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s43 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
                have hw := tau_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s44 : -(G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
              have s45 : -(G.edgeFinset.card : ℤ) ≥ -10 := by have hcc := hc2; omega
              have s46 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s47 : -(G.chromaticNumber.toNat : ℤ) ≥ -30 := by linarith [s42, s43, s44, s45, s46]
              have s48 : (G.chromaticNumber.toNat : ℤ) + 30 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 30 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (30 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s41]) (by linarith [s47])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s49 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc36; omega
              have s50 : -(G.indepNum : ℤ) ≥ -20 := by linarith [s43, s44, s45]
              have s51 : 20 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 60 := by
                have hmul : (0 : ℤ) ≤ (20 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
                  mul_nonneg (by linarith [s50]) (by linarith [s49])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s52 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s42, s49]
              have s53 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s54 : -(G.maxDegree : ℤ) ≥ -10 := by linarith [s53, s45]
              have s55 : 10 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 30 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (10 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s52]) (by linarith [s54])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s56 : 5174 * (G.edgeFinset.card : ℤ) + 7761 * (G.chromaticNumber.toNat : ℤ) + 7761 * (G.indepNum : ℤ) ≥ 78162 := by linarith [s37, s38, s39, s40, s48, s51, s55]
              have s57 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 31 := by have hr := s56; omega
              linarith [s57]
            · -- 1*chi <= 2
              have s58 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s59 : (G.edgeFinset.card : ℤ) ≥ 9 := by have hcc := hc2; omega
              have s60 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s61 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s62 : -(G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
              have s63 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s64 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
                have hw := tau_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s65 : -(G.edgeFinset.card : ℤ) ≥ -10 := by have hcc := hc2; omega
              have s66 : -(G.indepNum : ℤ) ≥ -20 := by linarith [s64, s62, s65]
              have s67 : 20 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 20 := by
                have hmul : (0 : ℤ) ≤ (20 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s66]) (by linarith [s63])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s68 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s69 : -(G.maxDegree : ℤ) ≥ -10 := by linarith [s68, s65]
              have s70 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s71 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s72 : 2 * (Fintype.card V : ℤ) ≥ 3 := by linarith [s70, s62, s71]
              have s73 : (Fintype.card V : ℤ) ≥ 2 := by have hr := s72; omega
              have s74 : 10 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 20 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * (10 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s73]) (by linarith [s69])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s75 : 18 * (G.chromaticNumber.toNat : ℤ) ≥ 19 := by linarith [s58, s59, s60, s61, s62, s67, s74, s71]
              have s76 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s75; omega
              have s77 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc36; omega
              have s78 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s70]) (by linarith [s77])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s79 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                try push_cast at hw
                linarith [hw]
              have s80 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s79, s77]
              have s81 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := turan_r2_int G (by linarith [s80])
                try push_cast at hw
                linarith [hw]
              have s82 : -(Fintype.card V : ℤ) ≥ -30 := by linarith [s64, s62, s65, s71]
              have s83 : 3 * (Fintype.card V : ℤ) ≥ 10 := by linarith [s58, s59, s60, s74]
              have s84 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s83; omega
              have s85 : 34 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 120 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (30 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s84]) (by linarith [s82])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s86 : 17 * (G.indepNum : ℤ) ≥ 39 := by linarith [s59, s61, s77, s78, s81, s85]
              have s87 : (G.indepNum : ℤ) ≥ 3 := by have hr := s86; omega
              have s88 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 33 := by linarith [s76, s87, s59]
              linarith [s88]
          linarith [s36]
      linarith [s2]
    · -- 1*m <= 8
      have s89 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 25 := by
        by_cases hc89 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s90 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 25 := by
            by_cases hc90 : (2 : ℤ) ≤ (G.indepNum : ℤ)
            · -- 1*alpha >= 2
              have s91 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc89; omega
              have s92 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc90; omega
              have s93 : (G.edgeFinset.card : ℤ) ≥ 5 := by linarith [hn2]
              have s94 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 25 := by linarith [s91, s92, s93]
              linarith [s94]
            · -- 1*alpha <= 1
              have s95 : (G.edgeFinset.card : ℤ) ≥ 5 := by linarith [hn2]
              have s96 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := two_mul_edges_le_card_sq_sub_card_int G
                try push_cast at hw
                linarith [hw]
              have s97 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s98 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc89; omega
              have s99 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s97, s98]
              have s100 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
                have hw := tau_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s101 : -(G.edgeFinset.card : ℤ) ≥ -8 := by have hcc := hc1; omega
              have s102 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc90; omega
              have s103 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s104 : -(Fintype.card V : ℤ) ≥ -9 := by linarith [s100, s101, s102, s103]
              have s105 : 12 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 27 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (9 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s99]) (by linarith [s104])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s106 : 11 * (Fintype.card V : ℤ) ≥ 37 := by linarith [s95, s96, s105]
              have s107 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s106; omega
              have s108 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s109 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
                  mul_nonneg (by linarith [s102]) (by linarith [s98])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s110 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 25 := by linarith [s107, s95, s108, s102, s109]
              linarith [s110]
          linarith [s90]
        · -- 1*chi <= 2
          have s111 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s112 : -(G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
          have s113 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s111, s112]
          have s114 : (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s113; omega
          have s115 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s116 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s117 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s118 : -(G.edgeFinset.card : ℤ) ≥ -8 := by have hcc := hc1; omega
          have s119 : -(G.indepNum : ℤ) ≥ -16 := by linarith [s117, s112, s118]
          have s120 : 16 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 16 := by
            have hmul : (0 : ℤ) ≤ (16 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s119]) (by linarith [s116])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s121 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s122 : 16 * (G.chromaticNumber.toNat : ℤ) ≥ 17 := by linarith [s114, s115, s120, s121]
          have s123 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s122; omega
          have s124 : (G.edgeFinset.card : ℤ) ≥ 5 := by linarith [hn2]
          have s125 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc89; omega
          have s126 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s111]) (by linarith [s125])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s127 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s128 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s127, s125]
          have s129 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := turan_r2_int G (by linarith [s128])
            try push_cast at hw
            linarith [hw]
          have s130 : -(Fintype.card V : ℤ) ≥ -24 := by linarith [s117, s112, s118, s121]
          have s131 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s132 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s133 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s134 : -(G.maxDegree : ℤ) ≥ -8 := by linarith [s133, s118]
          have s135 : 2 * (Fintype.card V : ℤ) ≥ 3 := by linarith [s111, s112, s121]
          have s136 : (Fintype.card V : ℤ) ≥ 2 := by have hr := s135; omega
          have s137 : 8 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 16 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * (8 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s136]) (by linarith [s134])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s138 : 5 * (Fintype.card V : ℤ) ≥ 14 := by linarith [s131, s124, s132, s137]
          have s139 : (Fintype.card V : ℤ) ≥ 3 := by have hr := s138; omega
          have s140 : 27 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 72 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (24 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s139]) (by linarith [s130])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s141 : 27 * (Fintype.card V : ℤ) ≥ 92 := by linarith [s124, s129, s140]
          have s142 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s141; omega
          have s143 : 28 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 96 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (24 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s142]) (by linarith [s130])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s144 : 14 * (G.indepNum : ℤ) ≥ 29 := by linarith [s124, s115, s125, s126, s129, s143]
          have s145 : (G.indepNum : ℤ) ≥ 3 := by have hr := s144; omega
          have s146 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 25 := by linarith [s123, s145, s124]
          linarith [s146]
      linarith [s89]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
