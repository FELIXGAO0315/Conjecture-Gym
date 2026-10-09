import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C7 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hp2 : G.Connected) (hn1 : (G.maxDegree : ℤ) ≥ 2) (hn2 : (Fintype.card V : ℤ) ≤ 6) :
    (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.indepNum : ℤ) + 2 * (G.diam : ℤ) + 2 := by
  have s1 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.diam : ℤ) ≥ -2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s3 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := radius_le_diam_int G hp2
        linarith [hw]
      have s4 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := diam_le_two_radius_int G hp2
        linarith [hw]
      have s5 : 2 * (G.diam : ℤ) - (G.girth : ℤ) ≥ -1 := by
        have hw := girth_le_diam_int G hp2 hp1
        linarith [hw]
      have s6 : (G.girth : ℤ) ≥ 3 := by
        have hw := girth_ge_three_int G hp1
        linarith [hw]
      have s7 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s4, s5, s6]
      have s8 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s7; omega
      have s9 : -(Fintype.card V : ℤ) ≥ -6 := by linarith [hn2]
      have s10 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s11 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s10]
      have s12 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
        have hw := tau_le_card_sub_one_int G (by omega)
        linarith [hw]
      have s13 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        linarith [hw]
      have s14 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.diam : ℤ) ≥ -2 := by linarith [s2, s3, s8, s9, s12, s13]
      linarith [s14]
    · -- 1*chi <= 2
      have s15 : 2 * (G.diam : ℤ) - (G.girth : ℤ) ≥ -1 := by
        have hw := girth_le_diam_int G hp2 hp1
        linarith [hw]
      have s16 : (G.girth : ℤ) ≥ 3 := by
        have hw := girth_ge_three_int G hp1
        linarith [hw]
      have s17 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s18 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s19 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.diam : ℤ) ≥ 0 := by linarith [s15, s16, s17, s18]
      linarith [s19]
  linarith [s1]
