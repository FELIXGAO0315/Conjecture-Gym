import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C110 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.maxDegree : ℤ) ≤ 5) (hn2 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0) :
    -(Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) ≤ 4 := by
  have s1 : (Fintype.card V : ℤ) - 2 * (G.maxDegree : ℤ) ≥ -4 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [hn1]
      have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s3, s4]
      have s6 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int G (by omega)
        linarith [hw]
      have s7 : (Fintype.card V : ℤ) - 2 * (G.maxDegree : ℤ) ≥ -4 := by linarith [s2, s6]
      linarith [s7]
    · -- 1*chi <= 2
      have s8 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s9 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s10 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s11 : (Fintype.card V : ℤ) - 2 * (G.maxDegree : ℤ) ≥ -2 := by linarith [s8, s9, s10]
      linarith [s11]
  linarith [s1]
