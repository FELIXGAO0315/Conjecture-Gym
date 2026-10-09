import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C52 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsEdgeConnected 3) (hp2 : ¬ G.IsAcyclic) (hn1 : (G.minDegree : ℤ) ≤ 5) (hn2 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.girth : ℤ) ≤ 0) :
    (G.chromaticNumber.toNat : ℤ) ≤ (G.indepNum : ℤ) + 2 * (G.girth : ℤ) - 1 := by
  have s1 : -(G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) + 2 * (G.girth : ℤ) ≥ 1 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s3]
      have s5 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int G (by omega)
        linarith [hw]
      have s6 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.girth : ℤ) ≥ 0 := by linarith [hn2]
      have s7 : -(G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) + 2 * (G.girth : ℤ) ≥ 1 := by linarith [s5, s6]
      linarith [s7]
    · -- 1*chi <= 2
      have s8 : (G.girth : ℤ) ≥ 3 := by
        have hw := girth_ge_three_int G hp2
        linarith [hw]
      have s9 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s10 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s11 : -(G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) + 2 * (G.girth : ℤ) ≥ 4 := by linarith [s8, s9, s10]
      linarith [s11]
  linarith [s1]
