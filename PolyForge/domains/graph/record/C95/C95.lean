import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C95 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : -2 * (G.vertexCoverNum.toNat : ℤ) + 2 * (G.girth : ℤ) ≥ 0) (hn2 : (G.minDegree : ℤ) - (G.indepNum : ℤ) ≥ 0) :
    -(G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.girth : ℤ) ≥ 4 := by
  have s1 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.girth : ℤ) ≥ 4 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s3 : (G.girth : ℤ) ≥ 3 := by
        have hw := girth_ge_three_int G hp1
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s4]
      have s6 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int G (by omega)
        linarith [hw]
      have s7 : -2 * (G.vertexCoverNum.toNat : ℤ) + 2 * (G.girth : ℤ) ≥ 0 := by linarith [hn1]
      have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        linarith [hw]
      have s9 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.girth : ℤ) ≥ 4 := by linarith [s2, s3, s6, s7, s8]
      linarith [s9]
    · -- 1*chi <= 2
      have s10 : (G.girth : ℤ) ≥ 3 := by
        have hw := girth_ge_three_int G hp1
        linarith [hw]
      have s11 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s12 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s13 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.girth : ℤ) ≥ 4 := by linarith [s10, s11, s12]
      linarith [s13]
  linarith [s1]
