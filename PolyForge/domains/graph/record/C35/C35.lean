import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C35 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 6) :
    2 * (G.chromaticNumber.toNat : ℤ) ≤ (Fintype.card V : ℤ) + 2 * (G.indepNum : ℤ) + 5 := by
  have s1 : (Fintype.card V : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ -5 := by
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
      have s6 : -(G.vertexCoverNum.toNat : ℤ) ≥ -6 := by linarith [hn1]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        linarith [hw]
      have s8 : (Fintype.card V : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ -5 := by linarith [s2, s5, s6, s7]
      linarith [s8]
    · -- 1*chi <= 2
      have s9 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s10 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s12 : (Fintype.card V : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ -2 := by linarith [s9, s10, s11]
      linarith [s12]
  linarith [s1]
