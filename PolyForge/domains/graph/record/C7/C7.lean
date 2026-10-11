import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C7 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.Connected) (hn1 : (G.maxDegree : ℤ) ≥ 3) (hn2 : (G.minDegree : ℤ) ≥ 2 * (G.indepNum : ℤ)) :
    (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.maxDegree : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) - 8 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    linarith [hw]
  have s3 : (G.maxDegree : ℤ) ≥ 3 := by linarith [hn1]
  have s4 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    linarith [hw]
  have s5 : (G.minDegree : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn2]
  have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s7 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 5 := by linarith [s2, s4, s3, s5, s6]
  have s8 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by have hr := s7; omega
  have s9 : 4 * (G.maxDegree : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) + 4 * (G.vertexCoverNum.toNat : ℤ) ≥ 15 := by linarith [s1, s2, s3, s8, s5, s6]
  have s10 : 2 * (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 8 := by have hr := s9; omega
  linarith [s10]
