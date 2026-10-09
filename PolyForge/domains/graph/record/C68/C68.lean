import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C68 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) ≤ 0) :
    2 * (Fintype.card V : ℤ) ≥ -2 * (G.maxDegree : ℤ) + (G.vertexCoverNum.toNat : ℤ) + 8 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s4 : -(Fintype.card V : ℤ) + 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : 2 * (G.minDegree : ℤ) ≥ 3 := by linarith [s2, s3, s4]
  have s6 : (G.minDegree : ℤ) ≥ 2 := by have hr := s5; omega
  have s7 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s3]
  have s8 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s9 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int G (by omega)
    linarith [hw]
  have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s11 : 2 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 8 := by linarith [s1, s6, s8, s9, s10]
  linarith [s11]
