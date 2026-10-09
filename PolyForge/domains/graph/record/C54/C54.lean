import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C54 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≤ 0) (hn2 : (G.chromaticNumber.toNat : ℤ) ≤ 4) :
    (G.minDegree : ℤ) ≤ 2 * (Fintype.card V : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) - 8 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s3]
  have s5 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s6 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s3, s5]
  have s7 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by have hr := s6; omega
  have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int G (by omega)
    linarith [hw]
  have s9 : 2 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 8 := by linarith [s1, s4, s7, s8]
  linarith [s9]
