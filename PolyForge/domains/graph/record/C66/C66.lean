import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C66 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (Fintype.card V : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0) :
    (Fintype.card V : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s1, s2]
  have s4 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s7 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s1, s2, s5, s6]
  have s8 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by have hr := s7; omega
  have s9 : (Fintype.card V : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by linarith [s4, s8, s6]
  linarith [s9]
