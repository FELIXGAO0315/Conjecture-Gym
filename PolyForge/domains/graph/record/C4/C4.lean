import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C4 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.chromaticNumber.toNat : ℤ) ≥ 2 * (G.indepNum : ℤ)) :
    2 * (G.vertexCoverNum.toNat : ℤ) ≥ (Fintype.card V : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) + 7 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s3 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s5 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s2, s1, s3, s4]
  have s6 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by have hr := s5; omega
  have s7 : -2 * (Fintype.card V : ℤ) + 4 * (G.chromaticNumber.toNat : ℤ) + 4 * (G.vertexCoverNum.toNat : ℤ) ≥ 13 := by linarith [s1, s6, s3, s4]
  have s8 : -(Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by have hr := s7; omega
  linarith [s8]
