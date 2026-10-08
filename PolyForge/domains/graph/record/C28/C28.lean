import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C28 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : G.IsTree) (hn1 : -2 * (G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) ≥ 0) :
    2 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≤ -1 := by
  have s1 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s2 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp2
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s1, s2]
  have s4 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s6 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int G (by omega)
    linarith [hw]
  have s7 : -2 * (G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
  have s8 : -2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ -1 := by linarith [s5, s6, s7, s2]
  have s9 : -(G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by have hr := s8; omega
  have s10 : -2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ 1 := by linarith [s4, s9]
  linarith [s10]
