import OmegaBound.ADVXXZT6Round82C5KernelK0
import OmegaBound.ADVXXZT6Round82C5KernelK1
import OmegaBound.ADVXXZT6Round82C5KernelK2
import OmegaBound.ADVXXZT6Round82C5KernelK3
import OmegaBound.ADVXXZT6Round82C5KernelK4
import OmegaBound.ADVXXZT6Round82C5KernelK5
import OmegaBound.ADVXXZT6Round82C5KernelK6
import OmegaBound.ADVXXZT6Round82C5KernelK7
import OmegaBound.ADVXXZT6Round82C5KernelK8
import OmegaBound.ADVXXZT6Round82C5KernelK9
import OmegaBound.ADVXXZT6Round82C5KernelK10
import OmegaBound.ADVXXZT6Round82C5KernelK11
import OmegaBound.ADVXXZT6Round82C5KernelK12
import OmegaBound.ADVXXZT6Round82C5KernelK13
import OmegaBound.ADVXXZT6Round82C5KernelK14
import OmegaBound.ADVXXZT6Round82C5KernelK15
import OmegaBound.ADVXXZT6Round82C5KernelK16
import OmegaBound.ADVXXZT6Round82C5KernelK17
import OmegaBound.ADVXXZT6Round82C5KernelK18
import OmegaBound.ADVXXZT6Round82C5KernelK19
import OmegaBound.ADVXXZT6Round82C5KernelK20
namespace OmegaBound.ADVXXZT6Round82
/-- All 126 parents and all three physical rows, assembled from 21 equal-cost cleared-integer shards. -/
theorem released_cleared_C5 (t : Fin 126) : ClearedC5At t := by
  by_cases h0 : t.1 < 22
  · exact c5ShardK0 t h0
  by_cases h1 : t.1 < 34
  · exact c5ShardK1 t (by omega) h1
  by_cases h2 : t.1 < 43
  · exact c5ShardK2 t (by omega) h2
  by_cases h3 : t.1 < 51
  · exact c5ShardK3 t (by omega) h3
  by_cases h4 : t.1 < 58
  · exact c5ShardK4 t (by omega) h4
  by_cases h5 : t.1 < 64
  · exact c5ShardK5 t (by omega) h5
  by_cases h6 : t.1 < 70
  · exact c5ShardK6 t (by omega) h6
  by_cases h7 : t.1 < 75
  · exact c5ShardK7 t (by omega) h7
  by_cases h8 : t.1 < 80
  · exact c5ShardK8 t (by omega) h8
  by_cases h9 : t.1 < 85
  · exact c5ShardK9 t (by omega) h9
  by_cases h10 : t.1 < 90
  · exact c5ShardK10 t (by omega) h10
  by_cases h11 : t.1 < 94
  · exact c5ShardK11 t (by omega) h11
  by_cases h12 : t.1 < 98
  · exact c5ShardK12 t (by omega) h12
  by_cases h13 : t.1 < 102
  · exact c5ShardK13 t (by omega) h13
  by_cases h14 : t.1 < 106
  · exact c5ShardK14 t (by omega) h14
  by_cases h15 : t.1 < 110
  · exact c5ShardK15 t (by omega) h15
  by_cases h16 : t.1 < 114
  · exact c5ShardK16 t (by omega) h16
  by_cases h17 : t.1 < 117
  · exact c5ShardK17 t (by omega) h17
  by_cases h18 : t.1 < 120
  · exact c5ShardK18 t (by omega) h18
  by_cases h19 : t.1 < 123
  · exact c5ShardK19 t (by omega) h19
  · exact c5ShardK20 t (by omega)
end OmegaBound.ADVXXZT6Round82
