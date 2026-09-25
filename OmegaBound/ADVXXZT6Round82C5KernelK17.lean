import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 17 of 21: parents 114 <= t < 117 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK17 : Prop := forall t : Fin 126, 114 <= t.1 -> t.1 < 117 -> ClearedC5At t
instance : Decidable C5ShardK17 := by unfold C5ShardK17; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK17 : C5ShardK17 := by native_decide
end OmegaBound.ADVXXZT6Round82
