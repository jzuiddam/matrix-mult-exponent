import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 16 of 21: parents 110 <= t < 114 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK16 : Prop := forall t : Fin 126, 110 <= t.1 -> t.1 < 114 -> ClearedC5At t
instance : Decidable C5ShardK16 := by unfold C5ShardK16; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK16 : C5ShardK16 := by native_decide
end OmegaBound.ADVXXZT6Round82
