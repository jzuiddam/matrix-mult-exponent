import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 1 of 21: parents 22 <= t < 34 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK1 : Prop := forall t : Fin 126, 22 <= t.1 -> t.1 < 34 -> ClearedC5At t
instance : Decidable C5ShardK1 := by unfold C5ShardK1; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK1 : C5ShardK1 := by native_decide
end OmegaBound.ADVXXZT6Round82
