import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 0 of 21: parents 0 <= t < 22 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK0 : Prop := forall t : Fin 126, t.1 < 22 -> ClearedC5At t
instance : Decidable C5ShardK0 := by unfold C5ShardK0; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK0 : C5ShardK0 := by native_decide
end OmegaBound.ADVXXZT6Round82
