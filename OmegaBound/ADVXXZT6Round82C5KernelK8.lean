import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 8 of 21: parents 75 <= t < 80 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK8 : Prop := forall t : Fin 126, 75 <= t.1 -> t.1 < 80 -> ClearedC5At t
instance : Decidable C5ShardK8 := by unfold C5ShardK8; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK8 : C5ShardK8 := by native_decide
end OmegaBound.ADVXXZT6Round82
