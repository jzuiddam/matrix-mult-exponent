import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 3 of 21: parents 43 <= t < 51 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK3 : Prop := forall t : Fin 126, 43 <= t.1 -> t.1 < 51 -> ClearedC5At t
instance : Decidable C5ShardK3 := by unfold C5ShardK3; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK3 : C5ShardK3 := by native_decide
end OmegaBound.ADVXXZT6Round82
