import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 11 of 21: parents 90 <= t < 94 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK11 : Prop := forall t : Fin 126, 90 <= t.1 -> t.1 < 94 -> ClearedC5At t
instance : Decidable C5ShardK11 := by unfold C5ShardK11; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK11 : C5ShardK11 := by native_decide
end OmegaBound.ADVXXZT6Round82
