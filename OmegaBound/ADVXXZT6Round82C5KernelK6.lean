import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 6 of 21: parents 64 <= t < 70 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK6 : Prop := forall t : Fin 126, 64 <= t.1 -> t.1 < 70 -> ClearedC5At t
instance : Decidable C5ShardK6 := by unfold C5ShardK6; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK6 : C5ShardK6 := by native_decide
end OmegaBound.ADVXXZT6Round82
