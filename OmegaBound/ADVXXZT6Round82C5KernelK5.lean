import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 5 of 21: parents 58 <= t < 64 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK5 : Prop := forall t : Fin 126, 58 <= t.1 -> t.1 < 64 -> ClearedC5At t
instance : Decidable C5ShardK5 := by unfold C5ShardK5; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK5 : C5ShardK5 := by native_decide
end OmegaBound.ADVXXZT6Round82
