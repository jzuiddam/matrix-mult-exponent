import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 15 of 21: parents 106 <= t < 110 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK15 : Prop := forall t : Fin 126, 106 <= t.1 -> t.1 < 110 -> ClearedC5At t
instance : Decidable C5ShardK15 := by unfold C5ShardK15; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK15 : C5ShardK15 := by native_decide
end OmegaBound.ADVXXZT6Round82
