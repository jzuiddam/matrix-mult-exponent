import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 7 of 21: parents 70 <= t < 75 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK7 : Prop := forall t : Fin 126, 70 <= t.1 -> t.1 < 75 -> ClearedC5At t
instance : Decidable C5ShardK7 := by unfold C5ShardK7; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK7 : C5ShardK7 := by native_decide
end OmegaBound.ADVXXZT6Round82
