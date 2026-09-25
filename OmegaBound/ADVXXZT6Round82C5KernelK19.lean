import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 19 of 21: parents 120 <= t < 123 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK19 : Prop := forall t : Fin 126, 120 <= t.1 -> t.1 < 123 -> ClearedC5At t
instance : Decidable C5ShardK19 := by unfold C5ShardK19; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK19 : C5ShardK19 := by native_decide
end OmegaBound.ADVXXZT6Round82
