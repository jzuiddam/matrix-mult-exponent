import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 20 of 21: parents 123 <= t < 126 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK20 : Prop := forall t : Fin 126, 123 <= t.1 -> ClearedC5At t
instance : Decidable C5ShardK20 := by unfold C5ShardK20; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK20 : C5ShardK20 := by native_decide
end OmegaBound.ADVXXZT6Round82
