import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 4 of 21: parents 51 <= t < 58 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK4 : Prop := forall t : Fin 126, 51 <= t.1 -> t.1 < 58 -> ClearedC5At t
instance : Decidable C5ShardK4 := by unfold C5ShardK4; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK4 : C5ShardK4 := by native_decide
end OmegaBound.ADVXXZT6Round82
