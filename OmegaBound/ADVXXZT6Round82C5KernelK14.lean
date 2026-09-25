import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 14 of 21: parents 102 <= t < 106 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK14 : Prop := forall t : Fin 126, 102 <= t.1 -> t.1 < 106 -> ClearedC5At t
instance : Decidable C5ShardK14 := by unfold C5ShardK14; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK14 : C5ShardK14 := by native_decide
end OmegaBound.ADVXXZT6Round82
