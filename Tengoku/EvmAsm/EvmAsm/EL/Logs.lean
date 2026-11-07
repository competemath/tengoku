/-
  EvmAsm.EL.Logs

  Pure LOG0-LOG4 event surface for GH #112.
-/

module

public import Tengoku.EvmAsm.EvmAsm.EL.WorldState

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace EvmAsm.EL

/-- A LOG topic is a full 256-bit EVM word.-/
abbrev LogTopic := Word256

/-- One EVM log entry emitted by LOG0 through LOG4.-/
structure LogEntry where
  emitter : Address
  topics : List LogTopic
  data : List Byte
  deriving Repr

namespace LogEntry

/-- Topic-count validity for LOG0 through LOG4.-/
def topicCountOk (entry : LogEntry) : Prop :=
  entry.topics.length ≤ 4

/-- Construct a log entry when the caller already has the concrete topics/data.-/
def mkChecked (emitter : Address) (topics : List LogTopic) (data : List Byte) : LogEntry :=
  { emitter := emitter, topics := topics, data := data }

/--
@isnad1 id=iff.0h1v.s4.3de59f052918 from=translated src=- shape=0932e97e vocab=3540b621
-/
theorem topicCountOk_iff (entry : LogEntry) :
    entry.topicCountOk ↔ entry.topics.length ≤ 4 := Iff.rfl

/--
@isnad1 id=topiccou.0h2v.s3.5d6100d535a1 from=translated src=- shape=5c8c86e4 vocab=718cbcd2
-/
theorem topicCountOk_nil (emitter : Address) (data : List Byte) :
    (mkChecked emitter [] data).topicCountOk := by
  simp [topicCountOk, mkChecked]

/--
@isnad1 id=topiccou.0h3v.s4.e4fe2859c573 from=translated src=- shape=3ff63240 vocab=8be9ef6d
-/
theorem topicCountOk_single (emitter : Address) (topic : LogTopic) (data : List Byte) :
    (mkChecked emitter [topic] data).topicCountOk := by
  simp [topicCountOk, mkChecked]

/--
@isnad1 id=topiccou.0h4v.s4.76b72cc4189d from=translated src=- shape=a2704766 vocab=8be9ef6d
-/
theorem topicCountOk_two
    (emitter : Address) (topic0 topic1 : LogTopic) (data : List Byte) :
    (mkChecked emitter [topic0, topic1] data).topicCountOk := by
  simp [topicCountOk, mkChecked]

/--
@isnad1 id=topiccou.0h5v.s4.d50e1e35e47f from=translated src=- shape=77d792df vocab=8be9ef6d
-/
theorem topicCountOk_three
    (emitter : Address) (topic0 topic1 topic2 : LogTopic) (data : List Byte) :
    (mkChecked emitter [topic0, topic1, topic2] data).topicCountOk := by
  simp [topicCountOk, mkChecked]

/--
@isnad1 id=topiccou.0h6v.s4.911ed8db7e29 from=translated src=- shape=f8d8eb69 vocab=8be9ef6d
-/
theorem topicCountOk_four
    (emitter : Address) (topic0 topic1 topic2 topic3 : LogTopic) (data : List Byte) :
    (mkChecked emitter [topic0, topic1, topic2, topic3] data).topicCountOk := by
  simp [topicCountOk, mkChecked]

end LogEntry

/-- Append-only sequence of EVM log entries accumulated during execution.-/
structure LogState where
  entries : List LogEntry
  deriving Repr

namespace LogState

def empty : LogState :=
  { entries := [] }

/-- Append one log entry to the end of the execution log.-/
def appendLog (logs : LogState) (entry : LogEntry) : LogState :=
  { entries := logs.entries ++ [entry] }

/--
@isnad1 id=eq.0h0v.s2.f9889c0337c7 from=translated src=- shape=0a817633 vocab=05591ab2
-/
@[simp] theorem entries_empty : empty.entries = [] := rfl

/--
@isnad1 id=eq.0h2v.s4.6bd1311322d3 from=translated src=- shape=78c7caf6 vocab=d6048996
-/
@[simp] theorem entries_appendLog (logs : LogState) (entry : LogEntry) :
    (appendLog logs entry).entries = logs.entries ++ [entry] := rfl

/--
@isnad1 id=eq.0h2v.s4.c2e9ab9767f0 from=translated src=- shape=952659f3 vocab=4df0c6d5
-/
theorem length_appendLog (logs : LogState) (entry : LogEntry) :
    (appendLog logs entry).entries.length = logs.entries.length + 1 := by
  simp [appendLog]

/--
@isnad1 id=eq.0h1v.s3.88936d131597 from=translated src=- shape=9c45f4ee vocab=d4b95815
-/
theorem appendLog_empty_entries (entry : LogEntry) :
    (appendLog empty entry).entries = [entry] := rfl

/--
@isnad1 id=topiccou.1h2v.s3.2d0cb4fa4f82 from=translated src=- shape=51d59715 vocab=d48b6087
-/
theorem appended_log_topicCountOk
    (logs : LogState) {entry : LogEntry} (h_topics : entry.topicCountOk) :
    (appendLog logs entry).entries.getLast (by simp [appendLog]) |>.topicCountOk := by
  simpa [appendLog] using h_topics

end LogState

end EvmAsm.EL
