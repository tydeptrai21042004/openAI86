# V71 source map

| Paper result | Candidate | Module |
|---|---|---|
| Lemma 8.6 | OpenAI086.ReferenceV71.paper_chain_bound | PaperDensity.lean |
| Lemma 8.6 | Auto.ModeSystem.paper_chain_events_bound | PaperDensity.lean |
| Lemma 8.6 | Auto.ModeSystem.paper_chain_length_schedule | PaperDensity.lean |
| Sections 8.5, 10.3 | OpenAI086.ReferenceV71.rank_le_eleven_log | PaperDensity.lean |
| Sections 8.5, 10.3 | OpenAI086.ReferenceV71.paper_height_reserve | PaperDensity.lean |
| Lemma 8.6 | Auto.ModeSystem.paper_chain_length_valid | PaperDensity.lean |
| Section 9.1 | OpenAI086.ReferenceV71.paper_mode_masks | PaperMasks.lean |

Both modules are in external_main_theorem/v71. The runner `verify_v71.sh` prepares and replays the source tracks when requested by the user. It has not been executed for this release. See V71_PROGRESS.md for hypotheses and gaps.
