# V64 new source declarations

| Paper result | Lean declaration | Source-level status |
|---|---|---|
| Lemma 3.4 | `OpenAI086.ReferenceV64.weighted_row_average` | Dependent row Bochner inequality; candidate |
| Lemma 3.4 | `OpenAI086.ReferenceV64.lemma34_average` | Applies reference compression to averaged products; candidate |
| Lemma 8.2 | `OpenAI086.SourceV64.exceptional_log_window` | Actual radii to log-window; candidate |
| Lemma 8.2 | `OpenAI086.SourceV64.actual_exceptional_count` | Actual filtered K-spaced schedule; candidate |
| Lemma 3.5 / 8.2 | `OpenAI086.ReferenceV64.height_value_iff` | Rational-height correspondence; candidate |
| Lemma 8.2 | `OpenAI086.ReferenceV64.exceptional_iff` | Predicate correspondence; candidate |
| Lemma 8.2 | `OpenAI086.ReferenceV64.paper_tiny_closure` | Closure with explicit numerical separation premise; candidate |

Source only. No new Lean compilation. Existing independent source and reference archive unchanged. The source correspondence and gap-size premise must still be established where the original parameter choices are used. See `V64_PROGRESS.md`.
