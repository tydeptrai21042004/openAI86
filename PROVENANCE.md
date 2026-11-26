# Independent code provenance

The independent root `OpenAI086` contains newly authored source for this
project, depending on Mathlib but **not** `TrilinearHT` or code adapted from
its published proof of Lemma 3.3.  The older `Lemma33Reviewed.lean` adapted
third-party code, so it has been **excluded** from this independent version.
It remains available in the earlier project ZIP supplied during this chat.

Mathematical ideas are from the user's October 5, 2026 93-page source paper.
Independence of Lean source does not mean the main paper has been proved.
The work is currently an independent partial formalization and is not
kernel-checked in this runtime.

## V56 separate source-fidelity track

`source_fidelity/v56/EntryRank.lean` contains an explicitly attributed adaptation from Joris Roos's `lean-trilinearht` commit `7b4209609e6a7fb9d9935973ee8541495f943660`, Apache-2.0, original file `TrilinearHT/Auto/Sec13_3BesselRowsLinearSideEnergy.lean`. The standalone file is not imported by `OpenAI086.lean`. `OpenAI086/PaperV56Lemma32.lean` and `OpenAI086/PaperV56ExceptionalBlocks.lean` extend the local candidate library. The reference crosswalk is a source-navigation aid, not proof certification.

## V60 consolidated release

The exact user-supplied reference archive is bundled under `reference_snapshot/` with its original Apache-2.0 license. The independent source tree is unchanged by consolidation; the attributed `source_fidelity/` and `external_main_theorem/` tracks remain separate. `final_source/FinalMain.lean` exports the existing reference-backed candidates, not a new independent proof. The replay script never upgrades the whole-paper certification status.
