# V73 source map

All new declarations are uncompiled candidates.

| Module | Declaration |
|---|---|
| `PaperGlobalEnergy.lean` | `Auto.ModeSystem.paper_class_count` |
| `PaperGlobalEnergy.lean` | `Auto.ModeSystem.paper_group_count` |
| `PaperGlobalEnergy.lean` | `Auto.ModeSystem.paper_side_errors_negligible` |
| `PaperGlobalEnergy.lean` | `Auto.ActiveSetup.BasicFamilies.FamParams.paper_linear_energy` |
| `PaperRollingEnergy.lean` | `Auto.ActiveSetup.BasicFamilies.FamParams.paperSideState` (definition) |
| `PaperRollingEnergy.lean` | `Auto.ActiveSetup.BasicFamilies.FamParams.paper_sideState_budget` |
| `PaperRollingEnergy.lean` | `Auto.ActiveSetup.BasicFamilies.FamParams.paper_sideState_budget_blocks` |
| `PaperRollingEnergy.lean` | `Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperSideAt_eq_restrict_state` |

Run `bash verify_v73.sh --work-dir /tmp/openai086-v73-check` locally if desired. The runner has been extended to include the new files and their imported Lake libraries; it has not been executed in this revision.
