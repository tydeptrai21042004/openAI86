from verify_external import check_axioms, source, NAMES
name = NAMES[-1]
assert 'theorem Theorem1_1_Proved : Theorem1_1_Goal := by' in source()
assert check_axioms(f"'{name}' depends on axioms: [propext, Quot.sound, Classical.choice]",name) == ['Classical.choice','Quot.sound','propext']
assert check_axioms(f"'{name}' does not depend on any axioms",name) == []
for bad in ['','PASS',f"'{name}' depends on axioms: [sorryAx]",f"'{name}' depends on axioms: [Lean.ofReduceBool]",f"'Other.{name}' depends on axioms: [propext]",f"'{name}' depends on axioms: [propext]\n'{name}' depends on axioms: [propext]"]:
    try: check_axioms(bad,name)
    except ValueError: pass
    else: raise AssertionError(bad)
print('PASS: locked source generation and 8 axiom-report cases')
