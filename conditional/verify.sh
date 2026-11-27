#!/bin/bash
# Immunization 6-check for R2125608282 (heilbronn RUNBOOK pattern + corpus byte-exactness):
#  1. lake build green            2. zero sorry
#  3. axioms exactly 3            4. -DautoImplicit=false clean
#  5. statement byte-exact vs corpus target (sha256)
#  6. bare-import audit dry-run (import + axioms print, NO opens)
set -u
cd "$(dirname "$0")"
TARGET=target/SnakyConditional.lean
ENTRY=OAI.SnakyConditional.snaky_winning_strategy_with_legal_states
FAIL=0

echo "== check 2: zero sorry"
if grep -rn 'sorry' Submission --include='*.lean' | grep -v 'Padding.lean:.*--' ; then echo "FAIL: sorry present"; FAIL=1; else echo "OK: no sorry"; fi

echo "== check 1: lake build"
lake build Submission.SnakyConditional > logs_verify_build.txt 2>&1
rc=$?
echo "build exit=$rc"
[ $rc -eq 0 ] || { echo "FAIL: build"; tail -20 logs_verify_build.txt; FAIL=1; }

echo "== check 3+4+6: independent replay (axioms + autoImplicit=false + bare-import dry-run)"
lake env lean -DautoImplicit=false AxiomCheck.lean > logs_axioms.txt 2>&1
rc=$?
echo "replay exit=$rc"; cat logs_axioms.txt
got=$(tr '\n' ' ' < logs_axioms.txt | sed 's/.*depends on axioms: \[\([^]]*\)\].*/\1/' | tr ',' '\n' | tr -d ' ' | grep -v '^$' | LC_ALL=C sort | tr '\n' ',')
want="Classical.choice,Quot.sound,propext,"
if [ "$got" = "$want" ]; then echo "OK: axioms exactly {propext, Classical.choice, Quot.sound}"; else echo "FAIL: axiom set = [$got]"; FAIL=1; fi
[ $rc -eq 0 ] || FAIL=1
# bare-import audit: AxiomCheck must carry no `open` (import + axioms print only)
if grep -qE '^\s*open\b' AxiomCheck.lean; then echo "FAIL: AxiomCheck uses open (not a bare-import audit)"; FAIL=1; else echo "OK: bare-import audit (no opens)"; fi

echo "== check 5: statement byte-exact vs corpus target (sha256)"
# extract the theorem statement region (from the theorem line to the ':= by' line) from both
extract_stmt() { awk '/^theorem snaky_winning_strategy_with_legal_states/{p=1} p{print} /:= by$/{if(p) exit}' "$1"; }
extract_stmt "$TARGET"   > /tmp/snaky35/stmt_target.txt
extract_stmt Submission/SnakyConditional.lean > /tmp/snaky35/stmt_mine.txt
h1=$(shasum -a 256 /tmp/snaky35/stmt_target.txt | awk '{print $1}')
h2=$(shasum -a 256 /tmp/snaky35/stmt_mine.txt   | awk '{print $1}')
echo "target stmt sha: $h1"
echo "mine   stmt sha: $h2"
if [ "$h1" = "$h2" ]; then echo "OK: theorem statement byte-exact"; else echo "FAIL: statement differs"; diff /tmp/snaky35/stmt_target.txt /tmp/snaky35/stmt_mine.txt; FAIL=1; fi

echo "== verdict: $([ $FAIL -eq 0 ] && echo GREEN 6/6 || echo RED)"
exit $FAIL
