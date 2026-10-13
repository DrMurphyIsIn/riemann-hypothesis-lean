"""The cron-only classifier and verdicts behind .github/workflows/ci-schedule-health.yml.

A workflow that GitHub can only start on a schedule has nothing watching it: on
2026-09-25 `telperion-legacy-boxes` had been red for four days and
`telperion-zeta-reflection`'s weekly cron had never fired once, and both were invisible.
The classifier decides which workflows are in that position; the verdicts decide what to
say about each.  Both are tested on fixtures rather than on the repository's own
workflows, so the tests keep their meaning as triggers legitimately change.
"""
from pathlib import Path

import pytest

yaml = pytest.importorskip("yaml")

import importlib.util

_SRC = Path(__file__).resolve().parents[1] / "scripts" / "schedule_health.py"
_spec = importlib.util.spec_from_file_location("schedule_health", _SRC)
sh = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(sh)


CRON_ONLY = """
name: w
on:
  workflow_dispatch:
  schedule:
    - cron: "17 3 * * 1"
jobs: {j: {runs-on: ubuntu-latest, steps: [{run: "true"}]}}
"""

CRON_PLUS_PUSH_MAIN = """
name: w
on:
  schedule:
    - cron: "17 3 * * 1"
  push:
    branches: [main]
    paths: ["telperion/**"]
jobs: {j: {runs-on: ubuntu-latest, steps: [{run: "true"}]}}
"""

CRON_PLUS_PUSH_OTHER_BRANCH = """
name: w
on:
  schedule:
    - cron: "17 3 * * 1"
  push:
    branches: [dev]
jobs: {j: {runs-on: ubuntu-latest, steps: [{run: "true"}]}}
"""

CRON_PLUS_UNFILTERED_PUSH = """
name: w
on:
  schedule:
    - cron: "17 3 * * 1"
  push:
jobs: {j: {runs-on: ubuntu-latest, steps: [{run: "true"}]}}
"""

PR_ONLY = """
name: w
on:
  pull_request:
jobs: {j: {runs-on: ubuntu-latest, steps: [{run: "true"}]}}
"""


@pytest.mark.parametrize("text,has_schedule,cron_only", [
    (CRON_ONLY, True, True),
    (CRON_PLUS_PUSH_MAIN, True, False),
    (CRON_PLUS_PUSH_OTHER_BRANCH, True, True),     # push exists but never on main
    (CRON_PLUS_UNFILTERED_PUSH, True, False),      # `push:` with no filter covers main
    (PR_ONLY, False, False),
])
def test_classify(text, has_schedule, cron_only):
    assert sh.classify(text) == (has_schedule, cron_only)


def test_pull_request_does_not_count_as_watching_main():
    """A PR run verifies the merge ref BEFORE the merge; it never re-verifies main after."""
    text = PR_ONLY.replace("  pull_request:\n",
                           '  pull_request:\n  schedule:\n    - cron: "17 3 * * 1"\n')
    assert sh.classify(text) == (True, True)


def test_cron_only_workflows_scans_a_directory(tmp_path):
    d = tmp_path / "workflows"
    d.mkdir()
    (d / "lonely.yml").write_text(CRON_ONLY)
    (d / "watched.yml").write_text(CRON_PLUS_PUSH_MAIN)
    (d / "prs.yml").write_text(PR_ONLY)
    assert sh.cron_only_workflows(d) == ["lonely.yml"]


def test_verdict_fails_on_a_red_latest_run():
    v, msg = sh.verdict("w.yml", {"last": {"conclusion": "failure", "created_at": "2026-09-21T08:57:00Z",
                                           "html_url": "u"},
                                  "last_scheduled": {"conclusion": "failure"}})
    assert v == sh.FAIL and "FAILED" in msg


def test_verdict_warns_when_no_schedule_ever_fired():
    """The zeta-reflection case: the cron was in place, GitHub simply never ran it."""
    v, msg = sh.verdict("w.yml", {"last": {"conclusion": "success"}, "last_scheduled": None})
    assert v == sh.WARN and "no scheduled run has ever happened" in msg


def test_verdict_warns_on_a_red_scheduled_run_even_if_a_later_manual_run_passed():
    v, _ = sh.verdict("w.yml", {"last": {"conclusion": "success"},
                                "last_scheduled": {"conclusion": "cancelled",
                                                   "created_at": "2026-09-21T08:57:00Z"}})
    assert v == sh.WARN


def test_verdict_ok():
    v, _ = sh.verdict("w.yml", {"last": {"conclusion": "success"},
                                "last_scheduled": {"conclusion": "success",
                                                   "created_at": "2026-09-22T03:17:00Z"}})
    assert v == sh.OK


def test_missing_run_data_is_not_silently_ok():
    """No history for a cron-only workflow must never read as healthy."""
    v, _ = sh.verdict("w.yml", {})
    assert v == sh.WARN


def test_report_exit_code_and_lines(tmp_path):
    d = tmp_path / "workflows"
    d.mkdir()
    (d / "red.yml").write_text(CRON_ONLY)
    (d / "fine.yml").write_text(CRON_PLUS_PUSH_MAIN)
    code, lines = sh.report(d, {"red.yml": {"last": {"conclusion": "failure"},
                                            "last_scheduled": {"conclusion": "failure"}}})
    assert code == 1
    assert any("[FAIL]" in ln and "red.yml" in ln for ln in lines)
    assert not any("fine.yml" in ln for ln in lines)


def test_report_says_so_when_nothing_is_cron_only(tmp_path):
    d = tmp_path / "workflows"
    d.mkdir()
    (d / "fine.yml").write_text(CRON_PLUS_PUSH_MAIN)
    code, lines = sh.report(d, {})
    assert code == 0 and "No cron-only workflows" in lines[0]


def test_the_watch_workflow_itself_is_not_cron_only():
    """Otherwise the watcher would be the next thing nobody watches."""
    wf = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "ci-schedule-health.yml"
    assert wf.exists(), "the watch workflow is missing"
    has_schedule, cron_only = sh.classify(wf.read_text())
    assert has_schedule and not cron_only
