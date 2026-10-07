#!/usr/bin/env bash
# Run only between build and cache steps on a disposable hosted runner.
set -euo pipefail
if [[ ${GITHUB_ACTIONS:-} != true || ${RUNNER_ENVIRONMENT:-} != github-hosted || ${RUNNER_OS:-} != Linux ]]; then
  echo "Refusing process cleanup outside a GitHub-hosted Linux runner." >&2
  exit 1
fi
# Stop the scheduler first so it cannot launch another writer during cleanup.
pkill -KILL -x lake || [[ $? == 1 ]]
pkill -TERM -x lean || [[ $? == 1 ]]
for ((attempt = 0; attempt < 20; attempt++)); do
  if ! pgrep -x lean >/dev/null; then
    echo "Lean workers stopped; cache files are no longer being written."
    exit 0
  fi
  sleep 1
done
pkill -KILL -x lean || [[ $? == 1 ]]
for ((attempt = 0; attempt < 10; attempt++)); do
  if ! pgrep -x lean >/dev/null; then
    echo "Lean workers stopped after forced termination."
    exit 0
  fi
  sleep 1
done
echo "Lean workers remain; refusing to archive a changing build tree." >&2
exit 1
