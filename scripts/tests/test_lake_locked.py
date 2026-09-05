#!/usr/bin/env python3
"""Exercise checkout-lock heartbeats without using Lean or real machine slots."""

import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile
import threading
import time
import unittest

WRAPPER = Path(os.environ.get(
    "LAKE_WRAPPER_UNDER_TEST", Path(__file__).resolve().parents[1] / "lake-locked.sh"
)).resolve()


def eventually(predicate, timeout=20):
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if predicate():
            return
        time.sleep(0.1)
    raise AssertionError("Timed out waiting for test process state")


class WaitingCheckoutHeartbeat(unittest.TestCase):
    def test_waiting_checkout_stays_owned_and_serialized(self):
        with tempfile.TemporaryDirectory(prefix="lake-lock-test-") as tmp:
            root = Path(tmp)
            checkout = root / "checkout"
            checkout.mkdir()
            subprocess.run(["git", "init", "-q", str(checkout)], check=True)
            binaries = root / "bin"
            binaries.mkdir()
            fake_lake = binaries / "lake"
            fake_lake.write_text('''#!/usr/bin/env python3
import os
from pathlib import Path
import sys
import time
root = Path(os.environ["FAKE_LAKE_STATE"])
role = sys.argv[-1]
active = root / "active"
try:
    active.mkdir()
except FileExistsError:
    (root / "overlap").touch()
    sys.exit(2)
(root / (role + ".started")).touch()
while not (root / (role + ".release")).exists():
    time.sleep(0.1)
active.rmdir()
''')
            fake_lake.chmod(0o755)
            slots = root / "slots"
            occupied = [slots / "slot-1", slots / "slot-2"]
            for slot in occupied:
                slot.mkdir(parents=True)
                (slot / "owner").write_text(f"{os.getpid()} test holder\n")
            stop_holder = threading.Event()

            def refresh_holder():
                while not stop_holder.is_set():
                    for slot in occupied:
                        pending = slot / "heartbeat.test"
                        pending.write_text(str(int(time.time())))
                        pending.replace(slot / "heartbeat")
                    stop_holder.wait(0.2)

            holder = threading.Thread(target=refresh_holder)
            holder.start()
            env = {
                **os.environ,
                "PATH": str(binaries) + os.pathsep + os.environ["PATH"],
                "FAKE_LAKE_STATE": str(root),
                "LAKE_LOCKED_DISABLE": "0",
                "LAKE_LOCKED_SLOTS": "2",
                "LAKE_LOCKED_SLOT_DIR": str(slots),
                "LAKE_LOCKED_STALE_SECS": "2",
                "LAKE_LOCKED_HEARTBEAT_SECS": "1",
                "LAKE_LOCKED_TIMEOUT_SECS": "30",
            }
            processes = []
            logs = []

            def launch(role):
                log = (root / (role + ".log")).open("w")
                logs.append(log)
                process = subprocess.Popen(
                    ["bash", str(WRAPPER), "build", role], cwd=checkout, env=env,
                    stdout=log, stderr=subprocess.STDOUT, start_new_session=True,
                )
                processes.append(process)
                return process

            lock = checkout / ".lake" / "agent-build.lock"
            try:
                first = launch("first")
                eventually(lambda: (lock / "owner").exists())
                self.assertEqual(int((lock / "owner").read_text().split()[0]), first.pid)
                # Wait longer than the stale threshold while every machine slot is occupied.
                time.sleep(4)
                self.assertIsNone(first.poll())
                self.assertFalse((root / "first.started").exists())
                self.assertLessEqual(int(time.time()) - int((lock / "heartbeat").read_text()), 2)
                second = launch("second")
                time.sleep(1)
                self.assertEqual(int((lock / "owner").read_text().split()[0]), first.pid)
                stop_holder.set()
                holder.join()
                for slot in occupied:
                    shutil.rmtree(slot)
                eventually(lambda: (root / "first.started").exists())
                time.sleep(3)
                self.assertFalse((root / "second.started").exists())
                (root / "first.release").touch()
                self.assertEqual(first.wait(timeout=15), 0)
                eventually(lambda: (root / "second.started").exists())
                (root / "second.release").touch()
                self.assertEqual(second.wait(timeout=15), 0)
                self.assertFalse((root / "overlap").exists())
                self.assertFalse(lock.exists())
                self.assertTrue(all(not slot.exists() for slot in occupied))
            finally:
                stop_holder.set()
                holder.join()
                for process in processes:
                    try:
                        os.killpg(process.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    if process.poll() is None:
                        process.wait(timeout=10)
                for log in logs:
                    log.close()


if __name__ == "__main__":
    unittest.main()
