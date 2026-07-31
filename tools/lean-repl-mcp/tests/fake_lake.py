#!/usr/bin/env python3
"""The small subset of `lake env PROGRAM` needed by the unit tests."""

import os
import sys


if len(sys.argv) != 3 or sys.argv[1] != "env":
    raise SystemExit("usage: fake_lake.py env PROGRAM")
os.execv(sys.argv[2], [sys.argv[2]])

