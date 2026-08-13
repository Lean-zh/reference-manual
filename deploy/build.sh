#!/usr/bin/env bash
set -euo pipefail

lake build
lake build Manual.ZhDocString.Smoke
