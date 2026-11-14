#!/usr/bin/env bash
set -euo pipefail

# VERSION is set by release-tag.yml from the git tag
if [ -z "${VERSION:-}" ]; then
    echo "Error: VERSION environment variable must be set"
    exit 1
fi

# Build both manual and tutorials using the combined generate script.
# Only current generated files belong in a release artifact.
rm -rf html/site
./generate-html.sh --mode production --version "$VERSION" --output "html/site"

# The Chinese deployment publishes one versioned tree. Bundle its tutorials so reference links
# stay within this translated version rather than pointing at the English tutorial site.
cp -a html/site/tutorials html/site/reference/tutorials
