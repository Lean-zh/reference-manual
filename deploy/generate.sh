#!/usr/bin/env bash

# lake --quiet exe generate-manual --depth 2 --verbose --without-html-single --output "html"
lake --log-level=error exe generate-manual --depth 2 --without-html-single --output "html"