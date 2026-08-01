#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
schema="$root/contracts/v1/protocol.schema.json"
lifecycle="$root/contracts/v1/lifecycle.json"

jq -e '."$schema" == "https://json-schema.org/draft/2020-12/schema" and (."$defs" | length == 11)' "$schema" >/dev/null
jq -e '.protocol_version == 1 and .initial_state == "unseen" and (.transitions | length == 9)' "$lifecycle" >/dev/null

for fixture in "$root"/contracts/fixtures/*.valid.json; do
  jq -e '.protocol_version == 1 and (.type | type == "string")' "$fixture" >/dev/null
done

jq -e '.request_id == "" and .core_id < 0' "$root/contracts/fixtures/request.invalid.json" >/dev/null
printf '%s\n' 'contract syntax and fixture sentinels: ok'
