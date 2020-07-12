#!/usr/bin/env bash
PRIVKEY=$(openssl genpkey -algorithm x25519 -outform pem) ; printf "%s" "$PRIVKEY" | openssl pkey -inform pem -pubout -outform der | tail -c 32 | base64 ; echo "$PRIVKEY" | openssl pkey -inform pem -outform der | tail -c 32 | base64
