#!/usr/bin/env bash

[ -f ./wireguard-vpn.deb ] && rm ./wireguard-vpn.deb
cp -R server wireguard-vpn &&
cp -R DEBIAN wireguard-vpn/ &&
dpkg-deb --root-owner-group --build wireguard-vpn ./wireguard-vpn.deb && rm -R wireguard-vpn
