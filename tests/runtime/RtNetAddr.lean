import Std.Async
import Std.Net.Addr
/-! Runtime test: `Std.Net` addresses and name resolution: IPv4 and IPv6
addresses from strings and back (libuv's `inet_pton`/`inet_ntop`),
`DNS.getAddrInfo` of `localhost` (as many entries as the system's resolver
gives, socket types included), `getNameInfo`, and the errors: a host name
that is not ASCII, an unknown service. -/
open Std.Async
open Std.Net

def main : IO Unit := do
  for s in ["127.0.0.1", "0.0.0.0", "255.255.255.255", "1.2.3", "01.2.3.4", "256.1.1.1", "1.2.3.4 ", ""] do
    IO.println s!"v4 {repr s}: {(IPv4Addr.ofString s).map toString}"
  for s in ["::1", "::", "fe80::1%eth0", "2001:db8::8:800:200c:417a", "::ffff:1.2.3.4", "1:2:3:4:5:6:7:8", "1::2::3", "12345::", "::1.2.3"] do
    IO.println s!"v6 {repr s}: {(IPv6Addr.ofString s).map toString}"
  IO.println s!"{IPv6Addr.ofParts 0 0 0 0 0 0xffff 0x0102 0x0304} {IPv6Addr.ofParts 1 0 0 0 1 0 0 1} {IPv6Addr.ofParts 0 0 1 0 0 0 0 0}"
  IO.println s!"{SocketAddressV4.mk (.ofParts 10 0 0 1) 80} {SocketAddressV6.mk (.ofParts 0 0 0 0 0 0 0 1) 443}"
  let addrs ← (DNS.getAddrInfo "localhost" "").block
  IO.println s!"localhost: {decide (addrs.size > 0)}, has 127.0.0.1: {addrs.any (· == .v4 (.ofParts 127 0 0 1))}"
  let v4 ← (DNS.getAddrInfo "127.0.0.1" "80" (some .ipv4)).block
  IO.println s!"numeric: {v4.map toString}"
  let ni ← (DNS.getNameInfo (SocketAddressV4.mk (.ofParts 127 0 0 1) 22)).block
  IO.println s!"name info: {decide (ni.host.length > 0)} {ni.service}"
  try discard <| (DNS.getAddrInfo "héllo" "").block catch e => IO.println s!"non-ASCII: {e}"
  try discard <| (DNS.getAddrInfo "localhost" "no-such-service-xyz").block catch e => IO.println s!"unknown service: {e}"
