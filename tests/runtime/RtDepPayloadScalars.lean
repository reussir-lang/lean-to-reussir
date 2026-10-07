/-! Runtime test: scalar values of every kind boxed and read back. Each
value goes, at its own type, through: an identity over any type stored in
a structure field (`poly.run`, applied where the type is not known), an
existential package with its printer (`Pk`), code over the unknown type
that copies the package, a thunk, a task, an `IO.Ref`, an `Array α`, an
`Option α` and a dependent pair; every read must give the value back (its
exact bits for floats). Kinds: `Bool`; an enumeration of 3 constructors
and one of 300 (natively a 16-bit value); `UInt8`, `UInt16`, `UInt32`,
`UInt64` (around 2^63 and 2^64 − 1) and `USize`; `Float` (NaN with a
payload, −0.0, ±inf, the smallest subnormal, the largest value) and
`Float32` (the same kinds); `Char` (0, the largest, around the surrogates);
`Nat` (0, 2^63 − 1, 2^63, 2^64, a 200-digit value); `Int` (negative,
around ±2^31 and ±2^63, large); `Unit` and `PUnit`. Native Lean prints one
line per value, the printout and `true` for each route. -/

inductive Color | red | green | blue

inductive E300 where
  | c0
  | c1
  | c2
  | c3
  | c4
  | c5
  | c6
  | c7
  | c8
  | c9
  | c10
  | c11
  | c12
  | c13
  | c14
  | c15
  | c16
  | c17
  | c18
  | c19
  | c20
  | c21
  | c22
  | c23
  | c24
  | c25
  | c26
  | c27
  | c28
  | c29
  | c30
  | c31
  | c32
  | c33
  | c34
  | c35
  | c36
  | c37
  | c38
  | c39
  | c40
  | c41
  | c42
  | c43
  | c44
  | c45
  | c46
  | c47
  | c48
  | c49
  | c50
  | c51
  | c52
  | c53
  | c54
  | c55
  | c56
  | c57
  | c58
  | c59
  | c60
  | c61
  | c62
  | c63
  | c64
  | c65
  | c66
  | c67
  | c68
  | c69
  | c70
  | c71
  | c72
  | c73
  | c74
  | c75
  | c76
  | c77
  | c78
  | c79
  | c80
  | c81
  | c82
  | c83
  | c84
  | c85
  | c86
  | c87
  | c88
  | c89
  | c90
  | c91
  | c92
  | c93
  | c94
  | c95
  | c96
  | c97
  | c98
  | c99
  | c100
  | c101
  | c102
  | c103
  | c104
  | c105
  | c106
  | c107
  | c108
  | c109
  | c110
  | c111
  | c112
  | c113
  | c114
  | c115
  | c116
  | c117
  | c118
  | c119
  | c120
  | c121
  | c122
  | c123
  | c124
  | c125
  | c126
  | c127
  | c128
  | c129
  | c130
  | c131
  | c132
  | c133
  | c134
  | c135
  | c136
  | c137
  | c138
  | c139
  | c140
  | c141
  | c142
  | c143
  | c144
  | c145
  | c146
  | c147
  | c148
  | c149
  | c150
  | c151
  | c152
  | c153
  | c154
  | c155
  | c156
  | c157
  | c158
  | c159
  | c160
  | c161
  | c162
  | c163
  | c164
  | c165
  | c166
  | c167
  | c168
  | c169
  | c170
  | c171
  | c172
  | c173
  | c174
  | c175
  | c176
  | c177
  | c178
  | c179
  | c180
  | c181
  | c182
  | c183
  | c184
  | c185
  | c186
  | c187
  | c188
  | c189
  | c190
  | c191
  | c192
  | c193
  | c194
  | c195
  | c196
  | c197
  | c198
  | c199
  | c200
  | c201
  | c202
  | c203
  | c204
  | c205
  | c206
  | c207
  | c208
  | c209
  | c210
  | c211
  | c212
  | c213
  | c214
  | c215
  | c216
  | c217
  | c218
  | c219
  | c220
  | c221
  | c222
  | c223
  | c224
  | c225
  | c226
  | c227
  | c228
  | c229
  | c230
  | c231
  | c232
  | c233
  | c234
  | c235
  | c236
  | c237
  | c238
  | c239
  | c240
  | c241
  | c242
  | c243
  | c244
  | c245
  | c246
  | c247
  | c248
  | c249
  | c250
  | c251
  | c252
  | c253
  | c254
  | c255
  | c256
  | c257
  | c258
  | c259
  | c260
  | c261
  | c262
  | c263
  | c264
  | c265
  | c266
  | c267
  | c268
  | c269
  | c270
  | c271
  | c272
  | c273
  | c274
  | c275
  | c276
  | c277
  | c278
  | c279
  | c280
  | c281
  | c282
  | c283
  | c284
  | c285
  | c286
  | c287
  | c288
  | c289
  | c290
  | c291
  | c292
  | c293
  | c294
  | c295
  | c296
  | c297
  | c298
  | c299

/-- An identity over any type, stored in a field: applied where the type
is not known, its argument and result are boxed. -/
structure Poly where
  run : {α : Type} → α → α

@[noinline] def poly : Poly := ⟨fun x => x⟩

structure Pk where
  α : Type
  v : α
  sh : α → String

@[noinline] def Pk.str (p : Pk) : String := p.sh p.v

/-- Code over the package's unknown type: two copies, one through `poly`. -/
@[noinline] def Pk.dup (p : Pk) : Pk × Pk := (p, ⟨p.α, poly.run p.v, p.sh⟩)

inductive Tag | a | b

@[reducible] def Tag.denote (α : Type) : Tag → Type
  | .a => α
  | .b => Nat

@[noinline] def viaSigma {α : Type} (v : α) : (t : Tag) × t.denote α := ⟨.a, v⟩

@[noinline] def check {α : Type} (sh : α → String) (name : String) (v : α) : IO Unit := do
  let s := sh v
  let r1 := sh (poly.run v) == s
  let r2 := Pk.str ⟨α, v, sh⟩ == s
  let (p1, p2) := Pk.dup ⟨α, v, sh⟩
  let r3 := p1.str == s && p2.str == s
  let th : Thunk α := Thunk.mk fun _ => poly.run v
  let r4 := sh th.get == s
  let t := Task.spawn fun _ => poly.run v
  let r5 := sh t.get == s
  let ref ← IO.mkRef v
  ref.modify poly.run
  let r6 := sh (← ref.get) == s
  let arr : Array α := #[v, poly.run v]
  let r7 := arr.size == 2 && arr.all (sh · == s)
  let o : Option α := poly.run (some v)
  let r8 := (o.map sh) == some s
  let r9 := match viaSigma v with
    | ⟨.a, w⟩ => sh w == s
    | ⟨.b, _⟩ => false
  IO.println s!"{name} {s} {r1} {r2} {r3} {r4} {r5} {r6} {r7} {r8} {r9}"

def f64 (x : Float) : String := s!"{x} {x.toBits}"
def f32 (x : Float32) : String := s!"{x} {x.toBits}"

def main : IO Unit := do
  check toString "bool" true
  check toString "bool" false
  check (fun (c : Color) => toString c.ctorIdx) "color" .red
  check (fun (c : Color) => toString c.ctorIdx) "color" .blue
  for e in [E300.c0, .c1, .c255, .c256, .c299] do
    check (fun (c : E300) => toString c.ctorIdx) "e300" e
  check toString "u8" (255 : UInt8)
  check toString "u8" (0 : UInt8)
  check toString "u16" (65535 : UInt16)
  check toString "u32" (4294967295 : UInt32)
  check toString "u32" (2147483648 : UInt32)
  for u in [(0 : UInt64), 1, 9223372036854775807, 9223372036854775808, 9223372036854775809,
            18446744073709551614, 18446744073709551615] do
    check toString "u64" u
  for u in [(0 : USize), 9223372036854775807, 9223372036854775808, USize.ofNat (USize.size - 1)] do
    check toString "usize" u
  for b in [0x7ff8000000000001, 0xfff0000000000001, 0x8000000000000000, 0x7ff0000000000000,
            0xfff0000000000000, 0x0000000000000001, 0x7fefffffffffffff, 0x3fb999999999999a] do
    check f64 "float" (Float.ofBits b)
  for b in [0x7fc00001, 0xff800001, 0x80000000, 0x7f800000, 0xff800000, 0x00000001, 0x7f7fffff,
            0x3dcccccd] do
    check f32 "float32" (Float32.ofBits b)
  for c in [0x61, 0, 0xD7FF, 0xE000, 0xFFFF, 0x10000, 0x10FFFF].map Char.ofNat do
    check (fun (c : Char) => s!"{c.toNat}") "char" c
  for n in [0, 1, 9223372036854775807, 9223372036854775808, 18446744073709551616,
            10 ^ 199 + 12345] do
    check toString "nat" n
  for i in [(-1 : Int), -2147483648, -2147483649, 2147483647, 2147483648, -9223372036854775808,
            -9223372036854775809, 9223372036854775807, 9223372036854775808, -(10 ^ 100) - 1] do
    check toString "int" i
  check (fun (_ : Unit) => "()") "unit" ()
  check (fun (_ : PUnit.{1}) => "PUnit.unit") "punit" PUnit.unit
