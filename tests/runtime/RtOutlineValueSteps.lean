/-! Runtime test: the step values of outlined recursive functions. A
self-recursive function whose body is deeper than Outline's trigger (32
levels) is cut into parts; a part that holds a tail call of the function
returns a step value (`L2RStep_k`: `done(v)`, or a variant with the call's
arguments), and the function matches it and makes the call. The step enum is
`[value]` when its layout is safe to move (no heap cell per iteration), and
shared otherwise. Each case runs its loop at the size given (`CASE N`);
without arguments every case runs. RtOutlineValueSteps.alloc pins the
allocations per iteration of the `[value]` cases to native's (none);
RtOutlineValueSteps.pipe also runs `mixed` and `ping` for 3000000 steps with
a 1 MiB stack (`LEAN_STACK_SIZE_KB=1024`): a `[value]` step must not cost
stack per iteration.
- `loop` (the allocation survey's repro, 2026-10-10): step `done(u64)`,
  `c0(Nat, u64, u64, u64)`; before, a heap cell for most iterations;
- `mixed`: a `Bool`, a `UInt8`, a `String`, an `Array Nat` updated in place
  (a copy per iteration would show if the step value took a reference) and
  a `UInt64`: the variant's fields are reordered (words first);
- `floaty`: only `Float`s, whose bytes the guard does not count as carried
  by a move, so the step enum stays shared;
- `pairLoop`: a pair result (the step's `done` holds a tuple or a record);
- `ping`/`pong`: mutual recursion, each step enum with a variant for both
  functions (the one with the longest carried prefix declared last);
- `pred`, `bp` (case `narrow`): a `done` arm narrower than a word, a `Bool`
  and a `Bool × UInt8` result (from the review of the change, ValStepNarrow);
- `tupC` (case `tupc`): the `done` arm, a tuple `(u64, u64, u8)`, is the
  representative, declared after the variant `c0(Nat, u64, bool)` (from the
  review, ValStepTie).
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The allocation survey's repro (OutlineStep2.lean): 40 nested `if`s, six
`let`s before each, every `else` a tail call. -/
def loop : Nat → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a, b, c => a + b + c
  | k + 1, a, b, c =>
    let a := (a ^^^ (b >>> 1)) * 3
    let b := (b ^^^ (c >>> 2)) * 5
    let c := (c ^^^ (a >>> 3)) * 7
    let a := (a ^^^ (b >>> 4)) * 9
    let b := (b ^^^ (c >>> 5)) * 11
    let c := (c ^^^ (a >>> 6)) * 13
    if a % 7 != 0 then
      let b := (b ^^^ (c >>> 8)) * 15
      let c := (c ^^^ (a >>> 9)) * 17
      let a := (a ^^^ (b >>> 10)) * 19
      let b := (b ^^^ (c >>> 11)) * 21
      let c := (c ^^^ (a >>> 12)) * 23
      let a := (a ^^^ (b >>> 13)) * 25
      if a % 8 != 1 then
        let c := (c ^^^ (a >>> 2)) * 27
        let a := (a ^^^ (b >>> 3)) * 29
        let b := (b ^^^ (c >>> 4)) * 31
        let c := (c ^^^ (a >>> 5)) * 33
        let a := (a ^^^ (b >>> 6)) * 35
        let b := (b ^^^ (c >>> 7)) * 37
        if a % 9 != 2 then
          let a := (a ^^^ (b >>> 9)) * 39
          let b := (b ^^^ (c >>> 10)) * 41
          let c := (c ^^^ (a >>> 11)) * 43
          let a := (a ^^^ (b >>> 12)) * 45
          let b := (b ^^^ (c >>> 13)) * 47
          let c := (c ^^^ (a >>> 1)) * 49
          if a % 10 != 0 then
            let b := (b ^^^ (c >>> 3)) * 51
            let c := (c ^^^ (a >>> 4)) * 53
            let a := (a ^^^ (b >>> 5)) * 55
            let b := (b ^^^ (c >>> 6)) * 57
            let c := (c ^^^ (a >>> 7)) * 59
            let a := (a ^^^ (b >>> 8)) * 61
            if a % 11 != 1 then
              let c := (c ^^^ (a >>> 10)) * 63
              let a := (a ^^^ (b >>> 11)) * 65
              let b := (b ^^^ (c >>> 12)) * 67
              let c := (c ^^^ (a >>> 13)) * 69
              let a := (a ^^^ (b >>> 1)) * 71
              let b := (b ^^^ (c >>> 2)) * 73
              if a % 7 != 2 then
                let a := (a ^^^ (b >>> 4)) * 75
                let b := (b ^^^ (c >>> 5)) * 77
                let c := (c ^^^ (a >>> 6)) * 79
                let a := (a ^^^ (b >>> 7)) * 81
                let b := (b ^^^ (c >>> 8)) * 83
                let c := (c ^^^ (a >>> 9)) * 85
                if a % 8 != 0 then
                  let b := (b ^^^ (c >>> 11)) * 87
                  let c := (c ^^^ (a >>> 12)) * 89
                  let a := (a ^^^ (b >>> 13)) * 91
                  let b := (b ^^^ (c >>> 1)) * 93
                  let c := (c ^^^ (a >>> 2)) * 95
                  let a := (a ^^^ (b >>> 3)) * 97
                  if a % 9 != 1 then
                    let c := (c ^^^ (a >>> 5)) * 99
                    let a := (a ^^^ (b >>> 6)) * 101
                    let b := (b ^^^ (c >>> 7)) * 103
                    let c := (c ^^^ (a >>> 8)) * 105
                    let a := (a ^^^ (b >>> 9)) * 107
                    let b := (b ^^^ (c >>> 10)) * 109
                    if a % 10 != 2 then
                      let a := (a ^^^ (b >>> 12)) * 111
                      let b := (b ^^^ (c >>> 13)) * 113
                      let c := (c ^^^ (a >>> 1)) * 115
                      let a := (a ^^^ (b >>> 2)) * 117
                      let b := (b ^^^ (c >>> 3)) * 119
                      let c := (c ^^^ (a >>> 4)) * 121
                      if a % 11 != 0 then
                        let b := (b ^^^ (c >>> 6)) * 123
                        let c := (c ^^^ (a >>> 7)) * 125
                        let a := (a ^^^ (b >>> 8)) * 127
                        let b := (b ^^^ (c >>> 9)) * 129
                        let c := (c ^^^ (a >>> 10)) * 131
                        let a := (a ^^^ (b >>> 11)) * 133
                        if a % 7 != 1 then
                          let c := (c ^^^ (a >>> 13)) * 135
                          let a := (a ^^^ (b >>> 1)) * 137
                          let b := (b ^^^ (c >>> 2)) * 139
                          let c := (c ^^^ (a >>> 3)) * 141
                          let a := (a ^^^ (b >>> 4)) * 143
                          let b := (b ^^^ (c >>> 5)) * 145
                          if a % 8 != 2 then
                            let a := (a ^^^ (b >>> 7)) * 147
                            let b := (b ^^^ (c >>> 8)) * 149
                            let c := (c ^^^ (a >>> 9)) * 151
                            let a := (a ^^^ (b >>> 10)) * 153
                            let b := (b ^^^ (c >>> 11)) * 155
                            let c := (c ^^^ (a >>> 12)) * 157
                            if a % 9 != 0 then
                              let b := (b ^^^ (c >>> 1)) * 159
                              let c := (c ^^^ (a >>> 2)) * 161
                              let a := (a ^^^ (b >>> 3)) * 163
                              let b := (b ^^^ (c >>> 4)) * 165
                              let c := (c ^^^ (a >>> 5)) * 167
                              let a := (a ^^^ (b >>> 6)) * 169
                              if a % 10 != 1 then
                                let c := (c ^^^ (a >>> 8)) * 171
                                let a := (a ^^^ (b >>> 9)) * 173
                                let b := (b ^^^ (c >>> 10)) * 175
                                let c := (c ^^^ (a >>> 11)) * 177
                                let a := (a ^^^ (b >>> 12)) * 179
                                let b := (b ^^^ (c >>> 13)) * 181
                                if a % 11 != 2 then
                                  let a := (a ^^^ (b >>> 2)) * 183
                                  let b := (b ^^^ (c >>> 3)) * 185
                                  let c := (c ^^^ (a >>> 4)) * 187
                                  let a := (a ^^^ (b >>> 5)) * 189
                                  let b := (b ^^^ (c >>> 6)) * 191
                                  let c := (c ^^^ (a >>> 7)) * 193
                                  if a % 7 != 0 then
                                    let b := (b ^^^ (c >>> 9)) * 195
                                    let c := (c ^^^ (a >>> 10)) * 197
                                    let a := (a ^^^ (b >>> 11)) * 199
                                    let b := (b ^^^ (c >>> 12)) * 201
                                    let c := (c ^^^ (a >>> 13)) * 203
                                    let a := (a ^^^ (b >>> 1)) * 205
                                    if a % 8 != 1 then
                                      let c := (c ^^^ (a >>> 3)) * 207
                                      let a := (a ^^^ (b >>> 4)) * 209
                                      let b := (b ^^^ (c >>> 5)) * 211
                                      let c := (c ^^^ (a >>> 6)) * 213
                                      let a := (a ^^^ (b >>> 7)) * 215
                                      let b := (b ^^^ (c >>> 8)) * 217
                                      if a % 9 != 2 then
                                        let a := (a ^^^ (b >>> 10)) * 219
                                        let b := (b ^^^ (c >>> 11)) * 221
                                        let c := (c ^^^ (a >>> 12)) * 223
                                        let a := (a ^^^ (b >>> 13)) * 225
                                        let b := (b ^^^ (c >>> 1)) * 227
                                        let c := (c ^^^ (a >>> 2)) * 229
                                        if a % 10 != 0 then
                                          let b := (b ^^^ (c >>> 4)) * 231
                                          let c := (c ^^^ (a >>> 5)) * 233
                                          let a := (a ^^^ (b >>> 6)) * 235
                                          let b := (b ^^^ (c >>> 7)) * 237
                                          let c := (c ^^^ (a >>> 8)) * 239
                                          let a := (a ^^^ (b >>> 9)) * 241
                                          if a % 11 != 1 then
                                            let c := (c ^^^ (a >>> 11)) * 243
                                            let a := (a ^^^ (b >>> 12)) * 245
                                            let b := (b ^^^ (c >>> 13)) * 247
                                            let c := (c ^^^ (a >>> 1)) * 249
                                            let a := (a ^^^ (b >>> 2)) * 251
                                            let b := (b ^^^ (c >>> 3)) * 253
                                            if a % 7 != 2 then
                                              let a := (a ^^^ (b >>> 5)) * 255
                                              let b := (b ^^^ (c >>> 6)) * 257
                                              let c := (c ^^^ (a >>> 7)) * 259
                                              let a := (a ^^^ (b >>> 8)) * 261
                                              let b := (b ^^^ (c >>> 9)) * 263
                                              let c := (c ^^^ (a >>> 10)) * 265
                                              if a % 8 != 0 then
                                                let b := (b ^^^ (c >>> 12)) * 267
                                                let c := (c ^^^ (a >>> 13)) * 269
                                                let a := (a ^^^ (b >>> 1)) * 271
                                                let b := (b ^^^ (c >>> 2)) * 273
                                                let c := (c ^^^ (a >>> 3)) * 275
                                                let a := (a ^^^ (b >>> 4)) * 277
                                                if a % 9 != 1 then
                                                  let c := (c ^^^ (a >>> 6)) * 279
                                                  let a := (a ^^^ (b >>> 7)) * 281
                                                  let b := (b ^^^ (c >>> 8)) * 283
                                                  let c := (c ^^^ (a >>> 9)) * 285
                                                  let a := (a ^^^ (b >>> 10)) * 287
                                                  let b := (b ^^^ (c >>> 11)) * 289
                                                  if a % 10 != 2 then
                                                    let a := (a ^^^ (b >>> 13)) * 291
                                                    let b := (b ^^^ (c >>> 1)) * 293
                                                    let c := (c ^^^ (a >>> 2)) * 295
                                                    let a := (a ^^^ (b >>> 3)) * 297
                                                    let b := (b ^^^ (c >>> 4)) * 299
                                                    let c := (c ^^^ (a >>> 5)) * 301
                                                    if a % 11 != 0 then
                                                      let b := (b ^^^ (c >>> 7)) * 303
                                                      let c := (c ^^^ (a >>> 8)) * 305
                                                      let a := (a ^^^ (b >>> 9)) * 307
                                                      let b := (b ^^^ (c >>> 10)) * 309
                                                      let c := (c ^^^ (a >>> 11)) * 311
                                                      let a := (a ^^^ (b >>> 12)) * 313
                                                      if a % 7 != 1 then
                                                        let c := (c ^^^ (a >>> 1)) * 315
                                                        let a := (a ^^^ (b >>> 2)) * 317
                                                        let b := (b ^^^ (c >>> 3)) * 319
                                                        let c := (c ^^^ (a >>> 4)) * 321
                                                        let a := (a ^^^ (b >>> 5)) * 323
                                                        let b := (b ^^^ (c >>> 6)) * 325
                                                        if a % 8 != 2 then
                                                          let a := (a ^^^ (b >>> 8)) * 327
                                                          let b := (b ^^^ (c >>> 9)) * 329
                                                          let c := (c ^^^ (a >>> 10)) * 331
                                                          let a := (a ^^^ (b >>> 11)) * 333
                                                          let b := (b ^^^ (c >>> 12)) * 335
                                                          let c := (c ^^^ (a >>> 13)) * 337
                                                          if a % 9 != 0 then
                                                            let b := (b ^^^ (c >>> 2)) * 339
                                                            let c := (c ^^^ (a >>> 3)) * 341
                                                            let a := (a ^^^ (b >>> 4)) * 343
                                                            let b := (b ^^^ (c >>> 5)) * 345
                                                            let c := (c ^^^ (a >>> 6)) * 347
                                                            let a := (a ^^^ (b >>> 7)) * 349
                                                            if a % 10 != 1 then
                                                              let c := (c ^^^ (a >>> 9)) * 351
                                                              let a := (a ^^^ (b >>> 10)) * 353
                                                              let b := (b ^^^ (c >>> 11)) * 355
                                                              let c := (c ^^^ (a >>> 12)) * 357
                                                              let a := (a ^^^ (b >>> 13)) * 359
                                                              let b := (b ^^^ (c >>> 1)) * 361
                                                              if a % 11 != 2 then
                                                                let a := (a ^^^ (b >>> 3)) * 363
                                                                let b := (b ^^^ (c >>> 4)) * 365
                                                                let c := (c ^^^ (a >>> 5)) * 367
                                                                let a := (a ^^^ (b >>> 6)) * 369
                                                                let b := (b ^^^ (c >>> 7)) * 371
                                                                let c := (c ^^^ (a >>> 8)) * 373
                                                                if a % 7 != 0 then
                                                                  let b := (b ^^^ (c >>> 10)) * 375
                                                                  let c := (c ^^^ (a >>> 11)) * 377
                                                                  let a := (a ^^^ (b >>> 12)) * 379
                                                                  let b := (b ^^^ (c >>> 13)) * 381
                                                                  let c := (c ^^^ (a >>> 1)) * 383
                                                                  let a := (a ^^^ (b >>> 2)) * 385
                                                                  if a % 8 != 1 then
                                                                    let c := (c ^^^ (a >>> 4)) * 387
                                                                    let a := (a ^^^ (b >>> 5)) * 389
                                                                    let b := (b ^^^ (c >>> 6)) * 391
                                                                    let c := (c ^^^ (a >>> 7)) * 393
                                                                    let a := (a ^^^ (b >>> 8)) * 395
                                                                    let b := (b ^^^ (c >>> 9)) * 397
                                                                    if a % 9 != 2 then
                                                                      let a := (a ^^^ (b >>> 11)) * 399
                                                                      let b := (b ^^^ (c >>> 12)) * 401
                                                                      let c := (c ^^^ (a >>> 13)) * 403
                                                                      let a := (a ^^^ (b >>> 1)) * 405
                                                                      let b := (b ^^^ (c >>> 2)) * 407
                                                                      let c := (c ^^^ (a >>> 3)) * 409
                                                                      if a % 10 != 0 then
                                                                        let b := (b ^^^ (c >>> 5)) * 411
                                                                        let c := (c ^^^ (a >>> 6)) * 413
                                                                        let a := (a ^^^ (b >>> 7)) * 415
                                                                        let b := (b ^^^ (c >>> 8)) * 417
                                                                        let c := (c ^^^ (a >>> 9)) * 419
                                                                        let a := (a ^^^ (b >>> 10)) * 421
                                                                        if a % 11 != 1 then
                                                                          let c := (c ^^^ (a >>> 12)) * 423
                                                                          let a := (a ^^^ (b >>> 13)) * 425
                                                                          let b := (b ^^^ (c >>> 1)) * 427
                                                                          let c := (c ^^^ (a >>> 2)) * 429
                                                                          let a := (a ^^^ (b >>> 3)) * 431
                                                                          let b := (b ^^^ (c >>> 4)) * 433
                                                                          if a % 7 != 2 then
                                                                            let a := (a ^^^ (b >>> 6)) * 435
                                                                            let b := (b ^^^ (c >>> 7)) * 437
                                                                            let c := (c ^^^ (a >>> 8)) * 439
                                                                            let a := (a ^^^ (b >>> 9)) * 441
                                                                            let b := (b ^^^ (c >>> 10)) * 443
                                                                            let c := (c ^^^ (a >>> 11)) * 445
                                                                            if a % 8 != 0 then
                                                                              let b := (b ^^^ (c >>> 13)) * 447
                                                                              let c := (c ^^^ (a >>> 1)) * 449
                                                                              let a := (a ^^^ (b >>> 2)) * 451
                                                                              let b := (b ^^^ (c >>> 3)) * 453
                                                                              let c := (c ^^^ (a >>> 4)) * 455
                                                                              let a := (a ^^^ (b >>> 5)) * 457
                                                                              if a % 9 != 1 then
                                                                                let c := (c ^^^ (a >>> 7)) * 459
                                                                                let a := (a ^^^ (b >>> 8)) * 461
                                                                                let b := (b ^^^ (c >>> 9)) * 463
                                                                                let c := (c ^^^ (a >>> 10)) * 465
                                                                                let a := (a ^^^ (b >>> 11)) * 467
                                                                                let b := (b ^^^ (c >>> 12)) * 469
                                                                                if a % 10 != 2 then
                                                                                  let a := (a ^^^ (b >>> 1)) * 471
                                                                                  let b := (b ^^^ (c >>> 2)) * 473
                                                                                  let c := (c ^^^ (a >>> 3)) * 475
                                                                                  let a := (a ^^^ (b >>> 4)) * 477
                                                                                  let b := (b ^^^ (c >>> 5)) * 479
                                                                                  let c := (c ^^^ (a >>> 6)) * 481
                                                                                  if a % 11 != 0 then
                                                                                    loop k (a + 1) b c
                                                                                  else loop k a (b + 39) c
                                                                                else loop k a (b + 38) c
                                                                              else loop k a (b + 37) c
                                                                            else loop k a (b + 36) c
                                                                          else loop k a (b + 35) c
                                                                        else loop k a (b + 34) c
                                                                      else loop k a (b + 33) c
                                                                    else loop k a (b + 32) c
                                                                  else loop k a (b + 31) c
                                                                else loop k a (b + 30) c
                                                              else loop k a (b + 29) c
                                                            else loop k a (b + 28) c
                                                          else loop k a (b + 27) c
                                                        else loop k a (b + 26) c
                                                      else loop k a (b + 25) c
                                                    else loop k a (b + 24) c
                                                  else loop k a (b + 23) c
                                                else loop k a (b + 22) c
                                              else loop k a (b + 21) c
                                            else loop k a (b + 20) c
                                          else loop k a (b + 19) c
                                        else loop k a (b + 18) c
                                      else loop k a (b + 17) c
                                    else loop k a (b + 16) c
                                  else loop k a (b + 15) c
                                else loop k a (b + 14) c
                              else loop k a (b + 13) c
                            else loop k a (b + 12) c
                          else loop k a (b + 11) c
                        else loop k a (b + 10) c
                      else loop k a (b + 9) c
                    else loop k a (b + 8) c
                  else loop k a (b + 7) c
                else loop k a (b + 6) c
              else loop k a (b + 5) c
            else loop k a (b + 4) c
          else loop k a (b + 3) c
        else loop k a (b + 2) c
      else loop k a (b + 1) c
    else loop k a (b + 0) c

partial def mixed (flag : Bool) (tag : UInt8) (s : String) (arr : Array Nat) (k : Nat) (acc : UInt64) : String :=
  if k == 0 then s ++ s!" {flag} {tag} {arr.foldl (· + ·) 0} {acc}" else
  match k % 41 with
  | 0 => if flag then mixed false (tag + 0) s (arr.set! (k % arr.size) (k + 0)) (k - 1) (acc * 31 + 0)
         else mixed true (tag ^^^ 0) s arr (k - 1) (acc + 0)
  | 1 => mixed (!flag) (tag + 1) s (arr.set! ((k + 1) % arr.size) (k % 1000 + 1)) (k - 1) (acc * 7 + 1)
  | 2 => mixed (!flag) (tag + 2) s (arr.set! ((k + 2) % arr.size) (k % 1000 + 2)) (k - 1) (acc * 7 + 2)
  | 3 => mixed (!flag) (tag + 3) s (arr.set! ((k + 3) % arr.size) (k % 1000 + 3)) (k - 1) (acc * 7 + 3)
  | 4 => mixed (!flag) (tag + 4) s (arr.set! ((k + 4) % arr.size) (k % 1000 + 4)) (k - 1) (acc * 7 + 4)
  | 5 => if flag then mixed false (tag + 5) s (arr.set! (k % arr.size) (k + 5)) (k - 1) (acc * 31 + 5)
         else mixed true (tag ^^^ 5) s arr (k - 1) (acc + 5)
  | 6 => mixed (!flag) (tag + 6) s (arr.set! ((k + 6) % arr.size) (k % 1000 + 6)) (k - 1) (acc * 7 + 6)
  | 7 => mixed (!flag) (tag + 7) s (arr.set! ((k + 7) % arr.size) (k % 1000 + 7)) (k - 1) (acc * 7 + 7)
  | 8 => mixed (!flag) (tag + 8) s (arr.set! ((k + 8) % arr.size) (k % 1000 + 8)) (k - 1) (acc * 7 + 8)
  | 9 => mixed (!flag) (tag + 9) s (arr.set! ((k + 9) % arr.size) (k % 1000 + 9)) (k - 1) (acc * 7 + 9)
  | 10 => if flag then mixed false (tag + 10) s (arr.set! (k % arr.size) (k + 10)) (k - 1) (acc * 31 + 10)
         else mixed true (tag ^^^ 10) s arr (k - 1) (acc + 10)
  | 11 => mixed (!flag) (tag + 11) s (arr.set! ((k + 11) % arr.size) (k % 1000 + 11)) (k - 1) (acc * 7 + 11)
  | 12 => mixed (!flag) (tag + 12) s (arr.set! ((k + 12) % arr.size) (k % 1000 + 12)) (k - 1) (acc * 7 + 12)
  | 13 => mixed (!flag) (tag + 13) s (arr.set! ((k + 13) % arr.size) (k % 1000 + 13)) (k - 1) (acc * 7 + 13)
  | 14 => mixed (!flag) (tag + 14) s (arr.set! ((k + 14) % arr.size) (k % 1000 + 14)) (k - 1) (acc * 7 + 14)
  | 15 => if flag then mixed false (tag + 15) s (arr.set! (k % arr.size) (k + 15)) (k - 1) (acc * 31 + 15)
         else mixed true (tag ^^^ 15) s arr (k - 1) (acc + 15)
  | 16 => mixed (!flag) (tag + 16) s (arr.set! ((k + 16) % arr.size) (k % 1000 + 16)) (k - 1) (acc * 7 + 16)
  | 17 => mixed (!flag) (tag + 17) s (arr.set! ((k + 17) % arr.size) (k % 1000 + 17)) (k - 1) (acc * 7 + 17)
  | 18 => mixed (!flag) (tag + 18) s (arr.set! ((k + 18) % arr.size) (k % 1000 + 18)) (k - 1) (acc * 7 + 18)
  | 19 => mixed (!flag) (tag + 19) s (arr.set! ((k + 19) % arr.size) (k % 1000 + 19)) (k - 1) (acc * 7 + 19)
  | 20 => if flag then mixed false (tag + 20) s (arr.set! (k % arr.size) (k + 20)) (k - 1) (acc * 31 + 20)
         else mixed true (tag ^^^ 20) s arr (k - 1) (acc + 20)
  | 21 => mixed (!flag) (tag + 21) s (arr.set! ((k + 21) % arr.size) (k % 1000 + 21)) (k - 1) (acc * 7 + 21)
  | 22 => mixed (!flag) (tag + 22) s (arr.set! ((k + 22) % arr.size) (k % 1000 + 22)) (k - 1) (acc * 7 + 22)
  | 23 => mixed (!flag) (tag + 23) s (arr.set! ((k + 23) % arr.size) (k % 1000 + 23)) (k - 1) (acc * 7 + 23)
  | 24 => mixed (!flag) (tag + 24) s (arr.set! ((k + 24) % arr.size) (k % 1000 + 24)) (k - 1) (acc * 7 + 24)
  | 25 => if flag then mixed false (tag + 25) s (arr.set! (k % arr.size) (k + 25)) (k - 1) (acc * 31 + 25)
         else mixed true (tag ^^^ 25) s arr (k - 1) (acc + 25)
  | 26 => mixed (!flag) (tag + 26) s (arr.set! ((k + 26) % arr.size) (k % 1000 + 26)) (k - 1) (acc * 7 + 26)
  | 27 => mixed (!flag) (tag + 27) s (arr.set! ((k + 27) % arr.size) (k % 1000 + 27)) (k - 1) (acc * 7 + 27)
  | 28 => mixed (!flag) (tag + 28) s (arr.set! ((k + 28) % arr.size) (k % 1000 + 28)) (k - 1) (acc * 7 + 28)
  | 29 => mixed (!flag) (tag + 29) s (arr.set! ((k + 29) % arr.size) (k % 1000 + 29)) (k - 1) (acc * 7 + 29)
  | 30 => if flag then mixed false (tag + 30) s (arr.set! (k % arr.size) (k + 30)) (k - 1) (acc * 31 + 30)
         else mixed true (tag ^^^ 30) s arr (k - 1) (acc + 30)
  | 31 => mixed (!flag) (tag + 31) s (arr.set! ((k + 31) % arr.size) (k % 1000 + 31)) (k - 1) (acc * 7 + 31)
  | 32 => mixed (!flag) (tag + 32) s (arr.set! ((k + 32) % arr.size) (k % 1000 + 32)) (k - 1) (acc * 7 + 32)
  | 33 => mixed (!flag) (tag + 33) s (arr.set! ((k + 33) % arr.size) (k % 1000 + 33)) (k - 1) (acc * 7 + 33)
  | 34 => mixed (!flag) (tag + 34) s (arr.set! ((k + 34) % arr.size) (k % 1000 + 34)) (k - 1) (acc * 7 + 34)
  | 35 => if flag then mixed false (tag + 35) s (arr.set! (k % arr.size) (k + 35)) (k - 1) (acc * 31 + 35)
         else mixed true (tag ^^^ 35) s arr (k - 1) (acc + 35)
  | 36 => mixed (!flag) (tag + 36) s (arr.set! ((k + 36) % arr.size) (k % 1000 + 36)) (k - 1) (acc * 7 + 36)
  | 37 => mixed (!flag) (tag + 37) s (arr.set! ((k + 37) % arr.size) (k % 1000 + 37)) (k - 1) (acc * 7 + 37)
  | 38 => mixed (!flag) (tag + 38) s (arr.set! ((k + 38) % arr.size) (k % 1000 + 38)) (k - 1) (acc * 7 + 38)
  | 39 => mixed (!flag) (tag + 39) s (arr.set! ((k + 39) % arr.size) (k % 1000 + 39)) (k - 1) (acc * 7 + 39)
  | _ => mixed flag tag s arr (k - 1) acc

partial def floaty (x y : Float) : Float :=
  if x > 1.0e300 || x < 0.0 then x + y else
  match x.toUInt64.toNat % 41 with
  | 0 => floaty (x * 1.0001 + 0.5) (y * 0.5 + x / 2.0)
  | 1 => floaty (x * 1.0011 + 1.5) (y * 0.5 + x / 3.0)
  | 2 => floaty (x * 1.0021 + 2.5) (y * 0.5 + x / 4.0)
  | 3 => floaty (x * 1.0031 + 3.5) (y * 0.5 + x / 5.0)
  | 4 => floaty (x * 1.0041 + 4.5) (y * 0.5 + x / 6.0)
  | 5 => floaty (x * 1.0051 + 5.5) (y * 0.5 + x / 7.0)
  | 6 => floaty (x * 1.0061 + 6.5) (y * 0.5 + x / 8.0)
  | 7 => floaty (x * 1.0071 + 7.5) (y * 0.5 + x / 9.0)
  | 8 => floaty (x * 1.0081 + 8.5) (y * 0.5 + x / 10.0)
  | 9 => floaty (x * 1.0091 + 9.5) (y * 0.5 + x / 11.0)
  | 10 => floaty (x * 1.0101 + 10.5) (y * 0.5 + x / 12.0)
  | 11 => floaty (x * 1.0111 + 11.5) (y * 0.5 + x / 13.0)
  | 12 => floaty (x * 1.0121 + 12.5) (y * 0.5 + x / 14.0)
  | 13 => floaty (x * 1.0131 + 13.5) (y * 0.5 + x / 15.0)
  | 14 => floaty (x * 1.0141 + 14.5) (y * 0.5 + x / 16.0)
  | 15 => floaty (x * 1.0151 + 15.5) (y * 0.5 + x / 17.0)
  | 16 => floaty (x * 1.0161 + 16.5) (y * 0.5 + x / 18.0)
  | 17 => floaty (x * 1.0171 + 17.5) (y * 0.5 + x / 19.0)
  | 18 => floaty (x * 1.0181 + 18.5) (y * 0.5 + x / 20.0)
  | 19 => floaty (x * 1.0191 + 19.5) (y * 0.5 + x / 21.0)
  | 20 => floaty (x * 1.0201 + 20.5) (y * 0.5 + x / 22.0)
  | 21 => floaty (x * 1.0211 + 21.5) (y * 0.5 + x / 23.0)
  | 22 => floaty (x * 1.0221 + 22.5) (y * 0.5 + x / 24.0)
  | 23 => floaty (x * 1.0231 + 23.5) (y * 0.5 + x / 25.0)
  | 24 => floaty (x * 1.0241 + 24.5) (y * 0.5 + x / 26.0)
  | 25 => floaty (x * 1.0251 + 25.5) (y * 0.5 + x / 27.0)
  | 26 => floaty (x * 1.0261 + 26.5) (y * 0.5 + x / 28.0)
  | 27 => floaty (x * 1.0271 + 27.5) (y * 0.5 + x / 29.0)
  | 28 => floaty (x * 1.0281 + 28.5) (y * 0.5 + x / 30.0)
  | 29 => floaty (x * 1.0291 + 29.5) (y * 0.5 + x / 31.0)
  | 30 => floaty (x * 1.0301 + 30.5) (y * 0.5 + x / 32.0)
  | 31 => floaty (x * 1.0311 + 31.5) (y * 0.5 + x / 33.0)
  | 32 => floaty (x * 1.0321 + 32.5) (y * 0.5 + x / 34.0)
  | 33 => floaty (x * 1.0331 + 33.5) (y * 0.5 + x / 35.0)
  | 34 => floaty (x * 1.0341 + 34.5) (y * 0.5 + x / 36.0)
  | 35 => floaty (x * 1.0351 + 35.5) (y * 0.5 + x / 37.0)
  | 36 => floaty (x * 1.0361 + 36.5) (y * 0.5 + x / 38.0)
  | 37 => floaty (x * 1.0371 + 37.5) (y * 0.5 + x / 39.0)
  | 38 => floaty (x * 1.0381 + 38.5) (y * 0.5 + x / 40.0)
  | 39 => floaty (x * 1.0391 + 39.5) (y * 0.5 + x / 41.0)
  | _ => floaty (x * 1.5 + 1.0) (y + 2.0)

partial def pairLoop (n a b : Nat) : Nat × Nat :=
  if n == 0 then (a, b) else
  match n % 41 with
  | 0 => pairLoop (n - 1) ((a * 3 + b) % 1000003) ((b + a + 0) % 999983)
  | 1 => pairLoop (n - 1) ((a * 4 + b) % 1000003) ((b + a + 1) % 999983)
  | 2 => pairLoop (n - 1) ((a * 5 + b) % 1000003) ((b + a + 2) % 999983)
  | 3 => pairLoop (n - 1) ((a * 6 + b) % 1000003) ((b + a + 3) % 999983)
  | 4 => pairLoop (n - 1) ((a * 7 + b) % 1000003) ((b + a + 4) % 999983)
  | 5 => pairLoop (n - 1) ((a * 8 + b) % 1000003) ((b + a + 5) % 999983)
  | 6 => pairLoop (n - 1) ((a * 9 + b) % 1000003) ((b + a + 6) % 999983)
  | 7 => pairLoop (n - 1) ((a * 10 + b) % 1000003) ((b + a + 7) % 999983)
  | 8 => pairLoop (n - 1) ((a * 11 + b) % 1000003) ((b + a + 8) % 999983)
  | 9 => pairLoop (n - 1) ((a * 12 + b) % 1000003) ((b + a + 9) % 999983)
  | 10 => pairLoop (n - 1) ((a * 13 + b) % 1000003) ((b + a + 10) % 999983)
  | 11 => pairLoop (n - 1) ((a * 14 + b) % 1000003) ((b + a + 11) % 999983)
  | 12 => pairLoop (n - 1) ((a * 15 + b) % 1000003) ((b + a + 12) % 999983)
  | 13 => pairLoop (n - 1) ((a * 16 + b) % 1000003) ((b + a + 13) % 999983)
  | 14 => pairLoop (n - 1) ((a * 17 + b) % 1000003) ((b + a + 14) % 999983)
  | 15 => pairLoop (n - 1) ((a * 18 + b) % 1000003) ((b + a + 15) % 999983)
  | 16 => pairLoop (n - 1) ((a * 19 + b) % 1000003) ((b + a + 16) % 999983)
  | 17 => pairLoop (n - 1) ((a * 20 + b) % 1000003) ((b + a + 17) % 999983)
  | 18 => pairLoop (n - 1) ((a * 21 + b) % 1000003) ((b + a + 18) % 999983)
  | 19 => pairLoop (n - 1) ((a * 22 + b) % 1000003) ((b + a + 19) % 999983)
  | 20 => pairLoop (n - 1) ((a * 23 + b) % 1000003) ((b + a + 20) % 999983)
  | 21 => pairLoop (n - 1) ((a * 24 + b) % 1000003) ((b + a + 21) % 999983)
  | 22 => pairLoop (n - 1) ((a * 25 + b) % 1000003) ((b + a + 22) % 999983)
  | 23 => pairLoop (n - 1) ((a * 26 + b) % 1000003) ((b + a + 23) % 999983)
  | 24 => pairLoop (n - 1) ((a * 27 + b) % 1000003) ((b + a + 24) % 999983)
  | 25 => pairLoop (n - 1) ((a * 28 + b) % 1000003) ((b + a + 25) % 999983)
  | 26 => pairLoop (n - 1) ((a * 29 + b) % 1000003) ((b + a + 26) % 999983)
  | 27 => pairLoop (n - 1) ((a * 30 + b) % 1000003) ((b + a + 27) % 999983)
  | 28 => pairLoop (n - 1) ((a * 31 + b) % 1000003) ((b + a + 28) % 999983)
  | 29 => pairLoop (n - 1) ((a * 32 + b) % 1000003) ((b + a + 29) % 999983)
  | 30 => pairLoop (n - 1) ((a * 33 + b) % 1000003) ((b + a + 30) % 999983)
  | 31 => pairLoop (n - 1) ((a * 34 + b) % 1000003) ((b + a + 31) % 999983)
  | 32 => pairLoop (n - 1) ((a * 35 + b) % 1000003) ((b + a + 32) % 999983)
  | 33 => pairLoop (n - 1) ((a * 36 + b) % 1000003) ((b + a + 33) % 999983)
  | 34 => pairLoop (n - 1) ((a * 37 + b) % 1000003) ((b + a + 34) % 999983)
  | 35 => pairLoop (n - 1) ((a * 38 + b) % 1000003) ((b + a + 35) % 999983)
  | 36 => pairLoop (n - 1) ((a * 39 + b) % 1000003) ((b + a + 36) % 999983)
  | 37 => pairLoop (n - 1) ((a * 40 + b) % 1000003) ((b + a + 37) % 999983)
  | 38 => pairLoop (n - 1) ((a * 41 + b) % 1000003) ((b + a + 38) % 999983)
  | 39 => pairLoop (n - 1) ((a * 42 + b) % 1000003) ((b + a + 39) % 999983)
  | _ => pairLoop (n - 1) b a

mutual
partial def ping (n : Nat) (s : String) : String :=
  if n == 0 then s ++ "!" else
  match n % 41 with
  | 0 => pong (n - 1) (s.length % 2 == 0) 0
  | 1 => ping (n - 1) s
  | 2 => ping (n - 1) s
  | 3 => ping (n - 1) s
  | 4 => ping (n - 1) s
  | 5 => ping (n - 1) s
  | 6 => ping (n - 1) s
  | 7 => ping (n - 1) s
  | 8 => ping (n - 1) s
  | 9 => ping (n - 1) s
  | 10 => ping (n - 1) s
  | 11 => ping (n - 1) s
  | 12 => ping (n - 1) s
  | 13 => pong (n - 1) (s.length % 2 == 0) 13
  | 14 => ping (n - 1) s
  | 15 => ping (n - 1) s
  | 16 => ping (n - 1) s
  | 17 => ping (n - 1) s
  | 18 => ping (n - 1) s
  | 19 => ping (n - 1) s
  | 20 => ping (n - 1) s
  | 21 => ping (n - 1) s
  | 22 => ping (n - 1) s
  | 23 => ping (n - 1) s
  | 24 => ping (n - 1) s
  | 25 => ping (n - 1) s
  | 26 => pong (n - 1) (s.length % 2 == 0) 26
  | 27 => ping (n - 1) s
  | 28 => ping (n - 1) s
  | 29 => ping (n - 1) s
  | 30 => ping (n - 1) s
  | 31 => ping (n - 1) s
  | 32 => ping (n - 1) s
  | 33 => ping (n - 1) s
  | 34 => ping (n - 1) s
  | 35 => ping (n - 1) s
  | 36 => ping (n - 1) s
  | 37 => ping (n - 1) s
  | 38 => ping (n - 1) s
  | 39 => pong (n - 1) (s.length % 2 == 0) 39
  | _ => ping (n - 1) s
partial def pong (n : Nat) (b : Bool) (x : UInt8) : String :=
  if n == 0 then s!"pong {b} {x}" else
  match n % 41 with
  | 0 => ping (n - 1) (if b then "even" else "odd")
  | 1 => pong (n - 1) (!b) (x + 1)
  | 2 => pong (n - 1) (!b) (x + 2)
  | 3 => pong (n - 1) (!b) (x + 3)
  | 4 => pong (n - 1) (!b) (x + 4)
  | 5 => pong (n - 1) (!b) (x + 5)
  | 6 => pong (n - 1) (!b) (x + 6)
  | 7 => pong (n - 1) (!b) (x + 7)
  | 8 => pong (n - 1) (!b) (x + 8)
  | 9 => pong (n - 1) (!b) (x + 9)
  | 10 => pong (n - 1) (!b) (x + 10)
  | 11 => ping (n - 1) (if b then "even" else "odd")
  | 12 => pong (n - 1) (!b) (x + 12)
  | 13 => pong (n - 1) (!b) (x + 13)
  | 14 => pong (n - 1) (!b) (x + 14)
  | 15 => pong (n - 1) (!b) (x + 15)
  | 16 => pong (n - 1) (!b) (x + 16)
  | 17 => pong (n - 1) (!b) (x + 17)
  | 18 => pong (n - 1) (!b) (x + 18)
  | 19 => pong (n - 1) (!b) (x + 19)
  | 20 => pong (n - 1) (!b) (x + 20)
  | 21 => pong (n - 1) (!b) (x + 21)
  | 22 => ping (n - 1) (if b then "even" else "odd")
  | 23 => pong (n - 1) (!b) (x + 23)
  | 24 => pong (n - 1) (!b) (x + 24)
  | 25 => pong (n - 1) (!b) (x + 25)
  | 26 => pong (n - 1) (!b) (x + 26)
  | 27 => pong (n - 1) (!b) (x + 27)
  | 28 => pong (n - 1) (!b) (x + 28)
  | 29 => pong (n - 1) (!b) (x + 29)
  | 30 => pong (n - 1) (!b) (x + 30)
  | 31 => pong (n - 1) (!b) (x + 31)
  | 32 => pong (n - 1) (!b) (x + 32)
  | 33 => ping (n - 1) (if b then "even" else "odd")
  | 34 => pong (n - 1) (!b) (x + 34)
  | 35 => pong (n - 1) (!b) (x + 35)
  | 36 => pong (n - 1) (!b) (x + 36)
  | 37 => pong (n - 1) (!b) (x + 37)
  | 38 => pong (n - 1) (!b) (x + 38)
  | 39 => pong (n - 1) (!b) (x + 39)
  | _ => pong (n - 1) b x
end

/-- From the review (ValStepNarrow): a `Bool` result. -/
partial def pred (k : Nat) (a : UInt64) : Bool :=
  if k == 0 then a % 2 == 0 else
  match k % 41 with
  | 0 => pred (k - 1) (a * 7 + 0 + a / 3)
  | 1 => pred (k - 1) (a * 7 + 1 + a / 3)
  | 2 => if a % 29 == 2 then a % 5 == 2 else pred (k - 1) (a * 31 + 2)
  | 3 => pred (k - 1) (a * 7 + 3 + a / 3)
  | 4 => pred (k - 1) (a * 7 + 4 + a / 3)
  | 5 => pred (k - 1) (a * 7 + 5 + a / 3)
  | 6 => pred (k - 1) (a * 7 + 6 + a / 3)
  | 7 => pred (k - 1) (a * 7 + 7 + a / 3)
  | 8 => if a % 29 == 8 then a % 11 == 2 else pred (k - 1) (a * 31 + 8)
  | 9 => pred (k - 1) (a * 7 + 9 + a / 3)
  | 10 => pred (k - 1) (a * 7 + 10 + a / 3)
  | 11 => pred (k - 1) (a * 7 + 11 + a / 3)
  | 12 => pred (k - 1) (a * 7 + 12 + a / 3)
  | 13 => pred (k - 1) (a * 7 + 13 + a / 3)
  | 14 => if a % 29 == 14 then a % 17 == 2 else pred (k - 1) (a * 31 + 14)
  | 15 => pred (k - 1) (a * 7 + 15 + a / 3)
  | 16 => pred (k - 1) (a * 7 + 16 + a / 3)
  | 17 => pred (k - 1) (a * 7 + 17 + a / 3)
  | 18 => pred (k - 1) (a * 7 + 18 + a / 3)
  | 19 => pred (k - 1) (a * 7 + 19 + a / 3)
  | 20 => if a % 29 == 20 then a % 23 == 2 else pred (k - 1) (a * 31 + 20)
  | 21 => pred (k - 1) (a * 7 + 21 + a / 3)
  | 22 => pred (k - 1) (a * 7 + 22 + a / 3)
  | 23 => pred (k - 1) (a * 7 + 23 + a / 3)
  | 24 => pred (k - 1) (a * 7 + 24 + a / 3)
  | 25 => pred (k - 1) (a * 7 + 25 + a / 3)
  | 26 => if a % 29 == 26 then a % 29 == 2 else pred (k - 1) (a * 31 + 26)
  | 27 => pred (k - 1) (a * 7 + 27 + a / 3)
  | 28 => pred (k - 1) (a * 7 + 28 + a / 3)
  | 29 => pred (k - 1) (a * 7 + 29 + a / 3)
  | 30 => pred (k - 1) (a * 7 + 30 + a / 3)
  | 31 => pred (k - 1) (a * 7 + 31 + a / 3)
  | 32 => if a % 29 == 3 then a % 35 == 2 else pred (k - 1) (a * 31 + 32)
  | 33 => pred (k - 1) (a * 7 + 33 + a / 3)
  | 34 => pred (k - 1) (a * 7 + 34 + a / 3)
  | 35 => pred (k - 1) (a * 7 + 35 + a / 3)
  | 36 => pred (k - 1) (a * 7 + 36 + a / 3)
  | 37 => pred (k - 1) (a * 7 + 37 + a / 3)
  | 38 => if a % 29 == 9 then a % 41 == 2 else pred (k - 1) (a * 31 + 38)
  | 39 => pred (k - 1) (a * 7 + 39 + a / 3)
  | _ => pred (k - 1) a

/-- From the review (ValStepNarrow): a `Bool × UInt8` result. -/
partial def bp (k : Nat) (a : UInt64) : Bool × UInt8 :=
  if k == 0 then (a % 2 == 0, (a % 253).toUInt8) else
  match k % 41 with
  | 0 => bp (k - 1) (a * 7 + 0 + a / 3)
  | 1 => bp (k - 1) (a * 7 + 1 + a / 3)
  | 2 => if a % 29 == 2 then (a % 5 == 2, (a % 251).toUInt8 + 134) else bp (k - 1) (a * 31 + 2)
  | 3 => bp (k - 1) (a * 7 + 3 + a / 3)
  | 4 => bp (k - 1) (a * 7 + 4 + a / 3)
  | 5 => bp (k - 1) (a * 7 + 5 + a / 3)
  | 6 => bp (k - 1) (a * 7 + 6 + a / 3)
  | 7 => bp (k - 1) (a * 7 + 7 + a / 3)
  | 8 => if a % 29 == 8 then (a % 11 == 2, (a % 251).toUInt8 + 152) else bp (k - 1) (a * 31 + 8)
  | 9 => bp (k - 1) (a * 7 + 9 + a / 3)
  | 10 => bp (k - 1) (a * 7 + 10 + a / 3)
  | 11 => bp (k - 1) (a * 7 + 11 + a / 3)
  | 12 => bp (k - 1) (a * 7 + 12 + a / 3)
  | 13 => bp (k - 1) (a * 7 + 13 + a / 3)
  | 14 => if a % 29 == 14 then (a % 17 == 2, (a % 251).toUInt8 + 170) else bp (k - 1) (a * 31 + 14)
  | 15 => bp (k - 1) (a * 7 + 15 + a / 3)
  | 16 => bp (k - 1) (a * 7 + 16 + a / 3)
  | 17 => bp (k - 1) (a * 7 + 17 + a / 3)
  | 18 => bp (k - 1) (a * 7 + 18 + a / 3)
  | 19 => bp (k - 1) (a * 7 + 19 + a / 3)
  | 20 => if a % 29 == 20 then (a % 23 == 2, (a % 251).toUInt8 + 188) else bp (k - 1) (a * 31 + 20)
  | 21 => bp (k - 1) (a * 7 + 21 + a / 3)
  | 22 => bp (k - 1) (a * 7 + 22 + a / 3)
  | 23 => bp (k - 1) (a * 7 + 23 + a / 3)
  | 24 => bp (k - 1) (a * 7 + 24 + a / 3)
  | 25 => bp (k - 1) (a * 7 + 25 + a / 3)
  | 26 => if a % 29 == 26 then (a % 29 == 2, (a % 251).toUInt8 + 206) else bp (k - 1) (a * 31 + 26)
  | 27 => bp (k - 1) (a * 7 + 27 + a / 3)
  | 28 => bp (k - 1) (a * 7 + 28 + a / 3)
  | 29 => bp (k - 1) (a * 7 + 29 + a / 3)
  | 30 => bp (k - 1) (a * 7 + 30 + a / 3)
  | 31 => bp (k - 1) (a * 7 + 31 + a / 3)
  | 32 => if a % 29 == 3 then (a % 35 == 2, (a % 251).toUInt8 + 224) else bp (k - 1) (a * 31 + 32)
  | 33 => bp (k - 1) (a * 7 + 33 + a / 3)
  | 34 => bp (k - 1) (a * 7 + 34 + a / 3)
  | 35 => bp (k - 1) (a * 7 + 35 + a / 3)
  | 36 => bp (k - 1) (a * 7 + 36 + a / 3)
  | 37 => bp (k - 1) (a * 7 + 37 + a / 3)
  | 38 => if a % 29 == 9 then (a % 41 == 2, (a % 251).toUInt8 + 242) else bp (k - 1) (a * 31 + 38)
  | 39 => bp (k - 1) (a * 7 + 39 + a / 3)
  | _ => bp (k - 1) a

/-- From the review (ValStepTie): the `done` tuple is the representative. -/
partial def tupC (k : Nat) (a : UInt64) (b : Bool) : UInt64 × UInt64 × UInt8 :=
  if k == 0 then (a, (if b then 1 else 2), 201) else
  match k % 41 with
  | 0 => tupC (k - 1) (a * 7 + 0 + (if b then 1 else 0)) (a % 3 == 0)
  | 1 => tupC (k - 1) (a * 7 + 1 + (if b then 1 else 0)) (a % 3 == 1)
  | 2 => tupC (k - 1) (a * 7 + 2 + (if b then 1 else 0)) (a % 3 == 2)
  | 3 => if a % 13 == 3 then (a, a * 6, (a % 251).toUInt8 + 16) else tupC (k - 1) (a * 31 + 3) (!b)
  | 4 => tupC (k - 1) (a * 7 + 4 + (if b then 1 else 0)) (a % 3 == 1)
  | 5 => tupC (k - 1) (a * 7 + 5 + (if b then 1 else 0)) (a % 3 == 2)
  | 6 => tupC (k - 1) (a * 7 + 6 + (if b then 1 else 0)) (a % 3 == 0)
  | 7 => tupC (k - 1) (a * 7 + 7 + (if b then 1 else 0)) (a % 3 == 1)
  | 8 => tupC (k - 1) (a * 7 + 8 + (if b then 1 else 0)) (a % 3 == 2)
  | 9 => tupC (k - 1) (a * 7 + 9 + (if b then 1 else 0)) (a % 3 == 0)
  | 10 => if a % 13 == 10 then (a, a * 13, (a % 251).toUInt8 + 51) else tupC (k - 1) (a * 31 + 10) (!b)
  | 11 => tupC (k - 1) (a * 7 + 11 + (if b then 1 else 0)) (a % 3 == 2)
  | 12 => tupC (k - 1) (a * 7 + 12 + (if b then 1 else 0)) (a % 3 == 0)
  | 13 => tupC (k - 1) (a * 7 + 13 + (if b then 1 else 0)) (a % 3 == 1)
  | 14 => tupC (k - 1) (a * 7 + 14 + (if b then 1 else 0)) (a % 3 == 2)
  | 15 => tupC (k - 1) (a * 7 + 15 + (if b then 1 else 0)) (a % 3 == 0)
  | 16 => tupC (k - 1) (a * 7 + 16 + (if b then 1 else 0)) (a % 3 == 1)
  | 17 => if a % 13 == 4 then (a, a * 20, (a % 251).toUInt8 + 86) else tupC (k - 1) (a * 31 + 17) (!b)
  | 18 => tupC (k - 1) (a * 7 + 18 + (if b then 1 else 0)) (a % 3 == 0)
  | 19 => tupC (k - 1) (a * 7 + 19 + (if b then 1 else 0)) (a % 3 == 1)
  | 20 => tupC (k - 1) (a * 7 + 20 + (if b then 1 else 0)) (a % 3 == 2)
  | 21 => tupC (k - 1) (a * 7 + 21 + (if b then 1 else 0)) (a % 3 == 0)
  | 22 => tupC (k - 1) (a * 7 + 22 + (if b then 1 else 0)) (a % 3 == 1)
  | 23 => tupC (k - 1) (a * 7 + 23 + (if b then 1 else 0)) (a % 3 == 2)
  | 24 => if a % 13 == 11 then (a, a * 27, (a % 251).toUInt8 + 121) else tupC (k - 1) (a * 31 + 24) (!b)
  | 25 => tupC (k - 1) (a * 7 + 25 + (if b then 1 else 0)) (a % 3 == 1)
  | 26 => tupC (k - 1) (a * 7 + 26 + (if b then 1 else 0)) (a % 3 == 2)
  | 27 => tupC (k - 1) (a * 7 + 27 + (if b then 1 else 0)) (a % 3 == 0)
  | 28 => tupC (k - 1) (a * 7 + 28 + (if b then 1 else 0)) (a % 3 == 1)
  | 29 => tupC (k - 1) (a * 7 + 29 + (if b then 1 else 0)) (a % 3 == 2)
  | 30 => tupC (k - 1) (a * 7 + 30 + (if b then 1 else 0)) (a % 3 == 0)
  | 31 => if a % 13 == 5 then (a, a * 34, (a % 251).toUInt8 + 156) else tupC (k - 1) (a * 31 + 31) (!b)
  | 32 => tupC (k - 1) (a * 7 + 32 + (if b then 1 else 0)) (a % 3 == 2)
  | 33 => tupC (k - 1) (a * 7 + 33 + (if b then 1 else 0)) (a % 3 == 0)
  | 34 => tupC (k - 1) (a * 7 + 34 + (if b then 1 else 0)) (a % 3 == 1)
  | 35 => tupC (k - 1) (a * 7 + 35 + (if b then 1 else 0)) (a % 3 == 2)
  | 36 => tupC (k - 1) (a * 7 + 36 + (if b then 1 else 0)) (a % 3 == 0)
  | 37 => tupC (k - 1) (a * 7 + 37 + (if b then 1 else 0)) (a % 3 == 1)
  | 38 => if a % 13 == 12 then (a, a * 41, (a % 251).toUInt8 + 191) else tupC (k - 1) (a * 31 + 38) (!b)
  | 39 => tupC (k - 1) (a * 7 + 39 + (if b then 1 else 0)) (a % 3 == 0)
  | _ => tupC (k - 1) a b

def runCase (c : String) (n : Nat) : IO Unit :=
  match c with
  | "loop" => IO.println s!"loop {n}: {loop n 1 2 3}"
  | "mixed" => IO.println s!"mixed {n}: {mixed true 7 "m" (Array.range 16) n 5}"
  | "floaty" => IO.println s!"floaty {n}: {(floaty (n.toFloat / 7.0) 1.0 / 1.0e290).floor.toUInt64}"
  | "pair" => IO.println s!"pair {n}: {pairLoop n 1 2}"
  | "ping" => IO.println s!"ping {n}: {ping n "start"}"
  | "narrow" =>
    for s in [5, 77, 1234567] do
      let a := n.toUInt64 * 977 + s
      IO.println s!"narrow {n} {s}: {pred n a} {bp n a}"
  | "tupc" =>
    let (p, q, r) := tupC n (n.toUInt64 * 977 + 5) (n % 2 == 0)
    IO.println s!"tupc {n}: {p} {q} {r}"
  | _ => IO.println s!"unknown case {c}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [c, n] => runCase c (n.toNat?.getD 0)
  | _ =>
    for c in ["loop", "mixed", "floaty", "pair", "ping", "narrow", "tupc"] do
      for n in [0, 1, 2, 3, 40, 41, 44, 1000, 30001] do runCase c n
  pure 0
