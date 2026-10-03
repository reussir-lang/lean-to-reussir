//! Unit test of the error decoding (`errno`, `error_kind`, `error_details`)
//! against native Lean 4.34.0: for every errno 0..=140, what
//! `lean_decode_io_error(e, "f")` and `lean_decode_uv_error(-e, "f")` of
//! Lean's runtime build (the constructor number of runtime/README.md's
//! table, the stored code, the details). The table was printed by a native
//! Lean program calling the two C functions (aarch64 Linux, libuv 1.48).
use super::*;

/// (errno, io kind, io code, io details, uv kind, uv code, uv details)
const NATIVE: &[(i32, u32, u32, &str, u32, u32, &str)] = &[
    (0, 0, 0, "Unknown system error 0", 0, 0, "Unknown system error 0"),
    (1, 6, 1, "operation not permitted", 6, 1, "operation not permitted"),
    (2, 4, 2, "no such file or directory", 4, 2, "no such file or directory"),
    (3, 12, 3, "no such process", 12, 3, "no such process"),
    (4, 1, 4, "interrupted system call", 1, 4, "interrupted system call"),
    (5, 15, 5, "i/o error", 15, 5, "i/o error"),
    (6, 12, 6, "no such device or address", 12, 6, "no such device or address"),
    (7, 8, 7, "argument list too long", 8, 7, "argument list too long"),
    (8, 3, 8, "Unknown system error -8", 3, 8, "Unknown system error -8"),
    (9, 3, 9, "bad file descriptor", 3, 9, "bad file descriptor"),
    (10, 12, 10, "no such process", 0, 10, "Unknown system error -10"),
    (11, 8, 11, "resource temporarily unavailable", 8, 11, "resource temporarily unavailable"),
    (12, 8, 12, "not enough memory", 8, 12, "not enough memory"),
    (13, 6, 13, "permission denied", 6, 13, "permission denied"),
    (14, 0, 14, "bad address in system call argument", 0, 14, "bad address in system call argument"),
    (15, 0, 15, "Unknown system error -15", 0, 15, "Unknown system error -15"),
    (16, 21, 16, "resource busy or locked", 21, 16, "resource busy or locked"),
    (17, 14, 17, "file already exists", 14, 17, "file already exists"),
    (18, 22, 18, "cross-device link not permitted", 22, 18, "cross-device link not permitted"),
    (19, 22, 19, "no such device", 22, 19, "no such device"),
    (20, 10, 20, "not a directory", 10, 20, "not a directory"),
    (21, 10, 21, "illegal operation on a directory", 10, 21, "illegal operation on a directory"),
    (22, 3, 22, "invalid argument", 3, 22, "invalid argument"),
    (23, 8, 23, "file table overflow", 8, 23, "file table overflow"),
    (24, 8, 24, "too many open files", 8, 24, "too many open files"),
    (25, 17, 25, "inappropriate ioctl for device", 17, 25, "inappropriate ioctl for device"),
    (26, 21, 26, "text file is busy", 21, 26, "text file is busy"),
    (27, 6, 27, "file too large", 6, 27, "file too large"),
    (28, 8, 28, "no space left on device", 8, 28, "no space left on device"),
    (29, 22, 29, "invalid seek", 22, 29, "invalid seek"),
    (30, 6, 30, "read-only file system", 6, 30, "read-only file system"),
    (31, 8, 31, "too many links", 8, 31, "too many links"),
    (32, 18, 32, "broken pipe", 18, 32, "broken pipe"),
    (33, 3, 33, "invalid argument", 0, 33, "Unknown system error -33"),
    (34, 22, 34, "result too large", 22, 34, "result too large"),
    (35, 21, 35, "resource busy or locked", 0, 35, "Unknown system error -35"),
    (36, 3, 36, "name too long", 3, 36, "name too long"),
    (37, 8, 37, "resource temporarily unavailable", 0, 37, "Unknown system error -37"),
    (38, 22, 38, "function not implemented", 22, 38, "function not implemented"),
    (39, 16, 39, "directory not empty", 16, 39, "directory not empty"),
    (40, 3, 40, "too many symbolic links encountered", 3, 40, "too many symbolic links encountered"),
    (41, 0, 41, "Unknown system error -41", 0, 41, "Unknown system error -41"),
    (42, 12, 42, "no data available", 0, 42, "Unknown system error -42"),
    (43, 18, 43, "broken pipe", 0, 43, "Unknown system error -43"),
    (44, 0, 44, "Unknown system error -44", 0, 44, "Unknown system error -44"),
    (45, 0, 45, "Unknown system error -45", 0, 45, "Unknown system error -45"),
    (46, 0, 46, "Unknown system error -46", 0, 46, "Unknown system error -46"),
    (47, 0, 47, "Unknown system error -47", 0, 47, "Unknown system error -47"),
    (48, 0, 48, "Unknown system error -48", 0, 48, "Unknown system error -48"),
    (49, 0, 49, "protocol driver not attached", 0, 49, "protocol driver not attached"),
    (50, 0, 50, "Unknown system error -50", 0, 50, "Unknown system error -50"),
    (51, 0, 51, "Unknown system error -51", 0, 51, "Unknown system error -51"),
    (52, 0, 52, "Unknown system error -52", 0, 52, "Unknown system error -52"),
    (53, 0, 53, "Unknown system error -53", 0, 53, "Unknown system error -53"),
    (54, 0, 54, "Unknown system error -54", 0, 54, "Unknown system error -54"),
    (55, 0, 55, "Unknown system error -55", 0, 55, "Unknown system error -55"),
    (56, 0, 56, "Unknown system error -56", 0, 56, "Unknown system error -56"),
    (57, 0, 57, "Unknown system error -57", 0, 57, "Unknown system error -57"),
    (58, 0, 58, "Unknown system error -58", 0, 58, "Unknown system error -58"),
    (59, 0, 59, "Unknown system error -59", 0, 59, "Unknown system error -59"),
    (60, 3, 60, "invalid argument", 0, 60, "Unknown system error -60"),
    (61, 12, 61, "no data available", 12, 61, "no data available"),
    (62, 20, 62, "connection timed out", 0, 62, "Unknown system error -62"),
    (63, 8, 63, "no buffer space available", 0, 63, "Unknown system error -63"),
    (64, 0, 64, "machine is not on the network", 0, 64, "machine is not on the network"),
    (65, 0, 65, "Unknown system error -65", 0, 65, "Unknown system error -65"),
    (66, 0, 66, "Unknown system error -66", 0, 66, "Unknown system error -66"),
    (67, 18, 67, "connection reset by peer", 0, 67, "Unknown system error -67"),
    (68, 0, 68, "Unknown system error -68", 0, 68, "Unknown system error -68"),
    (69, 0, 69, "Unknown system error -69", 0, 69, "Unknown system error -69"),
    (70, 0, 70, "Unknown system error -70", 0, 70, "Unknown system error -70"),
    (71, 19, 71, "protocol error", 19, 71, "protocol error"),
    (72, 0, 72, "Unknown system error -72", 0, 72, "Unknown system error -72"),
    (73, 0, 73, "Unknown system error -73", 0, 73, "Unknown system error -73"),
    (74, 19, 74, "protocol error", 0, 74, "Unknown system error -74"),
    (75, 0, 75, "value too large for defined data type", 0, 75, "value too large for defined data type"),
    (76, 0, 76, "Unknown system error -76", 0, 76, "Unknown system error -76"),
    (77, 0, 77, "Unknown system error -77", 0, 77, "Unknown system error -77"),
    (78, 0, 78, "Unknown system error -78", 0, 78, "Unknown system error -78"),
    (79, 0, 79, "Unknown system error -79", 0, 79, "Unknown system error -79"),
    (80, 0, 80, "Unknown system error -80", 0, 80, "Unknown system error -80"),
    (81, 0, 81, "Unknown system error -81", 0, 81, "Unknown system error -81"),
    (82, 0, 82, "Unknown system error -82", 0, 82, "Unknown system error -82"),
    (83, 0, 83, "Unknown system error -83", 0, 83, "Unknown system error -83"),
    (84, 3, 84, "illegal byte sequence", 3, 84, "illegal byte sequence"),
    (85, 0, 85, "Unknown system error -85", 0, 85, "Unknown system error -85"),
    (86, 0, 86, "Unknown system error -86", 0, 86, "Unknown system error -86"),
    (87, 0, 87, "Unknown system error -87", 0, 87, "Unknown system error -87"),
    (88, 3, 88, "socket operation on non-socket", 3, 88, "socket operation on non-socket"),
    (89, 3, 89, "destination address required", 3, 89, "destination address required"),
    (90, 8, 90, "message too long", 8, 90, "message too long"),
    (91, 19, 91, "protocol wrong type for socket", 19, 91, "protocol wrong type for socket"),
    (92, 22, 92, "protocol not available", 22, 92, "protocol not available"),
    (93, 19, 93, "protocol not supported", 19, 93, "protocol not supported"),
    (94, 0, 94, "socket type not supported", 0, 94, "socket type not supported"),
    (95, 22, 95, "operation not supported on socket", 22, 95, "operation not supported on socket"),
    (96, 0, 96, "Unknown system error -96", 0, 96, "Unknown system error -96"),
    (97, 22, 97, "address family not supported", 22, 97, "address family not supported"),
    (98, 21, 98, "address already in use", 21, 98, "address already in use"),
    (99, 22, 99, "address not available", 22, 99, "address not available"),
    (100, 18, 100, "network is down", 18, 100, "network is down"),
    (101, 12, 101, "network is unreachable", 12, 101, "network is unreachable"),
    (102, 18, 102, "connection reset by peer", 0, 102, "Unknown system error -102"),
    (103, 6, 103, "software caused connection abort", 6, 103, "software caused connection abort"),
    (104, 18, 104, "connection reset by peer", 18, 104, "connection reset by peer"),
    (105, 8, 105, "no buffer space available", 8, 105, "no buffer space available"),
    (106, 14, 106, "socket is already connected", 14, 106, "socket is already connected"),
    (107, 3, 107, "socket is not connected", 3, 107, "socket is not connected"),
    (108, 0, 108, "cannot send after transport endpoint shutdown", 0, 108, "cannot send after transport endpoint shutdown"),
    (109, 0, 109, "Unknown system error -109", 0, 109, "Unknown system error -109"),
    (110, 20, 110, "connection timed out", 20, 110, "connection timed out"),
    (111, 12, 111, "connection refused", 12, 111, "connection refused"),
    (112, 0, 112, "host is down", 0, 112, "host is down"),
    (113, 12, 113, "host is unreachable", 12, 113, "host is unreachable"),
    (114, 0, 114, "connection already in progress", 0, 114, "connection already in progress"),
    (115, 14, 115, "socket is already connected", 0, 115, "Unknown system error -115"),
    (116, 0, 116, "Unknown system error -116", 0, 116, "Unknown system error -116"),
    (117, 0, 117, "Unknown system error -117", 0, 117, "Unknown system error -117"),
    (118, 0, 118, "Unknown system error -118", 0, 118, "Unknown system error -118"),
    (119, 0, 119, "Unknown system error -119", 0, 119, "Unknown system error -119"),
    (120, 0, 120, "Unknown system error -120", 0, 120, "Unknown system error -120"),
    (121, 0, 121, "remote I/O error", 0, 121, "remote I/O error"),
    (122, 0, 122, "Unknown system error -122", 0, 122, "Unknown system error -122"),
    (123, 0, 123, "Unknown system error -123", 0, 123, "Unknown system error -123"),
    (124, 0, 124, "Unknown system error -124", 0, 124, "Unknown system error -124"),
    (125, 0, 125, "operation canceled", 0, 125, "operation canceled"),
    (126, 0, 126, "Unknown system error -126", 0, 126, "Unknown system error -126"),
    (127, 0, 127, "Unknown system error -127", 0, 127, "Unknown system error -127"),
    (128, 0, 128, "Unknown system error -128", 0, 128, "Unknown system error -128"),
    (129, 0, 129, "Unknown system error -129", 0, 129, "Unknown system error -129"),
    (130, 0, 130, "Unknown system error -130", 0, 130, "Unknown system error -130"),
    (131, 0, 131, "Unknown system error -131", 0, 131, "Unknown system error -131"),
    (132, 0, 132, "Unknown system error -132", 0, 132, "Unknown system error -132"),
    (133, 0, 133, "Unknown system error -133", 0, 133, "Unknown system error -133"),
    (134, 0, 134, "Unknown system error -134", 0, 134, "Unknown system error -134"),
    (135, 0, 135, "Unknown system error -135", 0, 135, "Unknown system error -135"),
    (136, 0, 136, "Unknown system error -136", 0, 136, "Unknown system error -136"),
    (137, 0, 137, "Unknown system error -137", 0, 137, "Unknown system error -137"),
    (138, 0, 138, "Unknown system error -138", 0, 138, "Unknown system error -138"),
    (139, 0, 139, "Unknown system error -139", 0, 139, "Unknown system error -139"),
    (140, 0, 140, "Unknown system error -140", 0, 140, "Unknown system error -140"),
];

fn last_error() -> (u32, u32, Vec<u8>) {
    let d = error_details();
    let r = (error_kind(), errno(), crate::string::bytes(&d).to_vec());
    drop(d);
    r
}

/// One test (the last-error slot is global): every mismatch is reported.
#[test]
fn decode_matches_native() {
    let mut bad = Vec::new();
    for &(e, k, c, d, uk, uc, ud) in NATIVE {
        set_err(e, Some(b"f"));
        let (k1, c1, d1) = last_error();
        let d1 = String::from_utf8_lossy(&d1).into_owned();
        if (k1, c1, d1.as_str()) != (k, c, d) {
            bad.push(format!("decode_io_error({e}): ({k1}, {c1}, {d1:?}), native ({k}, {c}, {d:?})"));
        }
        set_err_uv(e, Some(b"f"));
        let (k1, c1, d1) = last_error();
        let d1 = String::from_utf8_lossy(&d1).into_owned();
        if (k1, c1, d1.as_str()) != (uk, uc, ud) {
            bad.push(format!("decode_uv_error(-{e}): ({k1}, {c1}, {d1:?}), native ({uk}, {uc}, {ud:?})"));
        }
    }
    set_ok();
    assert!(bad.is_empty(), "{} mismatches:\n{}", bad.len(), bad.join("\n"));
}
