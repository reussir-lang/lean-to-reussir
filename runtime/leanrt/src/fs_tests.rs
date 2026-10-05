//! Unit test of the last-error slot's wiring (`ok`, `errno`, `error_kind`,
//! `error_fname`, `error_details`): an error lean-runtime decodes reaches the
//! slot's fields as lean2rr's generated code reads them. The decoding
//! itself (every errno against native Lean) is lean-runtime's, tested there
//! (`io::error`'s tests).
use super::*;

fn slot() -> (bool, u32, u32, Vec<u8>, Vec<u8>) {
    let (f, d) = (error_fname(), error_details());
    let r = (ok(), error_kind(), errno(), crate::string::bytes(&f).to_vec(), crate::string::bytes(&d).to_vec());
    drop((f, d));
    r
}

/// One test (the last-error slot is global).
#[test]
fn last_error_slot() {
    // ENOENT with a file name: `noFileOrDirectory` (builder 4).
    set_err(IoError::decode_io_error(2, Some(b"f")));
    assert_eq!(slot(), (false, 4, 2, b"f".to_vec(), b"no such file or directory".to_vec()));
    // EBADF with a file name: `invalidArgument` with the name (builder 3).
    set_err(IoError::decode_io_error(9, Some(b"f")));
    assert_eq!(slot(), (false, 3, 9, b"f".to_vec(), b"bad file descriptor".to_vec()));
    // A libuv code without a file name: `otherError` (builder 0), the code
    // its positive errno.
    set_err(IoError::decode_uv_error(-10, None));
    assert_eq!(slot(), (false, 0, 10, Vec::new(), b"Unknown system error -10".to_vec()));
    // A user error: builder 23, no code, the message as its details.
    set_err(IoError::user_error("boom"));
    assert_eq!(slot(), (false, 23, 0, Vec::new(), b"boom".to_vec()));
    set_ok();
    assert_eq!(slot(), (true, 0, 0, Vec::new(), Vec::new()));
}
