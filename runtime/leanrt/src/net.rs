//! The event loop (placeholder).
use std::time::{Duration, Instant};

pub fn due(_now: Instant) -> bool {
    false
}

pub fn wait(_timeout: Option<Duration>) -> bool {
    false
}

pub fn deliver() {}
