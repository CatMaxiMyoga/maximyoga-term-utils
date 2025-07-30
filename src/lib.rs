#![deny(missing_docs)]
#![deny(clippy::panic)]
#![deny(unused_must_use)]
#![deny(unused_crate_dependencies)]

//! Provides multiple terminal utilities.

pub mod cli;

/// Temporary Placeholder Function to simulate functionality
pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
