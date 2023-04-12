use crate::{stack::STACK_TOP_SIZE, StackTopState};

use super::{Felt, StarkField};
use winter_utils::collections::Vec;

// PROGRAM OUTPUTS
// ================================================================================================

/// Output container for Miden VM programs.
///
/// Miden program outputs contain the full state of the stack at the end of execution as well as the
/// addresses in the overflow table which are required to reconstruct the table (when combined with
/// the overflow values from the stack state).
///
/// `stack` is expected to be ordered as if they elements were popped off the stack one by one.
/// Thus, the value at the top of the stack is expected to be in the first position, and the order
/// of the rest of the output elements will also match the order on the stack.
///
/// `overflow_addrs` is expected to start with the `prev` address value from the first row in the
/// overflow table (the row representing the deepest element in the stack) and then be followed by
/// the address (`clk` value) of each row in the table starting from the deepest element in the
/// stack and finishing with the row which was added to the table last.
#[derive(Debug, Clone, Default)]
pub struct ProgramOutputs {
    /// The elements on the stack at the end of execution.
    pub stack: Vec<u64>,
    /// The overflow table row addresse required to reconstruct the final state of the table.
    pub overflow_addrs: Vec<u64>,
}

impl ProgramOutputs {
    // CONSTRUCTOR
    // --------------------------------------------------------------------------------------------
    pub fn new(stack: Vec<u64>, overflow_addrs: Vec<u64>) -> Self {
        debug_assert!(
            are_valid_elements(&stack),
            "stack outputs contain values that are not valid field elements",
        );
        debug_assert!(
            are_valid_elements(&overflow_addrs),
            "overflow address outputs contain values that are not valid field elements",
        );

        Self {
            stack,
            overflow_addrs,
        }
    }

    pub fn from_elements(stack: Vec<Felt>, overflow_addrs: Vec<Felt>) -> Self {
        let stack = stack.iter().map(|&v| v.as_int()).collect::<Vec<_>>();
        let overflow_addrs = overflow_addrs
            .iter()
            .map(|&v| v.as_int())
            .collect::<Vec<_>>();

        Self {
            stack,
            overflow_addrs,
        }
    }

    // PUBLIC ACCESSORS
    // --------------------------------------------------------------------------------------------

    /// Returns the stack outputs, which is state of the stack at the end of execution converted to
    /// integers.
    pub fn stack(&self) -> &[u64] {
        &self.stack
    }

    /// Returns the number of requested stack outputs or returns the full stack if fewer than the
    /// requested number of stack values exist.
    pub fn stack_outputs(&self, num_outputs: usize) -> &[u64] {
        if num_outputs < self.stack.len() {
            return &self.stack[..num_outputs];
        }

        &self.stack
    }

    /// Returns the state of the top of the stack at the end of execution.
    pub fn stack_top(&self) -> StackTopState {
        self.stack
            .iter()
            .take(STACK_TOP_SIZE)
            .map(|v| Felt::new(*v))
            .collect::<Vec<_>>()
            .try_into()
            .expect("failed to convert vector to array")
    }

    /// Returns the overflow address outputs, which are the addresses required to reconstruct the
    /// overflow table (when combined with the stack overflow values) converted to integers.
    pub fn overflow_addrs(&self) -> &[u64] {
        &self.overflow_addrs
    }

    /// Returns true if the overflow table outputs are non-empty.
    pub fn has_overflow(&self) -> bool {
        !self.overflow_addrs.is_empty()
    }

    /// Returns the previous address `prev` for the first row in the stack overflow table
    pub fn overflow_prev(&self) -> Felt {
        Felt::new(self.overflow_addrs[0])
    }

    /// Returns (address, value) for all rows which were on the overflow table at the end of
    /// execution in the order in which they were added to the table (deepest stack item first).
    pub fn stack_overflow(&self) -> Vec<(Felt, Felt)> {
        let mut overflow = Vec::with_capacity(self.overflow_addrs.len() - 1);
        for (addr, val) in self
            .overflow_addrs
            .iter()
            .skip(1)
            .zip(self.stack.iter().skip(STACK_TOP_SIZE).rev())
        {
            overflow.push((Felt::new(*addr), Felt::new(*val)));
        }

        overflow
    }

    // PUBLIC MUTATORS
    // --------------------------------------------------------------------------------------------

    /// Returns mutable access to the stack outputs, to be used for testing or running examples.
    /// TODO: this should be marked with #[cfg(test)] attribute, but that currently won't work with
    /// the integration test handler util.
    pub fn stack_mut(&mut self) -> &mut [u64] {
        &mut self.stack
    }
}

// HELPER FUNCTIONS
// ================================================================================================

/// Verify that each element in the provided slice of outputs is a valid field element.
fn are_valid_elements(outputs: &[u64]) -> bool {
    for val in outputs {
        if *val >= Felt::MODULUS {
            return false;
        }
    }
    true
}
