#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;

use std::fmt::Write;
use vm_core::{
    chiplets::hasher::Digest,
    utils::{collections::Vec, ByteWriter, Deserializable, PushMany, Serializable},
    ExtensionOf, ProgramOutputs, CLK_COL_IDX, FMP_COL_IDX, ONE, STACK_TRACE_OFFSET, ZERO,
};
use winter_air::{
    Air, AirContext, Assertion, AuxTraceRandElements, EvaluationFrame,
    ProofOptions as WinterProofOptions, TraceInfo, TransitionConstraintDegree,
};

mod chiplets;
mod options;
mod range;
pub mod stack;
mod utils;
use utils::TransitionConstraintRange;

// EXPORTS
// ================================================================================================

pub use options::ProofOptions;
pub use vm_core::{utils::ToElements, Felt, FieldElement, StarkField};
pub use winter_air::{FieldExtension, HashFunction};
use winter_crypto::{hashers::Blake2s_256, ElementHasher};

// PROCESSOR AIR
// ================================================================================================

/// TODO: add docs
pub struct ProcessorAir {
    context: AirContext<Felt>,
    stack_inputs: Vec<Felt>,
    outputs: ProgramOutputs,
    constraint_ranges: TransitionConstraintRange,
}

impl ProcessorAir {
    /// Returns last step of the execution trace.
    pub fn last_step(&self) -> usize {
        self.trace_length() - self.context().num_transition_exemptions()
    }
}

impl Air for ProcessorAir {
    type BaseField = Felt;
    type PublicInputs = PublicInputs;

    fn new(trace_info: TraceInfo, pub_inputs: PublicInputs, options: WinterProofOptions) -> Self {
        // --- system -----------------------------------------------------------------------------
        let mut main_degrees = vec![
            TransitionConstraintDegree::new(1), // clk' = clk + 1
        ];

        // --- stack constraints -------------------------------------------------------------------
        let mut stack_degrees = stack::get_transition_constraint_degrees();
        main_degrees.append(&mut stack_degrees);

        // --- range checker ----------------------------------------------------------------------
        let mut range_checker_degrees = range::get_transition_constraint_degrees();
        main_degrees.append(&mut range_checker_degrees);

        let aux_degrees = range::get_aux_transition_constraint_degrees();

        // --- chiplets (hasher, bitwise, memory) -------------------------
        let mut chiplets_degrees = chiplets::get_transition_constraint_degrees();
        main_degrees.append(&mut chiplets_degrees);

        // Define the transition constraint ranges.
        let constraint_ranges = TransitionConstraintRange::new(
            1,
            stack::get_transition_constraint_count(),
            range::get_transition_constraint_count(),
            chiplets::get_transition_constraint_count(),
        );

        // Define the number of boundary constraints for the main execution trace segment.
        // TODO: determine dynamically
        let num_main_assertions =
            2 + stack::NUM_ASSERTIONS + range::NUM_ASSERTIONS + chiplets::NUM_ASSERTIONS;

        // Define the number of boundary constraints for the auxiliary execution trace segment.
        let num_aux_assertions = stack::NUM_AUX_ASSERTIONS + range::NUM_AUX_ASSERTIONS;

        // Create the context and set the number of transition constraint exemptions to two; this
        // allows us to inject random values into the last row of the execution trace.
        let context = AirContext::new_multi_segment(
            trace_info,
            main_degrees,
            aux_degrees,
            num_main_assertions,
            num_aux_assertions,
            options,
        )
        .set_num_transition_exemptions(2);

        Self {
            context,
            stack_inputs: pub_inputs.stack_inputs,
            outputs: pub_inputs.outputs,
            constraint_ranges,
        }
    }

    // PERIODIC COLUMNS
    // --------------------------------------------------------------------------------------------

    /// Returns a set of periodic columns for the ProcessorAir.
    fn get_periodic_column_values(&self) -> Vec<Vec<Felt>> {
        chiplets::get_periodic_column_values()
    }

    // ASSERTIONS
    // --------------------------------------------------------------------------------------------

    #[allow(clippy::vec_init_then_push)]
    fn get_assertions(&self) -> Vec<Assertion<Felt>> {
        let mut result = Vec::new();

        // --- set assertions for the first step --------------------------------------------------
        // first value of clk is 0
        result.push(Assertion::single(CLK_COL_IDX, 0, Felt::ZERO));

        // first value of fmp is 2^30
        result.push(Assertion::single(FMP_COL_IDX, 0, Felt::new(2u64.pow(30))));

        // add initial assertions for the stack.
        stack::get_assertions_first_step(&mut result, &self.stack_inputs);

        // Add initial assertions for the range checker.
        range::get_assertions_first_step(&mut result);

        // Add initial assertions for the chiplets.
        chiplets::get_assertions_first_step(&mut result);

        // --- set assertions for the last step ---------------------------------------------------
        let last_step = self.last_step();

        // add the stack's assertions for the last step.
        stack::get_assertions_last_step(&mut result, last_step, &self.outputs);

        // Add the range checker's assertions for the last step.
        range::get_assertions_last_step(&mut result, last_step);

        result
    }

    fn get_aux_assertions<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        aux_rand_elements: &winter_air::AuxTraceRandElements<E>,
    ) -> Vec<Assertion<E>> {
        let mut result: Vec<Assertion<E>> = Vec::new();

        // --- set assertions for the first step --------------------------------------------------

        // add initial assertions for the stack's auxiliary columns.
        stack::get_aux_assertions_first_step(&mut result, aux_rand_elements, &self.stack_inputs);

        // Add initial assertions for the range checker's auxiliary columns.
        range::get_aux_assertions_first_step(&mut result);

        // --- set assertions for the last step ---------------------------------------------------
        let last_step = self.last_step();

        // add the stack's auxiliary column assertions for the last step.
        stack::get_aux_assertions_last_step(
            &mut result,
            aux_rand_elements,
            &self.outputs,
            last_step,
        );

        // Add the range checker's auxiliary column assertions for the last step.
        range::get_aux_assertions_last_step(&mut result, last_step);

        result
    }

    // TRANSITION CONSTRAINTS
    // --------------------------------------------------------------------------------------------

    fn evaluate_transition<E: FieldElement<BaseField = Felt>>(
        &self,
        frame: &EvaluationFrame<E>,
        periodic_values: &[E],
        result: &mut [E],
    ) {
        let current = frame.current();
        let next = frame.next();

        // --- system -----------------------------------------------------------------------------
        // clk' = clk + 1
        result[0] = next[CLK_COL_IDX] - (current[CLK_COL_IDX] + E::ONE);

        // --- stack operations -------------------------------------------------------------------
        stack::enforce_constraints::<E>(
            frame,
            select_result_range!(result, self.constraint_ranges.stack),
        );

        // --- range checker ----------------------------------------------------------------------
        range::enforce_constraints::<E>(
            frame,
            select_result_range!(result, self.constraint_ranges.range_checker),
        );

        // --- chiplets (hasher, bitwise, memory) -------------------------
        chiplets::enforce_constraints::<E>(
            frame,
            periodic_values,
            select_result_range!(result, self.constraint_ranges.chiplets),
        );
    }

    fn evaluate_aux_transition<F, E>(
        &self,
        main_frame: &EvaluationFrame<F>,
        aux_frame: &EvaluationFrame<E>,
        _periodic_values: &[F],
        aux_rand_elements: &AuxTraceRandElements<E>,
        result: &mut [E],
    ) where
        F: FieldElement<BaseField = Felt>,
        E: FieldElement<BaseField = Felt> + ExtensionOf<F>,
    {
        // --- range checker ----------------------------------------------------------------------
        range::enforce_aux_constraints::<F, E>(main_frame, aux_frame, aux_rand_elements, result);
    }

    fn context(&self) -> &AirContext<Felt> {
        &self.context
    }
}

// PUBLIC INPUTS
// ================================================================================================

#[derive(Debug, Clone)]
pub struct PublicInputs {
    pub program_hash: Digest,
    pub stack_inputs: Vec<Felt>,
    pub outputs: ProgramOutputs,
}

impl PublicInputs {
    pub fn new(program_hash: Digest, stack_inputs: Vec<Felt>, outputs: ProgramOutputs) -> Self {
        Self {
            program_hash,
            stack_inputs,
            outputs,
        }
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut result = Vec::new();
        result.write(self.program_hash);
        result.write_u64(self.stack_inputs.len() as u64);
        result.write(self.stack_inputs.clone());

        // write program outputs.
        let stack = self
            .outputs
            .stack()
            .iter()
            .map(|v| Felt::new(*v))
            .collect::<Vec<_>>();
        result.write_u64(stack.len() as u64);
        result.write(&stack);

        let overflow_addrs = self
            .outputs
            .overflow_addrs()
            .iter()
            .map(|v| Felt::new(*v))
            .collect::<Vec<_>>();
        result.write_u64(overflow_addrs.len() as u64);
        result.write(&overflow_addrs);
        result
    }
}

impl Serializable for PublicInputs {
    fn write_into<W: ByteWriter>(&self, target: &mut W) {
        let mut data: Vec<Felt> = Vec::new();

        data.extend(self.program_hash.as_elements().iter());
        data.extend(self.stack_inputs.as_slice().iter());

        // // write program outputs.
        let output_stack = self
            .outputs
            .stack()
            .iter()
            .map(|v| Felt::new(*v))
            .collect::<Vec<_>>();
        data.extend(output_stack.as_slice().iter());

        let overflow_addrs = self
            .outputs
            .overflow_addrs()
            .iter()
            .map(|v| Felt::new(*v))
            .collect::<Vec<_>>();
        data.extend(overflow_addrs.as_slice().iter());

        let hash = Blake2s_256::hash_elements(&data);

        println!("seed: ");
        for word in hash.clone().0.chunks(4) {
            println!("0x{:x}", u32::from_le_bytes(word.try_into().unwrap()));
        }

        target.write(hash);
    }
}

impl Deserializable for PublicInputs {
    fn read_from<R: vm_core::utils::ByteReader>(
        source: &mut R,
    ) -> Result<Self, vm_core::utils::DeserializationError> {
        let program_hash = Digest::read_from(source)?;
        let stack_inputs_len = source.read_u64()?;
        let stack_inputs = Felt::read_batch_from(source, stack_inputs_len as usize)?;

        let stack_outputs_len = source.read_u64()?;
        let stack_outputs = Felt::read_batch_from(source, stack_outputs_len as usize)?;
        let stack_outputs_u64 = stack_outputs.iter().map(|i| i.as_int()).collect();

        let overflow_addrs_len = source.read_u64()?;
        let overflow_addrs = Felt::read_batch_from(source, overflow_addrs_len as usize)?;
        let overflow_addrs_u64 = overflow_addrs.iter().map(|i| i.as_int()).collect();

        Ok(PublicInputs::new(
            program_hash,
            stack_inputs,
            ProgramOutputs {
                stack: stack_outputs_u64,
                overflow_addrs: overflow_addrs_u64,
            },
        ))
    }
}

#[cfg(test)]
mod tests {
    use vm_core::{
        chiplets::hasher::{self},
        utils::{Deserializable, Serializable, SliceReader},
        Felt, ProgramOutputs, StarkField,
    };

    use crate::PublicInputs;

    #[test]
    fn public_inputs_serde() {
        let program_hash =
            hasher::hash_elements(&[Felt::new(1), Felt::new(2), Felt::new(3), Felt::new(4)]);
        let public_inputs = PublicInputs::new(
            program_hash,
            vec![Felt::new(0), Felt::new(1)],
            ProgramOutputs {
                stack: vec![],
                overflow_addrs: vec![],
            },
        );

        let mut buf = vec![];
        public_inputs.write_into(&mut buf);
        let deser = PublicInputs::read_from(&mut SliceReader::new(&buf[..])).unwrap();

        assert_eq!(public_inputs.program_hash, deser.program_hash);
        assert_eq!(public_inputs.stack_inputs, deser.stack_inputs);
        assert_eq!(public_inputs.outputs.stack, deser.outputs.stack);
        assert_eq!(
            public_inputs.outputs.overflow_addrs,
            deser.outputs.overflow_addrs
        );
    }
}
