# Backwards-directed information flow analysis for concurrent programs

This project contains the Isabelle/HOL formalisation and soundness proof for an information flow logic implemented using weakest-precondition reasoning. 
The formalisation focuses on providing a high level of automation to assist in verification, as illustrated via a series of examples.

## Formalisation Details

The formalisation is broken down into a series of logics, with a relational rely/guarantee logic forming the basis.
This logic allows for assertions over two memories executing equivalent program traces and employs a shallow embedding over rely/guarantee and predicate specifications.
The next logic builds on this, introducing the concept of an invariant, value-dependent security policy.
Moreover, it alters the state space to a single memory coupled with a type context.
Finally, the final layer introduces a deeply embedded predicate language, over which the weakest-precondition transformer is defined and verified.
Automation is introduced using **Eisbach** and Isabelle/HOL's normalization tactics to compute and discharge implications.

Use of normalization tactics and a deeply embedded predicate language significantly restricts the specifications support by the automation.
Moreover, success of the automation is highly dependent on the size of the rely specification.
Consequently, ongoing work in a branch is exploring use of a shallow embedding coupled with smarter tactics to support
greater flexibility for specification without negatively impacting verification effort.

## Project Structure  
* Semantics.thy, Execution.thy: Small-step semantics for the While language
* Trace.thy: Trace semantics for the While language
* Bisimulation.thy: The relational rely/guarantee logic
* Typed_Memory.thy, Typed_Rely_Guarantee.thy: A logic over a single memory with a type context, coupled with a security policy
* Language_Lift.thy: Constraints on the language instantiation for the logic
* \*\_Typed_Predicate_Language.thy: Deeply embedded predicate languages with modifiers to extend the state space
* WP_Typed_Rely_Guarantee.thy: Logic rules and soundness proof
* Examples/Nat_Language.thy: Instantiation of the logic for a language over natural numbers, with Eisbach automation
