# A Reasoning Tool for the Modeling Language of Block based Cloud Storage

To improve the reliability of block based cloud storage, we propose using formal methods to verify and reason the storage management. Roughly speaking, formal methods may be divided into Model Checking and Theorem Proving. Considering such distributed systems are very large and complex, we advocate the use of theorem proving in modeling and verification of block based cloud storage.

##### Theorem proving 

Theorem proving is a formal verification method where mathematical logic is used to formulate a theorem about the correctness of a design, then a general purpose theorem-prover is used to construct the proof. The theorem can be expressed using first-order logic. On the other hand, relying on the theorem prover by user interaction, the proofs can be conducted mechanically and even automatically.

Developing in [Coq](https://coq.inria.fr/), we aim to generate an interactive theorem prover,
 which allows one to state the cloud storage and to prove it interactively. The entire development may be divided into three components. Modeling Language, Assertion Language and Specification Language.

##### HDFS and Separation Logic

We have focused on the most typical product in Block base Cloud Storage — [Hadoop Distributed File System(HDFS)](https://hadoop.apache.org/docs/r1.2.1/hdfs_design.html). Considering its representative architecture, which the block is a basic storage unit, we extend the Separation Logic to describe the storage. Separation Logic is a general theory for modular reasoning about explicit memory management. It is very suitable for our requirement.

##### Modeling Language

As the beginning but also the foundation, we define and implement the modeling language in our tool. The so-called modeling is mainly about describing the abstractions of system architecture and program operations, and the effect of program execution on system state.

To achieve this, we first define the domain of our language as the description of HDFS architecture. Then, a formal syntax of expressions and commands is defined. One may use it to rewrite a simple program to describe the program operations. Finally, we define the semantic of expressions and commands, to describe the effect of program execution on system state.