# Automatic Extraction of Lemmas from Proofs

This repository contains the benchmark proof scripts used in the experiments, as well as the raw measurements.
The repository has the following structure.
```plain
.
|-- benchmark
|   |-- Arithmetic
|   |   |-- factor_is_O
|   |   |   `-- Raw.v
|   |   |-- le_O_n
|   |   |   `-- Raw.v
|   |   ...
|   |   `-- prod_of_pows
|   |       `-- Raw.v
|   |-- Boolean
|   |   |-- andb_assoc
|   |   |   `-- Raw.v
|   |   |-- andb_comm
|   |   |   `-- Raw.v
|   |	...
|   |   `-- orb_comm
|   |       `-- Raw.v
|   |-- List
|   |   |-- app_assoc
|   |   |   `-- Raw.v
|   |   |-- app_cons_not_nil
|   |   |   `-- Raw.v
|   |	...
|   |   `-- zip_preserves_length
|   |       `-- Raw.v
|   |-- Logic
|   |   |-- and_assoc
|   |   |   `-- Raw.v
|   |   |-- and_comm
|   |   |   `-- Raw.v
|   |	...
|   |   `-- or_distr_and
|   |       `-- Raw.v
|   `-- String
|       `-- append_correct2
|           `-- Raw.v
`-- measurements
    |-- filtering.csv
    |-- ranking+filtering.csv
    `-- ranking.csv
```

The directory `benchmark` contains the benchmark proof scripts.
The proof scripts of different domains are stored inside different folders, e.g., Arithmetic, Logic, etc.
Within each directory corresponding to a domain, we have folders containing a signle file wherein we have stored the target theorems and all the definitions and theorems on which the target theorems depend.

The directory `benchamrk` contains raw measurements obtained from our experiments.
All the CSV files have the same format; the columns are as follows.
* _Theorem Id:_ Unique identifier for the target theorem in the benchmark directory. 
* _Domain:_ Domain of the target theorem, i.e., Arithmetic, Logic, etc.
* _LoC:_ Size of the benchmark script in lines of code
* _#Definitions:_ Size of the benchmark script in number of definitions, i.e., function definitions, lemmas, etc.
* _#Inlined (#Basic):_ Number of inlined lemmas, and inside the parenthesis, number of inlined basic lemmas.
* _#Generated:_ Number of generated lemmas
* _#Retrieved (Ranks):_ Number of basic lemmas retrieved by Magpie, and inside the parenthesis, their ranks in ascending order.
* _#Annotations:_ Number of annotations.
* _Description:_ Annotations and the statement of the target theorem.

Using the last column, one can understand what a basic definition and what a target definition/theorem is: all the annotated defintions are basic and the rest are target.
