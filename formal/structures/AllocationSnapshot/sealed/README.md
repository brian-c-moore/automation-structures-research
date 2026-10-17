# Captured allocation

This profile adds the post-capture obligation to the existing
`AllocationSnapshotFromRegistry` construction. Registry owns accepted key/cost
pairs; Budget owns its capacity and charges. Capture consumes admission authority.
The profile's captured fields are ghost observations of those owners at seal.

`SealedAllocationFixed` requires accepted pairs and every Budget field to remain
fixed after seal. The original Registry uniqueness, Budget safety and allocation
refinement properties keep their meanings. The TLC configuration checks them
together over three nodes and capacity six; the isolated configuration checks
only the new fixed-state property. The inductive proof establishes that clause
for `CaptureSpec` without a finite node or capacity bound.

The negative profile removes only the admission guard after seal. A later
accepted node changes the same Registry and Budget and violates the captured
observation. Its other owner actions and fixed-state declaration are retained.

The Rust captured type moves the existing allocation owner into a private field
and exposes immutable queries. The model's pair set omits Rust insertion order;
the Rust capture-fold contracts retain exact order and costs. Native, compiler
privacy and Verus checks qualify that implementation separately from this model.
