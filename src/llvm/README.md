# Durin LLVM plugin

This folder contains some C++ code that integrates with LLVM, called from Durin.
This is needed for two reasons:

1. The C API doesn't expose everything. Specifically, it's impossible to run RewriteStatepointsForGC or to make a call `musttail`.

2. We need two custom LLVM passes to remove some overhead created by limitations in RewriteStatepointsForGC:
one inlines a few functions which can't be inlined until after RS4GC runs, and the other rewrites statepoint calls in tail position to true tail calls.