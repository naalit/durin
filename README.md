# Durin
Durin ("Dependent Unboxed higher-oRder Intermediate Notation", inspired by [Thorin](https://github.com/AnyDSL/thorin)) is an optimizing functional intermediate representation and compiler backend.
Unlike other IRs, Durin is dependently typed, because it's a simple way to express rich polymorphism.
As Thorin is higher-order in order to optimize first-class functions, Durin is dependently typed in order to optimize polymorphism.

With dependent types, partial inlining (the primary transformation in Thorin) *is* monomorphization.
So, Durin monomorphizes as an optimization, in the same way and using the same heuristics as inlining.

Durin currently has a basic LLVM backend, and it will soon support passing things around unboxed as much as possible.
Since it's dependently typed, it actually passes around types at runtime (as sizes, like [Sixten](https://github.com/ollef/sixten)), so a polymorphic function can work with, for example, unboxed arrays of any type without needing monomorphization, boxing, or extra information in values.
It will figure out what needs to be boxed (and how much - some things need to be boxed but don't need GC)
after monomorphization and inlining, so it should be able to box as little as possible.

Durin is designed as the backend for [Pika](https://github.com/tolziplohu/pika), but it should work with other typed functional languages as well.
