# Change Log

All notable changes to this project will be documented in this file.

The format is based on Keep a Changelog and this project adheres to Semantic Versioning.

For all future releases, please manage versions as follows:

1. Briefly summarize notable changes in this file (`CHANGELOG.md`). If the release includes *breaking changes*, provide clear migration instructions.
2. Publish the new version on crates.io and create a new release on [GitHub Releases](https://github.com/kaist-cp/circ/releases).

---

## Version 0.2.0 - 2024-10-03

### Features

* Added implementation of standard traits for pointers. ([#3](https://github.com/kaist-cp/circ/pull/3))

### Bug Fixes

* `PartialEq` for `Rc` and `Snapshot` now compares the objects they point to, rather than the pointers themselves. ([#3](https://github.com/kaist-cp/circ/pull/3)) (See compatibility note below.)

### Compatibility Notes

* `Rc::eq` and `Snapshot::eq` now compare the objects they point to instead of their pointer values. This change aligns with the behavior of `PartialEq` for other smart pointer types (e.g., `std::rc::Rc`), where equality is based on the objects being pointed to. The original pointer-based comparison is still available via the `ptr_eq` method.
  * **Migration**: To compare pointer values, use the `ptr_eq` method. 

## Version 0.1.0 - 2024-06-12

* Initial release.
