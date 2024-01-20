# dynamic-memory-allocator

This repo contains my C implementation of a dynamic memory allocator for a course assignment. It applies textbook concepts and a lot of pointer arithmetic to replace the builtin `malloc`, `realloc`, and `free` functions. For each of these functions, the procedure is written to operate on a low average time complexity as much as possible.

### Note

This implementation contains minor edge case flaws for the `realloc` function. This repository should only be used as a study reference for how a very basic dynamic memory allocator can be implemented.

### Instructions

- Run `make clean` to remove built binaries.
- Run `make` to compile C files.
- The compiled bianries come with
    - an executable to run the main routine
    - an executable to run the Criterion tests (make sure your environment is configured to have Criterion first)
