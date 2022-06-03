pts-red-black-tree: balanced binary tree with node insertion and iteration in C
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
pts-red-black-tree is a collection of C functions doing operations on binary
tree data structures, most notably the insertion operation on red-black
trees. It is non-recursive, and has very little memory overhead (e.g. no
parent pointer within the red-black tree node).

Features of rbi.c:

* 3 tree implementations: unordered; ordered but unbalanced; balanced
* memory allocation is done outside the library
* lookup, iteration and insertion is without recursion and with constant memory
  usage
* compact memory representation: parent pointers are not used
* compact memory representation: option to store the red-black bit of the
  balanced implmenetation in the least signigicant bit of the (right) pointer
* operations other than lookup, insertion and iteration are not implemented

The red-black tree insertion implementation of rbi.c is based on
https://github.com/jemalloc/jemalloc/blob/70e3735f3a71d3e05faa05c58ff3ca82ebaad908/include/jemalloc/internal/rb.h
, which contains a much larger number of red-black tree operations (e.g.
node deletion), with the same compact memory representations.

The C implementation is provided as is. Some porting and refactoring work is
needed to make it useful as a library.

__END__
