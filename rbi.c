/*
 * rbi.c: binary tree with node insertion and iteration
 * by pts@fazekas.hu at Fri Jun  3 15:16:03 CEST 2022
 *
 * Implementation properties:
 *
 * * 3 tree implementations: unordered; ordered but unbalanced; balanced
 * * memory allocation is done outside the library
 * * lookup, iteration and insertion is without recursion and with constant memory usage
 * * compact memory representation: parent pointers are not used
 * * compact memory representation: option to store the red-black bit of the balanced implmenetation in the least signigicant bit of the (right) pointer
 * * operations other than lookup, insertion and iteration are not implemented
 *
 * rbi.c is free software, GNU GPL >=2.0. There is NO WARRANTY. Use at your risk.
 *
 * Compile with: gcc -DRB_BALANCED   -s -Os -W -Wall -Werror -o try_ba rbi.c
 * Compile with: gcc -DRB_UNBALANCED -s -Os -W -Wall -Werror -o try_ub rbi.c
 * Compile with: gcc -DRB_UNORDERED  -s -Os -W -Wall -Werror -o try_uo rbi.c
 * Compile for disassembly with: gcc -m32 -fno-pic -fno-stack-protector -c -Os -W -Wall -Werror -o try32.o rbi.c
 * Compile with: owcc -bcom -o try_ba.com  -DRB_BALANCED              -Os -s -fno-stack-check -march=i86 -W -Wall -Wextra rbi.c  # -DRB_UNORDERED + 208 bytes
 * Compile with: owcc -bcom -o try_ub.com  -DRB_UNBALANCED            -Os -s -fno-stack-check -march=i86 -W -Wall -Wextra rbi.c  # -DRB_UNORDERED + 48 bytes
 * Compile with: owcc -bcom -o try_uo.com  -DRB_UNORDERED             -Os -s -fno-stack-check -march=i86 -W -Wall -Wextra rbi.c
 * Compile with: owcc -bdos -o try_lba.exe -DRB_BALANCED   -mcmodel=l -Os -s -fno-stack-check -march=i86 -W -Wall -Wextra rbi.c  # -DRB_UNORDERED + 368 bytes (In the end, in mininasm, the code became larger: -DRB_UNBALANCED + 319 bytes.)
 * Compile with: owcc -bdos -o try_lub.exe -DRB_UNBALANCED -mcmodel=l -Os -s -fno-stack-check -march=i86 -W -Wall -Wextra rbi.c  # -DRB_UNORDERED + 128 bytes
 * Compile with: owcc -bdos -o try_luo.exe -DRB_UNORDERED  -mcmodel=l -Os -s -fno-stack-check -march=i86 -W -Wall -Wextra rbi.c
 */
#include <stdio.h>
#include <string.h>

#define LOG2_MAX_NODES 6

#define RB_LOG2_MAX_NODES LOG2_MAX_NODES  /* If defined, decreases stack usage if tree_insert. */
#undef  RB_COMPACT
#ifndef RB_UNORDERED
#ifndef RB_ORDERED
#define RB_ORDERED 1
#endif
#endif
#include <stdint.h>  /* unitptr_t. */
#define assert(x)

/* --- Generic binary tree implementation which supports only insertion.
 *
 * Based on: commit on 2021-03-17 https://github.com/jemalloc/jemalloc/blob/70e3735f3a71d3e05faa05c58ff3ca82ebaad908/include/jemalloc/internal/rb.h
 *
 * Parent pointers are not used, and color bits are stored in the least
 * significant bit of right-child pointers (if RB_COMPACT is defined), thus
 * making node linkage as compact as is possible for red-black trees.
 *
 * Usage:
 *
 *   #include <stdint.h>  // uintptr_t.
 *   #define NDEBUG // (Optional, see assert(3).)
 *   #include <assert.h>  // #define assert(x).
 *   #define RB_ORDERED
 *   #define RB_BALANCED
 *   #define RB_COMPACT // (Optional, embed color bits in right-child pointers.)
 *   ...
 */

#ifndef RB_BOOL
#define RB_BOOL char
#endif

#ifdef  RB_BALANCED
#ifndef RB_BALANCED
#define RB_ORDERED 1
#endif
#endif

#ifdef  RB_COMPACT
#ifndef RB_BALANCED
#undef  RB_COMPACT
#endif
#endif

#ifdef RB_BALANCED
#ifdef RB_COMPACT
/* Node structure. */
#define rb_node(a_type)							\
struct {								\
    a_type *rbn_left;							\
    a_type *rbn_right_red;						\
}
#else
#define rb_node(a_type)							\
struct {								\
    a_type *rbn_left;							\
    a_type *rbn_right;							\
    RB_BOOL rbn_red;						\
}
#endif
#else
#define rb_node(a_type)							\
struct {								\
    a_type *rbn_left;							\
    a_type *rbn_right;							\
}
#endif

/*
 * Each node in the RB tree consumes at least 1 byte of space (for the
 * linkage if nothing else, so there are a maximum of 1 << (sizeof(void *)
 * << 3 rb) tree nodes in any process, and thus, at most that many in any
 * tree.
 *
 * Maximum number of bytes in a process: 1 << (sizeof(void*) << 3).
 * Log2 of maximum number of bytes in a process: sizeof(void*) << 3.
 * Maximum number of tree nodes in a process: 1 << (sizeof(void*) << 3) / sizeof(tree_node).
 * Maximum number of tree nodes in a process is at most: 1 << (sizeof(void*) << 3) / sizeof(rb_node(a_type)).
 * Log2 of maximum number of tree nodes in a process is at most: (sizeof(void*) << 3) - log2(sizeof(rb_node(a_type)).
 * Log2 of maximum number of tree nodes in a process is at most without RB_COMPACT: (sizeof(void*) << 3) - (sizeof(void*) >= 8 ? 4 : sizeof(void*) >= 4 ? 3 : 2).
 */
#ifndef RB_LOG2_MAX_MEM_BYTES
#define RB_LOG2_MAX_MEM_BYTES (sizeof(void*) << 3)
#endif

#ifdef RB_BALANCED
#ifndef RB_LOG2_MAX_NODES
#ifdef RB_COMPACT
#define RB_LOG2_MAX_NODES (RB_LOG2_MAX_MEM_BYTES - (sizeof(void*) >= 8 ? 4 : sizeof(void*) >= 4 ? 3 : 2))
#else
#define RB_LOG2_MAX_NODES (RB_LOG2_MAX_MEM_BYTES - (sizeof(void*) >= 8 ? 4 : sizeof(void*) >= 4 ? 3 : 2) - 1)
#endif
#endif
/*
 * The choice of algorithm bounds the depth of a tree to twice the binary log of
 * the number of elements in the tree; the following bound follows.
 */
#define RB_MAX_DEPTH (RB_LOG2_MAX_NODES << 1)
#else
#undef RB_LOG2_MAX_NODES
#undef RB_MAX_DEPTH
#endif

/* Root structure. */
#define rb_tree(a_type)							\
struct {								\
    a_type *rbt_root;							\
}

/* Left accessors. */
#define rbtn_left_get(a_type, a_field, a_node)				\
    ((a_node)->a_field.rbn_left)
#define rbtn_left_set(a_type, a_field, a_node, a_left) do {		\
    (a_node)->a_field.rbn_left = a_left;				\
} while (0)

#ifdef RB_COMPACT
/* Right accessors. */
#define rbtn_right_get(a_type, a_field, a_node)				\
    ((a_type *) (((intptr_t) (a_node)->a_field.rbn_right_red)		\
      & ((ssize_t)-2)))
#define rbtn_right_set(a_type, a_field, a_node, a_right) do {		\
    (a_node)->a_field.rbn_right_red = (a_type *) (((uintptr_t) a_right)	\
      | (((uintptr_t) (a_node)->a_field.rbn_right_red) & ((size_t)1)));	\
} while (0)
#ifdef RB_BALANCED
/* Color accessors. */
#define rbtn_red_get(a_type, a_field, a_node)				\
    ((RB_BOOL) (((uintptr_t) (a_node)->a_field.rbn_right_red)		\
      & ((size_t)1)))
#define rbtn_red_set(a_type, a_field, a_node) do {			\
    (a_node)->a_field.rbn_right_red = (a_type *) (((uintptr_t)		\
      (a_node)->a_field.rbn_right_red) | ((size_t)1));			\
} while (0)
#define rbtn_color_set(a_type, a_field, a_node, a_red) do {		\
    (a_node)->a_field.rbn_right_red = (a_type *) ((((intptr_t)		\
      (a_node)->a_field.rbn_right_red) & ((ssize_t)-2))			\
      | ((ssize_t)a_red));						\
} while (0)
#define rbtn_black_set(a_type, a_field, a_node) do {			\
    (a_node)->a_field.rbn_right_red = (a_type *) (((intptr_t)		\
      (a_node)->a_field.rbn_right_red) & ((ssize_t)-2));		\
} while (0)
#endif
#else
/* Right accessors. */
#define rbtn_right_get(a_type, a_field, a_node)				\
    ((a_node)->a_field.rbn_right)
#define rbtn_right_set(a_type, a_field, a_node, a_right) do {		\
    (a_node)->a_field.rbn_right = a_right;				\
} while (0)
/* Color accessors. */
#ifdef RB_BALANCED
#define rbtn_red_get(a_type, a_field, a_node)				\
    ((a_node)->a_field.rbn_red)
#define rbtn_color_set(a_type, a_field, a_node, a_red) do {		\
    (a_node)->a_field.rbn_red = (a_red);				\
} while (0)
#define rbtn_red_set(a_type, a_field, a_node) do {			\
    (a_node)->a_field.rbn_red = 1;					\
} while (0)
#define rbtn_black_set(a_type, a_field, a_node) do {			\
    (a_node)->a_field.rbn_red = 0;					\
} while (0)
#endif
#endif

/* Node initializer. */
#ifdef RB_BALANCED
#ifdef RB_COMPACT
#define rbt_node_new(a_type, a_field, a_rbt, a_node) do {		\
    /* Bookkeeping bit cannot be used by node pointer. */		\
    assert(((uintptr_t)(a_node) & 0x1) == 0);				\
    rbtn_left_set(a_type, a_field, (a_node), NULL);	\
    rbtn_right_set(a_type, a_field, (a_node), NULL);	\
    rbtn_red_set(a_type, a_field, (a_node));				\
} while (0)
#else
#define rbt_node_new(a_type, a_field, a_rbt, a_node) do {		\
    rbtn_left_set(a_type, a_field, (a_node), NULL);	\
    rbtn_right_set(a_type, a_field, (a_node), NULL);	\
    rbtn_red_set(a_type, a_field, (a_node));				\
} while (0)
#endif
#else
#define rbt_node_new(a_type, a_field, a_rbt, a_node) do {		\
    rbtn_left_set(a_type, a_field, (a_node), NULL);	\
    rbtn_right_set(a_type, a_field, (a_node), NULL);	\
} while (0)
#endif

/* Tree initializer. */
#define rb_new(a_type, a_field, a_rbt) do {				\
    (a_rbt)->rbt_root = NULL;						\
} while (0)

/* Internal utility macros. */
#ifdef RB_BALANCED
#define rbtn_rotate_left(a_type, a_field, a_node, r_node) do {		\
    (r_node) = rbtn_right_get(a_type, a_field, (a_node));		\
    rbtn_right_set(a_type, a_field, (a_node),				\
      rbtn_left_get(a_type, a_field, (r_node)));			\
    rbtn_left_set(a_type, a_field, (r_node), (a_node));			\
} while (0)
#define rbtn_rotate_right(a_type, a_field, a_node, r_node) do {		\
    (r_node) = rbtn_left_get(a_type, a_field, (a_node));		\
    rbtn_left_set(a_type, a_field, (a_node),				\
      rbtn_right_get(a_type, a_field, (r_node)));			\
    rbtn_right_set(a_type, a_field, (r_node), (a_node));		\
} while (0)
#endif

/*
 * The rb_gen() macro generates a type-specific red-black tree implementation,
 * based on the above cpp macros.
 * Arguments:
 *
 *   a_attr:
 *     Function attribute for generated functions (ex: static).
 *   a_prefix:
 *     Prefix for generated functions (ex: ex_).
 *   a_rb_type:
 *     Type for red-black tree data structure (ex: ex_t).
 *   a_type:
 *     Type for red-black tree node data structure (ex: ex_node_t).
 *   a_field:
 *     Name of red-black tree node linkage (ex: ex_link).
 *   a_less:
 *     Node comparison function name, with the following prototype:
 *
 *     bool a_less(a_type *a_node, a_type *a_other);
 *                        ^^^^^^
 *                        or a_key
 *     Interpretation of comparison function return values:
 *        1 : a_node <  a_other
 *        0 : a_node >= a_other
 *     In all cases, the a_node or a_key macro argument is the first argument to
 *     the comparison function, which makes it possible to write comparison
 *     functions that treat the first argument specially.  a_less must be a total
 *     order on values inserted into the tree -- duplicates are not allowed.
 *
 * Assuming the following setup:
 *
 *   typedef struct ex_node_s ex_node_t;
 *   struct ex_node_s {
 *       rb_node(ex_node_t) ex_link;
 *   };
 *   typedef rb_tree(ex_node_t) ex_t;
 *   rb_gen(static, ex_, ex_t, ex_node_t, ex_link, ex_less)
 *
 * The following API is generated:
 *
 *   static void
 *   ex_new(ex_t *tree);
 *       Description: Initialize a red-black tree structure.
 *       Args:
 *         tree: Pointer to an uninitialized red-black tree object.
 *
 *   static void
 *   ex_insert(ex_t *tree, ex_node_t *node);
 *       Description: Insert node into tree.
 *       Assumes that equal nodes are not yet in the tree. (Is it still true?)
 *       Args:
 *         tree: Pointer to an initialized red-black tree object.
 *         node: Node to be inserted into tree.
 */
#define rb_gen(a_attr, a_prefix, a_rbt_type, a_type, a_field, a_less)	\
typedef struct {							\
    a_type *node;							\
    RB_BOOL less;								\
} a_prefix##path_entry_t;						\
a_attr void								\
a_prefix##new(a_rbt_type *rbtree) {					\
    rb_new(a_type, a_field, rbtree);					\
}									\
rb_gen_insert(a_attr, a_prefix, a_rbt_type, a_type, a_field, a_less)

#ifdef RB_BALANCED  /* Impelements an ordered and balanced binary search tree, as a red-black tree. */
#define rb_gen_insert(a_attr, a_prefix, a_rbt_type, a_type, a_field, a_less)	\
a_attr void								\
a_prefix##insert(a_rbt_type *rbtree, a_type *node) {			\
    a_prefix##path_entry_t path[RB_MAX_DEPTH];				\
    a_prefix##path_entry_t *pathp;					\
    rbt_node_new(a_type, a_field, rbtree, node);			\
    /* Wind. */								\
    path->node = rbtree->rbt_root;					\
    for (pathp = path; pathp->node != NULL; pathp++) {			\
	RB_BOOL less = pathp->less = a_less(node, pathp->node);		\
	/*assert(cmp != 0);*/						\
	if (less) {							\
	    pathp[1].node = rbtn_left_get(a_type, a_field,		\
	      pathp->node);						\
	} else {							\
	    pathp[1].node = rbtn_right_get(a_type, a_field,		\
	      pathp->node);						\
	}								\
    }									\
    pathp->node = node;							\
    assert(rbtn_left_get(a_type, a_field, node) == NULL);		\
    assert(rbtn_right_get(a_type, a_field, node) == NULL);		\
    /* Unwind. */							\
    while (pathp-- != path) {	\
	a_type *cnode = pathp->node;					\
	if (pathp->less) {						\
	    a_type *left = pathp[1].node;				\
	    rbtn_left_set(a_type, a_field, cnode, left);		\
	    if (rbtn_red_get(a_type, a_field, left)) {			\
		a_type *leftleft = rbtn_left_get(a_type, a_field, left);\
		if (leftleft != NULL && rbtn_red_get(a_type, a_field,	\
		  leftleft)) {						\
		    /* Fix up 4-node. */				\
		    a_type *tnode;					\
		    rbtn_black_set(a_type, a_field, leftleft);		\
		    rbtn_rotate_right(a_type, a_field, cnode, tnode);	\
		    cnode = tnode;					\
		}							\
	    } else {							\
		return;							\
	    }								\
	} else {							\
	    a_type *right = pathp[1].node;				\
	    rbtn_right_set(a_type, a_field, cnode, right);		\
	    if (rbtn_red_get(a_type, a_field, right)) {			\
		a_type *left = rbtn_left_get(a_type, a_field, cnode);	\
		if (left != NULL && rbtn_red_get(a_type, a_field,	\
		  left)) {						\
		    /* Split 4-node. */					\
		    rbtn_black_set(a_type, a_field, left);		\
		    rbtn_black_set(a_type, a_field, right);		\
		    rbtn_red_set(a_type, a_field, cnode);		\
		} else {						\
		    /* Lean left. */					\
		    a_type *tnode;					\
		    RB_BOOL tred = rbtn_red_get(a_type, a_field, cnode);	\
		    rbtn_rotate_left(a_type, a_field, cnode, tnode);	\
		    rbtn_color_set(a_type, a_field, tnode, tred);	\
		    rbtn_red_set(a_type, a_field, cnode);		\
		    cnode = tnode;					\
		}							\
	    } else {							\
		return;							\
	    }								\
	}								\
	pathp->node = cnode;						\
    }									\
    /* Set root, and make it black. */					\
    rbtree->rbt_root = path->node;					\
    rbtn_black_set(a_type, a_field, rbtree->rbt_root);			\
}									\

#else
#ifdef RB_ORDERED  /* Implements an ordered but unbalanced binary search tree. */
#define rb_gen_insert(a_attr, a_prefix, a_rbt_type, a_type, a_field, a_less)	\
a_attr void								\
a_prefix##insert(a_rbt_type *rbtree, a_type *node) {			\
    a_type *other;							\
    rbt_node_new(a_type, a_field, rbtree, node);			\
    if (rbtree->rbt_root == NULL) {					\
        rbtree->rbt_root = node;					\
    } else {								\
        other = rbtree->rbt_root;					\
        for (;;) {							\
            if (a_less(node, other)) {				\
                if (rbtn_left_get(node_t, link, other) == NULL) {	\
                    rbtn_left_set(a_type, a_field, other, node);	\
                    break;						\
                }							\
                other = rbtn_left_get(node_t, link, other);		\
            } else {							\
                if (rbtn_right_get(node_t, link, other) == NULL) {	\
                    rbtn_right_set(a_type, a_field, other, node);	\
                    break;						\
                }							\
                other = rbtn_right_get(node_t, link, other);		\
            }								\
        }								\
    }									\
}									\


#else  /* Implements an unordered (preserving insertion order) and unbalanced binary tree (no right children), ignores a_less. */
#define rb_gen_insert(a_attr, a_prefix, a_rbt_type, a_type, a_field, a_less)	\
a_attr void								\
a_prefix##insert(a_rbt_type *rbtree, a_type *node) {			\
    (void)a_less;							\
    rbt_node_new(a_type, a_field, rbtree, node);			\
    rbtn_left_set(a_type, a_field, node, rbtree->rbt_root);		\
    rbtree->rbt_root = node;						\
}									\

#endif
#endif

/* --- Tree instantiation. */

typedef struct node_s node_t;
struct node_s {
  rb_node(node_t) link;
  int value;
};
/* !! Why not just less(...) */
static RB_BOOL node_less(const node_t *a_node, const node_t *a_other) {
  return a_node->value < a_other->value;
}
typedef rb_tree(node_t) tree_t;
rb_gen(static, tree_, tree_t, node_t, link, node_less)

static tree_t tree;
static node_t nodes[1 << LOG2_MAX_NODES];

static int sum_subtree(node_t *node) {
  node_t *pre;
  int result = 0;
  /* Morris in-order traversal of binary tree: iterative (non-recursive,
   * so it uses O(1) stack), modifies the tree pointers temporarily, but
   * then restores them, runs in O(n) time.
   */
  while (node) {
    if (!rbtn_left_get(node_t, link, node)) goto do_print;
    for (pre = rbtn_left_get(node_t, link, node); rbtn_right_get(node_t, link, pre) && rbtn_right_get(node_t, link, pre) != node; pre = rbtn_right_get(node_t, link, pre)) {}
    if (!rbtn_right_get(node_t, link, pre)) {
      rbtn_right_get(node_t, link, pre) = node;
      node = rbtn_left_get(node_t, link, node);
    } else {
      rbtn_right_get(node_t, link, pre) = NULL;
     do_print:
      result += node->value;
      printf("value: %d\n", node->value);
      node = rbtn_right_get(node_t, link, node);
    }
  }
  return result;
}

static node_t *lookup(node_t *node, int value) {
  node_t tmp;
  tmp.value = value;
  while (node) {
    if (node_less(&tmp, node)) {
      node = rbtn_left_get(node_t, link, node);
    } else if (node_less(node, &tmp)) {
#if RB_UNORDERED
      node = rbtn_left_get(node_t, link, node);  /* Sequential search, it always follows the left node. */
#else
      node = rbtn_right_get(node_t, link, node);
#endif
    } else {
      break;
    }
  }
  return node;
}

int main(int argc, char **argv) {
  (void)argc;
  tree_new(&tree);
  { node_t *nodei = nodes;
    for (++argv; *argv; ++argv, ++nodei) {
      int v, n;
      if ((char*)nodei == (char*)nodes + sizeof(nodes)) {
        fprintf(stderr, "fatal: out of node memory\n");
        return 2;
      }
      if (sscanf(*argv, "%d%n", &v, &n) <= 0 || strlen(*argv) != n + 0U) {
        fprintf(stderr, "fatal: bad number in arg: %s\n", *argv);
        return 1;
      }
      printf("insert: %d\n", v);
      nodei->value = v;
      tree_insert(&tree, nodei);
    }
  }
  { node_t * const node = lookup(tree.rbt_root, 7);
    printf("---\nlookup(7): %d\n---\n", node ? node->value : -1);
  }
  {
    const int sum = sum_subtree(tree.rbt_root);
    printf("---\nsum: %d\n", sum);
  }

  return 0;
}
