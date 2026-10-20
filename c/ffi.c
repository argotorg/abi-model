#include <stddef.h>
#include <stdint.h>
#include <lean/lean.h>
#include "sha3.h"

#define KECCAK256_OUTPUT_SIZE 32

LEAN_EXPORT lean_obj_res abi_model_keccak256(b_lean_obj_arg input) {
  size_t len = lean_sarray_size(input);
  lean_obj_res res = lean_alloc_sarray(1, KECCAK256_OUTPUT_SIZE, KECCAK256_OUTPUT_SIZE);
  sha3_HashBuffer(256, SHA3_FLAGS_KECCAK, lean_sarray_cptr(input), (unsigned)len,
                  lean_sarray_cptr(res), KECCAK256_OUTPUT_SIZE);
  return res;
}
