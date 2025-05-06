//******************************************************************************
// Copyright (c) 2018, The Regents of the University of California (Regents).
// All Rights Reserved. See LICENSE for license details.
//------------------------------------------------------------------------------
#include <edge_call.h>
#include <keystone.h>
#include <fenv.h>
#include <math.h>

#define FRM_ATTACK 
//#define FFLAGS_ATTACK 

#if defined(FRM_ATTACK) || defined(FFLAGS_ATTACK)
unsigned long 
print_double(double str);
#else
unsigned long
print_string(char* str);
#endif 

void
print_string_wrapper(void* buffer);
#define OCALL_PRINT_STRING 1

/***
 * An example call that will be exposed to the enclave application as
 * an "ocall". This is performed by an edge_wrapper function (below,
 * print_string_wrapper) and by registering that wrapper with the
 * enclave object (below, main).
 ***/
#if defined(FRM_ATTACK) || defined(FFLAGS_ATTACK)
unsigned long
print_double(double str) {
  return printf("Enclave said: %.26f\n", str);
}
#else
unsigned long
print_string(char* str) {
  return printf("Enclave said: \"%s\"\n", str);
}
#endif

void
main_wrapper(int argc, char** argv) {
  Keystone::Enclave enclave;
  Keystone::Params params;

  params.setFreeMemSize(1024 * 1024);
  params.setUntrustedSize(1024 * 1024);

  enclave.init(argv[1], argv[2], argv[3], params);

  enclave.registerOcallDispatch(incoming_call_dispatch);

  /* We must specifically register functions we want to export to the
     enclave. */
  register_call(OCALL_PRINT_STRING, print_string_wrapper);

  edge_call_init_internals(
      (uintptr_t)enclave.getSharedBuffer(), enclave.getSharedBufferSize());

#if defined(FFLAGS_ATTACK)
  feclearexcept (FE_ALL_EXCEPT);

  enclave.run();
  
  int raised = fetestexcept (FE_ALL_EXCEPT);
  printf("Exceptions status = %08x\n", raised);

  if (raised & FE_OVERFLOW) { printf("Overflow");}
  if (raised & FE_UNDERFLOW) { printf("Underflow");}
  if (raised & FE_INEXACT) { printf("Inexact");}
  if (raised & FE_INVALID) { printf("Invalid");}
  if (raised & FE_DIVBYZERO) { printf("DivByZero");}
  printf("\n");
#else 
  enclave.run();
#endif
}

int
main(int argc, char** argv) {

#if defined(FRM_ATTACK)

  printf("Run with fesetround(FE_UPWARD)\n");
  fesetround(FE_UPWARD);
  main_wrapper(argc, argv);

  printf("Run with fesetround(FE_DOWNWARD)\n");
  fesetround(FE_DOWNWARD);
  main_wrapper(argc, argv);

#else

  main_wrapper(argc, argv);

#endif

  return 0;
}

/***
 * Example edge-wrapper function. These are currently hand-written
 * wrappers, but will have autogeneration tools in the future.
 ***/
void
print_string_wrapper(void* buffer) {
  /* Parse and validate the incoming call data */
  struct edge_call* edge_call = (struct edge_call*)buffer;
  uintptr_t call_args;
  unsigned long ret_val;
  size_t arg_len;
  if (edge_call_args_ptr(edge_call, &call_args, &arg_len) != 0) {
    edge_call->return_data.call_status = CALL_STATUS_BAD_OFFSET;
    return;
  }

#if defined(FRM_ATTACK) || defined(FFLAGS_ATTACK)
  double val = *((double*)call_args);  
  ret_val = print_double(val);
#else
  /* Pass the arguments from the eapp to the exported ocall function */
  ret_val = print_string((char*)call_args);
#endif

  /* Setup return data from the ocall function */
  uintptr_t data_section = edge_call_data_ptr();
  memcpy((void*)data_section, &ret_val, sizeof(unsigned long));
  if (edge_call_setup_ret(
          edge_call, (void*)data_section, sizeof(unsigned long))) {
    edge_call->return_data.call_status = CALL_STATUS_BAD_PTR;
  } else {
    edge_call->return_data.call_status = CALL_STATUS_OK;
  }

  /* This will now eventually return control to the enclave */
  return;
}
