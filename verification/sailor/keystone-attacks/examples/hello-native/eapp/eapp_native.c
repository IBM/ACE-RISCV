//******************************************************************************
// Copyright (c) 2018, The Regents of the University of California (Regents).
// All Rights Reserved. See LICENSE for license details.
//------------------------------------------------------------------------------
#include "eapp_utils.h"
#include "string.h"
#include "edge_call.h"
#include <syscall.h>

#define OCALL_PRINT_STRING 1

#define FRM_ATTACK 
//#define FFLAGS_ATTACK

#if defined(FRM_ATTACK)
unsigned long ocall_print_double(double value);
double test = 3.4;
#elif defined(FFLAGS_ATTACK)
unsigned long ocall_print_double(double value);
double test = 2.2250738585072009e-308;
#else
unsigned long ocall_print_string(char* string);
#endif

int main(){

#if defined(FRM_ATTACK)  
  double value = 2.1 * test;
  ocall_print_double(value);
#elif defined(FFLAGS_ATTACK)
  //double value = 0.9999999999 * test;
  double value = test / 0;
  ocall_print_double(value);
#else 
  ocall_print_string("Hello World");
#endif

  EAPP_RETURN(0);
}

#if defined(FRM_ATTACK) || defined(FFLAGS_ATTACK)
unsigned long ocall_print_double(double value){
  unsigned long retval;
  ocall(OCALL_PRINT_STRING, (void*)&value, sizeof(double), &retval ,sizeof(unsigned long));
  return retval;
}
#else 
unsigned long ocall_print_string(char* string){
  unsigned long retval;
  ocall(OCALL_PRINT_STRING, string, strlen(string)+1, &retval ,sizeof(unsigned long));
  return retval;
}
#endif 
