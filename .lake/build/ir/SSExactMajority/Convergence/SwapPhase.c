// Lean compiler output
// Module: SSExactMajority.Convergence.SwapPhase
// Imports: public import Init public import SSExactMajority.Convergence.Sets public import Mathlib.Data.Fintype.Prod
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_misorderedSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_misorderedCount(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableMisorderedPair(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableMisorderedPair___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg(lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqOpinion(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = 1;
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = lp_SSExactMajority_SSEM_instDecidableEqOpinion(x_9, x_8);
if (x_10 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_11 = lean_apply_1(x_1, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = 0;
x_15 = lean_unbox(x_13);
lean_dec(x_13);
x_16 = lp_SSExactMajority_SSEM_instDecidableEqOpinion(x_15, x_14);
if (x_16 == 0)
{
lean_dec(x_12);
lean_dec(x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_nat_dec_lt(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
return x_19;
}
}
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableMisorderedPair(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableMisorderedPair___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_SSExactMajority_SSEM_instDecidableMisorderedPair(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_1);
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc_ref(x_1);
x_8 = lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg(x_1, x_6);
if (x_8 == 0)
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_11);
lean_inc_ref(x_1);
x_13 = lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg(x_1, x_11);
if (x_13 == 0)
{
lean_dec(x_11);
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_3);
x_2 = x_12;
x_3 = x_15;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_misorderedSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_3 = l_List_finRange(x_1);
lean_inc(x_3);
x_4 = lp_mathlib_Multiset_product___redArg(x_3, x_3);
x_5 = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg(x_1, x_2, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_misorderedCount(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_SSExactMajority_SSEM_misorderedSet(x_1, x_2);
x_4 = l_List_lengthTR___redArg(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_Sets(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Prod(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_SwapPhase(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_Sets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
