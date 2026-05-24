// Lean compiler output
// Module: SSExactMajority.Protocol.Correctness
// Imports: public import Init public import SSExactMajority.Protocol.Transition public import SSExactMajority.Defs.Execution
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
static lean_object* lp_SSExactMajority_SSEM_instFintypeRole___closed__0;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instFintypeAnswer;
lean_object* lp_SSExactMajority_SSEM_instDecidableEqAnswer___boxed(lean_object*, lean_object*);
static lean_object* lp_SSExactMajority_SSEM_instFintypeLeader___closed__1;
static lean_object* lp_SSExactMajority_SSEM_instFintypeRole___closed__1;
static lean_object* lp_SSExactMajority_SSEM_instFintypeAnswer___closed__2;
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_instDecidableEqRole___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instFintypeLeader;
static lean_object* lp_SSExactMajority_SSEM_instFintypeAnswer___closed__0;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instFintypeRole;
static lean_object* lp_SSExactMajority_SSEM_instFintypeRole___closed__2;
static lean_object* lp_SSExactMajority_SSEM_instFintypeAnswer___closed__3;
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* lp_SSExactMajority_SSEM_instFintypeAnswer___closed__1;
static lean_object* lp_SSExactMajority_SSEM_instFintypeLeader___closed__0;
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndinsert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_instDecidableEqLeader___boxed(lean_object*, lean_object*);
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeRole___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 2;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeRole___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lp_SSExactMajority_SSEM_instFintypeRole___closed__0;
x_2 = 1;
x_3 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqRole___boxed), 2, 0);
x_4 = lean_box(x_2);
x_5 = lp_mathlib_Multiset_ndinsert___redArg(x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeRole___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lp_SSExactMajority_SSEM_instFintypeRole___closed__1;
x_2 = 0;
x_3 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqRole___boxed), 2, 0);
x_4 = lean_box(x_2);
x_5 = lp_mathlib_Multiset_ndinsert___redArg(x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeRole() {
_start:
{
lean_object* x_1; 
x_1 = lp_SSExactMajority_SSEM_instFintypeRole___closed__2;
return x_1;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeLeader___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeLeader___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lp_SSExactMajority_SSEM_instFintypeLeader___closed__0;
x_2 = 0;
x_3 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqLeader___boxed), 2, 0);
x_4 = lean_box(x_2);
x_5 = lp_mathlib_Multiset_ndinsert___redArg(x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeLeader() {
_start:
{
lean_object* x_1; 
x_1 = lp_SSExactMajority_SSEM_instFintypeLeader___closed__1;
return x_1;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeAnswer___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 3;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeAnswer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lp_SSExactMajority_SSEM_instFintypeAnswer___closed__0;
x_2 = 2;
x_3 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqAnswer___boxed), 2, 0);
x_4 = lean_box(x_2);
x_5 = lp_mathlib_Multiset_ndinsert___redArg(x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeAnswer___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lp_SSExactMajority_SSEM_instFintypeAnswer___closed__1;
x_2 = 1;
x_3 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqAnswer___boxed), 2, 0);
x_4 = lean_box(x_2);
x_5 = lp_mathlib_Multiset_ndinsert___redArg(x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeAnswer___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lp_SSExactMajority_SSEM_instFintypeAnswer___closed__2;
x_2 = 0;
x_3 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqAnswer___boxed), 2, 0);
x_4 = lean_box(x_2);
x_5 = lp_mathlib_Multiset_ndinsert___redArg(x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeAnswer() {
_start:
{
lean_object* x_1; 
x_1 = lp_SSExactMajority_SSEM_instFintypeAnswer___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___redArg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_Transition(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Execution(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_Correctness(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Protocol_Transition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Defs_Execution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_SSExactMajority_SSEM_instFintypeRole___closed__0 = _init_lp_SSExactMajority_SSEM_instFintypeRole___closed__0();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeRole___closed__0);
lp_SSExactMajority_SSEM_instFintypeRole___closed__1 = _init_lp_SSExactMajority_SSEM_instFintypeRole___closed__1();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeRole___closed__1);
lp_SSExactMajority_SSEM_instFintypeRole___closed__2 = _init_lp_SSExactMajority_SSEM_instFintypeRole___closed__2();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeRole___closed__2);
lp_SSExactMajority_SSEM_instFintypeRole = _init_lp_SSExactMajority_SSEM_instFintypeRole();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeRole);
lp_SSExactMajority_SSEM_instFintypeLeader___closed__0 = _init_lp_SSExactMajority_SSEM_instFintypeLeader___closed__0();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeLeader___closed__0);
lp_SSExactMajority_SSEM_instFintypeLeader___closed__1 = _init_lp_SSExactMajority_SSEM_instFintypeLeader___closed__1();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeLeader___closed__1);
lp_SSExactMajority_SSEM_instFintypeLeader = _init_lp_SSExactMajority_SSEM_instFintypeLeader();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeLeader);
lp_SSExactMajority_SSEM_instFintypeAnswer___closed__0 = _init_lp_SSExactMajority_SSEM_instFintypeAnswer___closed__0();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeAnswer___closed__0);
lp_SSExactMajority_SSEM_instFintypeAnswer___closed__1 = _init_lp_SSExactMajority_SSEM_instFintypeAnswer___closed__1();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeAnswer___closed__1);
lp_SSExactMajority_SSEM_instFintypeAnswer___closed__2 = _init_lp_SSExactMajority_SSEM_instFintypeAnswer___closed__2();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeAnswer___closed__2);
lp_SSExactMajority_SSEM_instFintypeAnswer___closed__3 = _init_lp_SSExactMajority_SSEM_instFintypeAnswer___closed__3();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeAnswer___closed__3);
lp_SSExactMajority_SSEM_instFintypeAnswer = _init_lp_SSExactMajority_SSEM_instFintypeAnswer();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeAnswer);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
