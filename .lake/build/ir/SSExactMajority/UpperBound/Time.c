// Lean compiler output
// Module: SSExactMajority.UpperBound.Time
// Imports: public import Init public import SSExactMajority.Convergence.BurmanConvergenceFinal public import SSExactMajority.Probability.ExpectedTime public import Mathlib.Analysis.PSeries
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
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongHighASet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter___redArg(lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_nonResettingCount(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_richResetSeedSet___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowASet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_richResetSeedSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowRankSet___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_richResetSeedSet___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongLowBSet___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocolCoupled(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongLowBSet(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_wrongLowBSet___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_majorityAnswer(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_lowRankSet___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_nAOf(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_lowASet___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqRole(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongHighASet___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocol___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ConcretePEM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ConcretePEM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocolCoupled___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_wrongHighASet___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_richResetSeedCount(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongLowBCount(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowASet___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqOpinion(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowRankSet(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongHighACount(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqAnswer(uint8_t, uint8_t);
lean_object* lp_SSExactMajority_SSEM_protocolPEM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocol(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed), 6, 5);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_5);
lean_closure_set(x_7, 4, lean_box(0));
x_8 = lp_SSExactMajority_SSEM_protocolPEM(x_1, x_2, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocol___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed), 6, 5);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
lean_closure_set(x_6, 4, lean_box(0));
x_7 = lp_SSExactMajority_SSEM_protocolPEM(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocolCoupled(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed), 6, 5);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_4);
lean_closure_set(x_6, 4, lean_box(0));
lean_inc(x_2);
x_7 = lp_SSExactMajority_SSEM_protocolPEM(x_1, x_2, x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocolCoupled___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed), 6, 5);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
lean_closure_set(x_5, 4, lean_box(0));
lean_inc(x_2);
x_6 = lp_SSExactMajority_SSEM_protocolPEM(x_1, x_2, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ConcretePEM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc_n(x_1, 2);
x_5 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed), 6, 5);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_1);
lean_closure_set(x_5, 2, x_2);
lean_closure_set(x_5, 3, x_3);
lean_closure_set(x_5, 4, lean_box(0));
lean_inc_n(x_1, 2);
x_6 = lp_SSExactMajority_SSEM_protocolPEM(x_1, x_1, x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ConcretePEM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc_n(x_1, 2);
x_4 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed), 6, 5);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
lean_closure_set(x_4, 3, x_3);
lean_closure_set(x_4, 4, lean_box(0));
lean_inc_n(x_1, 2);
x_5 = lp_SSExactMajority_SSEM_protocolPEM(x_1, x_1, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_wrongLowBSet___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
lean_inc_ref(x_1);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = 1;
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = lp_SSExactMajority_SSEM_instDecidableEqOpinion(x_8, x_7);
if (x_9 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lp_SSExactMajority_SSEM_nAOf(x_2, x_1);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongLowBSet___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_SSExactMajority_SSEM_wrongLowBSet___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongLowBSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_wrongLowBSet___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = l_List_finRange(x_1);
x_5 = lp_mathlib_Multiset_filter___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_wrongHighASet___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
lean_inc_ref(x_1);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = 0;
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = lp_SSExactMajority_SSEM_instDecidableEqOpinion(x_8, x_7);
if (x_9 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lp_SSExactMajority_SSEM_nAOf(x_2, x_1);
x_12 = lean_nat_dec_le(x_11, x_10);
lean_dec(x_10);
lean_dec(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongHighASet___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_SSExactMajority_SSEM_wrongHighASet___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongHighASet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_wrongHighASet___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = l_List_finRange(x_1);
x_5 = lp_mathlib_Multiset_filter___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_lowRankSet___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc_ref(x_1);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lp_SSExactMajority_SSEM_nAOf(x_2, x_1);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowRankSet___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_SSExactMajority_SSEM_lowRankSet___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowRankSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_lowRankSet___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = l_List_finRange(x_1);
x_5 = lp_mathlib_Multiset_filter___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_lowASet___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
lean_inc_ref(x_1);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = 0;
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = lp_SSExactMajority_SSEM_instDecidableEqOpinion(x_8, x_7);
if (x_9 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lp_SSExactMajority_SSEM_nAOf(x_2, x_1);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowASet___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_SSExactMajority_SSEM_lowASet___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowASet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_lowASet___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = l_List_finRange(x_1);
x_5 = lp_mathlib_Multiset_filter___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongLowBCount(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_SSExactMajority_SSEM_wrongLowBSet(x_1, x_2);
x_4 = l_List_lengthTR___redArg(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongHighACount(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_SSExactMajority_SSEM_wrongHighASet(x_1, x_2);
x_4 = l_List_lengthTR___redArg(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_richResetSeedSet___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
lean_inc_ref(x_1);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_5, sizeof(void*)*6 + 2);
lean_dec(x_5);
x_9 = 0;
x_10 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_6, x_9);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_inc_ref(x_1);
lean_inc(x_2);
x_11 = lp_SSExactMajority_SSEM_nonResettingCount(x_2, x_1);
x_12 = lean_nat_dec_lt(x_11, x_7);
lean_dec(x_7);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_12;
}
else
{
uint8_t x_13; uint8_t x_14; 
x_13 = lp_SSExactMajority_SSEM_majorityAnswer(x_2, x_1);
x_14 = lp_SSExactMajority_SSEM_instDecidableEqAnswer(x_8, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_richResetSeedSet___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_SSExactMajority_SSEM_richResetSeedSet___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_richResetSeedSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_richResetSeedSet___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = l_List_finRange(x_1);
x_5 = lp_mathlib_Multiset_filter___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_richResetSeedCount(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_SSExactMajority_SSEM_richResetSeedSet(x_1, x_2);
x_4 = l_List_lengthTR___redArg(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_BurmanConvergenceFinal(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Probability_ExpectedTime(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_PSeries(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_BurmanConvergenceFinal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Probability_ExpectedTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_PSeries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
