// Lean compiler output
// Module: SSExactMajority.Protocol.Correctness
// Imports: public import Init public meta import Init public import SSExactMajority.Protocol.Transition public import SSExactMajority.Defs.Execution
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
lean_object* lp_SSExactMajority_SSEM_instDecidableEqAnswer___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndinsert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_instDecidableEqRole___boxed(lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_instDecidableEqLeader___boxed(lean_object*, lean_object*);
static const lean_ctor_object lp_SSExactMajority_SSEM_instFintypeRole___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_SSExactMajority_SSEM_instFintypeRole___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instFintypeRole___closed__0_value;
static lean_once_cell_t lp_SSExactMajority_SSEM_instFintypeRole___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instFintypeRole___closed__1;
static lean_once_cell_t lp_SSExactMajority_SSEM_instFintypeRole___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instFintypeRole___closed__2;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instFintypeRole;
static const lean_ctor_object lp_SSExactMajority_SSEM_instFintypeLeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_SSExactMajority_SSEM_instFintypeLeader___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instFintypeLeader___closed__0_value;
static lean_once_cell_t lp_SSExactMajority_SSEM_instFintypeLeader___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instFintypeLeader___closed__1;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instFintypeLeader;
static const lean_ctor_object lp_SSExactMajority_SSEM_instFintypeAnswer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_SSExactMajority_SSEM_instFintypeAnswer___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instFintypeAnswer___closed__0_value;
static lean_once_cell_t lp_SSExactMajority_SSEM_instFintypeAnswer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instFintypeAnswer___closed__1;
static lean_once_cell_t lp_SSExactMajority_SSEM_instFintypeAnswer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instFintypeAnswer___closed__2;
static lean_once_cell_t lp_SSExactMajority_SSEM_instFintypeAnswer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instFintypeAnswer___closed__3;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instFintypeAnswer;
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeRole___closed__1(void){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_5_ = ((lean_object*)(lp_SSExactMajority_SSEM_instFintypeRole___closed__0));
v___x_6_ = 1;
v___x_7_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqRole___boxed), 2, 0);
v___x_8_ = lean_box(v___x_6_);
v___x_9_ = lp_mathlib_Multiset_ndinsert___redArg(v___x_7_, v___x_8_, v___x_5_);
return v___x_9_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeRole___closed__2(void){
_start:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_10_ = lean_obj_once(&lp_SSExactMajority_SSEM_instFintypeRole___closed__1, &lp_SSExactMajority_SSEM_instFintypeRole___closed__1_once, _init_lp_SSExactMajority_SSEM_instFintypeRole___closed__1);
v___x_11_ = 0;
v___x_12_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqRole___boxed), 2, 0);
v___x_13_ = lean_box(v___x_11_);
v___x_14_ = lp_mathlib_Multiset_ndinsert___redArg(v___x_12_, v___x_13_, v___x_10_);
return v___x_14_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeRole(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&lp_SSExactMajority_SSEM_instFintypeRole___closed__2, &lp_SSExactMajority_SSEM_instFintypeRole___closed__2_once, _init_lp_SSExactMajority_SSEM_instFintypeRole___closed__2);
return v___x_15_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeLeader___closed__1(void){
_start:
{
lean_object* v___x_20_; uint8_t v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_20_ = ((lean_object*)(lp_SSExactMajority_SSEM_instFintypeLeader___closed__0));
v___x_21_ = 0;
v___x_22_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqLeader___boxed), 2, 0);
v___x_23_ = lean_box(v___x_21_);
v___x_24_ = lp_mathlib_Multiset_ndinsert___redArg(v___x_22_, v___x_23_, v___x_20_);
return v___x_24_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeLeader(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_obj_once(&lp_SSExactMajority_SSEM_instFintypeLeader___closed__1, &lp_SSExactMajority_SSEM_instFintypeLeader___closed__1_once, _init_lp_SSExactMajority_SSEM_instFintypeLeader___closed__1);
return v___x_25_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeAnswer___closed__1(void){
_start:
{
lean_object* v___x_30_; uint8_t v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_30_ = ((lean_object*)(lp_SSExactMajority_SSEM_instFintypeAnswer___closed__0));
v___x_31_ = 2;
v___x_32_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqAnswer___boxed), 2, 0);
v___x_33_ = lean_box(v___x_31_);
v___x_34_ = lp_mathlib_Multiset_ndinsert___redArg(v___x_32_, v___x_33_, v___x_30_);
return v___x_34_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeAnswer___closed__2(void){
_start:
{
lean_object* v___x_35_; uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_35_ = lean_obj_once(&lp_SSExactMajority_SSEM_instFintypeAnswer___closed__1, &lp_SSExactMajority_SSEM_instFintypeAnswer___closed__1_once, _init_lp_SSExactMajority_SSEM_instFintypeAnswer___closed__1);
v___x_36_ = 1;
v___x_37_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqAnswer___boxed), 2, 0);
v___x_38_ = lean_box(v___x_36_);
v___x_39_ = lp_mathlib_Multiset_ndinsert___redArg(v___x_37_, v___x_38_, v___x_35_);
return v___x_39_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeAnswer___closed__3(void){
_start:
{
lean_object* v___x_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_40_ = lean_obj_once(&lp_SSExactMajority_SSEM_instFintypeAnswer___closed__2, &lp_SSExactMajority_SSEM_instFintypeAnswer___closed__2_once, _init_lp_SSExactMajority_SSEM_instFintypeAnswer___closed__2);
v___x_41_ = 0;
v___x_42_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqAnswer___boxed), 2, 0);
v___x_43_ = lean_box(v___x_41_);
v___x_44_ = lp_mathlib_Multiset_ndinsert___redArg(v___x_42_, v___x_43_, v___x_40_);
return v___x_44_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeAnswer(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_obj_once(&lp_SSExactMajority_SSEM_instFintypeAnswer___closed__3, &lp_SSExactMajority_SSEM_instFintypeAnswer___closed__3_once, _init_lp_SSExactMajority_SSEM_instFintypeAnswer___closed__3);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___redArg(uint8_t v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
if (v_x_46_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_48_);
v___x_49_ = lean_box(0);
v___x_50_ = lean_apply_1(v_h__1_47_, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec(v_h__1_47_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_apply_1(v_h__2_48_, v___x_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___redArg___boxed(lean_object* v_x_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_){
_start:
{
uint8_t v_x_26__boxed_56_; lean_object* v_res_57_; 
v_x_26__boxed_56_ = lean_unbox(v_x_53_);
v_res_57_ = lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___redArg(v_x_26__boxed_56_, v_h__1_54_, v_h__2_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter(lean_object* v_motive_58_, uint8_t v_x_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_){
_start:
{
if (v_x_59_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_h__2_61_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_1(v_h__1_60_, v___x_62_);
return v___x_63_;
}
else
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec(v_h__1_60_);
v___x_64_ = lean_box(0);
v___x_65_ = lean_apply_1(v_h__2_61_, v___x_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter___boxed(lean_object* v_motive_66_, lean_object* v_x_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
uint8_t v_x_37__boxed_70_; lean_object* v_res_71_; 
v_x_37__boxed_70_ = lean_unbox(v_x_67_);
v_res_71_ = lp_SSExactMajority___private_SSExactMajority_Protocol_Correctness_0__SSEM_opinionToAnswer_match__1_splitter(v_motive_66_, v_x_37__boxed_70_, v_h__1_68_, v_h__2_69_);
return v_res_71_;
}
}
lean_object* initialize_Init(uint8_t builtin);
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
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Protocol_Transition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Defs_Execution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_SSExactMajority_SSEM_instFintypeRole = _init_lp_SSExactMajority_SSEM_instFintypeRole();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeRole);
lp_SSExactMajority_SSEM_instFintypeLeader = _init_lp_SSExactMajority_SSEM_instFintypeLeader();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeLeader);
lp_SSExactMajority_SSEM_instFintypeAnswer = _init_lp_SSExactMajority_SSEM_instFintypeAnswer();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeAnswer);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
