// Lean compiler output
// Module: SSExactMajority.Convergence.Silent
// Imports: public import Init public meta import Init public import SSExactMajority.Protocol.Correctness public import SSExactMajority.Defs.Execution public import Mathlib.Data.Finset.Card public import Mathlib.Data.Fintype.Card
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
lean_object* lp_SSExactMajority_SSEM_Config_inputOf___redArg(lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqOpinion(uint8_t, uint8_t);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nAOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nBOf(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_majorityAnswer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_majorityAnswer___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___redArg___lam__0(lean_object* v_C_1_, uint8_t v_x_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; uint8_t v___x_6_; 
v___x_4_ = lp_SSExactMajority_SSEM_Config_inputOf___redArg(v_C_1_, v_a_3_);
v___x_5_ = lean_unbox(v___x_4_);
lean_dec(v___x_4_);
v___x_6_ = lp_SSExactMajority_SSEM_instDecidableEqOpinion(v___x_5_, v_x_2_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___redArg___lam__0___boxed(lean_object* v_C_7_, lean_object* v_x_8_, lean_object* v_a_9_){
_start:
{
uint8_t v_x_boxed_10_; uint8_t v_res_11_; lean_object* v_r_12_; 
v_x_boxed_10_ = lean_unbox(v_x_8_);
v_res_11_ = lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___redArg___lam__0(v_C_7_, v_x_boxed_10_, v_a_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___redArg(lean_object* v_n_13_, lean_object* v_C_14_, uint8_t v_x_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_16_ = lean_box(v_x_15_);
v___f_17_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_17_, 0, v_C_14_);
lean_closure_set(v___f_17_, 1, v___x_16_);
v___x_18_ = l_List_finRange(v_n_13_);
v___x_19_ = lp_mathlib_Multiset_filter___redArg(v___f_17_, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___redArg___boxed(lean_object* v_n_20_, lean_object* v_C_21_, lean_object* v_x_22_){
_start:
{
uint8_t v_x_boxed_23_; lean_object* v_res_24_; 
v_x_boxed_23_ = lean_unbox(v_x_22_);
v_res_24_ = lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___redArg(v_n_20_, v_C_21_, v_x_boxed_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0(lean_object* v_n_25_, lean_object* v_Q_26_, lean_object* v_n_27_, lean_object* v_C_28_, uint8_t v_x_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___redArg(v_n_25_, v_C_28_, v_x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___boxed(lean_object* v_n_31_, lean_object* v_Q_32_, lean_object* v_n_33_, lean_object* v_C_34_, lean_object* v_x_35_){
_start:
{
uint8_t v_x_boxed_36_; lean_object* v_res_37_; 
v_x_boxed_36_ = lean_unbox(v_x_35_);
v_res_37_ = lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0(v_n_31_, v_Q_32_, v_n_33_, v_C_34_, v_x_boxed_36_);
lean_dec(v_n_33_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nAOf(lean_object* v_n_38_, lean_object* v_C_39_){
_start:
{
uint8_t v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = 0;
v___x_41_ = lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___redArg(v_n_38_, v_C_39_, v___x_40_);
v___x_42_ = l_List_lengthTR___redArg(v___x_41_);
lean_dec(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nBOf(lean_object* v_n_43_, lean_object* v_C_44_){
_start:
{
uint8_t v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = 1;
v___x_46_ = lp_SSExactMajority_SSEM_Config_agentsWithInput___at___00SSEM_nAOf_spec__0___redArg(v_n_43_, v_C_44_, v___x_45_);
v___x_47_ = l_List_lengthTR___redArg(v___x_46_);
lean_dec(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_majorityAnswer(lean_object* v_n_48_, lean_object* v_C_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
lean_inc_ref(v_C_49_);
lean_inc(v_n_48_);
v___x_50_ = lp_SSExactMajority_SSEM_nBOf(v_n_48_, v_C_49_);
v___x_51_ = lp_SSExactMajority_SSEM_nAOf(v_n_48_, v_C_49_);
v___x_52_ = lean_nat_dec_lt(v___x_50_, v___x_51_);
if (v___x_52_ == 0)
{
uint8_t v___x_53_; 
v___x_53_ = lean_nat_dec_lt(v___x_51_, v___x_50_);
lean_dec(v___x_50_);
lean_dec(v___x_51_);
if (v___x_53_ == 0)
{
uint8_t v___x_54_; 
v___x_54_ = 1;
return v___x_54_;
}
else
{
uint8_t v___x_55_; 
v___x_55_ = 3;
return v___x_55_;
}
}
else
{
uint8_t v___x_56_; 
lean_dec(v___x_51_);
lean_dec(v___x_50_);
v___x_56_ = 2;
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_majorityAnswer___boxed(lean_object* v_n_57_, lean_object* v_C_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = lp_SSExactMajority_SSEM_majorityAnswer(v_n_57_, v_C_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_Correctness(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Execution(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Card(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Card(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_Silent(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Protocol_Correctness(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Defs_Execution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Card(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Card(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
