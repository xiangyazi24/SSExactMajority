// Lean compiler output
// Module: SSExactMajority.Impossibility.WithoutN
// Imports: public import Init public meta import Init public import SSExactMajority.Defs.ExactMajority public import SSExactMajority.Embed public import Mathlib.Tactic.FinCases public import Mathlib.Tactic.NormNum public import Mathlib.Data.Fintype.Card
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_liftSched(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_C_u2080__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_C_u2080__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_C_u2080__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_C_u2080__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25(lean_object* v_x_1_){
_start:
{
lean_object* v_zero_2_; uint8_t v_isZero_3_; 
v_zero_2_ = lean_unsigned_to_nat(0u);
v_isZero_3_ = lean_nat_dec_eq(v_x_1_, v_zero_2_);
if (v_isZero_3_ == 1)
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(3u);
return v___x_4_;
}
else
{
lean_object* v_one_5_; lean_object* v_n_6_; uint8_t v_isZero_7_; lean_object* v___x_8_; 
v_one_5_ = lean_unsigned_to_nat(1u);
v_n_6_ = lean_nat_sub(v_x_1_, v_one_5_);
v_isZero_7_ = lean_nat_dec_eq(v_n_6_, v_zero_2_);
lean_dec(v_n_6_);
v___x_8_ = lean_unsigned_to_nat(4u);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25___boxed(lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25(v_x_9_);
lean_dec(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25_match__1_splitter___redArg(lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
lean_object* v_zero_14_; uint8_t v_isZero_15_; 
v_zero_14_ = lean_unsigned_to_nat(0u);
v_isZero_15_ = lean_nat_dec_eq(v_x_11_, v_zero_14_);
if (v_isZero_15_ == 1)
{
lean_object* v___x_16_; 
lean_dec(v_h__2_13_);
v___x_16_ = lean_apply_1(v_h__1_12_, lean_box(0));
return v___x_16_;
}
else
{
lean_object* v_one_17_; lean_object* v_n_18_; uint8_t v_isZero_19_; lean_object* v___x_20_; 
lean_dec(v_h__1_12_);
v_one_17_ = lean_unsigned_to_nat(1u);
v_n_18_ = lean_nat_sub(v_x_11_, v_one_17_);
v_isZero_19_ = lean_nat_dec_eq(v_n_18_, v_zero_14_);
lean_dec(v_n_18_);
v___x_20_ = lean_apply_1(v_h__2_13_, lean_box(0));
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25_match__1_splitter___redArg___boxed(lean_object* v_x_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25_match__1_splitter___redArg(v_x_21_, v_h__1_22_, v_h__2_23_);
lean_dec(v_x_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25_match__1_splitter(lean_object* v_motive_25_, lean_object* v_x_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
_start:
{
lean_object* v_zero_29_; uint8_t v_isZero_30_; 
v_zero_29_ = lean_unsigned_to_nat(0u);
v_isZero_30_ = lean_nat_dec_eq(v_x_26_, v_zero_29_);
if (v_isZero_30_ == 1)
{
lean_object* v___x_31_; 
lean_dec(v_h__2_28_);
v___x_31_ = lean_apply_1(v_h__1_27_, lean_box(0));
return v___x_31_;
}
else
{
lean_object* v_one_32_; lean_object* v_n_33_; uint8_t v_isZero_34_; lean_object* v___x_35_; 
lean_dec(v_h__1_27_);
v_one_32_ = lean_unsigned_to_nat(1u);
v_n_33_ = lean_nat_sub(v_x_26_, v_one_32_);
v_isZero_34_ = lean_nat_dec_eq(v_n_33_, v_zero_29_);
lean_dec(v_n_33_);
v___x_35_ = lean_apply_1(v_h__2_28_, lean_box(0));
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25_match__1_splitter___boxed(lean_object* v_motive_36_, lean_object* v_x_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25_match__1_splitter(v_motive_36_, v_x_37_, v_h__1_38_, v_h__2_39_);
lean_dec(v_x_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_liftSched(lean_object* v_00_u03b3_x27_41_, lean_object* v_t_42_){
_start:
{
lean_object* v___x_43_; lean_object* v_fst_44_; lean_object* v_snd_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_54_; 
v___x_43_ = lean_apply_1(v_00_u03b3_x27_41_, v_t_42_);
v_fst_44_ = lean_ctor_get(v___x_43_, 0);
v_snd_45_ = lean_ctor_get(v___x_43_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_54_ == 0)
{
v___x_47_ = v___x_43_;
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_snd_45_);
lean_inc(v_fst_44_);
lean_dec(v___x_43_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
v___x_49_ = lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25(v_fst_44_);
lean_dec(v_fst_44_);
v___x_50_ = lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_embed25(v_snd_45_);
lean_dec(v_snd_45_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 1, v___x_50_);
lean_ctor_set(v___x_47_, 0, v___x_49_);
v___x_52_ = v___x_47_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_49_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v___x_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_C_u2080__5___redArg(lean_object* v_inst_55_, lean_object* v_v_56_){
_start:
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = lean_unsigned_to_nat(3u);
v___x_58_ = lean_nat_dec_lt(v_v_56_, v___x_57_);
if (v___x_58_ == 0)
{
uint8_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = 1;
v___x_60_ = lean_box(v___x_59_);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v_inst_55_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
return v___x_61_;
}
else
{
uint8_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = 0;
v___x_63_ = lean_box(v___x_62_);
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v_inst_55_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_C_u2080__5___redArg___boxed(lean_object* v_inst_65_, lean_object* v_v_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_C_u2080__5___redArg(v_inst_65_, v_v_66_);
lean_dec(v_v_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_C_u2080__5(lean_object* v_Q_68_, lean_object* v_inst_69_, lean_object* v_v_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_C_u2080__5___redArg(v_inst_69_, v_v_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_C_u2080__5___boxed(lean_object* v_Q_72_, lean_object* v_inst_73_, lean_object* v_v_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = lp_SSExactMajority___private_SSExactMajority_Impossibility_WithoutN_0__SSEM_C_u2080__5(v_Q_72_, v_inst_73_, v_v_74_);
lean_dec(v_v_74_);
return v_res_75_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_ExactMajority(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Embed(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_FinCases(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_NormNum(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Card(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Impossibility_WithoutN(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Defs_ExactMajority(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Embed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_FinCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_NormNum(builtin);
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
