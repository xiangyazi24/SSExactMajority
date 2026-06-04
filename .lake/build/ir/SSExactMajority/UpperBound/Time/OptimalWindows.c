// Lean compiler output
// Module: SSExactMajority.UpperBound.Time.OptimalWindows
// Imports: public import Init public meta import Init public import SSExactMajority.UpperBound.Time public import SSExactMajority.UpperBound.Time.DecisionTiming public import SSExactMajority.UpperBound.Time.DrainProductive public import SSExactMajority.UpperBound.Time.EpidemicBound public import SSExactMajority.UpperBound.Time.EpidemicMechanics public import SSExactMajority.UpperBound.Time.PolynomialBound
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_decisionWindow(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__swapWindow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__swapWindow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__macLiveWindow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__macLiveWindow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__answerEpidemicWindow(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__answerEpidemicWindow___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__liveConsensusWindow(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__liveConsensusWindow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__consensusCycleWindow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__consensusCycleWindow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__globalWindow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__globalWindow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__swapWindow(lean_object* v_n_1_, lean_object* v_T__timer_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_3_ = lean_unsigned_to_nat(2u);
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_sub(v_n_1_, v___x_4_);
v___x_6_ = lean_nat_mul(v_n_1_, v___x_5_);
v___x_7_ = lean_nat_mul(v___x_3_, v___x_6_);
lean_dec(v___x_6_);
v___x_8_ = lean_nat_mul(v_T__timer_2_, v_n_1_);
v___x_9_ = lean_nat_mul(v___x_8_, v___x_5_);
lean_dec(v___x_5_);
lean_dec(v___x_8_);
v___x_10_ = lean_nat_mul(v___x_3_, v___x_9_);
lean_dec(v___x_9_);
v___x_11_ = lean_nat_add(v___x_7_, v___x_10_);
lean_dec(v___x_10_);
lean_dec(v___x_7_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__swapWindow___boxed(lean_object* v_n_12_, lean_object* v_T__timer_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_SSExactMajority_SSEM_OW__swapWindow(v_n_12_, v_T__timer_13_);
lean_dec(v_T__timer_13_);
lean_dec(v_n_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__macLiveWindow(lean_object* v_n_15_, lean_object* v_T__timer_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_17_ = lean_unsigned_to_nat(2u);
v___x_18_ = lean_nat_mul(v_T__timer_16_, v_n_15_);
v___x_19_ = lean_unsigned_to_nat(1u);
v___x_20_ = lean_nat_sub(v_n_15_, v___x_19_);
v___x_21_ = lean_nat_mul(v___x_18_, v___x_20_);
lean_dec(v___x_18_);
v___x_22_ = lean_nat_mul(v_n_15_, v___x_20_);
lean_dec(v___x_20_);
v___x_23_ = lean_nat_add(v___x_21_, v___x_22_);
lean_dec(v___x_22_);
lean_dec(v___x_21_);
v___x_24_ = lean_nat_mul(v___x_17_, v___x_23_);
lean_dec(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__macLiveWindow___boxed(lean_object* v_n_25_, lean_object* v_T__timer_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_SSExactMajority_SSEM_OW__macLiveWindow(v_n_25_, v_T__timer_26_);
lean_dec(v_T__timer_26_);
lean_dec(v_n_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__answerEpidemicWindow(lean_object* v_n_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_unsigned_to_nat(2u);
v___x_30_ = lean_nat_mul(v___x_29_, v_n_28_);
v___x_31_ = lean_nat_mul(v___x_30_, v_n_28_);
lean_dec(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__answerEpidemicWindow___boxed(lean_object* v_n_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_SSExactMajority_SSEM_OW__answerEpidemicWindow(v_n_32_);
lean_dec(v_n_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__liveConsensusWindow(lean_object* v_n_34_, lean_object* v_T__timer_35_, lean_object* v_T__reset_36_, lean_object* v_T__rank_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_38_ = lp_SSExactMajority_SSEM_decisionWindow(v_n_34_);
v___x_39_ = lp_SSExactMajority_SSEM_OW__macLiveWindow(v_n_34_, v_T__timer_35_);
v___x_40_ = lean_nat_add(v___x_38_, v___x_39_);
lean_dec(v___x_39_);
lean_dec(v___x_38_);
v___x_41_ = lp_SSExactMajority_SSEM_OW__answerEpidemicWindow(v_n_34_);
v___x_42_ = lean_nat_add(v_T__reset_36_, v___x_41_);
lean_dec(v___x_41_);
v___x_43_ = lean_nat_add(v___x_42_, v_T__rank_37_);
lean_dec(v___x_42_);
v___x_44_ = lean_nat_add(v___x_40_, v___x_43_);
lean_dec(v___x_43_);
lean_dec(v___x_40_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__liveConsensusWindow___boxed(lean_object* v_n_45_, lean_object* v_T__timer_46_, lean_object* v_T__reset_47_, lean_object* v_T__rank_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_SSExactMajority_SSEM_OW__liveConsensusWindow(v_n_45_, v_T__timer_46_, v_T__reset_47_, v_T__rank_48_);
lean_dec(v_T__rank_48_);
lean_dec(v_T__reset_47_);
lean_dec(v_T__timer_46_);
lean_dec(v_n_45_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__consensusCycleWindow(lean_object* v_n_50_, lean_object* v_T__timer_51_, lean_object* v_T__reset_52_, lean_object* v_T__rank_53_, lean_object* v_T__rerank_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lp_SSExactMajority_SSEM_OW__liveConsensusWindow(v_n_50_, v_T__timer_51_, v_T__reset_52_, v_T__rank_53_);
v___x_56_ = lean_nat_add(v_T__rerank_54_, v___x_55_);
lean_dec(v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__consensusCycleWindow___boxed(lean_object* v_n_57_, lean_object* v_T__timer_58_, lean_object* v_T__reset_59_, lean_object* v_T__rank_60_, lean_object* v_T__rerank_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_SSExactMajority_SSEM_OW__consensusCycleWindow(v_n_57_, v_T__timer_58_, v_T__reset_59_, v_T__rank_60_, v_T__rerank_61_);
lean_dec(v_T__rerank_61_);
lean_dec(v_T__rank_60_);
lean_dec(v_T__reset_59_);
lean_dec(v_T__timer_58_);
lean_dec(v_n_57_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__globalWindow(lean_object* v_n_63_, lean_object* v_C__rank_64_, lean_object* v_T__timer_65_, lean_object* v_T__reset_66_, lean_object* v_T__rank_67_, lean_object* v_T__rerank_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_69_ = lean_unsigned_to_nat(2u);
v___x_70_ = lean_nat_mul(v___x_69_, v_C__rank_64_);
v___x_71_ = lean_nat_mul(v___x_70_, v_n_63_);
lean_dec(v___x_70_);
v___x_72_ = lean_nat_mul(v___x_71_, v_n_63_);
lean_dec(v___x_71_);
v___x_73_ = lean_nat_add(v___x_72_, v_T__rerank_68_);
lean_dec(v___x_72_);
v___x_74_ = lp_SSExactMajority_SSEM_OW__liveConsensusWindow(v_n_63_, v_T__timer_65_, v_T__reset_66_, v_T__rank_67_);
v___x_75_ = lean_nat_add(v___x_73_, v___x_74_);
lean_dec(v___x_74_);
lean_dec(v___x_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_OW__globalWindow___boxed(lean_object* v_n_76_, lean_object* v_C__rank_77_, lean_object* v_T__timer_78_, lean_object* v_T__reset_79_, lean_object* v_T__rank_80_, lean_object* v_T__rerank_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = lp_SSExactMajority_SSEM_OW__globalWindow(v_n_76_, v_C__rank_77_, v_T__timer_78_, v_T__reset_79_, v_T__rank_80_, v_T__rerank_81_);
lean_dec(v_T__rerank_81_);
lean_dec(v_T__rank_80_);
lean_dec(v_T__reset_79_);
lean_dec(v_T__timer_78_);
lean_dec(v_C__rank_77_);
lean_dec(v_n_76_);
return v_res_82_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_DecisionTiming(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_DrainProductive(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_EpidemicBound(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_EpidemicMechanics(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_PolynomialBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_OptimalWindows(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_UpperBound_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_UpperBound_Time_DecisionTiming(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_UpperBound_Time_DrainProductive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_UpperBound_Time_EpidemicBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_UpperBound_Time_EpidemicMechanics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_UpperBound_Time_PolynomialBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
