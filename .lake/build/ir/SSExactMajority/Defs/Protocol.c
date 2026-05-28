// Lean compiler output
// Module: SSExactMajority.Defs.Protocol
// Imports: public import Init public meta import Init public import Mathlib.Data.Fintype.Basic public import Mathlib.Data.Finset.Basic
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
lean_object* lp_mathlib_Multiset_ndinsert___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_A_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_A_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_A_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_A_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_B_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_B_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_B_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_B_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Opinion_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqOpinion(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqOpinion___boxed(lean_object*, lean_object*);
static const lean_string_object lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "SSEM.Opinion.A"};
static const lean_object* lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__0_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__0_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__1 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__1_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "SSEM.Opinion.B"};
static const lean_object* lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__2 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__2_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__2_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__3 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__3_value;
static lean_once_cell_t lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4;
static lean_once_cell_t lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprOpinion_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprOpinion_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_SSExactMajority_SSEM_instReprOpinion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SSExactMajority_SSEM_instReprOpinion_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SSExactMajority_SSEM_instReprOpinion___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprOpinion___closed__0_value;
LEAN_EXPORT const lean_object* lp_SSExactMajority_SSEM_instReprOpinion = (const lean_object*)&lp_SSExactMajority_SSEM_instReprOpinion___closed__0_value;
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instInhabitedOpinion_default;
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instInhabitedOpinion;
static const lean_ctor_object lp_SSExactMajority_SSEM_instFintypeOpinion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_SSExactMajority_SSEM_instFintypeOpinion___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instFintypeOpinion___closed__0_value;
static lean_once_cell_t lp_SSExactMajority_SSEM_instFintypeOpinion___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instFintypeOpinion___closed__1;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instFintypeOpinion;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_A_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_A_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_A_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_A_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_B_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_B_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_B_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_B_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_T_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_T_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_T_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_T_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Output_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqOutput(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqOutput___boxed(lean_object*, lean_object*);
static const lean_string_object lp_SSExactMajority_SSEM_instReprOutput_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SSEM.Output.A"};
static const lean_object* lp_SSExactMajority_SSEM_instReprOutput_repr___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprOutput_repr___closed__0_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprOutput_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprOutput_repr___closed__0_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprOutput_repr___closed__1 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprOutput_repr___closed__1_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprOutput_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SSEM.Output.B"};
static const lean_object* lp_SSExactMajority_SSEM_instReprOutput_repr___closed__2 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprOutput_repr___closed__2_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprOutput_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprOutput_repr___closed__2_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprOutput_repr___closed__3 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprOutput_repr___closed__3_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprOutput_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SSEM.Output.T"};
static const lean_object* lp_SSExactMajority_SSEM_instReprOutput_repr___closed__4 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprOutput_repr___closed__4_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprOutput_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprOutput_repr___closed__4_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprOutput_repr___closed__5 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprOutput_repr___closed__5_value;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprOutput_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprOutput_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_SSExactMajority_SSEM_instReprOutput___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SSExactMajority_SSEM_instReprOutput_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SSExactMajority_SSEM_instReprOutput___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprOutput___closed__0_value;
LEAN_EXPORT const lean_object* lp_SSExactMajority_SSEM_instReprOutput = (const lean_object*)&lp_SSExactMajority_SSEM_instReprOutput___closed__0_value;
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instInhabitedOutput_default;
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instInhabitedOutput;
static const lean_ctor_object lp_SSExactMajority_SSEM_instFintypeOutput___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_SSExactMajority_SSEM_instFintypeOutput___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instFintypeOutput___closed__0_value;
static lean_once_cell_t lp_SSExactMajority_SSEM_instFintypeOutput___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instFintypeOutput___closed__1;
static lean_once_cell_t lp_SSExactMajority_SSEM_instFintypeOutput___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instFintypeOutput___closed__2;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instFintypeOutput;
static const lean_string_object lp_SSExactMajority_SSEM_Opinion_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "A"};
static const lean_object* lp_SSExactMajority_SSEM_Opinion_toString___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_Opinion_toString___closed__0_value;
static const lean_string_object lp_SSExactMajority_SSEM_Opinion_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "B"};
static const lean_object* lp_SSExactMajority_SSEM_Opinion_toString___closed__1 = (const lean_object*)&lp_SSExactMajority_SSEM_Opinion_toString___closed__1_value;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_toString(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_toString___boxed(lean_object*);
static const lean_closure_object lp_SSExactMajority_SSEM_Opinion_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SSExactMajority_SSEM_Opinion_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SSExactMajority_SSEM_Opinion_instToString___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_Opinion_instToString___closed__0_value;
LEAN_EXPORT const lean_object* lp_SSExactMajority_SSEM_Opinion_instToString = (const lean_object*)&lp_SSExactMajority_SSEM_Opinion_instToString___closed__0_value;
static const lean_string_object lp_SSExactMajority_SSEM_Output_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "T"};
static const lean_object* lp_SSExactMajority_SSEM_Output_toString___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_Output_toString___closed__0_value;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_toString(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_toString___boxed(lean_object*);
static const lean_closure_object lp_SSExactMajority_SSEM_Output_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SSExactMajority_SSEM_Output_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SSExactMajority_SSEM_Output_instToString___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_Output_instToString___closed__0_value;
LEAN_EXPORT const lean_object* lp_SSExactMajority_SSEM_Output_instToString = (const lean_object*)&lp_SSExactMajority_SSEM_Output_instToString___closed__0_value;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = lp_SSExactMajority_SSEM_Opinion_ctorIdx(v_x_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_toCtorIdx(uint8_t v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_SSExactMajority_SSEM_Opinion_ctorIdx(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_toCtorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_4__boxed_10_; lean_object* v_res_11_; 
v_x_4__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = lp_SSExactMajority_SSEM_Opinion_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_ctorElim___redArg(lean_object* v_k_12_){
_start:
{
lean_inc(v_k_12_);
return v_k_12_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_ctorElim___redArg___boxed(lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_SSExactMajority_SSEM_Opinion_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, uint8_t v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
uint8_t v_t_boxed_25_; lean_object* v_res_26_; 
v_t_boxed_25_ = lean_unbox(v_t_22_);
v_res_26_ = lp_SSExactMajority_SSEM_Opinion_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_A_elim___redArg(lean_object* v_A_27_){
_start:
{
lean_inc(v_A_27_);
return v_A_27_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_A_elim___redArg___boxed(lean_object* v_A_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_SSExactMajority_SSEM_Opinion_A_elim___redArg(v_A_28_);
lean_dec(v_A_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_A_elim(lean_object* v_motive_30_, uint8_t v_t_31_, lean_object* v_h_32_, lean_object* v_A_33_){
_start:
{
lean_inc(v_A_33_);
return v_A_33_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_A_elim___boxed(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_A_37_){
_start:
{
uint8_t v_t_boxed_38_; lean_object* v_res_39_; 
v_t_boxed_38_ = lean_unbox(v_t_35_);
v_res_39_ = lp_SSExactMajority_SSEM_Opinion_A_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_A_37_);
lean_dec(v_A_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_B_elim___redArg(lean_object* v_B_40_){
_start:
{
lean_inc(v_B_40_);
return v_B_40_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_B_elim___redArg___boxed(lean_object* v_B_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_SSExactMajority_SSEM_Opinion_B_elim___redArg(v_B_41_);
lean_dec(v_B_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_B_elim(lean_object* v_motive_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_B_46_){
_start:
{
lean_inc(v_B_46_);
return v_B_46_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_B_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_B_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = lp_SSExactMajority_SSEM_Opinion_B_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_B_50_);
lean_dec(v_B_50_);
return v_res_52_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Opinion_ofNat(lean_object* v_n_53_){
_start:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = lean_nat_dec_le(v_n_53_, v___x_54_);
if (v___x_55_ == 0)
{
uint8_t v___x_56_; 
v___x_56_ = 1;
return v___x_56_;
}
else
{
uint8_t v___x_57_; 
v___x_57_ = 0;
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_ofNat___boxed(lean_object* v_n_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = lp_SSExactMajority_SSEM_Opinion_ofNat(v_n_58_);
lean_dec(v_n_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqOpinion(uint8_t v_x_61_, uint8_t v_y_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_63_ = lp_SSExactMajority_SSEM_Opinion_ctorIdx(v_x_61_);
v___x_64_ = lp_SSExactMajority_SSEM_Opinion_ctorIdx(v_y_62_);
v___x_65_ = lean_nat_dec_eq(v___x_63_, v___x_64_);
lean_dec(v___x_64_);
lean_dec(v___x_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqOpinion___boxed(lean_object* v_x_66_, lean_object* v_y_67_){
_start:
{
uint8_t v_x_13__boxed_68_; uint8_t v_y_14__boxed_69_; uint8_t v_res_70_; lean_object* v_r_71_; 
v_x_13__boxed_68_ = lean_unbox(v_x_66_);
v_y_14__boxed_69_ = lean_unbox(v_y_67_);
v_res_70_ = lp_SSExactMajority_SSEM_instDecidableEqOpinion(v_x_13__boxed_68_, v_y_14__boxed_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(2u);
v___x_79_ = lean_nat_to_int(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprOpinion_repr(uint8_t v_x_82_, lean_object* v_prec_83_){
_start:
{
lean_object* v___y_85_; lean_object* v___y_92_; 
if (v_x_82_ == 0)
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(1024u);
v___x_99_ = lean_nat_dec_le(v___x_98_, v_prec_83_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4, &lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4_once, _init_lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4);
v___y_85_ = v___x_100_;
goto v___jp_84_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5, &lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5_once, _init_lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5);
v___y_85_ = v___x_101_;
goto v___jp_84_;
}
}
else
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1024u);
v___x_103_ = lean_nat_dec_le(v___x_102_, v_prec_83_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4, &lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4_once, _init_lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4);
v___y_92_ = v___x_104_;
goto v___jp_91_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5, &lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5_once, _init_lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5);
v___y_92_ = v___x_105_;
goto v___jp_91_;
}
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__1));
lean_inc(v___y_85_);
v___x_87_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_87_, 0, v___y_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = 0;
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_88_);
v___x_90_ = l_Repr_addAppParen(v___x_89_, v_prec_83_);
return v___x_90_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__3));
lean_inc(v___y_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___y_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = l_Repr_addAppParen(v___x_96_, v_prec_83_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprOpinion_repr___boxed(lean_object* v_x_106_, lean_object* v_prec_107_){
_start:
{
uint8_t v_x_121__boxed_108_; lean_object* v_res_109_; 
v_x_121__boxed_108_ = lean_unbox(v_x_106_);
v_res_109_ = lp_SSExactMajority_SSEM_instReprOpinion_repr(v_x_121__boxed_108_, v_prec_107_);
lean_dec(v_prec_107_);
return v_res_109_;
}
}
static uint8_t _init_lp_SSExactMajority_SSEM_instInhabitedOpinion_default(void){
_start:
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
}
static uint8_t _init_lp_SSExactMajority_SSEM_instInhabitedOpinion(void){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = 0;
return v___x_113_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeOpinion___closed__1(void){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_118_ = ((lean_object*)(lp_SSExactMajority_SSEM_instFintypeOpinion___closed__0));
v___x_119_ = 0;
v___x_120_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqOpinion___boxed), 2, 0);
v___x_121_ = lean_box(v___x_119_);
v___x_122_ = lp_mathlib_Multiset_ndinsert___redArg(v___x_120_, v___x_121_, v___x_118_);
return v___x_122_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeOpinion(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&lp_SSExactMajority_SSEM_instFintypeOpinion___closed__1, &lp_SSExactMajority_SSEM_instFintypeOpinion___closed__1_once, _init_lp_SSExactMajority_SSEM_instFintypeOpinion___closed__1);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_ctorIdx(uint8_t v_x_124_){
_start:
{
switch(v_x_124_)
{
case 0:
{
lean_object* v___x_125_; 
v___x_125_ = lean_unsigned_to_nat(0u);
return v___x_125_;
}
case 1:
{
lean_object* v___x_126_; 
v___x_126_ = lean_unsigned_to_nat(1u);
return v___x_126_;
}
default: 
{
lean_object* v___x_127_; 
v___x_127_ = lean_unsigned_to_nat(2u);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_ctorIdx___boxed(lean_object* v_x_128_){
_start:
{
uint8_t v_x_boxed_129_; lean_object* v_res_130_; 
v_x_boxed_129_ = lean_unbox(v_x_128_);
v_res_130_ = lp_SSExactMajority_SSEM_Output_ctorIdx(v_x_boxed_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_toCtorIdx(uint8_t v_x_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lp_SSExactMajority_SSEM_Output_ctorIdx(v_x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_toCtorIdx___boxed(lean_object* v_x_133_){
_start:
{
uint8_t v_x_4__boxed_134_; lean_object* v_res_135_; 
v_x_4__boxed_134_ = lean_unbox(v_x_133_);
v_res_135_ = lp_SSExactMajority_SSEM_Output_toCtorIdx(v_x_4__boxed_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_ctorElim___redArg(lean_object* v_k_136_){
_start:
{
lean_inc(v_k_136_);
return v_k_136_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_ctorElim___redArg___boxed(lean_object* v_k_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = lp_SSExactMajority_SSEM_Output_ctorElim___redArg(v_k_137_);
lean_dec(v_k_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_ctorElim(lean_object* v_motive_139_, lean_object* v_ctorIdx_140_, uint8_t v_t_141_, lean_object* v_h_142_, lean_object* v_k_143_){
_start:
{
lean_inc(v_k_143_);
return v_k_143_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_ctorElim___boxed(lean_object* v_motive_144_, lean_object* v_ctorIdx_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_k_148_){
_start:
{
uint8_t v_t_boxed_149_; lean_object* v_res_150_; 
v_t_boxed_149_ = lean_unbox(v_t_146_);
v_res_150_ = lp_SSExactMajority_SSEM_Output_ctorElim(v_motive_144_, v_ctorIdx_145_, v_t_boxed_149_, v_h_147_, v_k_148_);
lean_dec(v_k_148_);
lean_dec(v_ctorIdx_145_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_A_elim___redArg(lean_object* v_A_151_){
_start:
{
lean_inc(v_A_151_);
return v_A_151_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_A_elim___redArg___boxed(lean_object* v_A_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = lp_SSExactMajority_SSEM_Output_A_elim___redArg(v_A_152_);
lean_dec(v_A_152_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_A_elim(lean_object* v_motive_154_, uint8_t v_t_155_, lean_object* v_h_156_, lean_object* v_A_157_){
_start:
{
lean_inc(v_A_157_);
return v_A_157_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_A_elim___boxed(lean_object* v_motive_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_A_161_){
_start:
{
uint8_t v_t_boxed_162_; lean_object* v_res_163_; 
v_t_boxed_162_ = lean_unbox(v_t_159_);
v_res_163_ = lp_SSExactMajority_SSEM_Output_A_elim(v_motive_158_, v_t_boxed_162_, v_h_160_, v_A_161_);
lean_dec(v_A_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_B_elim___redArg(lean_object* v_B_164_){
_start:
{
lean_inc(v_B_164_);
return v_B_164_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_B_elim___redArg___boxed(lean_object* v_B_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = lp_SSExactMajority_SSEM_Output_B_elim___redArg(v_B_165_);
lean_dec(v_B_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_B_elim(lean_object* v_motive_167_, uint8_t v_t_168_, lean_object* v_h_169_, lean_object* v_B_170_){
_start:
{
lean_inc(v_B_170_);
return v_B_170_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_B_elim___boxed(lean_object* v_motive_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_B_174_){
_start:
{
uint8_t v_t_boxed_175_; lean_object* v_res_176_; 
v_t_boxed_175_ = lean_unbox(v_t_172_);
v_res_176_ = lp_SSExactMajority_SSEM_Output_B_elim(v_motive_171_, v_t_boxed_175_, v_h_173_, v_B_174_);
lean_dec(v_B_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_T_elim___redArg(lean_object* v_T_177_){
_start:
{
lean_inc(v_T_177_);
return v_T_177_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_T_elim___redArg___boxed(lean_object* v_T_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = lp_SSExactMajority_SSEM_Output_T_elim___redArg(v_T_178_);
lean_dec(v_T_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_T_elim(lean_object* v_motive_180_, uint8_t v_t_181_, lean_object* v_h_182_, lean_object* v_T_183_){
_start:
{
lean_inc(v_T_183_);
return v_T_183_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_T_elim___boxed(lean_object* v_motive_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_T_187_){
_start:
{
uint8_t v_t_boxed_188_; lean_object* v_res_189_; 
v_t_boxed_188_ = lean_unbox(v_t_185_);
v_res_189_ = lp_SSExactMajority_SSEM_Output_T_elim(v_motive_184_, v_t_boxed_188_, v_h_186_, v_T_187_);
lean_dec(v_T_187_);
return v_res_189_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Output_ofNat(lean_object* v_n_190_){
_start:
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = lean_nat_dec_le(v_n_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_dec_le(v_n_190_, v___x_193_);
if (v___x_194_ == 0)
{
uint8_t v___x_195_; 
v___x_195_ = 2;
return v___x_195_;
}
else
{
uint8_t v___x_196_; 
v___x_196_ = 1;
return v___x_196_;
}
}
else
{
uint8_t v___x_197_; 
v___x_197_ = 0;
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_ofNat___boxed(lean_object* v_n_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = lp_SSExactMajority_SSEM_Output_ofNat(v_n_198_);
lean_dec(v_n_198_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqOutput(uint8_t v_x_201_, uint8_t v_y_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_203_ = lp_SSExactMajority_SSEM_Output_ctorIdx(v_x_201_);
v___x_204_ = lp_SSExactMajority_SSEM_Output_ctorIdx(v_y_202_);
v___x_205_ = lean_nat_dec_eq(v___x_203_, v___x_204_);
lean_dec(v___x_204_);
lean_dec(v___x_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqOutput___boxed(lean_object* v_x_206_, lean_object* v_y_207_){
_start:
{
uint8_t v_x_13__boxed_208_; uint8_t v_y_14__boxed_209_; uint8_t v_res_210_; lean_object* v_r_211_; 
v_x_13__boxed_208_ = lean_unbox(v_x_206_);
v_y_14__boxed_209_ = lean_unbox(v_y_207_);
v_res_210_ = lp_SSExactMajority_SSEM_instDecidableEqOutput(v_x_13__boxed_208_, v_y_14__boxed_209_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprOutput_repr(uint8_t v_x_221_, lean_object* v_prec_222_){
_start:
{
lean_object* v___y_224_; lean_object* v___y_231_; lean_object* v___y_238_; 
switch(v_x_221_)
{
case 0:
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(1024u);
v___x_245_ = lean_nat_dec_le(v___x_244_, v_prec_222_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4, &lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4_once, _init_lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4);
v___y_224_ = v___x_246_;
goto v___jp_223_;
}
else
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5, &lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5_once, _init_lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5);
v___y_224_ = v___x_247_;
goto v___jp_223_;
}
}
case 1:
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = lean_unsigned_to_nat(1024u);
v___x_249_ = lean_nat_dec_le(v___x_248_, v_prec_222_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
v___x_250_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4, &lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4_once, _init_lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4);
v___y_231_ = v___x_250_;
goto v___jp_230_;
}
else
{
lean_object* v___x_251_; 
v___x_251_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5, &lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5_once, _init_lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5);
v___y_231_ = v___x_251_;
goto v___jp_230_;
}
}
default: 
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = lean_unsigned_to_nat(1024u);
v___x_253_ = lean_nat_dec_le(v___x_252_, v_prec_222_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
v___x_254_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4, &lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4_once, _init_lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__4);
v___y_238_ = v___x_254_;
goto v___jp_237_;
}
else
{
lean_object* v___x_255_; 
v___x_255_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5, &lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5_once, _init_lp_SSExactMajority_SSEM_instReprOpinion_repr___closed__5);
v___y_238_ = v___x_255_;
goto v___jp_237_;
}
}
}
v___jp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_225_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprOutput_repr___closed__1));
lean_inc(v___y_224_);
v___x_226_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_226_, 0, v___y_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = 0;
v___x_228_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1, v___x_227_);
v___x_229_ = l_Repr_addAppParen(v___x_228_, v_prec_222_);
return v___x_229_;
}
v___jp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_232_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprOutput_repr___closed__3));
lean_inc(v___y_231_);
v___x_233_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_233_, 0, v___y_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = 0;
v___x_235_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*1, v___x_234_);
v___x_236_ = l_Repr_addAppParen(v___x_235_, v_prec_222_);
return v___x_236_;
}
v___jp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_239_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprOutput_repr___closed__5));
lean_inc(v___y_238_);
v___x_240_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_240_, 0, v___y_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = 0;
v___x_242_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*1, v___x_241_);
v___x_243_ = l_Repr_addAppParen(v___x_242_, v_prec_222_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprOutput_repr___boxed(lean_object* v_x_256_, lean_object* v_prec_257_){
_start:
{
uint8_t v_x_173__boxed_258_; lean_object* v_res_259_; 
v_x_173__boxed_258_ = lean_unbox(v_x_256_);
v_res_259_ = lp_SSExactMajority_SSEM_instReprOutput_repr(v_x_173__boxed_258_, v_prec_257_);
lean_dec(v_prec_257_);
return v_res_259_;
}
}
static uint8_t _init_lp_SSExactMajority_SSEM_instInhabitedOutput_default(void){
_start:
{
uint8_t v___x_262_; 
v___x_262_ = 0;
return v___x_262_;
}
}
static uint8_t _init_lp_SSExactMajority_SSEM_instInhabitedOutput(void){
_start:
{
uint8_t v___x_263_; 
v___x_263_ = 0;
return v___x_263_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeOutput___closed__1(void){
_start:
{
lean_object* v___x_268_; uint8_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_268_ = ((lean_object*)(lp_SSExactMajority_SSEM_instFintypeOutput___closed__0));
v___x_269_ = 1;
v___x_270_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqOutput___boxed), 2, 0);
v___x_271_ = lean_box(v___x_269_);
v___x_272_ = lp_mathlib_Multiset_ndinsert___redArg(v___x_270_, v___x_271_, v___x_268_);
return v___x_272_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeOutput___closed__2(void){
_start:
{
lean_object* v___x_273_; uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_273_ = lean_obj_once(&lp_SSExactMajority_SSEM_instFintypeOutput___closed__1, &lp_SSExactMajority_SSEM_instFintypeOutput___closed__1_once, _init_lp_SSExactMajority_SSEM_instFintypeOutput___closed__1);
v___x_274_ = 0;
v___x_275_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instDecidableEqOutput___boxed), 2, 0);
v___x_276_ = lean_box(v___x_274_);
v___x_277_ = lp_mathlib_Multiset_ndinsert___redArg(v___x_275_, v___x_276_, v___x_273_);
return v___x_277_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instFintypeOutput(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_obj_once(&lp_SSExactMajority_SSEM_instFintypeOutput___closed__2, &lp_SSExactMajority_SSEM_instFintypeOutput___closed__2_once, _init_lp_SSExactMajority_SSEM_instFintypeOutput___closed__2);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_toString(uint8_t v_x_281_){
_start:
{
if (v_x_281_ == 0)
{
lean_object* v___x_282_; 
v___x_282_ = ((lean_object*)(lp_SSExactMajority_SSEM_Opinion_toString___closed__0));
return v___x_282_;
}
else
{
lean_object* v___x_283_; 
v___x_283_ = ((lean_object*)(lp_SSExactMajority_SSEM_Opinion_toString___closed__1));
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Opinion_toString___boxed(lean_object* v_x_284_){
_start:
{
uint8_t v_x_22__boxed_285_; lean_object* v_res_286_; 
v_x_22__boxed_285_ = lean_unbox(v_x_284_);
v_res_286_ = lp_SSExactMajority_SSEM_Opinion_toString(v_x_22__boxed_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_toString(uint8_t v_x_290_){
_start:
{
switch(v_x_290_)
{
case 0:
{
lean_object* v___x_291_; 
v___x_291_ = ((lean_object*)(lp_SSExactMajority_SSEM_Opinion_toString___closed__0));
return v___x_291_;
}
case 1:
{
lean_object* v___x_292_; 
v___x_292_ = ((lean_object*)(lp_SSExactMajority_SSEM_Opinion_toString___closed__1));
return v___x_292_;
}
default: 
{
lean_object* v___x_293_; 
v___x_293_ = ((lean_object*)(lp_SSExactMajority_SSEM_Output_toString___closed__0));
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Output_toString___boxed(lean_object* v_x_294_){
_start:
{
uint8_t v_x_29__boxed_295_; lean_object* v_res_296_; 
v_x_29__boxed_295_ = lean_unbox(v_x_294_);
v_res_296_ = lp_SSExactMajority_SSEM_Output_toString(v_x_29__boxed_295_);
return v_res_296_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Protocol(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_SSExactMajority_SSEM_instInhabitedOpinion_default = _init_lp_SSExactMajority_SSEM_instInhabitedOpinion_default();
lp_SSExactMajority_SSEM_instInhabitedOpinion = _init_lp_SSExactMajority_SSEM_instInhabitedOpinion();
lp_SSExactMajority_SSEM_instFintypeOpinion = _init_lp_SSExactMajority_SSEM_instFintypeOpinion();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeOpinion);
lp_SSExactMajority_SSEM_instInhabitedOutput_default = _init_lp_SSExactMajority_SSEM_instInhabitedOutput_default();
lp_SSExactMajority_SSEM_instInhabitedOutput = _init_lp_SSExactMajority_SSEM_instInhabitedOutput();
lp_SSExactMajority_SSEM_instFintypeOutput = _init_lp_SSExactMajority_SSEM_instFintypeOutput();
lean_mark_persistent(lp_SSExactMajority_SSEM_instFintypeOutput);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
