// Lean compiler output
// Module: SSExactMajority.Protocol.State
// Imports: public import Init public meta import Init public import SSExactMajority.Defs.Protocol
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Resetting_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Resetting_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Resetting_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Resetting_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Settled_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Settled_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Settled_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Settled_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Unsettled_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Unsettled_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Unsettled_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Unsettled_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Role_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqRole(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqRole___boxed(lean_object*, lean_object*);
static const lean_string_object lp_SSExactMajority_SSEM_instReprRole_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "SSEM.Role.Resetting"};
static const lean_object* lp_SSExactMajority_SSEM_instReprRole_repr___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprRole_repr___closed__0_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprRole_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprRole_repr___closed__0_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprRole_repr___closed__1 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprRole_repr___closed__1_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprRole_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "SSEM.Role.Settled"};
static const lean_object* lp_SSExactMajority_SSEM_instReprRole_repr___closed__2 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprRole_repr___closed__2_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprRole_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprRole_repr___closed__2_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprRole_repr___closed__3 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprRole_repr___closed__3_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprRole_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "SSEM.Role.Unsettled"};
static const lean_object* lp_SSExactMajority_SSEM_instReprRole_repr___closed__4 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprRole_repr___closed__4_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprRole_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprRole_repr___closed__4_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprRole_repr___closed__5 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprRole_repr___closed__5_value;
static lean_once_cell_t lp_SSExactMajority_SSEM_instReprRole_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instReprRole_repr___closed__6;
static lean_once_cell_t lp_SSExactMajority_SSEM_instReprRole_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instReprRole_repr___closed__7;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprRole_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprRole_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_SSExactMajority_SSEM_instReprRole___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SSExactMajority_SSEM_instReprRole_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SSExactMajority_SSEM_instReprRole___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprRole___closed__0_value;
LEAN_EXPORT const lean_object* lp_SSExactMajority_SSEM_instReprRole = (const lean_object*)&lp_SSExactMajority_SSEM_instReprRole___closed__0_value;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_L_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_L_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_L_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_L_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_F_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_F_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_F_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_F_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Leader_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqLeader(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqLeader___boxed(lean_object*, lean_object*);
static const lean_string_object lp_SSExactMajority_SSEM_instReprLeader_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SSEM.Leader.L"};
static const lean_object* lp_SSExactMajority_SSEM_instReprLeader_repr___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprLeader_repr___closed__0_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprLeader_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprLeader_repr___closed__0_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprLeader_repr___closed__1 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprLeader_repr___closed__1_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprLeader_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SSEM.Leader.F"};
static const lean_object* lp_SSExactMajority_SSEM_instReprLeader_repr___closed__2 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprLeader_repr___closed__2_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprLeader_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprLeader_repr___closed__2_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprLeader_repr___closed__3 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprLeader_repr___closed__3_value;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprLeader_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprLeader_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_SSExactMajority_SSEM_instReprLeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SSExactMajority_SSEM_instReprLeader_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SSExactMajority_SSEM_instReprLeader___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprLeader___closed__0_value;
LEAN_EXPORT const lean_object* lp_SSExactMajority_SSEM_instReprLeader = (const lean_object*)&lp_SSExactMajority_SSEM_instReprLeader___closed__0_value;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_phi_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_phi_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_phi_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_phi_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outT_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outT_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outT_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outT_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outA_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outA_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outA_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outA_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outB_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outB_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outB_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outB_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Answer_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqAnswer(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqAnswer___boxed(lean_object*, lean_object*);
static const lean_string_object lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "SSEM.Answer.phi"};
static const lean_object* lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__0_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__0_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__1 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__1_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SSEM.Answer.outT"};
static const lean_object* lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__2 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__2_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__2_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__3 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__3_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SSEM.Answer.outA"};
static const lean_object* lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__4 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__4_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__4_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__5 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__5_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SSEM.Answer.outB"};
static const lean_object* lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__6 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__6_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__6_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__7 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__7_value;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprAnswer_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprAnswer_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_SSExactMajority_SSEM_instReprAnswer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SSExactMajority_SSEM_instReprAnswer_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SSExactMajority_SSEM_instReprAnswer___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAnswer___closed__0_value;
LEAN_EXPORT const lean_object* lp_SSExactMajority_SSEM_instReprAnswer = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAnswer___closed__0_value;
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Answer_toOutput(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_toOutput___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqAgentState_decEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqAgentState_decEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqAgentState_decEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqAgentState_decEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqAgentState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqAgentState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqAgentState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqAgentState___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__0_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "role"};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__1 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__1_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__1_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__2 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__2_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__2_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__3 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__3_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__4 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__4_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__4_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__5 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__5_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__3_value),((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__5_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__6 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__6_value;
static lean_once_cell_t lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__7;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__8 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__8_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__8_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__9 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__9_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "rank"};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__10 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__10_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__10_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__11 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__11_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "leader"};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__12 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__12_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__12_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__13 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__13_value;
static lean_once_cell_t lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__14;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "resetcount"};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__15 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__15_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__15_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__16 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__16_value;
static lean_once_cell_t lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__17;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "answer"};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__18 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__18_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__18_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__19 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__19_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "timer"};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__20 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__20_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__20_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__21 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__21_value;
static lean_once_cell_t lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__22;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "children"};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__23 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__23_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__23_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__24 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__24_value;
static lean_once_cell_t lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__25;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "errorcount"};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__26 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__26_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__26_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__27 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__27_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "delaytimer"};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__28 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__28_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__28_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__29 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__29_value;
static const lean_string_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__30 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__30_value;
static lean_once_cell_t lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__31;
static lean_once_cell_t lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__32;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__0_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__33 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__33_value;
static const lean_ctor_object lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__30_value)}};
static const lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__34 = (const lean_object*)&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__34_value;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprAgentState(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_agentOutput___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_agentOutput___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_agentOutput(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_agentOutput___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = lp_SSExactMajority_SSEM_Role_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lp_SSExactMajority_SSEM_Role_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = lp_SSExactMajority_SSEM_Role_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_SSExactMajority_SSEM_Role_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = lp_SSExactMajority_SSEM_Role_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Resetting_elim___redArg(lean_object* v_Resetting_28_){
_start:
{
lean_inc(v_Resetting_28_);
return v_Resetting_28_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Resetting_elim___redArg___boxed(lean_object* v_Resetting_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_SSExactMajority_SSEM_Role_Resetting_elim___redArg(v_Resetting_29_);
lean_dec(v_Resetting_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Resetting_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_Resetting_34_){
_start:
{
lean_inc(v_Resetting_34_);
return v_Resetting_34_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Resetting_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_Resetting_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = lp_SSExactMajority_SSEM_Role_Resetting_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_Resetting_38_);
lean_dec(v_Resetting_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Settled_elim___redArg(lean_object* v_Settled_41_){
_start:
{
lean_inc(v_Settled_41_);
return v_Settled_41_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Settled_elim___redArg___boxed(lean_object* v_Settled_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_SSExactMajority_SSEM_Role_Settled_elim___redArg(v_Settled_42_);
lean_dec(v_Settled_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Settled_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_Settled_47_){
_start:
{
lean_inc(v_Settled_47_);
return v_Settled_47_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Settled_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_Settled_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = lp_SSExactMajority_SSEM_Role_Settled_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_Settled_51_);
lean_dec(v_Settled_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Unsettled_elim___redArg(lean_object* v_Unsettled_54_){
_start:
{
lean_inc(v_Unsettled_54_);
return v_Unsettled_54_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Unsettled_elim___redArg___boxed(lean_object* v_Unsettled_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_SSExactMajority_SSEM_Role_Unsettled_elim___redArg(v_Unsettled_55_);
lean_dec(v_Unsettled_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Unsettled_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_Unsettled_60_){
_start:
{
lean_inc(v_Unsettled_60_);
return v_Unsettled_60_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_Unsettled_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_Unsettled_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = lp_SSExactMajority_SSEM_Role_Unsettled_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_Unsettled_64_);
lean_dec(v_Unsettled_64_);
return v_res_66_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Role_ofNat(lean_object* v_n_67_){
_start:
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_nat_dec_le(v_n_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_dec_le(v_n_67_, v___x_70_);
if (v___x_71_ == 0)
{
uint8_t v___x_72_; 
v___x_72_ = 2;
return v___x_72_;
}
else
{
uint8_t v___x_73_; 
v___x_73_ = 1;
return v___x_73_;
}
}
else
{
uint8_t v___x_74_; 
v___x_74_ = 0;
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Role_ofNat___boxed(lean_object* v_n_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = lp_SSExactMajority_SSEM_Role_ofNat(v_n_75_);
lean_dec(v_n_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqRole(uint8_t v_x_78_, uint8_t v_y_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_80_ = lp_SSExactMajority_SSEM_Role_ctorIdx(v_x_78_);
v___x_81_ = lp_SSExactMajority_SSEM_Role_ctorIdx(v_y_79_);
v___x_82_ = lean_nat_dec_eq(v___x_80_, v___x_81_);
lean_dec(v___x_81_);
lean_dec(v___x_80_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqRole___boxed(lean_object* v_x_83_, lean_object* v_y_84_){
_start:
{
uint8_t v_x_13__boxed_85_; uint8_t v_y_14__boxed_86_; uint8_t v_res_87_; lean_object* v_r_88_; 
v_x_13__boxed_85_ = lean_unbox(v_x_83_);
v_y_14__boxed_86_ = lean_unbox(v_y_84_);
v_res_87_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_x_13__boxed_85_, v_y_14__boxed_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__6(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(2u);
v___x_99_ = lean_nat_to_int(v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__7(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_to_int(v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprRole_repr(uint8_t v_x_102_, lean_object* v_prec_103_){
_start:
{
lean_object* v___y_105_; lean_object* v___y_112_; lean_object* v___y_119_; 
switch(v_x_102_)
{
case 0:
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(1024u);
v___x_126_ = lean_nat_dec_le(v___x_125_, v_prec_103_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__6, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__6_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__6);
v___y_105_ = v___x_127_;
goto v___jp_104_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__7, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__7_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__7);
v___y_105_ = v___x_128_;
goto v___jp_104_;
}
}
case 1:
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(1024u);
v___x_130_ = lean_nat_dec_le(v___x_129_, v_prec_103_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__6, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__6_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__6);
v___y_112_ = v___x_131_;
goto v___jp_111_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__7, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__7_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__7);
v___y_112_ = v___x_132_;
goto v___jp_111_;
}
}
default: 
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(1024u);
v___x_134_ = lean_nat_dec_le(v___x_133_, v_prec_103_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__6, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__6_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__6);
v___y_119_ = v___x_135_;
goto v___jp_118_;
}
else
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__7, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__7_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__7);
v___y_119_ = v___x_136_;
goto v___jp_118_;
}
}
}
v___jp_104_:
{
lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_106_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprRole_repr___closed__1));
lean_inc(v___y_105_);
v___x_107_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_107_, 0, v___y_105_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = 0;
v___x_109_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_109_, 0, v___x_107_);
lean_ctor_set_uint8(v___x_109_, sizeof(void*)*1, v___x_108_);
v___x_110_ = l_Repr_addAppParen(v___x_109_, v_prec_103_);
return v___x_110_;
}
v___jp_111_:
{
lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_113_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprRole_repr___closed__3));
lean_inc(v___y_112_);
v___x_114_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_114_, 0, v___y_112_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = 0;
v___x_116_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*1, v___x_115_);
v___x_117_ = l_Repr_addAppParen(v___x_116_, v_prec_103_);
return v___x_117_;
}
v___jp_118_:
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_120_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprRole_repr___closed__5));
lean_inc(v___y_119_);
v___x_121_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_121_, 0, v___y_119_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = 0;
v___x_123_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*1, v___x_122_);
v___x_124_ = l_Repr_addAppParen(v___x_123_, v_prec_103_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprRole_repr___boxed(lean_object* v_x_137_, lean_object* v_prec_138_){
_start:
{
uint8_t v_x_177__boxed_139_; lean_object* v_res_140_; 
v_x_177__boxed_139_ = lean_unbox(v_x_137_);
v_res_140_ = lp_SSExactMajority_SSEM_instReprRole_repr(v_x_177__boxed_139_, v_prec_138_);
lean_dec(v_prec_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_ctorIdx(uint8_t v_x_143_){
_start:
{
if (v_x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_unsigned_to_nat(0u);
return v___x_144_;
}
else
{
lean_object* v___x_145_; 
v___x_145_ = lean_unsigned_to_nat(1u);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_ctorIdx___boxed(lean_object* v_x_146_){
_start:
{
uint8_t v_x_boxed_147_; lean_object* v_res_148_; 
v_x_boxed_147_ = lean_unbox(v_x_146_);
v_res_148_ = lp_SSExactMajority_SSEM_Leader_ctorIdx(v_x_boxed_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_toCtorIdx(uint8_t v_x_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lp_SSExactMajority_SSEM_Leader_ctorIdx(v_x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_toCtorIdx___boxed(lean_object* v_x_151_){
_start:
{
uint8_t v_x_4__boxed_152_; lean_object* v_res_153_; 
v_x_4__boxed_152_ = lean_unbox(v_x_151_);
v_res_153_ = lp_SSExactMajority_SSEM_Leader_toCtorIdx(v_x_4__boxed_152_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_ctorElim___redArg(lean_object* v_k_154_){
_start:
{
lean_inc(v_k_154_);
return v_k_154_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_ctorElim___redArg___boxed(lean_object* v_k_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = lp_SSExactMajority_SSEM_Leader_ctorElim___redArg(v_k_155_);
lean_dec(v_k_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_ctorElim(lean_object* v_motive_157_, lean_object* v_ctorIdx_158_, uint8_t v_t_159_, lean_object* v_h_160_, lean_object* v_k_161_){
_start:
{
lean_inc(v_k_161_);
return v_k_161_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_ctorElim___boxed(lean_object* v_motive_162_, lean_object* v_ctorIdx_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_k_166_){
_start:
{
uint8_t v_t_boxed_167_; lean_object* v_res_168_; 
v_t_boxed_167_ = lean_unbox(v_t_164_);
v_res_168_ = lp_SSExactMajority_SSEM_Leader_ctorElim(v_motive_162_, v_ctorIdx_163_, v_t_boxed_167_, v_h_165_, v_k_166_);
lean_dec(v_k_166_);
lean_dec(v_ctorIdx_163_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_L_elim___redArg(lean_object* v_L_169_){
_start:
{
lean_inc(v_L_169_);
return v_L_169_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_L_elim___redArg___boxed(lean_object* v_L_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = lp_SSExactMajority_SSEM_Leader_L_elim___redArg(v_L_170_);
lean_dec(v_L_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_L_elim(lean_object* v_motive_172_, uint8_t v_t_173_, lean_object* v_h_174_, lean_object* v_L_175_){
_start:
{
lean_inc(v_L_175_);
return v_L_175_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_L_elim___boxed(lean_object* v_motive_176_, lean_object* v_t_177_, lean_object* v_h_178_, lean_object* v_L_179_){
_start:
{
uint8_t v_t_boxed_180_; lean_object* v_res_181_; 
v_t_boxed_180_ = lean_unbox(v_t_177_);
v_res_181_ = lp_SSExactMajority_SSEM_Leader_L_elim(v_motive_176_, v_t_boxed_180_, v_h_178_, v_L_179_);
lean_dec(v_L_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_F_elim___redArg(lean_object* v_F_182_){
_start:
{
lean_inc(v_F_182_);
return v_F_182_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_F_elim___redArg___boxed(lean_object* v_F_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = lp_SSExactMajority_SSEM_Leader_F_elim___redArg(v_F_183_);
lean_dec(v_F_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_F_elim(lean_object* v_motive_185_, uint8_t v_t_186_, lean_object* v_h_187_, lean_object* v_F_188_){
_start:
{
lean_inc(v_F_188_);
return v_F_188_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_F_elim___boxed(lean_object* v_motive_189_, lean_object* v_t_190_, lean_object* v_h_191_, lean_object* v_F_192_){
_start:
{
uint8_t v_t_boxed_193_; lean_object* v_res_194_; 
v_t_boxed_193_ = lean_unbox(v_t_190_);
v_res_194_ = lp_SSExactMajority_SSEM_Leader_F_elim(v_motive_189_, v_t_boxed_193_, v_h_191_, v_F_192_);
lean_dec(v_F_192_);
return v_res_194_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Leader_ofNat(lean_object* v_n_195_){
_start:
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = lean_nat_dec_le(v_n_195_, v___x_196_);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; 
v___x_198_ = 1;
return v___x_198_;
}
else
{
uint8_t v___x_199_; 
v___x_199_ = 0;
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Leader_ofNat___boxed(lean_object* v_n_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = lp_SSExactMajority_SSEM_Leader_ofNat(v_n_200_);
lean_dec(v_n_200_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqLeader(uint8_t v_x_203_, uint8_t v_y_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_205_ = lp_SSExactMajority_SSEM_Leader_ctorIdx(v_x_203_);
v___x_206_ = lp_SSExactMajority_SSEM_Leader_ctorIdx(v_y_204_);
v___x_207_ = lean_nat_dec_eq(v___x_205_, v___x_206_);
lean_dec(v___x_206_);
lean_dec(v___x_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqLeader___boxed(lean_object* v_x_208_, lean_object* v_y_209_){
_start:
{
uint8_t v_x_13__boxed_210_; uint8_t v_y_14__boxed_211_; uint8_t v_res_212_; lean_object* v_r_213_; 
v_x_13__boxed_210_ = lean_unbox(v_x_208_);
v_y_14__boxed_211_ = lean_unbox(v_y_209_);
v_res_212_ = lp_SSExactMajority_SSEM_instDecidableEqLeader(v_x_13__boxed_210_, v_y_14__boxed_211_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprLeader_repr(uint8_t v_x_220_, lean_object* v_prec_221_){
_start:
{
lean_object* v___y_223_; lean_object* v___y_230_; 
if (v_x_220_ == 0)
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(1024u);
v___x_237_ = lean_nat_dec_le(v___x_236_, v_prec_221_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__6, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__6_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__6);
v___y_223_ = v___x_238_;
goto v___jp_222_;
}
else
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__7, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__7_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__7);
v___y_223_ = v___x_239_;
goto v___jp_222_;
}
}
else
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(1024u);
v___x_241_ = lean_nat_dec_le(v___x_240_, v_prec_221_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
v___x_242_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__6, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__6_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__6);
v___y_230_ = v___x_242_;
goto v___jp_229_;
}
else
{
lean_object* v___x_243_; 
v___x_243_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__7, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__7_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__7);
v___y_230_ = v___x_243_;
goto v___jp_229_;
}
}
v___jp_222_:
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_224_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprLeader_repr___closed__1));
lean_inc(v___y_223_);
v___x_225_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_225_, 0, v___y_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = 0;
v___x_227_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*1, v___x_226_);
v___x_228_ = l_Repr_addAppParen(v___x_227_, v_prec_221_);
return v___x_228_;
}
v___jp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_231_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprLeader_repr___closed__3));
lean_inc(v___y_230_);
v___x_232_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_232_, 0, v___y_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = 0;
v___x_234_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*1, v___x_233_);
v___x_235_ = l_Repr_addAppParen(v___x_234_, v_prec_221_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprLeader_repr___boxed(lean_object* v_x_244_, lean_object* v_prec_245_){
_start:
{
uint8_t v_x_117__boxed_246_; lean_object* v_res_247_; 
v_x_117__boxed_246_ = lean_unbox(v_x_244_);
v_res_247_ = lp_SSExactMajority_SSEM_instReprLeader_repr(v_x_117__boxed_246_, v_prec_245_);
lean_dec(v_prec_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_ctorIdx(uint8_t v_x_250_){
_start:
{
switch(v_x_250_)
{
case 0:
{
lean_object* v___x_251_; 
v___x_251_ = lean_unsigned_to_nat(0u);
return v___x_251_;
}
case 1:
{
lean_object* v___x_252_; 
v___x_252_ = lean_unsigned_to_nat(1u);
return v___x_252_;
}
case 2:
{
lean_object* v___x_253_; 
v___x_253_ = lean_unsigned_to_nat(2u);
return v___x_253_;
}
default: 
{
lean_object* v___x_254_; 
v___x_254_ = lean_unsigned_to_nat(3u);
return v___x_254_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_ctorIdx___boxed(lean_object* v_x_255_){
_start:
{
uint8_t v_x_boxed_256_; lean_object* v_res_257_; 
v_x_boxed_256_ = lean_unbox(v_x_255_);
v_res_257_ = lp_SSExactMajority_SSEM_Answer_ctorIdx(v_x_boxed_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_toCtorIdx(uint8_t v_x_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lp_SSExactMajority_SSEM_Answer_ctorIdx(v_x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_toCtorIdx___boxed(lean_object* v_x_260_){
_start:
{
uint8_t v_x_4__boxed_261_; lean_object* v_res_262_; 
v_x_4__boxed_261_ = lean_unbox(v_x_260_);
v_res_262_ = lp_SSExactMajority_SSEM_Answer_toCtorIdx(v_x_4__boxed_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_ctorElim___redArg(lean_object* v_k_263_){
_start:
{
lean_inc(v_k_263_);
return v_k_263_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_ctorElim___redArg___boxed(lean_object* v_k_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = lp_SSExactMajority_SSEM_Answer_ctorElim___redArg(v_k_264_);
lean_dec(v_k_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_ctorElim(lean_object* v_motive_266_, lean_object* v_ctorIdx_267_, uint8_t v_t_268_, lean_object* v_h_269_, lean_object* v_k_270_){
_start:
{
lean_inc(v_k_270_);
return v_k_270_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_ctorElim___boxed(lean_object* v_motive_271_, lean_object* v_ctorIdx_272_, lean_object* v_t_273_, lean_object* v_h_274_, lean_object* v_k_275_){
_start:
{
uint8_t v_t_boxed_276_; lean_object* v_res_277_; 
v_t_boxed_276_ = lean_unbox(v_t_273_);
v_res_277_ = lp_SSExactMajority_SSEM_Answer_ctorElim(v_motive_271_, v_ctorIdx_272_, v_t_boxed_276_, v_h_274_, v_k_275_);
lean_dec(v_k_275_);
lean_dec(v_ctorIdx_272_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_phi_elim___redArg(lean_object* v_phi_278_){
_start:
{
lean_inc(v_phi_278_);
return v_phi_278_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_phi_elim___redArg___boxed(lean_object* v_phi_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = lp_SSExactMajority_SSEM_Answer_phi_elim___redArg(v_phi_279_);
lean_dec(v_phi_279_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_phi_elim(lean_object* v_motive_281_, uint8_t v_t_282_, lean_object* v_h_283_, lean_object* v_phi_284_){
_start:
{
lean_inc(v_phi_284_);
return v_phi_284_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_phi_elim___boxed(lean_object* v_motive_285_, lean_object* v_t_286_, lean_object* v_h_287_, lean_object* v_phi_288_){
_start:
{
uint8_t v_t_boxed_289_; lean_object* v_res_290_; 
v_t_boxed_289_ = lean_unbox(v_t_286_);
v_res_290_ = lp_SSExactMajority_SSEM_Answer_phi_elim(v_motive_285_, v_t_boxed_289_, v_h_287_, v_phi_288_);
lean_dec(v_phi_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outT_elim___redArg(lean_object* v_outT_291_){
_start:
{
lean_inc(v_outT_291_);
return v_outT_291_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outT_elim___redArg___boxed(lean_object* v_outT_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = lp_SSExactMajority_SSEM_Answer_outT_elim___redArg(v_outT_292_);
lean_dec(v_outT_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outT_elim(lean_object* v_motive_294_, uint8_t v_t_295_, lean_object* v_h_296_, lean_object* v_outT_297_){
_start:
{
lean_inc(v_outT_297_);
return v_outT_297_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outT_elim___boxed(lean_object* v_motive_298_, lean_object* v_t_299_, lean_object* v_h_300_, lean_object* v_outT_301_){
_start:
{
uint8_t v_t_boxed_302_; lean_object* v_res_303_; 
v_t_boxed_302_ = lean_unbox(v_t_299_);
v_res_303_ = lp_SSExactMajority_SSEM_Answer_outT_elim(v_motive_298_, v_t_boxed_302_, v_h_300_, v_outT_301_);
lean_dec(v_outT_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outA_elim___redArg(lean_object* v_outA_304_){
_start:
{
lean_inc(v_outA_304_);
return v_outA_304_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outA_elim___redArg___boxed(lean_object* v_outA_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = lp_SSExactMajority_SSEM_Answer_outA_elim___redArg(v_outA_305_);
lean_dec(v_outA_305_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outA_elim(lean_object* v_motive_307_, uint8_t v_t_308_, lean_object* v_h_309_, lean_object* v_outA_310_){
_start:
{
lean_inc(v_outA_310_);
return v_outA_310_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outA_elim___boxed(lean_object* v_motive_311_, lean_object* v_t_312_, lean_object* v_h_313_, lean_object* v_outA_314_){
_start:
{
uint8_t v_t_boxed_315_; lean_object* v_res_316_; 
v_t_boxed_315_ = lean_unbox(v_t_312_);
v_res_316_ = lp_SSExactMajority_SSEM_Answer_outA_elim(v_motive_311_, v_t_boxed_315_, v_h_313_, v_outA_314_);
lean_dec(v_outA_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outB_elim___redArg(lean_object* v_outB_317_){
_start:
{
lean_inc(v_outB_317_);
return v_outB_317_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outB_elim___redArg___boxed(lean_object* v_outB_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = lp_SSExactMajority_SSEM_Answer_outB_elim___redArg(v_outB_318_);
lean_dec(v_outB_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outB_elim(lean_object* v_motive_320_, uint8_t v_t_321_, lean_object* v_h_322_, lean_object* v_outB_323_){
_start:
{
lean_inc(v_outB_323_);
return v_outB_323_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_outB_elim___boxed(lean_object* v_motive_324_, lean_object* v_t_325_, lean_object* v_h_326_, lean_object* v_outB_327_){
_start:
{
uint8_t v_t_boxed_328_; lean_object* v_res_329_; 
v_t_boxed_328_ = lean_unbox(v_t_325_);
v_res_329_ = lp_SSExactMajority_SSEM_Answer_outB_elim(v_motive_324_, v_t_boxed_328_, v_h_326_, v_outB_327_);
lean_dec(v_outB_327_);
return v_res_329_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Answer_ofNat(lean_object* v_n_330_){
_start:
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = lean_nat_dec_le(v_n_330_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(2u);
v___x_334_ = lean_nat_dec_le(v_n_330_, v___x_333_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; 
v___x_335_ = 3;
return v___x_335_;
}
else
{
uint8_t v___x_336_; 
v___x_336_ = 2;
return v___x_336_;
}
}
else
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_nat_dec_le(v_n_330_, v___x_337_);
if (v___x_338_ == 0)
{
uint8_t v___x_339_; 
v___x_339_ = 1;
return v___x_339_;
}
else
{
uint8_t v___x_340_; 
v___x_340_ = 0;
return v___x_340_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_ofNat___boxed(lean_object* v_n_341_){
_start:
{
uint8_t v_res_342_; lean_object* v_r_343_; 
v_res_342_ = lp_SSExactMajority_SSEM_Answer_ofNat(v_n_341_);
lean_dec(v_n_341_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqAnswer(uint8_t v_x_344_, uint8_t v_y_345_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_346_ = lp_SSExactMajority_SSEM_Answer_ctorIdx(v_x_344_);
v___x_347_ = lp_SSExactMajority_SSEM_Answer_ctorIdx(v_y_345_);
v___x_348_ = lean_nat_dec_eq(v___x_346_, v___x_347_);
lean_dec(v___x_347_);
lean_dec(v___x_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqAnswer___boxed(lean_object* v_x_349_, lean_object* v_y_350_){
_start:
{
uint8_t v_x_13__boxed_351_; uint8_t v_y_14__boxed_352_; uint8_t v_res_353_; lean_object* v_r_354_; 
v_x_13__boxed_351_ = lean_unbox(v_x_349_);
v_y_14__boxed_352_ = lean_unbox(v_y_350_);
v_res_353_ = lp_SSExactMajority_SSEM_instDecidableEqAnswer(v_x_13__boxed_351_, v_y_14__boxed_352_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprAnswer_repr(uint8_t v_x_367_, lean_object* v_prec_368_){
_start:
{
lean_object* v___y_370_; lean_object* v___y_377_; lean_object* v___y_384_; lean_object* v___y_391_; 
switch(v_x_367_)
{
case 0:
{
lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_397_ = lean_unsigned_to_nat(1024u);
v___x_398_ = lean_nat_dec_le(v___x_397_, v_prec_368_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__6, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__6_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__6);
v___y_370_ = v___x_399_;
goto v___jp_369_;
}
else
{
lean_object* v___x_400_; 
v___x_400_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__7, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__7_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__7);
v___y_370_ = v___x_400_;
goto v___jp_369_;
}
}
case 1:
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = lean_unsigned_to_nat(1024u);
v___x_402_ = lean_nat_dec_le(v___x_401_, v_prec_368_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; 
v___x_403_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__6, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__6_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__6);
v___y_377_ = v___x_403_;
goto v___jp_376_;
}
else
{
lean_object* v___x_404_; 
v___x_404_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__7, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__7_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__7);
v___y_377_ = v___x_404_;
goto v___jp_376_;
}
}
case 2:
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = lean_unsigned_to_nat(1024u);
v___x_406_ = lean_nat_dec_le(v___x_405_, v_prec_368_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
v___x_407_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__6, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__6_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__6);
v___y_384_ = v___x_407_;
goto v___jp_383_;
}
else
{
lean_object* v___x_408_; 
v___x_408_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__7, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__7_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__7);
v___y_384_ = v___x_408_;
goto v___jp_383_;
}
}
default: 
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = lean_unsigned_to_nat(1024u);
v___x_410_ = lean_nat_dec_le(v___x_409_, v_prec_368_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
v___x_411_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__6, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__6_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__6);
v___y_391_ = v___x_411_;
goto v___jp_390_;
}
else
{
lean_object* v___x_412_; 
v___x_412_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprRole_repr___closed__7, &lp_SSExactMajority_SSEM_instReprRole_repr___closed__7_once, _init_lp_SSExactMajority_SSEM_instReprRole_repr___closed__7);
v___y_391_ = v___x_412_;
goto v___jp_390_;
}
}
}
v___jp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_371_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__1));
lean_inc(v___y_370_);
v___x_372_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_372_, 0, v___y_370_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = 0;
v___x_374_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*1, v___x_373_);
v___x_375_ = l_Repr_addAppParen(v___x_374_, v_prec_368_);
return v___x_375_;
}
v___jp_376_:
{
lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_378_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__3));
lean_inc(v___y_377_);
v___x_379_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_379_, 0, v___y_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = 0;
v___x_381_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*1, v___x_380_);
v___x_382_ = l_Repr_addAppParen(v___x_381_, v_prec_368_);
return v___x_382_;
}
v___jp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_385_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__5));
lean_inc(v___y_384_);
v___x_386_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_386_, 0, v___y_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = 0;
v___x_388_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*1, v___x_387_);
v___x_389_ = l_Repr_addAppParen(v___x_388_, v_prec_368_);
return v___x_389_;
}
v___jp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_392_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAnswer_repr___closed__7));
lean_inc(v___y_391_);
v___x_393_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_393_, 0, v___y_391_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = 0;
v___x_395_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*1, v___x_394_);
v___x_396_ = l_Repr_addAppParen(v___x_395_, v_prec_368_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprAnswer_repr___boxed(lean_object* v_x_413_, lean_object* v_prec_414_){
_start:
{
uint8_t v_x_229__boxed_415_; lean_object* v_res_416_; 
v_x_229__boxed_415_ = lean_unbox(v_x_413_);
v_res_416_ = lp_SSExactMajority_SSEM_instReprAnswer_repr(v_x_229__boxed_415_, v_prec_414_);
lean_dec(v_prec_414_);
return v_res_416_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Answer_toOutput(uint8_t v_x_419_){
_start:
{
switch(v_x_419_)
{
case 2:
{
uint8_t v___x_420_; 
v___x_420_ = 0;
return v___x_420_;
}
case 3:
{
uint8_t v___x_421_; 
v___x_421_ = 1;
return v___x_421_;
}
default: 
{
uint8_t v___x_422_; 
v___x_422_ = 2;
return v___x_422_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Answer_toOutput___boxed(lean_object* v_x_423_){
_start:
{
uint8_t v_x_30__boxed_424_; uint8_t v_res_425_; lean_object* v_r_426_; 
v_x_30__boxed_424_ = lean_unbox(v_x_423_);
v_res_425_ = lp_SSExactMajority_SSEM_Answer_toOutput(v_x_30__boxed_424_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqAgentState_decEq___redArg(lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
uint8_t v_role_429_; lean_object* v_rank_430_; uint8_t v_leader_431_; lean_object* v_resetcount_432_; uint8_t v_answer_433_; lean_object* v_timer_434_; lean_object* v_children_435_; lean_object* v_errorcount_436_; lean_object* v_delaytimer_437_; uint8_t v_role_438_; lean_object* v_rank_439_; uint8_t v_leader_440_; lean_object* v_resetcount_441_; uint8_t v_answer_442_; lean_object* v_timer_443_; lean_object* v_children_444_; lean_object* v_errorcount_445_; lean_object* v_delaytimer_446_; uint8_t v___x_447_; 
v_role_429_ = lean_ctor_get_uint8(v_x_427_, sizeof(void*)*6);
v_rank_430_ = lean_ctor_get(v_x_427_, 0);
v_leader_431_ = lean_ctor_get_uint8(v_x_427_, sizeof(void*)*6 + 1);
v_resetcount_432_ = lean_ctor_get(v_x_427_, 1);
v_answer_433_ = lean_ctor_get_uint8(v_x_427_, sizeof(void*)*6 + 2);
v_timer_434_ = lean_ctor_get(v_x_427_, 2);
v_children_435_ = lean_ctor_get(v_x_427_, 3);
v_errorcount_436_ = lean_ctor_get(v_x_427_, 4);
v_delaytimer_437_ = lean_ctor_get(v_x_427_, 5);
v_role_438_ = lean_ctor_get_uint8(v_x_428_, sizeof(void*)*6);
v_rank_439_ = lean_ctor_get(v_x_428_, 0);
v_leader_440_ = lean_ctor_get_uint8(v_x_428_, sizeof(void*)*6 + 1);
v_resetcount_441_ = lean_ctor_get(v_x_428_, 1);
v_answer_442_ = lean_ctor_get_uint8(v_x_428_, sizeof(void*)*6 + 2);
v_timer_443_ = lean_ctor_get(v_x_428_, 2);
v_children_444_ = lean_ctor_get(v_x_428_, 3);
v_errorcount_445_ = lean_ctor_get(v_x_428_, 4);
v_delaytimer_446_ = lean_ctor_get(v_x_428_, 5);
v___x_447_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_429_, v_role_438_);
if (v___x_447_ == 0)
{
return v___x_447_;
}
else
{
uint8_t v___x_448_; 
v___x_448_ = lean_nat_dec_eq(v_rank_430_, v_rank_439_);
if (v___x_448_ == 0)
{
return v___x_448_;
}
else
{
uint8_t v___x_449_; 
v___x_449_ = lp_SSExactMajority_SSEM_instDecidableEqLeader(v_leader_431_, v_leader_440_);
if (v___x_449_ == 0)
{
return v___x_449_;
}
else
{
uint8_t v___x_450_; 
v___x_450_ = lean_nat_dec_eq(v_resetcount_432_, v_resetcount_441_);
if (v___x_450_ == 0)
{
return v___x_450_;
}
else
{
uint8_t v___x_451_; 
v___x_451_ = lp_SSExactMajority_SSEM_instDecidableEqAnswer(v_answer_433_, v_answer_442_);
if (v___x_451_ == 0)
{
return v___x_451_;
}
else
{
uint8_t v___x_452_; 
v___x_452_ = lean_nat_dec_eq(v_timer_434_, v_timer_443_);
if (v___x_452_ == 0)
{
return v___x_452_;
}
else
{
uint8_t v___x_453_; 
v___x_453_ = lean_nat_dec_eq(v_children_435_, v_children_444_);
if (v___x_453_ == 0)
{
return v___x_453_;
}
else
{
uint8_t v___x_454_; 
v___x_454_ = lean_nat_dec_eq(v_errorcount_436_, v_errorcount_445_);
if (v___x_454_ == 0)
{
return v___x_454_;
}
else
{
uint8_t v___x_455_; 
v___x_455_ = lean_nat_dec_eq(v_delaytimer_437_, v_delaytimer_446_);
return v___x_455_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqAgentState_decEq___redArg___boxed(lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = lp_SSExactMajority_SSEM_instDecidableEqAgentState_decEq___redArg(v_x_456_, v_x_457_);
lean_dec_ref(v_x_457_);
lean_dec_ref(v_x_456_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqAgentState_decEq(lean_object* v_n_460_, lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
uint8_t v___x_463_; 
v___x_463_ = lp_SSExactMajority_SSEM_instDecidableEqAgentState_decEq___redArg(v_x_461_, v_x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqAgentState_decEq___boxed(lean_object* v_n_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
uint8_t v_res_467_; lean_object* v_r_468_; 
v_res_467_ = lp_SSExactMajority_SSEM_instDecidableEqAgentState_decEq(v_n_464_, v_x_465_, v_x_466_);
lean_dec_ref(v_x_466_);
lean_dec_ref(v_x_465_);
lean_dec(v_n_464_);
v_r_468_ = lean_box(v_res_467_);
return v_r_468_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqAgentState___redArg(lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
uint8_t v___x_471_; 
v___x_471_ = lp_SSExactMajority_SSEM_instDecidableEqAgentState_decEq___redArg(v_x_469_, v_x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqAgentState___redArg___boxed(lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
uint8_t v_res_474_; lean_object* v_r_475_; 
v_res_474_ = lp_SSExactMajority_SSEM_instDecidableEqAgentState___redArg(v_x_472_, v_x_473_);
lean_dec_ref(v_x_473_);
lean_dec_ref(v_x_472_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableEqAgentState(lean_object* v_n_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
uint8_t v___x_479_; 
v___x_479_ = lp_SSExactMajority_SSEM_instDecidableEqAgentState_decEq___redArg(v_x_477_, v_x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableEqAgentState___boxed(lean_object* v_n_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
uint8_t v_res_483_; lean_object* v_r_484_; 
v_res_483_ = lp_SSExactMajority_SSEM_instDecidableEqAgentState(v_n_480_, v_x_481_, v_x_482_);
lean_dec_ref(v_x_482_);
lean_dec_ref(v_x_481_);
lean_dec(v_n_480_);
v_r_484_ = lean_box(v_res_483_);
return v_r_484_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_unsigned_to_nat(8u);
v___x_499_ = lean_nat_to_int(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_unsigned_to_nat(10u);
v___x_510_ = lean_nat_to_int(v___x_509_);
return v___x_510_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(14u);
v___x_515_ = lean_nat_to_int(v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(9u);
v___x_523_ = lean_nat_to_int(v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_unsigned_to_nat(12u);
v___x_528_ = lean_nat_to_int(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__31(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__0));
v___x_537_ = lean_string_length(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__31, &lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__31_once, _init_lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__31);
v___x_539_ = lean_nat_to_int(v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg(lean_object* v_x_544_){
_start:
{
uint8_t v_role_545_; lean_object* v_rank_546_; uint8_t v_leader_547_; lean_object* v_resetcount_548_; uint8_t v_answer_549_; lean_object* v_timer_550_; lean_object* v_children_551_; lean_object* v_errorcount_552_; lean_object* v_delaytimer_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_role_545_ = lean_ctor_get_uint8(v_x_544_, sizeof(void*)*6);
v_rank_546_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_rank_546_);
v_leader_547_ = lean_ctor_get_uint8(v_x_544_, sizeof(void*)*6 + 1);
v_resetcount_548_ = lean_ctor_get(v_x_544_, 1);
lean_inc(v_resetcount_548_);
v_answer_549_ = lean_ctor_get_uint8(v_x_544_, sizeof(void*)*6 + 2);
v_timer_550_ = lean_ctor_get(v_x_544_, 2);
lean_inc(v_timer_550_);
v_children_551_ = lean_ctor_get(v_x_544_, 3);
lean_inc(v_children_551_);
v_errorcount_552_ = lean_ctor_get(v_x_544_, 4);
lean_inc(v_errorcount_552_);
v_delaytimer_553_ = lean_ctor_get(v_x_544_, 5);
lean_inc(v_delaytimer_553_);
lean_dec_ref(v_x_544_);
v___x_554_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__5));
v___x_555_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__6));
v___x_556_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__7, &lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__7_once, _init_lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__7);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lp_SSExactMajority_SSEM_instReprRole_repr(v_role_545_, v___x_557_);
v___x_559_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_556_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = 0;
v___x_561_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*1, v___x_560_);
v___x_562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_555_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__9));
v___x_564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = lean_box(1);
v___x_566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__11));
v___x_568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_566_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_554_);
v___x_570_ = l_Nat_reprFast(v_rank_546_);
v___x_571_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
v___x_572_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_556_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set_uint8(v___x_573_, sizeof(void*)*1, v___x_560_);
v___x_574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_569_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___x_563_);
v___x_576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___x_565_);
v___x_577_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__13));
v___x_578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v___x_554_);
v___x_580_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__14, &lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__14_once, _init_lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__14);
v___x_581_ = lp_SSExactMajority_SSEM_instReprLeader_repr(v_leader_547_, v___x_557_);
v___x_582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*1, v___x_560_);
v___x_584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_579_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___x_563_);
v___x_586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_565_);
v___x_587_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__16));
v___x_588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v___x_554_);
v___x_590_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__17, &lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__17_once, _init_lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__17);
v___x_591_ = l_Nat_reprFast(v_resetcount_548_);
v___x_592_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
v___x_593_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_590_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set_uint8(v___x_594_, sizeof(void*)*1, v___x_560_);
v___x_595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_589_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_563_);
v___x_597_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_565_);
v___x_598_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__19));
v___x_599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_554_);
v___x_601_ = lp_SSExactMajority_SSEM_instReprAnswer_repr(v_answer_549_, v___x_557_);
v___x_602_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_580_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set_uint8(v___x_603_, sizeof(void*)*1, v___x_560_);
v___x_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_600_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_563_);
v___x_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_565_);
v___x_607_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__21));
v___x_608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___x_554_);
v___x_610_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__22, &lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__22_once, _init_lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__22);
v___x_611_ = l_Nat_reprFast(v_timer_550_);
v___x_612_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
v___x_613_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_610_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*1, v___x_560_);
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_609_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v___x_563_);
v___x_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_565_);
v___x_618_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__24));
v___x_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_554_);
v___x_621_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__25, &lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__25_once, _init_lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__25);
v___x_622_ = l_Nat_reprFast(v_children_551_);
v___x_623_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
v___x_624_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_621_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*1, v___x_560_);
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_620_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_563_);
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_565_);
v___x_629_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__27));
v___x_630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___x_554_);
v___x_632_ = l_Nat_reprFast(v_errorcount_552_);
v___x_633_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___x_634_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_590_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*1, v___x_560_);
v___x_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_631_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_563_);
v___x_638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_565_);
v___x_639_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__29));
v___x_640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v___x_554_);
v___x_642_ = l_Nat_reprFast(v_delaytimer_553_);
v___x_643_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
v___x_644_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_590_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set_uint8(v___x_645_, sizeof(void*)*1, v___x_560_);
v___x_646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_641_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = lean_obj_once(&lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__32, &lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__32_once, _init_lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__32);
v___x_648_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__33));
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v___x_646_);
v___x_650_ = ((lean_object*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg___closed__34));
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_647_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set_uint8(v___x_653_, sizeof(void*)*1, v___x_560_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr(lean_object* v_n_654_, lean_object* v_x_655_, lean_object* v_prec_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = lp_SSExactMajority_SSEM_instReprAgentState_repr___redArg(v_x_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprAgentState_repr___boxed(lean_object* v_n_658_, lean_object* v_x_659_, lean_object* v_prec_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = lp_SSExactMajority_SSEM_instReprAgentState_repr(v_n_658_, v_x_659_, v_prec_660_);
lean_dec(v_prec_660_);
lean_dec(v_n_658_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instReprAgentState(lean_object* v_n_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_instReprAgentState_repr___boxed), 3, 1);
lean_closure_set(v___x_663_, 0, v_n_662_);
return v___x_663_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_agentOutput___redArg(lean_object* v_s_664_){
_start:
{
uint8_t v_answer_665_; uint8_t v___x_666_; 
v_answer_665_ = lean_ctor_get_uint8(v_s_664_, sizeof(void*)*6 + 2);
v___x_666_ = lp_SSExactMajority_SSEM_Answer_toOutput(v_answer_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_agentOutput___redArg___boxed(lean_object* v_s_667_){
_start:
{
uint8_t v_res_668_; lean_object* v_r_669_; 
v_res_668_ = lp_SSExactMajority_SSEM_agentOutput___redArg(v_s_667_);
lean_dec_ref(v_s_667_);
v_r_669_ = lean_box(v_res_668_);
return v_r_669_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_agentOutput(lean_object* v_n_670_, lean_object* v_s_671_){
_start:
{
uint8_t v___x_672_; 
v___x_672_ = lp_SSExactMajority_SSEM_agentOutput___redArg(v_s_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_agentOutput___boxed(lean_object* v_n_673_, lean_object* v_s_674_){
_start:
{
uint8_t v_res_675_; lean_object* v_r_676_; 
v_res_675_ = lp_SSExactMajority_SSEM_agentOutput(v_n_673_, v_s_674_);
lean_dec_ref(v_s_674_);
lean_dec(v_n_673_);
v_r_676_ = lean_box(v_res_675_);
return v_r_676_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Protocol(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_State(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Defs_Protocol(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
