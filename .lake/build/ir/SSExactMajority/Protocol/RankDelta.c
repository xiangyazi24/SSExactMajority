// Lean compiler output
// Module: SSExactMajority.Protocol.RankDelta
// Imports: public import Init public import SSExactMajority.Protocol.State public import SSExactMajority.Convergence.Silent
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
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetOSSR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_propagateReset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqRole(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_propagateReset___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetOSSR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqLeader(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_propagateReset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetOSSR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetOSSR___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 3);
lean_dec(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = 1;
x_8 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_2, 3, x_8);
lean_ctor_set(x_2, 0, x_8);
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_7);
return x_2;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 2);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_dec(x_2);
x_14 = 1;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_12);
lean_ctor_set(x_16, 5, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*6, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*6 + 1, x_3);
lean_ctor_set_uint8(x_16, sizeof(void*)*6 + 2, x_10);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_2, 4);
lean_dec(x_18);
x_19 = 2;
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 2);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
x_25 = lean_ctor_get(x_2, 5);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_26 = 2;
x_27 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_1);
lean_ctor_set(x_27, 5, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*6, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*6 + 1, x_3);
lean_ctor_set_uint8(x_27, sizeof(void*)*6 + 2, x_22);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetOSSR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_SSExactMajority_SSEM_resetOSSR___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetOSSR___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_SSExactMajority_SSEM_resetOSSR(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_3, 5);
x_15 = 0;
x_16 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_6, x_15);
if (x_16 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_24; 
x_17 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_9, x_17);
if (x_24 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_25; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_7);
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_3, 5);
lean_dec(x_26);
x_27 = lean_ctor_get(x_3, 4);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 3);
lean_dec(x_28);
x_29 = lean_ctor_get(x_3, 2);
lean_dec(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_3, 0);
lean_dec(x_31);
x_32 = lean_nat_dec_lt(x_17, x_4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_sub(x_14, x_33);
lean_dec(x_14);
lean_inc(x_34);
lean_ctor_set(x_3, 5, x_34);
x_18 = x_3;
x_19 = x_34;
goto block_23;
}
else
{
lean_dec(x_14);
lean_inc(x_2);
lean_ctor_set(x_3, 5, x_2);
x_18 = x_3;
x_19 = x_2;
goto block_23;
}
}
else
{
uint8_t x_35; 
lean_dec(x_3);
x_35 = lean_nat_dec_lt(x_17, x_4);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_sub(x_14, x_36);
lean_dec(x_14);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_38, 0, x_7);
lean_ctor_set(x_38, 1, x_9);
lean_ctor_set(x_38, 2, x_11);
lean_ctor_set(x_38, 3, x_12);
lean_ctor_set(x_38, 4, x_13);
lean_ctor_set(x_38, 5, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*6, x_6);
lean_ctor_set_uint8(x_38, sizeof(void*)*6 + 1, x_8);
lean_ctor_set_uint8(x_38, sizeof(void*)*6 + 2, x_10);
x_18 = x_38;
x_19 = x_37;
goto block_23;
}
else
{
lean_object* x_39; 
lean_dec(x_14);
lean_inc(x_2);
x_39 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_39, 0, x_7);
lean_ctor_set(x_39, 1, x_9);
lean_ctor_set(x_39, 2, x_11);
lean_ctor_set(x_39, 3, x_12);
lean_ctor_set(x_39, 4, x_13);
lean_ctor_set(x_39, 5, x_2);
lean_ctor_set_uint8(x_39, sizeof(void*)*6, x_6);
lean_ctor_set_uint8(x_39, sizeof(void*)*6 + 1, x_8);
lean_ctor_set_uint8(x_39, sizeof(void*)*6 + 2, x_10);
x_18 = x_39;
x_19 = x_2;
goto block_23;
}
}
}
block_23:
{
uint8_t x_20; 
x_20 = lean_nat_dec_eq(x_19, x_17);
lean_dec(x_19);
if (x_20 == 0)
{
if (x_5 == 0)
{
lean_object* x_21; 
x_21 = lp_SSExactMajority_SSEM_resetOSSR___redArg(x_1, x_18);
return x_21;
}
else
{
lean_dec(x_1);
return x_18;
}
}
else
{
lean_object* x_22; 
x_22 = lp_SSExactMajority_SSEM_resetOSSR___redArg(x_1, x_18);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_SSExactMajority_SSEM_processAgent___redArg(x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
x_9 = lp_SSExactMajority_SSEM_processAgent(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
x_7 = lp_SSExactMajority_SSEM_processAgent___redArg(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_propagateReset___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_47; uint8_t x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; 
x_75 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_76 = lean_ctor_get(x_3, 0);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_78 = lean_ctor_get(x_3, 1);
x_79 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_80 = lean_ctor_get(x_3, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_3, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_3, 4);
lean_inc(x_82);
x_83 = lean_ctor_get(x_3, 5);
x_84 = 0;
x_85 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_75, x_84);
if (x_85 == 0)
{
goto block_106;
}
else
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_nat_dec_lt(x_107, x_78);
if (x_108 == 0)
{
goto block_106;
}
else
{
uint8_t x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_109 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_110 = lean_ctor_get(x_4, 0);
x_111 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_112 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 2);
x_113 = lean_ctor_get(x_4, 2);
x_114 = lean_ctor_get(x_4, 3);
x_115 = lean_ctor_get(x_4, 4);
x_116 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_109, x_84);
if (x_116 == 0)
{
if (x_108 == 0)
{
goto block_106;
}
else
{
uint8_t x_117; 
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_110);
lean_inc(x_83);
lean_inc(x_78);
x_117 = !lean_is_exclusive(x_4);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_4, 5);
lean_dec(x_118);
x_119 = lean_ctor_get(x_4, 4);
lean_dec(x_119);
x_120 = lean_ctor_get(x_4, 3);
lean_dec(x_120);
x_121 = lean_ctor_get(x_4, 2);
lean_dec(x_121);
x_122 = lean_ctor_get(x_4, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_4, 0);
lean_dec(x_123);
lean_inc(x_2);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_110);
lean_ctor_set(x_4, 5, x_2);
lean_ctor_set(x_4, 1, x_107);
lean_ctor_set_uint8(x_4, sizeof(void*)*6, x_84);
lean_inc(x_2);
x_47 = x_3;
x_48 = x_75;
x_49 = x_76;
x_50 = x_77;
x_51 = x_78;
x_52 = x_79;
x_53 = x_80;
x_54 = x_81;
x_55 = x_82;
x_56 = x_83;
x_57 = x_4;
x_58 = x_84;
x_59 = x_110;
x_60 = x_111;
x_61 = x_107;
x_62 = x_112;
x_63 = x_113;
x_64 = x_114;
x_65 = x_115;
x_66 = x_2;
goto block_74;
}
else
{
lean_object* x_124; 
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_110);
x_124 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_124, 0, x_110);
lean_ctor_set(x_124, 1, x_107);
lean_ctor_set(x_124, 2, x_113);
lean_ctor_set(x_124, 3, x_114);
lean_ctor_set(x_124, 4, x_115);
lean_ctor_set(x_124, 5, x_2);
lean_ctor_set_uint8(x_124, sizeof(void*)*6, x_84);
lean_ctor_set_uint8(x_124, sizeof(void*)*6 + 1, x_111);
lean_ctor_set_uint8(x_124, sizeof(void*)*6 + 2, x_112);
lean_inc(x_2);
x_47 = x_3;
x_48 = x_75;
x_49 = x_76;
x_50 = x_77;
x_51 = x_78;
x_52 = x_79;
x_53 = x_80;
x_54 = x_81;
x_55 = x_82;
x_56 = x_83;
x_57 = x_124;
x_58 = x_84;
x_59 = x_110;
x_60 = x_111;
x_61 = x_107;
x_62 = x_112;
x_63 = x_113;
x_64 = x_114;
x_65 = x_115;
x_66 = x_2;
goto block_74;
}
}
}
else
{
goto block_106;
}
}
}
block_17:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = 0;
x_12 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_10, x_11);
x_13 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_8, x_11);
lean_inc(x_2);
lean_inc(x_1);
x_14 = lp_SSExactMajority_SSEM_processAgent___redArg(x_1, x_2, x_7, x_5, x_12);
lean_dec(x_5);
x_15 = lp_SSExactMajority_SSEM_processAgent___redArg(x_1, x_2, x_9, x_6, x_13);
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
lean_inc(x_36);
x_37 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_21);
lean_ctor_set(x_37, 4, x_20);
lean_ctor_set(x_37, 5, x_29);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_23);
lean_ctor_set_uint8(x_37, sizeof(void*)*6 + 1, x_27);
lean_ctor_set_uint8(x_37, sizeof(void*)*6 + 2, x_28);
x_38 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_32);
lean_ctor_set(x_38, 3, x_18);
lean_ctor_set(x_38, 4, x_35);
lean_ctor_set(x_38, 5, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*6, x_31);
lean_ctor_set_uint8(x_38, sizeof(void*)*6 + 1, x_24);
lean_ctor_set_uint8(x_38, sizeof(void*)*6 + 2, x_25);
x_5 = x_19;
x_6 = x_22;
x_7 = x_37;
x_8 = x_23;
x_9 = x_38;
x_10 = x_31;
goto block_17;
}
block_46:
{
uint8_t x_45; 
x_45 = lean_ctor_get_uint8(x_42, sizeof(void*)*6);
x_5 = x_40;
x_6 = x_41;
x_7 = x_42;
x_8 = x_45;
x_9 = x_43;
x_10 = x_44;
goto block_17;
}
block_74:
{
uint8_t x_67; uint8_t x_68; 
x_67 = 0;
x_68 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_48, x_67);
if (x_68 == 0)
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_49);
x_40 = x_51;
x_41 = x_61;
x_42 = x_47;
x_43 = x_57;
x_44 = x_58;
goto block_46;
}
else
{
uint8_t x_69; 
x_69 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_58, x_67);
if (x_69 == 0)
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_49);
x_40 = x_51;
x_41 = x_61;
x_42 = x_47;
x_43 = x_57;
x_44 = x_58;
goto block_46;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec_ref(x_57);
lean_dec_ref(x_47);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_51, x_70);
x_72 = lean_nat_sub(x_61, x_70);
x_73 = lean_nat_dec_le(x_71, x_72);
if (x_73 == 0)
{
lean_dec(x_72);
x_18 = x_64;
x_19 = x_51;
x_20 = x_55;
x_21 = x_54;
x_22 = x_61;
x_23 = x_48;
x_24 = x_60;
x_25 = x_62;
x_26 = x_59;
x_27 = x_50;
x_28 = x_52;
x_29 = x_56;
x_30 = x_53;
x_31 = x_58;
x_32 = x_63;
x_33 = x_49;
x_34 = x_66;
x_35 = x_65;
x_36 = x_71;
goto block_39;
}
else
{
lean_dec(x_71);
x_18 = x_64;
x_19 = x_51;
x_20 = x_55;
x_21 = x_54;
x_22 = x_61;
x_23 = x_48;
x_24 = x_60;
x_25 = x_62;
x_26 = x_59;
x_27 = x_50;
x_28 = x_52;
x_29 = x_56;
x_30 = x_53;
x_31 = x_58;
x_32 = x_63;
x_33 = x_49;
x_34 = x_66;
x_35 = x_65;
x_36 = x_72;
goto block_39;
}
}
}
}
block_106:
{
uint8_t x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_86 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_87 = lean_ctor_get(x_4, 0);
lean_inc(x_87);
x_88 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_89 = lean_ctor_get(x_4, 1);
lean_inc(x_89);
x_90 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 2);
x_91 = lean_ctor_get(x_4, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_4, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_4, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_4, 5);
lean_inc(x_94);
x_95 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_86, x_84);
if (x_95 == 0)
{
lean_inc(x_83);
lean_inc(x_78);
x_47 = x_3;
x_48 = x_75;
x_49 = x_76;
x_50 = x_77;
x_51 = x_78;
x_52 = x_79;
x_53 = x_80;
x_54 = x_81;
x_55 = x_82;
x_56 = x_83;
x_57 = x_4;
x_58 = x_86;
x_59 = x_87;
x_60 = x_88;
x_61 = x_89;
x_62 = x_90;
x_63 = x_91;
x_64 = x_92;
x_65 = x_93;
x_66 = x_94;
goto block_74;
}
else
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_nat_dec_lt(x_96, x_89);
if (x_97 == 0)
{
lean_inc(x_83);
lean_inc(x_78);
x_47 = x_3;
x_48 = x_75;
x_49 = x_76;
x_50 = x_77;
x_51 = x_78;
x_52 = x_79;
x_53 = x_80;
x_54 = x_81;
x_55 = x_82;
x_56 = x_83;
x_57 = x_4;
x_58 = x_86;
x_59 = x_87;
x_60 = x_88;
x_61 = x_89;
x_62 = x_90;
x_63 = x_91;
x_64 = x_92;
x_65 = x_93;
x_66 = x_94;
goto block_74;
}
else
{
if (x_85 == 0)
{
if (x_97 == 0)
{
lean_inc(x_83);
lean_inc(x_78);
x_47 = x_3;
x_48 = x_75;
x_49 = x_76;
x_50 = x_77;
x_51 = x_78;
x_52 = x_79;
x_53 = x_80;
x_54 = x_81;
x_55 = x_82;
x_56 = x_83;
x_57 = x_4;
x_58 = x_86;
x_59 = x_87;
x_60 = x_88;
x_61 = x_89;
x_62 = x_90;
x_63 = x_91;
x_64 = x_92;
x_65 = x_93;
x_66 = x_94;
goto block_74;
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_3);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_3, 5);
lean_dec(x_99);
x_100 = lean_ctor_get(x_3, 4);
lean_dec(x_100);
x_101 = lean_ctor_get(x_3, 3);
lean_dec(x_101);
x_102 = lean_ctor_get(x_3, 2);
lean_dec(x_102);
x_103 = lean_ctor_get(x_3, 1);
lean_dec(x_103);
x_104 = lean_ctor_get(x_3, 0);
lean_dec(x_104);
lean_inc(x_2);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_76);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 1, x_96);
lean_ctor_set_uint8(x_3, sizeof(void*)*6, x_84);
lean_inc(x_2);
x_47 = x_3;
x_48 = x_84;
x_49 = x_76;
x_50 = x_77;
x_51 = x_96;
x_52 = x_79;
x_53 = x_80;
x_54 = x_81;
x_55 = x_82;
x_56 = x_2;
x_57 = x_4;
x_58 = x_86;
x_59 = x_87;
x_60 = x_88;
x_61 = x_89;
x_62 = x_90;
x_63 = x_91;
x_64 = x_92;
x_65 = x_93;
x_66 = x_94;
goto block_74;
}
else
{
lean_object* x_105; 
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_76);
x_105 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_105, 0, x_76);
lean_ctor_set(x_105, 1, x_96);
lean_ctor_set(x_105, 2, x_80);
lean_ctor_set(x_105, 3, x_81);
lean_ctor_set(x_105, 4, x_82);
lean_ctor_set(x_105, 5, x_2);
lean_ctor_set_uint8(x_105, sizeof(void*)*6, x_84);
lean_ctor_set_uint8(x_105, sizeof(void*)*6 + 1, x_77);
lean_ctor_set_uint8(x_105, sizeof(void*)*6 + 2, x_79);
lean_inc(x_2);
x_47 = x_105;
x_48 = x_84;
x_49 = x_76;
x_50 = x_77;
x_51 = x_96;
x_52 = x_79;
x_53 = x_80;
x_54 = x_81;
x_55 = x_82;
x_56 = x_2;
x_57 = x_4;
x_58 = x_86;
x_59 = x_87;
x_60 = x_88;
x_61 = x_89;
x_62 = x_90;
x_63 = x_91;
x_64 = x_92;
x_65 = x_93;
x_66 = x_94;
goto block_74;
}
}
}
else
{
lean_inc(x_83);
lean_inc(x_78);
x_47 = x_3;
x_48 = x_75;
x_49 = x_76;
x_50 = x_77;
x_51 = x_78;
x_52 = x_79;
x_53 = x_80;
x_54 = x_81;
x_55 = x_82;
x_56 = x_83;
x_57 = x_4;
x_58 = x_86;
x_59 = x_87;
x_60 = x_88;
x_61 = x_89;
x_62 = x_90;
x_63 = x_91;
x_64 = x_92;
x_65 = x_93;
x_66 = x_94;
goto block_74;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_propagateReset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_SSExactMajority_SSEM_propagateReset___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_propagateReset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_SSExactMajority_SSEM_propagateReset(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_117; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 1);
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 2);
x_14 = lean_ctor_get(x_6, 2);
x_15 = lean_ctor_get(x_6, 3);
x_16 = lean_ctor_get(x_6, 4);
x_17 = lean_ctor_get(x_6, 5);
x_18 = 0;
x_117 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_9, x_18);
if (x_117 == 0)
{
uint8_t x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; lean_object* x_129; uint8_t x_173; 
x_118 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
x_119 = lean_ctor_get(x_7, 0);
x_120 = lean_ctor_get_uint8(x_7, sizeof(void*)*6 + 1);
x_121 = lean_ctor_get(x_7, 1);
x_122 = lean_ctor_get_uint8(x_7, sizeof(void*)*6 + 2);
x_123 = lean_ctor_get(x_7, 2);
x_124 = lean_ctor_get(x_7, 3);
x_125 = lean_ctor_get(x_7, 4);
x_126 = lean_ctor_get(x_7, 5);
x_173 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_118, x_18);
if (x_173 == 0)
{
uint8_t x_174; uint8_t x_213; 
lean_dec(x_4);
lean_dec(x_3);
x_174 = 1;
x_213 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_9, x_174);
if (x_213 == 0)
{
goto block_250;
}
else
{
uint8_t x_251; 
x_251 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_118, x_174);
if (x_251 == 0)
{
goto block_250;
}
else
{
uint8_t x_252; 
x_252 = lean_nat_dec_eq(x_10, x_119);
if (x_252 == 0)
{
goto block_250;
}
else
{
uint8_t x_253; 
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_119);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_10);
lean_dec(x_8);
x_253 = !lean_is_exclusive(x_6);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_254 = lean_ctor_get(x_6, 5);
lean_dec(x_254);
x_255 = lean_ctor_get(x_6, 4);
lean_dec(x_255);
x_256 = lean_ctor_get(x_6, 3);
lean_dec(x_256);
x_257 = lean_ctor_get(x_6, 2);
lean_dec(x_257);
x_258 = lean_ctor_get(x_6, 1);
lean_dec(x_258);
x_259 = lean_ctor_get(x_6, 0);
lean_dec(x_259);
x_260 = !lean_is_exclusive(x_7);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; 
x_261 = lean_ctor_get(x_7, 5);
lean_dec(x_261);
x_262 = lean_ctor_get(x_7, 4);
lean_dec(x_262);
x_263 = lean_ctor_get(x_7, 3);
lean_dec(x_263);
x_264 = lean_ctor_get(x_7, 2);
lean_dec(x_264);
x_265 = lean_ctor_get(x_7, 1);
lean_dec(x_265);
x_266 = lean_ctor_get(x_7, 0);
lean_dec(x_266);
x_267 = 0;
lean_inc(x_2);
lean_ctor_set(x_7, 5, x_17);
lean_ctor_set(x_7, 4, x_16);
lean_ctor_set(x_7, 3, x_15);
lean_ctor_set(x_7, 2, x_14);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*6, x_18);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 1, x_267);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 2, x_13);
lean_ctor_set(x_6, 5, x_126);
lean_ctor_set(x_6, 4, x_125);
lean_ctor_set(x_6, 3, x_124);
lean_ctor_set(x_6, 2, x_123);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_119);
lean_ctor_set_uint8(x_6, sizeof(void*)*6, x_18);
lean_ctor_set_uint8(x_6, sizeof(void*)*6 + 1, x_267);
lean_ctor_set_uint8(x_6, sizeof(void*)*6 + 2, x_122);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_7);
lean_ctor_set(x_268, 1, x_6);
return x_268;
}
else
{
uint8_t x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_7);
x_269 = 0;
lean_inc(x_2);
x_270 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_270, 0, x_10);
lean_ctor_set(x_270, 1, x_2);
lean_ctor_set(x_270, 2, x_14);
lean_ctor_set(x_270, 3, x_15);
lean_ctor_set(x_270, 4, x_16);
lean_ctor_set(x_270, 5, x_17);
lean_ctor_set_uint8(x_270, sizeof(void*)*6, x_18);
lean_ctor_set_uint8(x_270, sizeof(void*)*6 + 1, x_269);
lean_ctor_set_uint8(x_270, sizeof(void*)*6 + 2, x_13);
lean_ctor_set(x_6, 5, x_126);
lean_ctor_set(x_6, 4, x_125);
lean_ctor_set(x_6, 3, x_124);
lean_ctor_set(x_6, 2, x_123);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_119);
lean_ctor_set_uint8(x_6, sizeof(void*)*6, x_18);
lean_ctor_set_uint8(x_6, sizeof(void*)*6 + 1, x_269);
lean_ctor_set_uint8(x_6, sizeof(void*)*6 + 2, x_122);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_6);
return x_271;
}
}
else
{
lean_object* x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_6);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 x_272 = x_7;
} else {
 lean_dec_ref(x_7);
 x_272 = lean_box(0);
}
x_273 = 0;
lean_inc(x_2);
if (lean_is_scalar(x_272)) {
 x_274 = lean_alloc_ctor(0, 6, 3);
} else {
 x_274 = x_272;
}
lean_ctor_set(x_274, 0, x_10);
lean_ctor_set(x_274, 1, x_2);
lean_ctor_set(x_274, 2, x_14);
lean_ctor_set(x_274, 3, x_15);
lean_ctor_set(x_274, 4, x_16);
lean_ctor_set(x_274, 5, x_17);
lean_ctor_set_uint8(x_274, sizeof(void*)*6, x_18);
lean_ctor_set_uint8(x_274, sizeof(void*)*6 + 1, x_273);
lean_ctor_set_uint8(x_274, sizeof(void*)*6 + 2, x_13);
x_275 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_275, 0, x_119);
lean_ctor_set(x_275, 1, x_2);
lean_ctor_set(x_275, 2, x_123);
lean_ctor_set(x_275, 3, x_124);
lean_ctor_set(x_275, 4, x_125);
lean_ctor_set(x_275, 5, x_126);
lean_ctor_set_uint8(x_275, sizeof(void*)*6, x_18);
lean_ctor_set_uint8(x_275, sizeof(void*)*6 + 1, x_273);
lean_ctor_set_uint8(x_275, sizeof(void*)*6 + 2, x_122);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
}
block_212:
{
uint8_t x_175; 
x_175 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_118, x_174);
if (x_175 == 0)
{
goto block_172;
}
else
{
uint8_t x_176; uint8_t x_177; 
x_176 = 2;
x_177 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_9, x_176);
if (x_177 == 0)
{
goto block_172;
}
else
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_unsigned_to_nat(2u);
x_179 = lean_nat_dec_lt(x_124, x_178);
if (x_179 == 0)
{
goto block_172;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_180 = lean_nat_mul(x_178, x_119);
x_181 = lean_nat_add(x_180, x_124);
lean_dec(x_180);
x_182 = lean_unsigned_to_nat(1u);
x_183 = lean_nat_add(x_181, x_182);
lean_dec(x_181);
x_184 = lean_nat_dec_lt(x_183, x_1);
if (x_184 == 0)
{
lean_dec(x_183);
goto block_172;
}
else
{
uint8_t x_185; 
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_121);
lean_inc(x_119);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_12);
lean_dec(x_8);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_6);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_186 = lean_ctor_get(x_6, 5);
lean_dec(x_186);
x_187 = lean_ctor_get(x_6, 4);
lean_dec(x_187);
x_188 = lean_ctor_get(x_6, 3);
lean_dec(x_188);
x_189 = lean_ctor_get(x_6, 2);
lean_dec(x_189);
x_190 = lean_ctor_get(x_6, 1);
lean_dec(x_190);
x_191 = lean_ctor_get(x_6, 0);
lean_dec(x_191);
x_192 = !lean_is_exclusive(x_7);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_193 = lean_ctor_get(x_7, 5);
lean_dec(x_193);
x_194 = lean_ctor_get(x_7, 4);
lean_dec(x_194);
x_195 = lean_ctor_get(x_7, 3);
lean_dec(x_195);
x_196 = lean_ctor_get(x_7, 2);
lean_dec(x_196);
x_197 = lean_ctor_get(x_7, 1);
lean_dec(x_197);
x_198 = lean_ctor_get(x_7, 0);
lean_dec(x_198);
x_199 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_7, 5, x_17);
lean_ctor_set(x_7, 4, x_16);
lean_ctor_set(x_7, 3, x_199);
lean_ctor_set(x_7, 2, x_14);
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_183);
lean_ctor_set_uint8(x_7, sizeof(void*)*6, x_174);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 1, x_11);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 2, x_13);
x_200 = lean_nat_add(x_124, x_182);
lean_dec(x_124);
lean_ctor_set(x_6, 5, x_126);
lean_ctor_set(x_6, 4, x_125);
lean_ctor_set(x_6, 3, x_200);
lean_ctor_set(x_6, 2, x_123);
lean_ctor_set(x_6, 1, x_121);
lean_ctor_set(x_6, 0, x_119);
lean_ctor_set_uint8(x_6, sizeof(void*)*6, x_118);
lean_ctor_set_uint8(x_6, sizeof(void*)*6 + 1, x_120);
lean_ctor_set_uint8(x_6, sizeof(void*)*6 + 2, x_122);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_7);
lean_ctor_set(x_201, 1, x_6);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_7);
x_202 = lean_unsigned_to_nat(0u);
x_203 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_203, 0, x_183);
lean_ctor_set(x_203, 1, x_12);
lean_ctor_set(x_203, 2, x_14);
lean_ctor_set(x_203, 3, x_202);
lean_ctor_set(x_203, 4, x_16);
lean_ctor_set(x_203, 5, x_17);
lean_ctor_set_uint8(x_203, sizeof(void*)*6, x_174);
lean_ctor_set_uint8(x_203, sizeof(void*)*6 + 1, x_11);
lean_ctor_set_uint8(x_203, sizeof(void*)*6 + 2, x_13);
x_204 = lean_nat_add(x_124, x_182);
lean_dec(x_124);
lean_ctor_set(x_6, 5, x_126);
lean_ctor_set(x_6, 4, x_125);
lean_ctor_set(x_6, 3, x_204);
lean_ctor_set(x_6, 2, x_123);
lean_ctor_set(x_6, 1, x_121);
lean_ctor_set(x_6, 0, x_119);
lean_ctor_set_uint8(x_6, sizeof(void*)*6, x_118);
lean_ctor_set_uint8(x_6, sizeof(void*)*6 + 1, x_120);
lean_ctor_set_uint8(x_6, sizeof(void*)*6 + 2, x_122);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_6);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_6);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 x_206 = x_7;
} else {
 lean_dec_ref(x_7);
 x_206 = lean_box(0);
}
x_207 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 6, 3);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_183);
lean_ctor_set(x_208, 1, x_12);
lean_ctor_set(x_208, 2, x_14);
lean_ctor_set(x_208, 3, x_207);
lean_ctor_set(x_208, 4, x_16);
lean_ctor_set(x_208, 5, x_17);
lean_ctor_set_uint8(x_208, sizeof(void*)*6, x_174);
lean_ctor_set_uint8(x_208, sizeof(void*)*6 + 1, x_11);
lean_ctor_set_uint8(x_208, sizeof(void*)*6 + 2, x_13);
x_209 = lean_nat_add(x_124, x_182);
lean_dec(x_124);
x_210 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_210, 0, x_119);
lean_ctor_set(x_210, 1, x_121);
lean_ctor_set(x_210, 2, x_123);
lean_ctor_set(x_210, 3, x_209);
lean_ctor_set(x_210, 4, x_125);
lean_ctor_set(x_210, 5, x_126);
lean_ctor_set_uint8(x_210, sizeof(void*)*6, x_118);
lean_ctor_set_uint8(x_210, sizeof(void*)*6 + 1, x_120);
lean_ctor_set_uint8(x_210, sizeof(void*)*6 + 2, x_122);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
}
}
}
block_250:
{
if (x_213 == 0)
{
goto block_212;
}
else
{
uint8_t x_214; uint8_t x_215; 
x_214 = 2;
x_215 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_118, x_214);
if (x_215 == 0)
{
goto block_212;
}
else
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_unsigned_to_nat(2u);
x_217 = lean_nat_dec_lt(x_15, x_216);
if (x_217 == 0)
{
goto block_212;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_218 = lean_nat_mul(x_216, x_10);
x_219 = lean_nat_add(x_218, x_15);
lean_dec(x_218);
x_220 = lean_unsigned_to_nat(1u);
x_221 = lean_nat_add(x_219, x_220);
lean_dec(x_219);
x_222 = lean_nat_dec_lt(x_221, x_1);
if (x_222 == 0)
{
lean_dec(x_221);
goto block_212;
}
else
{
uint8_t x_223; 
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_123);
lean_inc(x_121);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_223 = !lean_is_exclusive(x_6);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_224 = lean_ctor_get(x_6, 5);
lean_dec(x_224);
x_225 = lean_ctor_get(x_6, 4);
lean_dec(x_225);
x_226 = lean_ctor_get(x_6, 3);
lean_dec(x_226);
x_227 = lean_ctor_get(x_6, 2);
lean_dec(x_227);
x_228 = lean_ctor_get(x_6, 1);
lean_dec(x_228);
x_229 = lean_ctor_get(x_6, 0);
lean_dec(x_229);
x_230 = !lean_is_exclusive(x_7);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_231 = lean_ctor_get(x_7, 5);
lean_dec(x_231);
x_232 = lean_ctor_get(x_7, 4);
lean_dec(x_232);
x_233 = lean_ctor_get(x_7, 3);
lean_dec(x_233);
x_234 = lean_ctor_get(x_7, 2);
lean_dec(x_234);
x_235 = lean_ctor_get(x_7, 1);
lean_dec(x_235);
x_236 = lean_ctor_get(x_7, 0);
lean_dec(x_236);
x_237 = lean_nat_add(x_15, x_220);
lean_dec(x_15);
lean_ctor_set(x_7, 5, x_17);
lean_ctor_set(x_7, 4, x_16);
lean_ctor_set(x_7, 3, x_237);
lean_ctor_set(x_7, 2, x_14);
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*6, x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 1, x_11);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 2, x_13);
x_238 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_6, 5, x_126);
lean_ctor_set(x_6, 4, x_125);
lean_ctor_set(x_6, 3, x_238);
lean_ctor_set(x_6, 2, x_123);
lean_ctor_set(x_6, 1, x_121);
lean_ctor_set(x_6, 0, x_221);
lean_ctor_set_uint8(x_6, sizeof(void*)*6, x_174);
lean_ctor_set_uint8(x_6, sizeof(void*)*6 + 1, x_120);
lean_ctor_set_uint8(x_6, sizeof(void*)*6 + 2, x_122);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_7);
lean_ctor_set(x_239, 1, x_6);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_7);
x_240 = lean_nat_add(x_15, x_220);
lean_dec(x_15);
x_241 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_241, 0, x_10);
lean_ctor_set(x_241, 1, x_12);
lean_ctor_set(x_241, 2, x_14);
lean_ctor_set(x_241, 3, x_240);
lean_ctor_set(x_241, 4, x_16);
lean_ctor_set(x_241, 5, x_17);
lean_ctor_set_uint8(x_241, sizeof(void*)*6, x_9);
lean_ctor_set_uint8(x_241, sizeof(void*)*6 + 1, x_11);
lean_ctor_set_uint8(x_241, sizeof(void*)*6 + 2, x_13);
x_242 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_6, 5, x_126);
lean_ctor_set(x_6, 4, x_125);
lean_ctor_set(x_6, 3, x_242);
lean_ctor_set(x_6, 2, x_123);
lean_ctor_set(x_6, 1, x_121);
lean_ctor_set(x_6, 0, x_221);
lean_ctor_set_uint8(x_6, sizeof(void*)*6, x_174);
lean_ctor_set_uint8(x_6, sizeof(void*)*6 + 1, x_120);
lean_ctor_set_uint8(x_6, sizeof(void*)*6 + 2, x_122);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_6);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_6);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 x_244 = x_7;
} else {
 lean_dec_ref(x_7);
 x_244 = lean_box(0);
}
x_245 = lean_nat_add(x_15, x_220);
lean_dec(x_15);
if (lean_is_scalar(x_244)) {
 x_246 = lean_alloc_ctor(0, 6, 3);
} else {
 x_246 = x_244;
}
lean_ctor_set(x_246, 0, x_10);
lean_ctor_set(x_246, 1, x_12);
lean_ctor_set(x_246, 2, x_14);
lean_ctor_set(x_246, 3, x_245);
lean_ctor_set(x_246, 4, x_16);
lean_ctor_set(x_246, 5, x_17);
lean_ctor_set_uint8(x_246, sizeof(void*)*6, x_9);
lean_ctor_set_uint8(x_246, sizeof(void*)*6 + 1, x_11);
lean_ctor_set_uint8(x_246, sizeof(void*)*6 + 2, x_13);
x_247 = lean_unsigned_to_nat(0u);
x_248 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_248, 0, x_221);
lean_ctor_set(x_248, 1, x_121);
lean_ctor_set(x_248, 2, x_123);
lean_ctor_set(x_248, 3, x_247);
lean_ctor_set(x_248, 4, x_125);
lean_ctor_set(x_248, 5, x_126);
lean_ctor_set_uint8(x_248, sizeof(void*)*6, x_174);
lean_ctor_set_uint8(x_248, sizeof(void*)*6 + 1, x_120);
lean_ctor_set_uint8(x_248, sizeof(void*)*6 + 2, x_122);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
}
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_2);
goto block_116;
}
block_150:
{
uint8_t x_130; 
x_130 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_118, x_128);
if (x_130 == 0)
{
x_56 = x_130;
x_57 = x_127;
x_58 = x_129;
x_59 = x_7;
goto block_74;
}
else
{
uint8_t x_131; 
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_121);
lean_inc(x_119);
x_131 = !lean_is_exclusive(x_7);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_132 = lean_ctor_get(x_7, 5);
lean_dec(x_132);
x_133 = lean_ctor_get(x_7, 4);
lean_dec(x_133);
x_134 = lean_ctor_get(x_7, 3);
lean_dec(x_134);
x_135 = lean_ctor_get(x_7, 2);
lean_dec(x_135);
x_136 = lean_ctor_get(x_7, 1);
lean_dec(x_136);
x_137 = lean_ctor_get(x_7, 0);
lean_dec(x_137);
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_nat_sub(x_125, x_138);
lean_dec(x_125);
x_140 = lean_unsigned_to_nat(0u);
x_141 = lean_nat_dec_eq(x_139, x_140);
if (x_141 == 0)
{
lean_ctor_set(x_7, 4, x_139);
x_56 = x_130;
x_57 = x_127;
x_58 = x_129;
x_59 = x_7;
goto block_74;
}
else
{
uint8_t x_142; 
lean_dec(x_121);
x_142 = 0;
lean_inc(x_2);
lean_ctor_set(x_7, 4, x_139);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set_uint8(x_7, sizeof(void*)*6, x_18);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 1, x_142);
x_56 = x_130;
x_57 = x_127;
x_58 = x_129;
x_59 = x_7;
goto block_74;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
lean_dec(x_7);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_nat_sub(x_125, x_143);
lean_dec(x_125);
x_145 = lean_unsigned_to_nat(0u);
x_146 = lean_nat_dec_eq(x_144, x_145);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_147, 0, x_119);
lean_ctor_set(x_147, 1, x_121);
lean_ctor_set(x_147, 2, x_123);
lean_ctor_set(x_147, 3, x_124);
lean_ctor_set(x_147, 4, x_144);
lean_ctor_set(x_147, 5, x_126);
lean_ctor_set_uint8(x_147, sizeof(void*)*6, x_118);
lean_ctor_set_uint8(x_147, sizeof(void*)*6 + 1, x_120);
lean_ctor_set_uint8(x_147, sizeof(void*)*6 + 2, x_122);
x_56 = x_130;
x_57 = x_127;
x_58 = x_129;
x_59 = x_147;
goto block_74;
}
else
{
uint8_t x_148; lean_object* x_149; 
lean_dec(x_121);
x_148 = 0;
lean_inc(x_2);
x_149 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_149, 0, x_119);
lean_ctor_set(x_149, 1, x_2);
lean_ctor_set(x_149, 2, x_123);
lean_ctor_set(x_149, 3, x_124);
lean_ctor_set(x_149, 4, x_144);
lean_ctor_set(x_149, 5, x_126);
lean_ctor_set_uint8(x_149, sizeof(void*)*6, x_18);
lean_ctor_set_uint8(x_149, sizeof(void*)*6 + 1, x_148);
lean_ctor_set_uint8(x_149, sizeof(void*)*6 + 2, x_122);
x_56 = x_130;
x_57 = x_127;
x_58 = x_129;
x_59 = x_149;
goto block_74;
}
}
}
}
block_172:
{
uint8_t x_151; uint8_t x_152; 
x_151 = 2;
x_152 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_9, x_151);
if (x_152 == 0)
{
x_127 = x_152;
x_128 = x_151;
x_129 = x_6;
goto block_150;
}
else
{
uint8_t x_153; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_10);
x_153 = !lean_is_exclusive(x_6);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_154 = lean_ctor_get(x_6, 5);
lean_dec(x_154);
x_155 = lean_ctor_get(x_6, 4);
lean_dec(x_155);
x_156 = lean_ctor_get(x_6, 3);
lean_dec(x_156);
x_157 = lean_ctor_get(x_6, 2);
lean_dec(x_157);
x_158 = lean_ctor_get(x_6, 1);
lean_dec(x_158);
x_159 = lean_ctor_get(x_6, 0);
lean_dec(x_159);
x_160 = lean_unsigned_to_nat(1u);
x_161 = lean_nat_sub(x_16, x_160);
lean_dec(x_16);
x_162 = lean_unsigned_to_nat(0u);
x_163 = lean_nat_dec_eq(x_161, x_162);
if (x_163 == 0)
{
lean_ctor_set(x_6, 4, x_161);
x_127 = x_152;
x_128 = x_151;
x_129 = x_6;
goto block_150;
}
else
{
uint8_t x_164; 
lean_dec(x_12);
x_164 = 0;
lean_inc(x_2);
lean_ctor_set(x_6, 4, x_161);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*6, x_18);
lean_ctor_set_uint8(x_6, sizeof(void*)*6 + 1, x_164);
x_127 = x_152;
x_128 = x_151;
x_129 = x_6;
goto block_150;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
lean_dec(x_6);
x_165 = lean_unsigned_to_nat(1u);
x_166 = lean_nat_sub(x_16, x_165);
lean_dec(x_16);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_nat_dec_eq(x_166, x_167);
if (x_168 == 0)
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_169, 0, x_10);
lean_ctor_set(x_169, 1, x_12);
lean_ctor_set(x_169, 2, x_14);
lean_ctor_set(x_169, 3, x_15);
lean_ctor_set(x_169, 4, x_166);
lean_ctor_set(x_169, 5, x_17);
lean_ctor_set_uint8(x_169, sizeof(void*)*6, x_9);
lean_ctor_set_uint8(x_169, sizeof(void*)*6 + 1, x_11);
lean_ctor_set_uint8(x_169, sizeof(void*)*6 + 2, x_13);
x_127 = x_152;
x_128 = x_151;
x_129 = x_169;
goto block_150;
}
else
{
uint8_t x_170; lean_object* x_171; 
lean_dec(x_12);
x_170 = 0;
lean_inc(x_2);
x_171 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_171, 0, x_10);
lean_ctor_set(x_171, 1, x_2);
lean_ctor_set(x_171, 2, x_14);
lean_ctor_set(x_171, 3, x_15);
lean_ctor_set(x_171, 4, x_166);
lean_ctor_set(x_171, 5, x_17);
lean_ctor_set_uint8(x_171, sizeof(void*)*6, x_18);
lean_ctor_set_uint8(x_171, sizeof(void*)*6 + 1, x_170);
lean_ctor_set_uint8(x_171, sizeof(void*)*6 + 2, x_13);
x_127 = x_152;
x_128 = x_151;
x_129 = x_171;
goto block_150;
}
}
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_2);
goto block_116;
}
block_35:
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = 0;
lean_inc(x_2);
x_32 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_2);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_28);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 5, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*6, x_18);
lean_ctor_set_uint8(x_32, sizeof(void*)*6 + 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*6 + 2, x_26);
x_33 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_2);
lean_ctor_set(x_33, 2, x_21);
lean_ctor_set(x_33, 3, x_22);
lean_ctor_set(x_33, 4, x_23);
lean_ctor_set(x_33, 5, x_24);
lean_ctor_set_uint8(x_33, sizeof(void*)*6, x_18);
lean_ctor_set_uint8(x_33, sizeof(void*)*6 + 1, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*6 + 2, x_20);
if (lean_is_scalar(x_8)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_8;
}
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
block_55:
{
uint8_t x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_39 = lean_ctor_get_uint8(x_37, sizeof(void*)*6);
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_ctor_get_uint8(x_37, sizeof(void*)*6 + 2);
x_42 = lean_ctor_get(x_37, 2);
x_43 = lean_ctor_get(x_37, 3);
x_44 = lean_ctor_get(x_37, 4);
x_45 = lean_ctor_get(x_37, 5);
x_46 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_39, x_18);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_8);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_37);
return x_47;
}
else
{
if (x_36 == 0)
{
lean_object* x_48; 
lean_dec(x_8);
lean_dec(x_2);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_37);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_40);
lean_dec_ref(x_37);
x_49 = lean_ctor_get(x_38, 0);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_38, sizeof(void*)*6 + 2);
x_51 = lean_ctor_get(x_38, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_38, 4);
lean_inc(x_53);
x_54 = lean_ctor_get(x_38, 5);
lean_inc(x_54);
lean_dec_ref(x_38);
x_19 = x_40;
x_20 = x_41;
x_21 = x_42;
x_22 = x_43;
x_23 = x_44;
x_24 = x_45;
x_25 = x_49;
x_26 = x_50;
x_27 = x_51;
x_28 = x_52;
x_29 = x_53;
x_30 = x_54;
goto block_35;
}
}
}
block_74:
{
uint8_t x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_60 = lean_ctor_get_uint8(x_58, sizeof(void*)*6);
x_61 = lean_ctor_get(x_58, 0);
x_62 = lean_ctor_get_uint8(x_58, sizeof(void*)*6 + 2);
x_63 = lean_ctor_get(x_58, 2);
x_64 = lean_ctor_get(x_58, 3);
x_65 = lean_ctor_get(x_58, 4);
x_66 = lean_ctor_get(x_58, 5);
x_67 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_60, x_18);
if (x_67 == 0)
{
x_36 = x_56;
x_37 = x_59;
x_38 = x_58;
goto block_55;
}
else
{
if (x_57 == 0)
{
x_36 = x_56;
x_37 = x_59;
x_38 = x_58;
goto block_55;
}
else
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_61);
lean_dec_ref(x_58);
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_59, sizeof(void*)*6 + 2);
x_70 = lean_ctor_get(x_59, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_59, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_59, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_59, 5);
lean_inc(x_73);
lean_dec_ref(x_59);
x_19 = x_68;
x_20 = x_69;
x_21 = x_70;
x_22 = x_71;
x_23 = x_72;
x_24 = x_73;
x_25 = x_61;
x_26 = x_62;
x_27 = x_63;
x_28 = x_64;
x_29 = x_65;
x_30 = x_66;
goto block_35;
}
}
}
block_116:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; 
x_75 = lp_SSExactMajority_SSEM_propagateReset___redArg(x_3, x_4, x_6, x_7);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
x_78 = lean_ctor_get_uint8(x_76, sizeof(void*)*6);
x_79 = lean_ctor_get_uint8(x_76, sizeof(void*)*6 + 1);
x_80 = 0;
x_81 = lp_SSExactMajority_SSEM_instDecidableEqLeader(x_79, x_80);
if (x_81 == 0)
{
lean_dec(x_77);
lean_dec(x_76);
return x_75;
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
uint8_t x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_83 = lean_ctor_get_uint8(x_77, sizeof(void*)*6);
x_84 = lean_ctor_get(x_77, 0);
x_85 = lean_ctor_get_uint8(x_77, sizeof(void*)*6 + 1);
x_86 = lean_ctor_get(x_77, 1);
x_87 = lean_ctor_get(x_77, 2);
x_88 = lean_ctor_get(x_77, 3);
x_89 = lean_ctor_get(x_77, 4);
x_90 = lean_ctor_get(x_77, 5);
x_91 = lp_SSExactMajority_SSEM_instDecidableEqLeader(x_85, x_80);
if (x_91 == 0)
{
lean_free_object(x_77);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_76);
return x_75;
}
else
{
uint8_t x_92; 
x_92 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_78, x_18);
if (x_92 == 0)
{
lean_free_object(x_77);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_76);
return x_75;
}
else
{
uint8_t x_93; 
x_93 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_83, x_18);
if (x_93 == 0)
{
lean_free_object(x_77);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_76);
return x_75;
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_75);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_75, 1);
lean_dec(x_95);
x_96 = lean_ctor_get(x_75, 0);
lean_dec(x_96);
x_97 = 1;
lean_ctor_set_uint8(x_77, sizeof(void*)*6 + 1, x_97);
return x_75;
}
else
{
uint8_t x_98; lean_object* x_99; 
lean_dec(x_75);
x_98 = 1;
lean_ctor_set_uint8(x_77, sizeof(void*)*6 + 1, x_98);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_76);
lean_ctor_set(x_99, 1, x_77);
return x_99;
}
}
}
}
}
else
{
uint8_t x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_100 = lean_ctor_get_uint8(x_77, sizeof(void*)*6);
x_101 = lean_ctor_get(x_77, 0);
x_102 = lean_ctor_get_uint8(x_77, sizeof(void*)*6 + 1);
x_103 = lean_ctor_get(x_77, 1);
x_104 = lean_ctor_get_uint8(x_77, sizeof(void*)*6 + 2);
x_105 = lean_ctor_get(x_77, 2);
x_106 = lean_ctor_get(x_77, 3);
x_107 = lean_ctor_get(x_77, 4);
x_108 = lean_ctor_get(x_77, 5);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_103);
lean_inc(x_101);
lean_dec(x_77);
x_109 = lp_SSExactMajority_SSEM_instDecidableEqLeader(x_102, x_80);
if (x_109 == 0)
{
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_76);
return x_75;
}
else
{
uint8_t x_110; 
x_110 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_78, x_18);
if (x_110 == 0)
{
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_76);
return x_75;
}
else
{
uint8_t x_111; 
x_111 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_100, x_18);
if (x_111 == 0)
{
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_76);
return x_75;
}
else
{
lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; 
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_112 = x_75;
} else {
 lean_dec_ref(x_75);
 x_112 = lean_box(0);
}
x_113 = 1;
x_114 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_114, 0, x_101);
lean_ctor_set(x_114, 1, x_103);
lean_ctor_set(x_114, 2, x_105);
lean_ctor_set(x_114, 3, x_106);
lean_ctor_set(x_114, 4, x_107);
lean_ctor_set(x_114, 5, x_108);
lean_ctor_set_uint8(x_114, sizeof(void*)*6, x_100);
lean_ctor_set_uint8(x_114, sizeof(void*)*6 + 1, x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*6 + 2, x_104);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_76);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_SSExactMajority_SSEM_rankDeltaOSSR(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
x_9 = 1;
x_10 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg(x_1, x_2, x_3, x_4, x_5);
return x_11;
}
else
{
uint8_t x_12; uint8_t x_13; 
x_12 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
x_13 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_12, x_9);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg(x_1, x_2, x_3, x_4, x_5);
return x_14;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_SSExactMajority_SSEM_rankDeltaStable___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_SSExactMajority_SSEM_rankDeltaStable(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_SSExactMajority_SSEM_rankDeltaStable___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_State(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_Silent(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_RankDelta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Protocol_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_Silent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
