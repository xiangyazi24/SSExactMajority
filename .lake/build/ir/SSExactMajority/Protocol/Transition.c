// Lean compiler output
// Module: SSExactMajority.Protocol.Transition
// Imports: public import Init public import SSExactMajority.Defs.Protocol public import SSExactMajority.Protocol.State
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
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_opinionToAnswer___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_outputPEM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__decide(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__decide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ceilHalf(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_outputPEM___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__phase4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_outputPEM___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqRole(uint8_t, uint8_t);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_opinionToAnswer(uint8_t);
uint8_t lp_SSExactMajority_SSEM_agentOutput___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap___redArg(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_outputPEM___redArg___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__propagate(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__propagate___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ceilHalf___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__phase4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqOpinion(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqAnswer(uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_protocolPEM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ceilHalf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_nat_shiftr(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ceilHalf___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_SSExactMajority_SSEM_ceilHalf(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_opinionToAnswer(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 2;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 3;
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_opinionToAnswer___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lp_SSExactMajority_SSEM_opinionToAnswer(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_120; lean_object* x_121; lean_object* x_161; uint8_t x_184; 
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_5);
x_28 = lean_apply_1(x_3, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get_uint8(x_29, sizeof(void*)*6);
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get_uint8(x_29, sizeof(void*)*6 + 1);
x_35 = lean_ctor_get(x_29, 1);
x_36 = lean_ctor_get(x_29, 2);
x_37 = lean_ctor_get(x_29, 3);
x_38 = lean_ctor_get(x_29, 4);
x_39 = lean_ctor_get(x_29, 5);
x_40 = 0;
x_184 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_32, x_40);
if (x_184 == 0)
{
x_161 = x_29;
goto block_183;
}
else
{
uint8_t x_185; uint8_t x_186; 
x_185 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_186 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_185, x_40);
if (x_186 == 0)
{
if (x_184 == 0)
{
x_161 = x_29;
goto block_183;
}
else
{
uint8_t x_187; 
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_33);
x_187 = !lean_is_exclusive(x_29);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_188 = lean_ctor_get(x_29, 5);
lean_dec(x_188);
x_189 = lean_ctor_get(x_29, 4);
lean_dec(x_189);
x_190 = lean_ctor_get(x_29, 3);
lean_dec(x_190);
x_191 = lean_ctor_get(x_29, 2);
lean_dec(x_191);
x_192 = lean_ctor_get(x_29, 1);
lean_dec(x_192);
x_193 = lean_ctor_get(x_29, 0);
lean_dec(x_193);
x_194 = 0;
lean_ctor_set_uint8(x_29, sizeof(void*)*6 + 2, x_194);
x_161 = x_29;
goto block_183;
}
else
{
uint8_t x_195; lean_object* x_196; 
lean_dec(x_29);
x_195 = 0;
x_196 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_196, 0, x_33);
lean_ctor_set(x_196, 1, x_35);
lean_ctor_set(x_196, 2, x_36);
lean_ctor_set(x_196, 3, x_37);
lean_ctor_set(x_196, 4, x_38);
lean_ctor_set(x_196, 5, x_39);
lean_ctor_set_uint8(x_196, sizeof(void*)*6, x_32);
lean_ctor_set_uint8(x_196, sizeof(void*)*6 + 1, x_34);
lean_ctor_set_uint8(x_196, sizeof(void*)*6 + 2, x_195);
x_161 = x_196;
goto block_183;
}
}
}
else
{
x_161 = x_29;
goto block_183;
}
}
block_26:
{
uint8_t x_20; 
x_20 = lp_SSExactMajority_SSEM_instDecidableEqAnswer(x_16, x_9);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
if (x_19 == 0)
{
if (x_20 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_17);
x_23 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_10);
lean_ctor_set(x_23, 3, x_11);
lean_ctor_set(x_23, 4, x_15);
lean_ctor_set(x_23, 5, x_6);
lean_ctor_set_uint8(x_23, sizeof(void*)*6, x_13);
lean_ctor_set_uint8(x_23, sizeof(void*)*6 + 1, x_12);
lean_ctor_set_uint8(x_23, sizeof(void*)*6 + 2, x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
}
}
block_78:
{
uint8_t x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_43 = lean_ctor_get_uint8(x_41, sizeof(void*)*6);
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get_uint8(x_41, sizeof(void*)*6 + 1);
x_46 = lean_ctor_get(x_41, 1);
x_47 = lean_ctor_get_uint8(x_41, sizeof(void*)*6 + 2);
x_48 = lean_ctor_get(x_41, 2);
x_49 = lean_ctor_get(x_41, 3);
x_50 = lean_ctor_get(x_41, 4);
x_51 = lean_ctor_get(x_41, 5);
x_52 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_43, x_40);
if (x_52 == 0)
{
lean_object* x_53; 
if (lean_is_scalar(x_31)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_31;
}
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_42);
return x_53;
}
else
{
uint8_t x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_ctor_get_uint8(x_42, sizeof(void*)*6);
x_55 = lean_ctor_get(x_42, 0);
x_56 = lean_ctor_get_uint8(x_42, sizeof(void*)*6 + 1);
x_57 = lean_ctor_get(x_42, 1);
x_58 = lean_ctor_get_uint8(x_42, sizeof(void*)*6 + 2);
x_59 = lean_ctor_get(x_42, 2);
x_60 = lean_ctor_get(x_42, 3);
x_61 = lean_ctor_get(x_42, 4);
x_62 = lean_ctor_get(x_42, 5);
x_63 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_54, x_40);
if (x_63 == 0)
{
lean_object* x_64; 
if (lean_is_scalar(x_31)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_31;
}
lean_ctor_set(x_64, 0, x_41);
lean_ctor_set(x_64, 1, x_42);
return x_64;
}
else
{
uint8_t x_65; uint8_t x_66; 
x_65 = 0;
x_66 = lp_SSExactMajority_SSEM_instDecidableEqAnswer(x_47, x_65);
if (x_66 == 0)
{
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_31);
x_6 = x_62;
x_7 = x_47;
x_8 = x_41;
x_9 = x_65;
x_10 = x_59;
x_11 = x_60;
x_12 = x_56;
x_13 = x_54;
x_14 = x_55;
x_15 = x_61;
x_16 = x_58;
x_17 = x_42;
x_18 = x_57;
x_19 = x_66;
goto block_26;
}
else
{
uint8_t x_67; 
x_67 = lp_SSExactMajority_SSEM_instDecidableEqAnswer(x_58, x_65);
if (x_67 == 0)
{
if (x_66 == 0)
{
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_31);
x_6 = x_62;
x_7 = x_47;
x_8 = x_41;
x_9 = x_65;
x_10 = x_59;
x_11 = x_60;
x_12 = x_56;
x_13 = x_54;
x_14 = x_55;
x_15 = x_61;
x_16 = x_58;
x_17 = x_42;
x_18 = x_57;
x_19 = x_66;
goto block_26;
}
else
{
uint8_t x_68; 
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_46);
lean_inc(x_44);
x_68 = !lean_is_exclusive(x_41);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_41, 5);
lean_dec(x_69);
x_70 = lean_ctor_get(x_41, 4);
lean_dec(x_70);
x_71 = lean_ctor_get(x_41, 3);
lean_dec(x_71);
x_72 = lean_ctor_get(x_41, 2);
lean_dec(x_72);
x_73 = lean_ctor_get(x_41, 1);
lean_dec(x_73);
x_74 = lean_ctor_get(x_41, 0);
lean_dec(x_74);
lean_ctor_set_uint8(x_41, sizeof(void*)*6 + 2, x_58);
if (lean_is_scalar(x_31)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_31;
}
lean_ctor_set(x_75, 0, x_41);
lean_ctor_set(x_75, 1, x_42);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_41);
x_76 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_76, 0, x_44);
lean_ctor_set(x_76, 1, x_46);
lean_ctor_set(x_76, 2, x_48);
lean_ctor_set(x_76, 3, x_49);
lean_ctor_set(x_76, 4, x_50);
lean_ctor_set(x_76, 5, x_51);
lean_ctor_set_uint8(x_76, sizeof(void*)*6, x_43);
lean_ctor_set_uint8(x_76, sizeof(void*)*6 + 1, x_45);
lean_ctor_set_uint8(x_76, sizeof(void*)*6 + 2, x_58);
if (lean_is_scalar(x_31)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_31;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_42);
return x_77;
}
}
}
else
{
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_31);
x_6 = x_62;
x_7 = x_47;
x_8 = x_41;
x_9 = x_65;
x_10 = x_59;
x_11 = x_60;
x_12 = x_56;
x_13 = x_54;
x_14 = x_55;
x_15 = x_61;
x_16 = x_58;
x_17 = x_42;
x_18 = x_57;
x_19 = x_66;
goto block_26;
}
}
}
}
}
block_119:
{
uint8_t x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_82 = lean_ctor_get_uint8(x_79, sizeof(void*)*6);
x_83 = lean_ctor_get(x_79, 0);
x_84 = lean_ctor_get_uint8(x_79, sizeof(void*)*6 + 1);
x_85 = lean_ctor_get(x_79, 1);
x_86 = lean_ctor_get_uint8(x_79, sizeof(void*)*6 + 2);
x_87 = lean_ctor_get(x_79, 3);
x_88 = lean_ctor_get(x_79, 4);
x_89 = lean_ctor_get(x_79, 5);
x_90 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_82, x_80);
if (x_90 == 0)
{
lean_dec_ref(x_5);
x_41 = x_81;
x_42 = x_79;
goto block_78;
}
else
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_5);
if (x_91 == 0)
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_92 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
x_93 = lean_ctor_get(x_5, 5);
lean_dec(x_93);
x_94 = lean_ctor_get(x_5, 4);
lean_dec(x_94);
x_95 = lean_ctor_get(x_5, 3);
lean_dec(x_95);
x_96 = lean_ctor_get(x_5, 2);
lean_dec(x_96);
x_97 = lean_ctor_get(x_5, 1);
lean_dec(x_97);
x_98 = lean_ctor_get(x_5, 0);
lean_dec(x_98);
x_99 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_92, x_80);
if (x_99 == 0)
{
if (x_90 == 0)
{
lean_free_object(x_5);
x_41 = x_81;
x_42 = x_79;
goto block_78;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_add(x_83, x_100);
x_102 = lp_SSExactMajority_SSEM_ceilHalf(x_1);
x_103 = lean_nat_dec_eq(x_101, x_102);
lean_dec(x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_free_object(x_5);
x_41 = x_81;
x_42 = x_79;
goto block_78;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_85);
lean_inc(x_83);
lean_dec_ref(x_79);
x_104 = lean_unsigned_to_nat(7u);
x_105 = lean_unsigned_to_nat(4u);
x_106 = lean_nat_add(x_2, x_105);
x_107 = lean_nat_mul(x_104, x_106);
lean_dec(x_106);
lean_ctor_set(x_5, 5, x_89);
lean_ctor_set(x_5, 4, x_88);
lean_ctor_set(x_5, 3, x_87);
lean_ctor_set(x_5, 2, x_107);
lean_ctor_set(x_5, 1, x_85);
lean_ctor_set(x_5, 0, x_83);
lean_ctor_set_uint8(x_5, sizeof(void*)*6, x_82);
lean_ctor_set_uint8(x_5, sizeof(void*)*6 + 1, x_84);
lean_ctor_set_uint8(x_5, sizeof(void*)*6 + 2, x_86);
x_41 = x_81;
x_42 = x_5;
goto block_78;
}
}
}
else
{
lean_free_object(x_5);
x_41 = x_81;
x_42 = x_79;
goto block_78;
}
}
else
{
uint8_t x_108; uint8_t x_109; 
x_108 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
lean_dec(x_5);
x_109 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_108, x_80);
if (x_109 == 0)
{
if (x_90 == 0)
{
x_41 = x_81;
x_42 = x_79;
goto block_78;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_add(x_83, x_110);
x_112 = lp_SSExactMajority_SSEM_ceilHalf(x_1);
x_113 = lean_nat_dec_eq(x_111, x_112);
lean_dec(x_112);
lean_dec(x_111);
if (x_113 == 0)
{
x_41 = x_81;
x_42 = x_79;
goto block_78;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_85);
lean_inc(x_83);
lean_dec_ref(x_79);
x_114 = lean_unsigned_to_nat(7u);
x_115 = lean_unsigned_to_nat(4u);
x_116 = lean_nat_add(x_2, x_115);
x_117 = lean_nat_mul(x_114, x_116);
lean_dec(x_116);
x_118 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_118, 0, x_83);
lean_ctor_set(x_118, 1, x_85);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_87);
lean_ctor_set(x_118, 4, x_88);
lean_ctor_set(x_118, 5, x_89);
lean_ctor_set_uint8(x_118, sizeof(void*)*6, x_82);
lean_ctor_set_uint8(x_118, sizeof(void*)*6 + 1, x_84);
lean_ctor_set_uint8(x_118, sizeof(void*)*6 + 2, x_86);
x_41 = x_81;
x_42 = x_118;
goto block_78;
}
}
}
else
{
x_41 = x_81;
x_42 = x_79;
goto block_78;
}
}
}
}
block_160:
{
uint8_t x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; 
x_122 = lean_ctor_get_uint8(x_120, sizeof(void*)*6);
x_123 = lean_ctor_get(x_120, 0);
x_124 = lean_ctor_get_uint8(x_120, sizeof(void*)*6 + 1);
x_125 = lean_ctor_get(x_120, 1);
x_126 = lean_ctor_get_uint8(x_120, sizeof(void*)*6 + 2);
x_127 = lean_ctor_get(x_120, 3);
x_128 = lean_ctor_get(x_120, 4);
x_129 = lean_ctor_get(x_120, 5);
x_130 = 1;
x_131 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_122, x_130);
if (x_131 == 0)
{
lean_dec_ref(x_4);
x_79 = x_121;
x_80 = x_130;
x_81 = x_120;
goto block_119;
}
else
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_4);
if (x_132 == 0)
{
uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_133 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_134 = lean_ctor_get(x_4, 5);
lean_dec(x_134);
x_135 = lean_ctor_get(x_4, 4);
lean_dec(x_135);
x_136 = lean_ctor_get(x_4, 3);
lean_dec(x_136);
x_137 = lean_ctor_get(x_4, 2);
lean_dec(x_137);
x_138 = lean_ctor_get(x_4, 1);
lean_dec(x_138);
x_139 = lean_ctor_get(x_4, 0);
lean_dec(x_139);
x_140 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_133, x_130);
if (x_140 == 0)
{
if (x_131 == 0)
{
lean_free_object(x_4);
x_79 = x_121;
x_80 = x_130;
x_81 = x_120;
goto block_119;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = lean_unsigned_to_nat(1u);
x_142 = lean_nat_add(x_123, x_141);
x_143 = lp_SSExactMajority_SSEM_ceilHalf(x_1);
x_144 = lean_nat_dec_eq(x_142, x_143);
lean_dec(x_143);
lean_dec(x_142);
if (x_144 == 0)
{
lean_free_object(x_4);
x_79 = x_121;
x_80 = x_130;
x_81 = x_120;
goto block_119;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_125);
lean_inc(x_123);
lean_dec_ref(x_120);
x_145 = lean_unsigned_to_nat(7u);
x_146 = lean_unsigned_to_nat(4u);
x_147 = lean_nat_add(x_2, x_146);
x_148 = lean_nat_mul(x_145, x_147);
lean_dec(x_147);
lean_ctor_set(x_4, 5, x_129);
lean_ctor_set(x_4, 4, x_128);
lean_ctor_set(x_4, 3, x_127);
lean_ctor_set(x_4, 2, x_148);
lean_ctor_set(x_4, 1, x_125);
lean_ctor_set(x_4, 0, x_123);
lean_ctor_set_uint8(x_4, sizeof(void*)*6, x_122);
lean_ctor_set_uint8(x_4, sizeof(void*)*6 + 1, x_124);
lean_ctor_set_uint8(x_4, sizeof(void*)*6 + 2, x_126);
x_79 = x_121;
x_80 = x_130;
x_81 = x_4;
goto block_119;
}
}
}
else
{
lean_free_object(x_4);
x_79 = x_121;
x_80 = x_130;
x_81 = x_120;
goto block_119;
}
}
else
{
uint8_t x_149; uint8_t x_150; 
x_149 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
lean_dec(x_4);
x_150 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_149, x_130);
if (x_150 == 0)
{
if (x_131 == 0)
{
x_79 = x_121;
x_80 = x_130;
x_81 = x_120;
goto block_119;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_151 = lean_unsigned_to_nat(1u);
x_152 = lean_nat_add(x_123, x_151);
x_153 = lp_SSExactMajority_SSEM_ceilHalf(x_1);
x_154 = lean_nat_dec_eq(x_152, x_153);
lean_dec(x_153);
lean_dec(x_152);
if (x_154 == 0)
{
x_79 = x_121;
x_80 = x_130;
x_81 = x_120;
goto block_119;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_125);
lean_inc(x_123);
lean_dec_ref(x_120);
x_155 = lean_unsigned_to_nat(7u);
x_156 = lean_unsigned_to_nat(4u);
x_157 = lean_nat_add(x_2, x_156);
x_158 = lean_nat_mul(x_155, x_157);
lean_dec(x_157);
x_159 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_159, 0, x_123);
lean_ctor_set(x_159, 1, x_125);
lean_ctor_set(x_159, 2, x_158);
lean_ctor_set(x_159, 3, x_127);
lean_ctor_set(x_159, 4, x_128);
lean_ctor_set(x_159, 5, x_129);
lean_ctor_set_uint8(x_159, sizeof(void*)*6, x_122);
lean_ctor_set_uint8(x_159, sizeof(void*)*6 + 1, x_124);
lean_ctor_set_uint8(x_159, sizeof(void*)*6 + 2, x_126);
x_79 = x_121;
x_80 = x_130;
x_81 = x_159;
goto block_119;
}
}
}
else
{
x_79 = x_121;
x_80 = x_130;
x_81 = x_120;
goto block_119;
}
}
}
}
block_183:
{
uint8_t x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_162 = lean_ctor_get_uint8(x_30, sizeof(void*)*6);
x_163 = lean_ctor_get(x_30, 0);
x_164 = lean_ctor_get_uint8(x_30, sizeof(void*)*6 + 1);
x_165 = lean_ctor_get(x_30, 1);
x_166 = lean_ctor_get(x_30, 2);
x_167 = lean_ctor_get(x_30, 3);
x_168 = lean_ctor_get(x_30, 4);
x_169 = lean_ctor_get(x_30, 5);
x_170 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_162, x_40);
if (x_170 == 0)
{
x_120 = x_161;
x_121 = x_30;
goto block_160;
}
else
{
uint8_t x_171; uint8_t x_172; 
x_171 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
x_172 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_171, x_40);
if (x_172 == 0)
{
if (x_170 == 0)
{
x_120 = x_161;
x_121 = x_30;
goto block_160;
}
else
{
uint8_t x_173; 
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_163);
x_173 = !lean_is_exclusive(x_30);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_174 = lean_ctor_get(x_30, 5);
lean_dec(x_174);
x_175 = lean_ctor_get(x_30, 4);
lean_dec(x_175);
x_176 = lean_ctor_get(x_30, 3);
lean_dec(x_176);
x_177 = lean_ctor_get(x_30, 2);
lean_dec(x_177);
x_178 = lean_ctor_get(x_30, 1);
lean_dec(x_178);
x_179 = lean_ctor_get(x_30, 0);
lean_dec(x_179);
x_180 = 0;
lean_ctor_set_uint8(x_30, sizeof(void*)*6 + 2, x_180);
x_120 = x_161;
x_121 = x_30;
goto block_160;
}
else
{
uint8_t x_181; lean_object* x_182; 
lean_dec(x_30);
x_181 = 0;
x_182 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_182, 0, x_163);
lean_ctor_set(x_182, 1, x_165);
lean_ctor_set(x_182, 2, x_166);
lean_ctor_set(x_182, 3, x_167);
lean_ctor_set(x_182, 4, x_168);
lean_ctor_set(x_182, 5, x_169);
lean_ctor_set_uint8(x_182, sizeof(void*)*6, x_162);
lean_ctor_set_uint8(x_182, sizeof(void*)*6 + 1, x_164);
lean_ctor_set_uint8(x_182, sizeof(void*)*6 + 2, x_181);
x_120 = x_161;
x_121 = x_182;
goto block_160;
}
}
}
else
{
x_120 = x_161;
x_121 = x_30;
goto block_160;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_SSExactMajority_SSEM_transitionPEM__prePhase4___redArg(x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = lp_SSExactMajority_SSEM_transitionPEM__prePhase4(x_1, x_2, x_3, x_4, x_5, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_SSExactMajority_SSEM_transitionPEM__prePhase4___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
else
{
uint8_t x_9; uint8_t x_10; 
x_9 = 1;
x_10 = lp_SSExactMajority_SSEM_instDecidableEqOpinion(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
else
{
uint8_t x_12; uint8_t x_13; 
x_12 = 0;
x_13 = lp_SSExactMajority_SSEM_instDecidableEqOpinion(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_1);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_SSExactMajority_SSEM_phase4__swap___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_4);
x_7 = lean_unbox(x_5);
x_8 = lp_SSExactMajority_SSEM_phase4__swap(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
x_6 = lean_unbox(x_4);
x_7 = lp_SSExactMajority_SSEM_phase4__swap___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__decide(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_mod(x_1, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_46; 
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
x_15 = lean_ctor_get(x_2, 3);
x_16 = lean_ctor_get(x_2, 4);
x_17 = lean_ctor_get(x_2, 5);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_11, x_18);
x_20 = lp_SSExactMajority_SSEM_ceilHalf(x_1);
x_46 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_46 == 0)
{
x_21 = x_2;
goto block_45;
}
else
{
uint8_t x_47; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_48 = lean_ctor_get(x_2, 5);
lean_dec(x_48);
x_49 = lean_ctor_get(x_2, 4);
lean_dec(x_49);
x_50 = lean_ctor_get(x_2, 3);
lean_dec(x_50);
x_51 = lean_ctor_get(x_2, 2);
lean_dec(x_51);
x_52 = lean_ctor_get(x_2, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_2, 0);
lean_dec(x_53);
x_54 = lp_SSExactMajority_SSEM_opinionToAnswer(x_4);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 2, x_54);
x_21 = x_2;
goto block_45;
}
else
{
uint8_t x_55; lean_object* x_56; 
lean_dec(x_2);
x_55 = lp_SSExactMajority_SSEM_opinionToAnswer(x_4);
x_56 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_56, 0, x_11);
lean_ctor_set(x_56, 1, x_13);
lean_ctor_set(x_56, 2, x_14);
lean_ctor_set(x_56, 3, x_15);
lean_ctor_set(x_56, 4, x_16);
lean_ctor_set(x_56, 5, x_17);
lean_ctor_set_uint8(x_56, sizeof(void*)*6, x_10);
lean_ctor_set_uint8(x_56, sizeof(void*)*6 + 1, x_12);
lean_ctor_set_uint8(x_56, sizeof(void*)*6 + 2, x_55);
x_21 = x_56;
goto block_45;
}
}
block_45:
{
uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
x_27 = lean_ctor_get(x_3, 3);
x_28 = lean_ctor_get(x_3, 4);
x_29 = lean_ctor_get(x_3, 5);
x_30 = lean_nat_add(x_23, x_18);
x_31 = lean_nat_dec_eq(x_30, x_20);
lean_dec(x_20);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
else
{
uint8_t x_33; 
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_23);
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_3, 5);
lean_dec(x_34);
x_35 = lean_ctor_get(x_3, 4);
lean_dec(x_35);
x_36 = lean_ctor_get(x_3, 3);
lean_dec(x_36);
x_37 = lean_ctor_get(x_3, 2);
lean_dec(x_37);
x_38 = lean_ctor_get(x_3, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_3, 0);
lean_dec(x_39);
x_40 = lp_SSExactMajority_SSEM_opinionToAnswer(x_5);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 2, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_21);
lean_ctor_set(x_41, 1, x_3);
return x_41;
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_3);
x_42 = lp_SSExactMajority_SSEM_opinionToAnswer(x_5);
x_43 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_25);
lean_ctor_set(x_43, 2, x_26);
lean_ctor_set(x_43, 3, x_27);
lean_ctor_set(x_43, 4, x_28);
lean_ctor_set(x_43, 5, x_29);
lean_ctor_set_uint8(x_43, sizeof(void*)*6, x_22);
lean_ctor_set_uint8(x_43, sizeof(void*)*6 + 1, x_24);
lean_ctor_set_uint8(x_43, sizeof(void*)*6 + 2, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_21);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_119; 
x_57 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_58 = lean_ctor_get(x_2, 0);
x_59 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_60 = lean_ctor_get(x_2, 1);
x_61 = lean_ctor_get(x_2, 2);
x_62 = lean_ctor_get(x_2, 3);
x_63 = lean_ctor_get(x_2, 4);
x_64 = lean_ctor_get(x_2, 5);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_58, x_65);
x_67 = lean_nat_shiftr(x_1, x_65);
x_119 = lean_nat_dec_eq(x_66, x_67);
if (x_119 == 0)
{
goto block_118;
}
else
{
uint8_t x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_120 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_121 = lean_ctor_get(x_3, 0);
x_122 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_123 = lean_ctor_get(x_3, 1);
x_124 = lean_ctor_get(x_3, 2);
x_125 = lean_ctor_get(x_3, 3);
x_126 = lean_ctor_get(x_3, 4);
x_127 = lean_ctor_get(x_3, 5);
x_128 = lean_nat_add(x_121, x_65);
x_129 = lean_nat_add(x_67, x_65);
x_130 = lean_nat_dec_eq(x_128, x_129);
lean_dec(x_129);
lean_dec(x_128);
if (x_130 == 0)
{
goto block_118;
}
else
{
uint8_t x_131; 
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_121);
lean_dec(x_67);
lean_dec(x_66);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_58);
x_131 = !lean_is_exclusive(x_2);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_132 = lean_ctor_get(x_2, 5);
lean_dec(x_132);
x_133 = lean_ctor_get(x_2, 4);
lean_dec(x_133);
x_134 = lean_ctor_get(x_2, 3);
lean_dec(x_134);
x_135 = lean_ctor_get(x_2, 2);
lean_dec(x_135);
x_136 = lean_ctor_get(x_2, 1);
lean_dec(x_136);
x_137 = lean_ctor_get(x_2, 0);
lean_dec(x_137);
x_138 = !lean_is_exclusive(x_3);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_139 = lean_ctor_get(x_3, 5);
lean_dec(x_139);
x_140 = lean_ctor_get(x_3, 4);
lean_dec(x_140);
x_141 = lean_ctor_get(x_3, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_3, 2);
lean_dec(x_142);
x_143 = lean_ctor_get(x_3, 1);
lean_dec(x_143);
x_144 = lean_ctor_get(x_3, 0);
lean_dec(x_144);
x_145 = lp_SSExactMajority_SSEM_instDecidableEqOpinion(x_4, x_5);
if (x_145 == 0)
{
uint8_t x_146; lean_object* x_147; 
x_146 = 1;
lean_ctor_set(x_3, 5, x_64);
lean_ctor_set(x_3, 4, x_63);
lean_ctor_set(x_3, 3, x_62);
lean_ctor_set(x_3, 2, x_61);
lean_ctor_set(x_3, 1, x_60);
lean_ctor_set(x_3, 0, x_58);
lean_ctor_set_uint8(x_3, sizeof(void*)*6, x_57);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 1, x_59);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 2, x_146);
lean_ctor_set(x_2, 5, x_127);
lean_ctor_set(x_2, 4, x_126);
lean_ctor_set(x_2, 3, x_125);
lean_ctor_set(x_2, 2, x_124);
lean_ctor_set(x_2, 1, x_123);
lean_ctor_set(x_2, 0, x_121);
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_120);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 1, x_122);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 2, x_146);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_3);
lean_ctor_set(x_147, 1, x_2);
return x_147;
}
else
{
uint8_t x_148; lean_object* x_149; 
x_148 = lp_SSExactMajority_SSEM_opinionToAnswer(x_4);
lean_ctor_set(x_3, 5, x_64);
lean_ctor_set(x_3, 4, x_63);
lean_ctor_set(x_3, 3, x_62);
lean_ctor_set(x_3, 2, x_61);
lean_ctor_set(x_3, 1, x_60);
lean_ctor_set(x_3, 0, x_58);
lean_ctor_set_uint8(x_3, sizeof(void*)*6, x_57);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 1, x_59);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 2, x_148);
lean_ctor_set(x_2, 5, x_127);
lean_ctor_set(x_2, 4, x_126);
lean_ctor_set(x_2, 3, x_125);
lean_ctor_set(x_2, 2, x_124);
lean_ctor_set(x_2, 1, x_123);
lean_ctor_set(x_2, 0, x_121);
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_120);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 1, x_122);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 2, x_148);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_3);
lean_ctor_set(x_149, 1, x_2);
return x_149;
}
}
else
{
uint8_t x_150; 
lean_dec(x_3);
x_150 = lp_SSExactMajority_SSEM_instDecidableEqOpinion(x_4, x_5);
if (x_150 == 0)
{
uint8_t x_151; lean_object* x_152; lean_object* x_153; 
x_151 = 1;
x_152 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_152, 0, x_58);
lean_ctor_set(x_152, 1, x_60);
lean_ctor_set(x_152, 2, x_61);
lean_ctor_set(x_152, 3, x_62);
lean_ctor_set(x_152, 4, x_63);
lean_ctor_set(x_152, 5, x_64);
lean_ctor_set_uint8(x_152, sizeof(void*)*6, x_57);
lean_ctor_set_uint8(x_152, sizeof(void*)*6 + 1, x_59);
lean_ctor_set_uint8(x_152, sizeof(void*)*6 + 2, x_151);
lean_ctor_set(x_2, 5, x_127);
lean_ctor_set(x_2, 4, x_126);
lean_ctor_set(x_2, 3, x_125);
lean_ctor_set(x_2, 2, x_124);
lean_ctor_set(x_2, 1, x_123);
lean_ctor_set(x_2, 0, x_121);
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_120);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 1, x_122);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 2, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_2);
return x_153;
}
else
{
uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lp_SSExactMajority_SSEM_opinionToAnswer(x_4);
x_155 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_155, 0, x_58);
lean_ctor_set(x_155, 1, x_60);
lean_ctor_set(x_155, 2, x_61);
lean_ctor_set(x_155, 3, x_62);
lean_ctor_set(x_155, 4, x_63);
lean_ctor_set(x_155, 5, x_64);
lean_ctor_set_uint8(x_155, sizeof(void*)*6, x_57);
lean_ctor_set_uint8(x_155, sizeof(void*)*6 + 1, x_59);
lean_ctor_set_uint8(x_155, sizeof(void*)*6 + 2, x_154);
lean_ctor_set(x_2, 5, x_127);
lean_ctor_set(x_2, 4, x_126);
lean_ctor_set(x_2, 3, x_125);
lean_ctor_set(x_2, 2, x_124);
lean_ctor_set(x_2, 1, x_123);
lean_ctor_set(x_2, 0, x_121);
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_120);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 1, x_122);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 2, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_2);
return x_156;
}
}
}
else
{
lean_object* x_157; uint8_t x_158; 
lean_dec(x_2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_157 = x_3;
} else {
 lean_dec_ref(x_3);
 x_157 = lean_box(0);
}
x_158 = lp_SSExactMajority_SSEM_instDecidableEqOpinion(x_4, x_5);
if (x_158 == 0)
{
uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = 1;
if (lean_is_scalar(x_157)) {
 x_160 = lean_alloc_ctor(0, 6, 3);
} else {
 x_160 = x_157;
}
lean_ctor_set(x_160, 0, x_58);
lean_ctor_set(x_160, 1, x_60);
lean_ctor_set(x_160, 2, x_61);
lean_ctor_set(x_160, 3, x_62);
lean_ctor_set(x_160, 4, x_63);
lean_ctor_set(x_160, 5, x_64);
lean_ctor_set_uint8(x_160, sizeof(void*)*6, x_57);
lean_ctor_set_uint8(x_160, sizeof(void*)*6 + 1, x_59);
lean_ctor_set_uint8(x_160, sizeof(void*)*6 + 2, x_159);
x_161 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_161, 0, x_121);
lean_ctor_set(x_161, 1, x_123);
lean_ctor_set(x_161, 2, x_124);
lean_ctor_set(x_161, 3, x_125);
lean_ctor_set(x_161, 4, x_126);
lean_ctor_set(x_161, 5, x_127);
lean_ctor_set_uint8(x_161, sizeof(void*)*6, x_120);
lean_ctor_set_uint8(x_161, sizeof(void*)*6 + 1, x_122);
lean_ctor_set_uint8(x_161, sizeof(void*)*6 + 2, x_159);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
else
{
uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lp_SSExactMajority_SSEM_opinionToAnswer(x_4);
if (lean_is_scalar(x_157)) {
 x_164 = lean_alloc_ctor(0, 6, 3);
} else {
 x_164 = x_157;
}
lean_ctor_set(x_164, 0, x_58);
lean_ctor_set(x_164, 1, x_60);
lean_ctor_set(x_164, 2, x_61);
lean_ctor_set(x_164, 3, x_62);
lean_ctor_set(x_164, 4, x_63);
lean_ctor_set(x_164, 5, x_64);
lean_ctor_set_uint8(x_164, sizeof(void*)*6, x_57);
lean_ctor_set_uint8(x_164, sizeof(void*)*6 + 1, x_59);
lean_ctor_set_uint8(x_164, sizeof(void*)*6 + 2, x_163);
x_165 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_165, 0, x_121);
lean_ctor_set(x_165, 1, x_123);
lean_ctor_set(x_165, 2, x_124);
lean_ctor_set(x_165, 3, x_125);
lean_ctor_set(x_165, 4, x_126);
lean_ctor_set(x_165, 5, x_127);
lean_ctor_set_uint8(x_165, sizeof(void*)*6, x_120);
lean_ctor_set_uint8(x_165, sizeof(void*)*6 + 1, x_122);
lean_ctor_set_uint8(x_165, sizeof(void*)*6 + 2, x_163);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
}
block_118:
{
uint8_t x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_68 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_69 = lean_ctor_get(x_3, 0);
x_70 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_71 = lean_ctor_get(x_3, 1);
x_72 = lean_ctor_get(x_3, 2);
x_73 = lean_ctor_get(x_3, 3);
x_74 = lean_ctor_get(x_3, 4);
x_75 = lean_ctor_get(x_3, 5);
x_76 = lean_nat_add(x_69, x_65);
x_77 = lean_nat_dec_eq(x_76, x_67);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_67);
lean_dec(x_66);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_2);
lean_ctor_set(x_78, 1, x_3);
return x_78;
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_nat_add(x_67, x_65);
lean_dec(x_67);
x_80 = lean_nat_dec_eq(x_66, x_79);
lean_dec(x_79);
lean_dec(x_66);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_2);
lean_ctor_set(x_81, 1, x_3);
return x_81;
}
else
{
uint8_t x_82; 
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_69);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_58);
x_82 = !lean_is_exclusive(x_2);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_83 = lean_ctor_get(x_2, 5);
lean_dec(x_83);
x_84 = lean_ctor_get(x_2, 4);
lean_dec(x_84);
x_85 = lean_ctor_get(x_2, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_2, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_2, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_2, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_3);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_90 = lean_ctor_get(x_3, 5);
lean_dec(x_90);
x_91 = lean_ctor_get(x_3, 4);
lean_dec(x_91);
x_92 = lean_ctor_get(x_3, 3);
lean_dec(x_92);
x_93 = lean_ctor_get(x_3, 2);
lean_dec(x_93);
x_94 = lean_ctor_get(x_3, 1);
lean_dec(x_94);
x_95 = lean_ctor_get(x_3, 0);
lean_dec(x_95);
x_96 = lp_SSExactMajority_SSEM_instDecidableEqOpinion(x_5, x_4);
if (x_96 == 0)
{
uint8_t x_97; lean_object* x_98; 
x_97 = 1;
lean_ctor_set(x_3, 5, x_64);
lean_ctor_set(x_3, 4, x_63);
lean_ctor_set(x_3, 3, x_62);
lean_ctor_set(x_3, 2, x_61);
lean_ctor_set(x_3, 1, x_60);
lean_ctor_set(x_3, 0, x_58);
lean_ctor_set_uint8(x_3, sizeof(void*)*6, x_57);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 1, x_59);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 2, x_97);
lean_ctor_set(x_2, 5, x_75);
lean_ctor_set(x_2, 4, x_74);
lean_ctor_set(x_2, 3, x_73);
lean_ctor_set(x_2, 2, x_72);
lean_ctor_set(x_2, 1, x_71);
lean_ctor_set(x_2, 0, x_69);
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_68);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 1, x_70);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 2, x_97);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_3);
lean_ctor_set(x_98, 1, x_2);
return x_98;
}
else
{
uint8_t x_99; lean_object* x_100; 
x_99 = lp_SSExactMajority_SSEM_opinionToAnswer(x_5);
lean_ctor_set(x_3, 5, x_64);
lean_ctor_set(x_3, 4, x_63);
lean_ctor_set(x_3, 3, x_62);
lean_ctor_set(x_3, 2, x_61);
lean_ctor_set(x_3, 1, x_60);
lean_ctor_set(x_3, 0, x_58);
lean_ctor_set_uint8(x_3, sizeof(void*)*6, x_57);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 1, x_59);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 2, x_99);
lean_ctor_set(x_2, 5, x_75);
lean_ctor_set(x_2, 4, x_74);
lean_ctor_set(x_2, 3, x_73);
lean_ctor_set(x_2, 2, x_72);
lean_ctor_set(x_2, 1, x_71);
lean_ctor_set(x_2, 0, x_69);
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_68);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 1, x_70);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 2, x_99);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_3);
lean_ctor_set(x_100, 1, x_2);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_3);
x_101 = lp_SSExactMajority_SSEM_instDecidableEqOpinion(x_5, x_4);
if (x_101 == 0)
{
uint8_t x_102; lean_object* x_103; lean_object* x_104; 
x_102 = 1;
x_103 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_103, 0, x_58);
lean_ctor_set(x_103, 1, x_60);
lean_ctor_set(x_103, 2, x_61);
lean_ctor_set(x_103, 3, x_62);
lean_ctor_set(x_103, 4, x_63);
lean_ctor_set(x_103, 5, x_64);
lean_ctor_set_uint8(x_103, sizeof(void*)*6, x_57);
lean_ctor_set_uint8(x_103, sizeof(void*)*6 + 1, x_59);
lean_ctor_set_uint8(x_103, sizeof(void*)*6 + 2, x_102);
lean_ctor_set(x_2, 5, x_75);
lean_ctor_set(x_2, 4, x_74);
lean_ctor_set(x_2, 3, x_73);
lean_ctor_set(x_2, 2, x_72);
lean_ctor_set(x_2, 1, x_71);
lean_ctor_set(x_2, 0, x_69);
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_68);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 1, x_70);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 2, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_2);
return x_104;
}
else
{
uint8_t x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lp_SSExactMajority_SSEM_opinionToAnswer(x_5);
x_106 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_106, 0, x_58);
lean_ctor_set(x_106, 1, x_60);
lean_ctor_set(x_106, 2, x_61);
lean_ctor_set(x_106, 3, x_62);
lean_ctor_set(x_106, 4, x_63);
lean_ctor_set(x_106, 5, x_64);
lean_ctor_set_uint8(x_106, sizeof(void*)*6, x_57);
lean_ctor_set_uint8(x_106, sizeof(void*)*6 + 1, x_59);
lean_ctor_set_uint8(x_106, sizeof(void*)*6 + 2, x_105);
lean_ctor_set(x_2, 5, x_75);
lean_ctor_set(x_2, 4, x_74);
lean_ctor_set(x_2, 3, x_73);
lean_ctor_set(x_2, 2, x_72);
lean_ctor_set(x_2, 1, x_71);
lean_ctor_set(x_2, 0, x_69);
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_68);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 1, x_70);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 2, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_2);
return x_107;
}
}
}
else
{
lean_object* x_108; uint8_t x_109; 
lean_dec(x_2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_108 = x_3;
} else {
 lean_dec_ref(x_3);
 x_108 = lean_box(0);
}
x_109 = lp_SSExactMajority_SSEM_instDecidableEqOpinion(x_5, x_4);
if (x_109 == 0)
{
uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = 1;
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(0, 6, 3);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_58);
lean_ctor_set(x_111, 1, x_60);
lean_ctor_set(x_111, 2, x_61);
lean_ctor_set(x_111, 3, x_62);
lean_ctor_set(x_111, 4, x_63);
lean_ctor_set(x_111, 5, x_64);
lean_ctor_set_uint8(x_111, sizeof(void*)*6, x_57);
lean_ctor_set_uint8(x_111, sizeof(void*)*6 + 1, x_59);
lean_ctor_set_uint8(x_111, sizeof(void*)*6 + 2, x_110);
x_112 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_112, 0, x_69);
lean_ctor_set(x_112, 1, x_71);
lean_ctor_set(x_112, 2, x_72);
lean_ctor_set(x_112, 3, x_73);
lean_ctor_set(x_112, 4, x_74);
lean_ctor_set(x_112, 5, x_75);
lean_ctor_set_uint8(x_112, sizeof(void*)*6, x_68);
lean_ctor_set_uint8(x_112, sizeof(void*)*6 + 1, x_70);
lean_ctor_set_uint8(x_112, sizeof(void*)*6 + 2, x_110);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
else
{
uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lp_SSExactMajority_SSEM_opinionToAnswer(x_5);
if (lean_is_scalar(x_108)) {
 x_115 = lean_alloc_ctor(0, 6, 3);
} else {
 x_115 = x_108;
}
lean_ctor_set(x_115, 0, x_58);
lean_ctor_set(x_115, 1, x_60);
lean_ctor_set(x_115, 2, x_61);
lean_ctor_set(x_115, 3, x_62);
lean_ctor_set(x_115, 4, x_63);
lean_ctor_set(x_115, 5, x_64);
lean_ctor_set_uint8(x_115, sizeof(void*)*6, x_57);
lean_ctor_set_uint8(x_115, sizeof(void*)*6 + 1, x_59);
lean_ctor_set_uint8(x_115, sizeof(void*)*6 + 2, x_114);
x_116 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_116, 0, x_69);
lean_ctor_set(x_116, 1, x_71);
lean_ctor_set(x_116, 2, x_72);
lean_ctor_set(x_116, 3, x_73);
lean_ctor_set(x_116, 4, x_74);
lean_ctor_set(x_116, 5, x_75);
lean_ctor_set_uint8(x_116, sizeof(void*)*6, x_68);
lean_ctor_set_uint8(x_116, sizeof(void*)*6 + 1, x_70);
lean_ctor_set_uint8(x_116, sizeof(void*)*6 + 2, x_114);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__decide___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_4);
x_7 = lean_unbox(x_5);
x_8 = lp_SSExactMajority_SSEM_phase4__decide(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__propagate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_5 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_12 = lean_ctor_get(x_3, 4);
x_13 = lean_ctor_get(x_3, 5);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_6, x_44);
x_46 = lp_SSExactMajority_SSEM_ceilHalf(x_1);
x_47 = lean_nat_dec_eq(x_45, x_46);
if (x_47 == 0)
{
uint8_t x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_48 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_49 = lean_ctor_get(x_4, 0);
x_50 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_51 = lean_ctor_get(x_4, 1);
x_52 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 2);
x_53 = lean_ctor_get(x_4, 2);
x_54 = lean_ctor_get(x_4, 3);
x_55 = lean_ctor_get(x_4, 4);
x_56 = lean_ctor_get(x_4, 5);
x_57 = lean_nat_add(x_49, x_44);
x_58 = lean_nat_dec_eq(x_57, x_46);
lean_dec(x_46);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_45);
lean_dec(x_2);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_3);
lean_ctor_set(x_59, 1, x_4);
return x_59;
}
else
{
uint8_t x_60; 
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_49);
x_60 = lean_nat_dec_eq(x_45, x_1);
lean_dec(x_45);
if (x_60 == 0)
{
x_14 = x_4;
x_15 = x_49;
x_16 = x_52;
x_17 = x_53;
x_18 = x_54;
x_19 = x_55;
x_20 = x_56;
goto block_43;
}
else
{
uint8_t x_61; 
lean_inc(x_51);
x_61 = !lean_is_exclusive(x_4);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_4, 5);
lean_dec(x_62);
x_63 = lean_ctor_get(x_4, 4);
lean_dec(x_63);
x_64 = lean_ctor_get(x_4, 3);
lean_dec(x_64);
x_65 = lean_ctor_get(x_4, 2);
lean_dec(x_65);
x_66 = lean_ctor_get(x_4, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_4, 0);
lean_dec(x_67);
x_68 = lean_nat_sub(x_53, x_44);
lean_dec(x_53);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_68);
lean_inc(x_49);
lean_ctor_set(x_4, 2, x_68);
x_14 = x_4;
x_15 = x_49;
x_16 = x_52;
x_17 = x_68;
x_18 = x_54;
x_19 = x_55;
x_20 = x_56;
goto block_43;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_4);
x_69 = lean_nat_sub(x_53, x_44);
lean_dec(x_53);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_69);
lean_inc(x_49);
x_70 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_70, 0, x_49);
lean_ctor_set(x_70, 1, x_51);
lean_ctor_set(x_70, 2, x_69);
lean_ctor_set(x_70, 3, x_54);
lean_ctor_set(x_70, 4, x_55);
lean_ctor_set(x_70, 5, x_56);
lean_ctor_set_uint8(x_70, sizeof(void*)*6, x_48);
lean_ctor_set_uint8(x_70, sizeof(void*)*6 + 1, x_50);
lean_ctor_set_uint8(x_70, sizeof(void*)*6 + 2, x_52);
x_14 = x_70;
x_15 = x_49;
x_16 = x_52;
x_17 = x_69;
x_18 = x_54;
x_19 = x_55;
x_20 = x_56;
goto block_43;
}
}
}
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_107; uint8_t x_108; 
lean_dec(x_46);
lean_dec(x_45);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_71 = lean_ctor_get(x_4, 0);
x_72 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 2);
x_73 = lean_ctor_get(x_4, 2);
x_74 = lean_ctor_get(x_4, 3);
x_75 = lean_ctor_get(x_4, 4);
x_76 = lean_ctor_get(x_4, 5);
x_107 = lean_nat_add(x_71, x_44);
x_108 = lean_nat_dec_eq(x_107, x_1);
lean_dec(x_107);
if (x_108 == 0)
{
x_77 = x_3;
x_78 = x_6;
x_79 = x_9;
x_80 = x_10;
x_81 = x_11;
x_82 = x_12;
x_83 = x_13;
goto block_106;
}
else
{
uint8_t x_109; 
lean_inc(x_8);
x_109 = !lean_is_exclusive(x_3);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_110 = lean_ctor_get(x_3, 5);
lean_dec(x_110);
x_111 = lean_ctor_get(x_3, 4);
lean_dec(x_111);
x_112 = lean_ctor_get(x_3, 3);
lean_dec(x_112);
x_113 = lean_ctor_get(x_3, 2);
lean_dec(x_113);
x_114 = lean_ctor_get(x_3, 1);
lean_dec(x_114);
x_115 = lean_ctor_get(x_3, 0);
lean_dec(x_115);
x_116 = lean_nat_sub(x_10, x_44);
lean_dec(x_10);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_116);
lean_inc(x_6);
lean_ctor_set(x_3, 2, x_116);
x_77 = x_3;
x_78 = x_6;
x_79 = x_9;
x_80 = x_116;
x_81 = x_11;
x_82 = x_12;
x_83 = x_13;
goto block_106;
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_3);
x_117 = lean_nat_sub(x_10, x_44);
lean_dec(x_10);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_117);
lean_inc(x_6);
x_118 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_118, 0, x_6);
lean_ctor_set(x_118, 1, x_8);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_11);
lean_ctor_set(x_118, 4, x_12);
lean_ctor_set(x_118, 5, x_13);
lean_ctor_set_uint8(x_118, sizeof(void*)*6, x_5);
lean_ctor_set_uint8(x_118, sizeof(void*)*6 + 1, x_7);
lean_ctor_set_uint8(x_118, sizeof(void*)*6 + 2, x_9);
x_77 = x_118;
x_78 = x_6;
x_79 = x_9;
x_80 = x_117;
x_81 = x_11;
x_82 = x_12;
x_83 = x_13;
goto block_106;
}
}
block_106:
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_eq(x_80, x_84);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_2);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_77);
lean_ctor_set(x_86, 1, x_4);
return x_86;
}
else
{
uint8_t x_87; 
x_87 = lp_SSExactMajority_SSEM_instDecidableEqAnswer(x_79, x_72);
if (x_87 == 0)
{
if (x_85 == 0)
{
lean_object* x_88; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_2);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_77);
lean_ctor_set(x_88, 1, x_4);
return x_88;
}
else
{
uint8_t x_89; 
lean_dec_ref(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_71);
x_89 = !lean_is_exclusive(x_4);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_90 = lean_ctor_get(x_4, 5);
lean_dec(x_90);
x_91 = lean_ctor_get(x_4, 4);
lean_dec(x_91);
x_92 = lean_ctor_get(x_4, 3);
lean_dec(x_92);
x_93 = lean_ctor_get(x_4, 2);
lean_dec(x_93);
x_94 = lean_ctor_get(x_4, 1);
lean_dec(x_94);
x_95 = lean_ctor_get(x_4, 0);
lean_dec(x_95);
x_96 = 0;
x_97 = 0;
lean_inc(x_2);
lean_ctor_set(x_4, 5, x_83);
lean_ctor_set(x_4, 4, x_82);
lean_ctor_set(x_4, 3, x_81);
lean_ctor_set(x_4, 2, x_80);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_78);
lean_ctor_set_uint8(x_4, sizeof(void*)*6, x_96);
lean_ctor_set_uint8(x_4, sizeof(void*)*6 + 1, x_97);
lean_ctor_set_uint8(x_4, sizeof(void*)*6 + 2, x_79);
x_98 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_98, 0, x_71);
lean_ctor_set(x_98, 1, x_2);
lean_ctor_set(x_98, 2, x_73);
lean_ctor_set(x_98, 3, x_74);
lean_ctor_set(x_98, 4, x_75);
lean_ctor_set(x_98, 5, x_76);
lean_ctor_set_uint8(x_98, sizeof(void*)*6, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*6 + 1, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*6 + 2, x_79);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_4);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
else
{
uint8_t x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_4);
x_100 = 0;
x_101 = 0;
lean_inc(x_2);
x_102 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_102, 0, x_78);
lean_ctor_set(x_102, 1, x_2);
lean_ctor_set(x_102, 2, x_80);
lean_ctor_set(x_102, 3, x_81);
lean_ctor_set(x_102, 4, x_82);
lean_ctor_set(x_102, 5, x_83);
lean_ctor_set_uint8(x_102, sizeof(void*)*6, x_100);
lean_ctor_set_uint8(x_102, sizeof(void*)*6 + 1, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*6 + 2, x_79);
x_103 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_103, 0, x_71);
lean_ctor_set(x_103, 1, x_2);
lean_ctor_set(x_103, 2, x_73);
lean_ctor_set(x_103, 3, x_74);
lean_ctor_set(x_103, 4, x_75);
lean_ctor_set(x_103, 5, x_76);
lean_ctor_set_uint8(x_103, sizeof(void*)*6, x_100);
lean_ctor_set_uint8(x_103, sizeof(void*)*6 + 1, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*6 + 2, x_79);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_2);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_77);
lean_ctor_set(x_105, 1, x_4);
return x_105;
}
}
}
}
block_43:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_17, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lp_SSExactMajority_SSEM_instDecidableEqAnswer(x_16, x_9);
if (x_24 == 0)
{
if (x_22 == 0)
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_14);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_3, 5);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 4);
lean_dec(x_28);
x_29 = lean_ctor_get(x_3, 3);
lean_dec(x_29);
x_30 = lean_ctor_get(x_3, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_3, 0);
lean_dec(x_32);
x_33 = 0;
x_34 = 0;
lean_inc(x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*6, x_33);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 1, x_34);
lean_ctor_set_uint8(x_3, sizeof(void*)*6 + 2, x_16);
x_35 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_35, 0, x_15);
lean_ctor_set(x_35, 1, x_2);
lean_ctor_set(x_35, 2, x_17);
lean_ctor_set(x_35, 3, x_18);
lean_ctor_set(x_35, 4, x_19);
lean_ctor_set(x_35, 5, x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*6, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*6 + 1, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*6 + 2, x_16);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
else
{
uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_3);
x_37 = 0;
x_38 = 0;
lean_inc(x_2);
x_39 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_39, 0, x_6);
lean_ctor_set(x_39, 1, x_2);
lean_ctor_set(x_39, 2, x_10);
lean_ctor_set(x_39, 3, x_11);
lean_ctor_set(x_39, 4, x_12);
lean_ctor_set(x_39, 5, x_13);
lean_ctor_set_uint8(x_39, sizeof(void*)*6, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*6 + 1, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*6 + 2, x_16);
x_40 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_40, 0, x_15);
lean_ctor_set(x_40, 1, x_2);
lean_ctor_set(x_40, 2, x_17);
lean_ctor_set(x_40, 3, x_18);
lean_ctor_set(x_40, 4, x_19);
lean_ctor_set(x_40, 5, x_20);
lean_ctor_set_uint8(x_40, sizeof(void*)*6, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*6 + 1, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*6 + 2, x_16);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_14);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__propagate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_SSExactMajority_SSEM_phase4__propagate(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__phase4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
x_9 = 1;
x_10 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
x_12 = lp_SSExactMajority_SSEM_instDecidableEqRole(x_11, x_9);
if (x_12 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_7);
lean_inc(x_6);
lean_dec_ref(x_3);
x_13 = lp_SSExactMajority_SSEM_phase4__swap___redArg(x_6, x_7, x_4, x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lp_SSExactMajority_SSEM_phase4__decide(x_1, x_14, x_15, x_4, x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lp_SSExactMajority_SSEM_phase4__propagate(x_1, x_2, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__phase4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_4);
x_7 = lean_unbox(x_5);
x_8 = lp_SSExactMajority_SSEM_transitionPEM__phase4(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lp_SSExactMajority_SSEM_transitionPEM__prePhase4___redArg(x_1, x_2, x_4, x_8, x_10);
x_13 = lean_unbox(x_9);
lean_dec(x_9);
x_14 = lean_unbox(x_11);
lean_dec(x_11);
x_15 = lp_SSExactMajority_SSEM_transitionPEM__phase4(x_1, x_3, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_SSExactMajority_SSEM_transitionPEM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_outputPEM___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lp_SSExactMajority_SSEM_agentOutput___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_outputPEM(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lp_SSExactMajority_SSEM_outputPEM___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_outputPEM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_SSExactMajority_SSEM_outputPEM(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_outputPEM___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_SSExactMajority_SSEM_outputPEM___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_protocolPEM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_transitionPEM___boxed), 5, 4);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
x_6 = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_outputPEM___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Protocol(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_State(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_Transition(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Defs_Protocol(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Protocol_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
