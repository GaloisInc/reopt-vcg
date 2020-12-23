def bzhil : instruction :=
  definst "bzhil" $ do
    instr_pat $ fun (r32_0 : reg (bv 32)) (mem_1 : Mem) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg r32_0);
      let (v_4 : expression (bv 8)) <- eval (extract v_3 24 32);
      let v_5 <- eval (ult v_4 (expression.bv_nat 8 32));
      let v_6 <- evaluateAddress mem_1;
      let v_7 <- load v_6 4;
      let (v_8 : expression (bv 31)) <- eval (extract v_7 1 32);
      let v_9 <- eval (concat (expression.bv_nat 1 0) v_8);
      let (v_10 : expression (bv 30)) <- eval (extract v_7 2 32);
      let v_11 <- eval (concat (expression.bv_nat 2 0) v_10);
      let (v_12 : expression (bv 29)) <- eval (extract v_7 3 32);
      let v_13 <- eval (concat (expression.bv_nat 3 0) v_12);
      let (v_14 : expression (bv 28)) <- eval (extract v_7 4 32);
      let v_15 <- eval (concat (expression.bv_nat 4 0) v_14);
      let (v_16 : expression (bv 27)) <- eval (extract v_7 5 32);
      let v_17 <- eval (concat (expression.bv_nat 5 0) v_16);
      let (v_18 : expression (bv 26)) <- eval (extract v_7 6 32);
      let v_19 <- eval (concat (expression.bv_nat 6 0) v_18);
      let (v_20 : expression (bv 25)) <- eval (extract v_7 7 32);
      let v_21 <- eval (concat (expression.bv_nat 7 0) v_20);
      let (v_22 : expression (bv 24)) <- eval (extract v_7 8 32);
      let v_23 <- eval (concat (expression.bv_nat 8 0) v_22);
      let (v_24 : expression (bv 23)) <- eval (extract v_7 9 32);
      let v_25 <- eval (concat (expression.bv_nat 9 0) v_24);
      let (v_26 : expression (bv 22)) <- eval (extract v_7 10 32);
      let v_27 <- eval (concat (expression.bv_nat 10 0) v_26);
      let (v_28 : expression (bv 21)) <- eval (extract v_7 11 32);
      let v_29 <- eval (concat (expression.bv_nat 11 0) v_28);
      let (v_30 : expression (bv 20)) <- eval (extract v_7 12 32);
      let v_31 <- eval (concat (expression.bv_nat 12 0) v_30);
      let (v_32 : expression (bv 19)) <- eval (extract v_7 13 32);
      let v_33 <- eval (concat (expression.bv_nat 13 0) v_32);
      let (v_34 : expression (bv 18)) <- eval (extract v_7 14 32);
      let v_35 <- eval (concat (expression.bv_nat 14 0) v_34);
      let (v_36 : expression (bv 17)) <- eval (extract v_7 15 32);
      let v_37 <- eval (concat (expression.bv_nat 15 0) v_36);
      let (v_38 : expression (bv 16)) <- eval (extract v_7 16 32);
      let v_39 <- eval (concat (expression.bv_nat 16 0) v_38);
      let (v_40 : expression (bv 15)) <- eval (extract v_7 17 32);
      let v_41 <- eval (concat (expression.bv_nat 17 0) v_40);
      let (v_42 : expression (bv 14)) <- eval (extract v_7 18 32);
      let v_43 <- eval (concat (expression.bv_nat 18 0) v_42);
      let (v_44 : expression (bv 13)) <- eval (extract v_7 19 32);
      let v_45 <- eval (concat (expression.bv_nat 19 0) v_44);
      let (v_46 : expression (bv 12)) <- eval (extract v_7 20 32);
      let v_47 <- eval (concat (expression.bv_nat 20 0) v_46);
      let (v_48 : expression (bv 11)) <- eval (extract v_7 21 32);
      let v_49 <- eval (concat (expression.bv_nat 21 0) v_48);
      let (v_50 : expression (bv 10)) <- eval (extract v_7 22 32);
      let v_51 <- eval (concat (expression.bv_nat 22 0) v_50);
      let (v_52 : expression (bv 9)) <- eval (extract v_7 23 32);
      let v_53 <- eval (concat (expression.bv_nat 23 0) v_52);
      let (v_54 : expression (bv 8)) <- eval (extract v_7 24 32);
      let v_55 <- eval (concat (expression.bv_nat 24 0) v_54);
      let (v_56 : expression (bv 7)) <- eval (extract v_7 25 32);
      let v_57 <- eval (concat (expression.bv_nat 25 0) v_56);
      let (v_58 : expression (bv 6)) <- eval (extract v_7 26 32);
      let v_59 <- eval (concat (expression.bv_nat 26 0) v_58);
      let (v_60 : expression (bv 5)) <- eval (extract v_7 27 32);
      let v_61 <- eval (concat (expression.bv_nat 27 0) v_60);
      let (v_62 : expression (bv 4)) <- eval (extract v_7 28 32);
      let v_63 <- eval (concat (expression.bv_nat 28 0) v_62);
      let (v_64 : expression (bv 3)) <- eval (extract v_7 29 32);
      let v_65 <- eval (concat (expression.bv_nat 29 0) v_64);
      let (v_66 : expression (bv 2)) <- eval (extract v_7 30 32);
      let v_67 <- eval (concat (expression.bv_nat 30 0) v_66);
      let (v_68 : expression (bv 1)) <- eval (extract v_7 31 32);
      let v_69 <- eval (concat (expression.bv_nat 31 0) (mux (eq v_4 (expression.bv_nat 8 1)) v_68 (expression.bv_nat 1 0)));
      let v_70 <- eval (mux v_5 (mux (eq v_4 (expression.bv_nat 8 31)) v_9 (mux (eq v_4 (expression.bv_nat 8 30)) v_11 (mux (eq v_4 (expression.bv_nat 8 29)) v_13 (mux (eq v_4 (expression.bv_nat 8 28)) v_15 (mux (eq v_4 (expression.bv_nat 8 27)) v_17 (mux (eq v_4 (expression.bv_nat 8 26)) v_19 (mux (eq v_4 (expression.bv_nat 8 25)) v_21 (mux (eq v_4 (expression.bv_nat 8 24)) v_23 (mux (eq v_4 (expression.bv_nat 8 23)) v_25 (mux (eq v_4 (expression.bv_nat 8 22)) v_27 (mux (eq v_4 (expression.bv_nat 8 21)) v_29 (mux (eq v_4 (expression.bv_nat 8 20)) v_31 (mux (eq v_4 (expression.bv_nat 8 19)) v_33 (mux (eq v_4 (expression.bv_nat 8 18)) v_35 (mux (eq v_4 (expression.bv_nat 8 17)) v_37 (mux (eq v_4 (expression.bv_nat 8 16)) v_39 (mux (eq v_4 (expression.bv_nat 8 15)) v_41 (mux (eq v_4 (expression.bv_nat 8 14)) v_43 (mux (eq v_4 (expression.bv_nat 8 13)) v_45 (mux (eq v_4 (expression.bv_nat 8 12)) v_47 (mux (eq v_4 (expression.bv_nat 8 11)) v_49 (mux (eq v_4 (expression.bv_nat 8 10)) v_51 (mux (eq v_4 (expression.bv_nat 8 9)) v_53 (mux (eq v_4 (expression.bv_nat 8 8)) v_55 (mux (eq v_4 (expression.bv_nat 8 7)) v_57 (mux (eq v_4 (expression.bv_nat 8 6)) v_59 (mux (eq v_4 (expression.bv_nat 8 5)) v_61 (mux (eq v_4 (expression.bv_nat 8 4)) v_63 (mux (eq v_4 (expression.bv_nat 8 3)) v_65 (mux (eq v_4 (expression.bv_nat 8 2)) v_67 v_69)))))))))))))))))))))))))))))) v_7);
      setRegister (lhs.of_reg r32_2) v_70;
      setRegister af undef;
      setRegister cf (uge v_4 (expression.bv_nat 8 32));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (mux v_5 bit_zero (isBitSet v_7 0));
      setRegister zf (zeroFlag v_70);
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg r32_0);
      let (v_4 : expression (bv 8)) <- eval (extract v_3 24 32);
      let v_5 <- eval (ult v_4 (expression.bv_nat 8 32));
      let v_6 <- getRegister (lhs.of_reg r32_1);
      let (v_7 : expression (bv 31)) <- eval (extract v_6 1 32);
      let v_8 <- eval (concat (expression.bv_nat 1 0) v_7);
      let (v_9 : expression (bv 30)) <- eval (extract v_6 2 32);
      let v_10 <- eval (concat (expression.bv_nat 2 0) v_9);
      let (v_11 : expression (bv 29)) <- eval (extract v_6 3 32);
      let v_12 <- eval (concat (expression.bv_nat 3 0) v_11);
      let (v_13 : expression (bv 28)) <- eval (extract v_6 4 32);
      let v_14 <- eval (concat (expression.bv_nat 4 0) v_13);
      let (v_15 : expression (bv 27)) <- eval (extract v_6 5 32);
      let v_16 <- eval (concat (expression.bv_nat 5 0) v_15);
      let (v_17 : expression (bv 26)) <- eval (extract v_6 6 32);
      let v_18 <- eval (concat (expression.bv_nat 6 0) v_17);
      let (v_19 : expression (bv 25)) <- eval (extract v_6 7 32);
      let v_20 <- eval (concat (expression.bv_nat 7 0) v_19);
      let (v_21 : expression (bv 24)) <- eval (extract v_6 8 32);
      let v_22 <- eval (concat (expression.bv_nat 8 0) v_21);
      let (v_23 : expression (bv 23)) <- eval (extract v_6 9 32);
      let v_24 <- eval (concat (expression.bv_nat 9 0) v_23);
      let (v_25 : expression (bv 22)) <- eval (extract v_6 10 32);
      let v_26 <- eval (concat (expression.bv_nat 10 0) v_25);
      let (v_27 : expression (bv 21)) <- eval (extract v_6 11 32);
      let v_28 <- eval (concat (expression.bv_nat 11 0) v_27);
      let (v_29 : expression (bv 20)) <- eval (extract v_6 12 32);
      let v_30 <- eval (concat (expression.bv_nat 12 0) v_29);
      let (v_31 : expression (bv 19)) <- eval (extract v_6 13 32);
      let v_32 <- eval (concat (expression.bv_nat 13 0) v_31);
      let (v_33 : expression (bv 18)) <- eval (extract v_6 14 32);
      let v_34 <- eval (concat (expression.bv_nat 14 0) v_33);
      let (v_35 : expression (bv 17)) <- eval (extract v_6 15 32);
      let v_36 <- eval (concat (expression.bv_nat 15 0) v_35);
      let (v_37 : expression (bv 16)) <- eval (extract v_6 16 32);
      let v_38 <- eval (concat (expression.bv_nat 16 0) v_37);
      let (v_39 : expression (bv 15)) <- eval (extract v_6 17 32);
      let v_40 <- eval (concat (expression.bv_nat 17 0) v_39);
      let (v_41 : expression (bv 14)) <- eval (extract v_6 18 32);
      let v_42 <- eval (concat (expression.bv_nat 18 0) v_41);
      let (v_43 : expression (bv 13)) <- eval (extract v_6 19 32);
      let v_44 <- eval (concat (expression.bv_nat 19 0) v_43);
      let (v_45 : expression (bv 12)) <- eval (extract v_6 20 32);
      let v_46 <- eval (concat (expression.bv_nat 20 0) v_45);
      let (v_47 : expression (bv 11)) <- eval (extract v_6 21 32);
      let v_48 <- eval (concat (expression.bv_nat 21 0) v_47);
      let (v_49 : expression (bv 10)) <- eval (extract v_6 22 32);
      let v_50 <- eval (concat (expression.bv_nat 22 0) v_49);
      let (v_51 : expression (bv 9)) <- eval (extract v_6 23 32);
      let v_52 <- eval (concat (expression.bv_nat 23 0) v_51);
      let (v_53 : expression (bv 8)) <- eval (extract v_6 24 32);
      let v_54 <- eval (concat (expression.bv_nat 24 0) v_53);
      let (v_55 : expression (bv 7)) <- eval (extract v_6 25 32);
      let v_56 <- eval (concat (expression.bv_nat 25 0) v_55);
      let (v_57 : expression (bv 6)) <- eval (extract v_6 26 32);
      let v_58 <- eval (concat (expression.bv_nat 26 0) v_57);
      let (v_59 : expression (bv 5)) <- eval (extract v_6 27 32);
      let v_60 <- eval (concat (expression.bv_nat 27 0) v_59);
      let (v_61 : expression (bv 4)) <- eval (extract v_6 28 32);
      let v_62 <- eval (concat (expression.bv_nat 28 0) v_61);
      let (v_63 : expression (bv 3)) <- eval (extract v_6 29 32);
      let v_64 <- eval (concat (expression.bv_nat 29 0) v_63);
      let (v_65 : expression (bv 2)) <- eval (extract v_6 30 32);
      let v_66 <- eval (concat (expression.bv_nat 30 0) v_65);
      let (v_67 : expression (bv 1)) <- eval (extract v_6 31 32);
      let v_68 <- eval (concat (expression.bv_nat 31 0) (mux (eq v_4 (expression.bv_nat 8 1)) v_67 (expression.bv_nat 1 0)));
      let v_69 <- eval (mux v_5 (mux (eq v_4 (expression.bv_nat 8 31)) v_8 (mux (eq v_4 (expression.bv_nat 8 30)) v_10 (mux (eq v_4 (expression.bv_nat 8 29)) v_12 (mux (eq v_4 (expression.bv_nat 8 28)) v_14 (mux (eq v_4 (expression.bv_nat 8 27)) v_16 (mux (eq v_4 (expression.bv_nat 8 26)) v_18 (mux (eq v_4 (expression.bv_nat 8 25)) v_20 (mux (eq v_4 (expression.bv_nat 8 24)) v_22 (mux (eq v_4 (expression.bv_nat 8 23)) v_24 (mux (eq v_4 (expression.bv_nat 8 22)) v_26 (mux (eq v_4 (expression.bv_nat 8 21)) v_28 (mux (eq v_4 (expression.bv_nat 8 20)) v_30 (mux (eq v_4 (expression.bv_nat 8 19)) v_32 (mux (eq v_4 (expression.bv_nat 8 18)) v_34 (mux (eq v_4 (expression.bv_nat 8 17)) v_36 (mux (eq v_4 (expression.bv_nat 8 16)) v_38 (mux (eq v_4 (expression.bv_nat 8 15)) v_40 (mux (eq v_4 (expression.bv_nat 8 14)) v_42 (mux (eq v_4 (expression.bv_nat 8 13)) v_44 (mux (eq v_4 (expression.bv_nat 8 12)) v_46 (mux (eq v_4 (expression.bv_nat 8 11)) v_48 (mux (eq v_4 (expression.bv_nat 8 10)) v_50 (mux (eq v_4 (expression.bv_nat 8 9)) v_52 (mux (eq v_4 (expression.bv_nat 8 8)) v_54 (mux (eq v_4 (expression.bv_nat 8 7)) v_56 (mux (eq v_4 (expression.bv_nat 8 6)) v_58 (mux (eq v_4 (expression.bv_nat 8 5)) v_60 (mux (eq v_4 (expression.bv_nat 8 4)) v_62 (mux (eq v_4 (expression.bv_nat 8 3)) v_64 (mux (eq v_4 (expression.bv_nat 8 2)) v_66 v_68)))))))))))))))))))))))))))))) v_6);
      setRegister (lhs.of_reg r32_2) v_69;
      setRegister af undef;
      setRegister cf (uge v_4 (expression.bv_nat 8 32));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (mux v_5 bit_zero (isBitSet v_6 0));
      setRegister zf (zeroFlag v_69);
      pure ()
     action
