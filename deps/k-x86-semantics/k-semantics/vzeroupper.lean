def vzeroupper : instruction :=
  definst "vzeroupper" $ do
    instr_pat $
     let action : semantics Unit := do
      let v_0 <- getRegister ymm9;
      let (v_1 : expression (bv 128)) <- eval (extract v_0 128 256);
      let v_2 <- eval (concat (expression.bv_nat 128 0) v_1);
      let v_3 <- getRegister ymm8;
      let (v_4 : expression (bv 128)) <- eval (extract v_3 128 256);
      let v_5 <- eval (concat (expression.bv_nat 128 0) v_4);
      let v_6 <- getRegister ymm7;
      let (v_7 : expression (bv 128)) <- eval (extract v_6 128 256);
      let v_8 <- eval (concat (expression.bv_nat 128 0) v_7);
      let v_9 <- getRegister ymm6;
      let (v_10 : expression (bv 128)) <- eval (extract v_9 128 256);
      let v_11 <- eval (concat (expression.bv_nat 128 0) v_10);
      let v_12 <- getRegister ymm5;
      let (v_13 : expression (bv 128)) <- eval (extract v_12 128 256);
      let v_14 <- eval (concat (expression.bv_nat 128 0) v_13);
      let v_15 <- getRegister ymm4;
      let (v_16 : expression (bv 128)) <- eval (extract v_15 128 256);
      let v_17 <- eval (concat (expression.bv_nat 128 0) v_16);
      let v_18 <- getRegister ymm3;
      let (v_19 : expression (bv 128)) <- eval (extract v_18 128 256);
      let v_20 <- eval (concat (expression.bv_nat 128 0) v_19);
      let v_21 <- getRegister ymm2;
      let (v_22 : expression (bv 128)) <- eval (extract v_21 128 256);
      let v_23 <- eval (concat (expression.bv_nat 128 0) v_22);
      let v_24 <- getRegister ymm15;
      let (v_25 : expression (bv 128)) <- eval (extract v_24 128 256);
      let v_26 <- eval (concat (expression.bv_nat 128 0) v_25);
      let v_27 <- getRegister ymm14;
      let (v_28 : expression (bv 128)) <- eval (extract v_27 128 256);
      let v_29 <- eval (concat (expression.bv_nat 128 0) v_28);
      let v_30 <- getRegister ymm13;
      let (v_31 : expression (bv 128)) <- eval (extract v_30 128 256);
      let v_32 <- eval (concat (expression.bv_nat 128 0) v_31);
      let v_33 <- getRegister ymm12;
      let (v_34 : expression (bv 128)) <- eval (extract v_33 128 256);
      let v_35 <- eval (concat (expression.bv_nat 128 0) v_34);
      let v_36 <- getRegister ymm11;
      let (v_37 : expression (bv 128)) <- eval (extract v_36 128 256);
      let v_38 <- eval (concat (expression.bv_nat 128 0) v_37);
      let v_39 <- getRegister ymm10;
      let (v_40 : expression (bv 128)) <- eval (extract v_39 128 256);
      let v_41 <- eval (concat (expression.bv_nat 128 0) v_40);
      let v_42 <- getRegister ymm1;
      let (v_43 : expression (bv 128)) <- eval (extract v_42 128 256);
      let v_44 <- eval (concat (expression.bv_nat 128 0) v_43);
      let v_45 <- getRegister ymm0;
      let (v_46 : expression (bv 128)) <- eval (extract v_45 128 256);
      let v_47 <- eval (concat (expression.bv_nat 128 0) v_46);
      setRegister ymm0 v_47;
      setRegister ymm1 v_44;
      setRegister ymm10 v_41;
      setRegister ymm11 v_38;
      setRegister ymm12 v_35;
      setRegister ymm13 v_32;
      setRegister ymm14 v_29;
      setRegister ymm15 v_26;
      setRegister ymm2 v_23;
      setRegister ymm3 v_20;
      setRegister ymm4 v_17;
      setRegister ymm5 v_14;
      setRegister ymm6 v_11;
      setRegister ymm7 v_8;
      setRegister ymm8 v_5;
      setRegister ymm9 v_2;
      pure ()
     action
