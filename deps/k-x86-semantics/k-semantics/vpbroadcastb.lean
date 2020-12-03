def vpbroadcastb : instruction :=
  definst "vpbroadcastb" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 1;
      let v_4 <- eval (concat v_3 v_3);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat v_3 v_5);
      let v_7 <- eval (concat v_3 v_6);
      let v_8 <- eval (concat v_3 v_7);
      let v_9 <- eval (concat v_3 v_8);
      let v_10 <- eval (concat v_3 v_9);
      let v_11 <- eval (concat v_3 v_10);
      let v_12 <- eval (concat v_3 v_11);
      let v_13 <- eval (concat v_3 v_12);
      let v_14 <- eval (concat v_3 v_13);
      let v_15 <- eval (concat v_3 v_14);
      let v_16 <- eval (concat v_3 v_15);
      let v_17 <- eval (concat v_3 v_16);
      let v_18 <- eval (concat v_3 v_17);
      setRegister (lhs.of_reg xmm_1) v_18;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 1;
      let v_4 <- eval (concat v_3 v_3);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat v_3 v_5);
      let v_7 <- eval (concat v_3 v_6);
      let v_8 <- eval (concat v_3 v_7);
      let v_9 <- eval (concat v_3 v_8);
      let v_10 <- eval (concat v_3 v_9);
      let v_11 <- eval (concat v_3 v_10);
      let v_12 <- eval (concat v_3 v_11);
      let v_13 <- eval (concat v_3 v_12);
      let v_14 <- eval (concat v_3 v_13);
      let v_15 <- eval (concat v_3 v_14);
      let v_16 <- eval (concat v_3 v_15);
      let v_17 <- eval (concat v_3 v_16);
      let v_18 <- eval (concat v_3 v_17);
      let v_19 <- eval (concat v_3 v_18);
      let v_20 <- eval (concat v_3 v_19);
      let v_21 <- eval (concat v_3 v_20);
      let v_22 <- eval (concat v_3 v_21);
      let v_23 <- eval (concat v_3 v_22);
      let v_24 <- eval (concat v_3 v_23);
      let v_25 <- eval (concat v_3 v_24);
      let v_26 <- eval (concat v_3 v_25);
      let v_27 <- eval (concat v_3 v_26);
      let v_28 <- eval (concat v_3 v_27);
      let v_29 <- eval (concat v_3 v_28);
      let v_30 <- eval (concat v_3 v_29);
      let v_31 <- eval (concat v_3 v_30);
      let v_32 <- eval (concat v_3 v_31);
      let v_33 <- eval (concat v_3 v_32);
      let v_34 <- eval (concat v_3 v_33);
      setRegister (lhs.of_reg ymm_1) v_34;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 8)) <- eval (extract v_2 120 128);
      let v_4 <- eval (concat v_3 v_3);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat v_3 v_5);
      let v_7 <- eval (concat v_3 v_6);
      let v_8 <- eval (concat v_3 v_7);
      let v_9 <- eval (concat v_3 v_8);
      let v_10 <- eval (concat v_3 v_9);
      let v_11 <- eval (concat v_3 v_10);
      let v_12 <- eval (concat v_3 v_11);
      let v_13 <- eval (concat v_3 v_12);
      let v_14 <- eval (concat v_3 v_13);
      let v_15 <- eval (concat v_3 v_14);
      let v_16 <- eval (concat v_3 v_15);
      let v_17 <- eval (concat v_3 v_16);
      let v_18 <- eval (concat v_3 v_17);
      setRegister (lhs.of_reg xmm_1) v_18;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 8)) <- eval (extract v_2 120 128);
      let v_4 <- eval (concat v_3 v_3);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat v_3 v_5);
      let v_7 <- eval (concat v_3 v_6);
      let v_8 <- eval (concat v_3 v_7);
      let v_9 <- eval (concat v_3 v_8);
      let v_10 <- eval (concat v_3 v_9);
      let v_11 <- eval (concat v_3 v_10);
      let v_12 <- eval (concat v_3 v_11);
      let v_13 <- eval (concat v_3 v_12);
      let v_14 <- eval (concat v_3 v_13);
      let v_15 <- eval (concat v_3 v_14);
      let v_16 <- eval (concat v_3 v_15);
      let v_17 <- eval (concat v_3 v_16);
      let v_18 <- eval (concat v_3 v_17);
      let v_19 <- eval (concat v_3 v_18);
      let v_20 <- eval (concat v_3 v_19);
      let v_21 <- eval (concat v_3 v_20);
      let v_22 <- eval (concat v_3 v_21);
      let v_23 <- eval (concat v_3 v_22);
      let v_24 <- eval (concat v_3 v_23);
      let v_25 <- eval (concat v_3 v_24);
      let v_26 <- eval (concat v_3 v_25);
      let v_27 <- eval (concat v_3 v_26);
      let v_28 <- eval (concat v_3 v_27);
      let v_29 <- eval (concat v_3 v_28);
      let v_30 <- eval (concat v_3 v_29);
      let v_31 <- eval (concat v_3 v_30);
      let v_32 <- eval (concat v_3 v_31);
      let v_33 <- eval (concat v_3 v_32);
      let v_34 <- eval (concat v_3 v_33);
      setRegister (lhs.of_reg ymm_1) v_34;
      pure ()
     action
