def vpmovsxbw : instruction :=
  definst "vpmovsxbw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_6 : expression (bv 8)) <- eval (extract v_3 16 24);
      let (v_7 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_8 : expression (bv 8)) <- eval (extract v_3 32 40);
      let (v_9 : expression (bv 8)) <- eval (extract v_3 40 48);
      let (v_10 : expression (bv 8)) <- eval (extract v_3 48 56);
      let (v_11 : expression (bv 8)) <- eval (extract v_3 56 64);
      let v_12 <- eval (concat (sext v_10 16) (sext v_11 16));
      let v_13 <- eval (concat (sext v_9 16) v_12);
      let v_14 <- eval (concat (sext v_8 16) v_13);
      let v_15 <- eval (concat (sext v_7 16) v_14);
      let v_16 <- eval (concat (sext v_6 16) v_15);
      let v_17 <- eval (concat (sext v_5 16) v_16);
      let v_18 <- eval (concat (sext v_4 16) v_17);
      setRegister (lhs.of_reg xmm_1) v_18;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_6 : expression (bv 8)) <- eval (extract v_3 16 24);
      let (v_7 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_8 : expression (bv 8)) <- eval (extract v_3 32 40);
      let (v_9 : expression (bv 8)) <- eval (extract v_3 40 48);
      let (v_10 : expression (bv 8)) <- eval (extract v_3 48 56);
      let (v_11 : expression (bv 8)) <- eval (extract v_3 56 64);
      let (v_12 : expression (bv 8)) <- eval (extract v_3 64 72);
      let (v_13 : expression (bv 8)) <- eval (extract v_3 72 80);
      let (v_14 : expression (bv 8)) <- eval (extract v_3 80 88);
      let (v_15 : expression (bv 8)) <- eval (extract v_3 88 96);
      let (v_16 : expression (bv 8)) <- eval (extract v_3 96 104);
      let (v_17 : expression (bv 8)) <- eval (extract v_3 104 112);
      let (v_18 : expression (bv 8)) <- eval (extract v_3 112 120);
      let (v_19 : expression (bv 8)) <- eval (extract v_3 120 128);
      let v_20 <- eval (concat (sext v_18 16) (sext v_19 16));
      let v_21 <- eval (concat (sext v_17 16) v_20);
      let v_22 <- eval (concat (sext v_16 16) v_21);
      let v_23 <- eval (concat (sext v_15 16) v_22);
      let v_24 <- eval (concat (sext v_14 16) v_23);
      let v_25 <- eval (concat (sext v_13 16) v_24);
      let v_26 <- eval (concat (sext v_12 16) v_25);
      let v_27 <- eval (concat (sext v_11 16) v_26);
      let v_28 <- eval (concat (sext v_10 16) v_27);
      let v_29 <- eval (concat (sext v_9 16) v_28);
      let v_30 <- eval (concat (sext v_8 16) v_29);
      let v_31 <- eval (concat (sext v_7 16) v_30);
      let v_32 <- eval (concat (sext v_6 16) v_31);
      let v_33 <- eval (concat (sext v_5 16) v_32);
      let v_34 <- eval (concat (sext v_4 16) v_33);
      setRegister (lhs.of_reg ymm_1) v_34;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 8)) <- eval (extract v_2 64 72);
      let (v_4 : expression (bv 8)) <- eval (extract v_2 72 80);
      let (v_5 : expression (bv 8)) <- eval (extract v_2 80 88);
      let (v_6 : expression (bv 8)) <- eval (extract v_2 88 96);
      let (v_7 : expression (bv 8)) <- eval (extract v_2 96 104);
      let (v_8 : expression (bv 8)) <- eval (extract v_2 104 112);
      let (v_9 : expression (bv 8)) <- eval (extract v_2 112 120);
      let (v_10 : expression (bv 8)) <- eval (extract v_2 120 128);
      let v_11 <- eval (concat (sext v_9 16) (sext v_10 16));
      let v_12 <- eval (concat (sext v_8 16) v_11);
      let v_13 <- eval (concat (sext v_7 16) v_12);
      let v_14 <- eval (concat (sext v_6 16) v_13);
      let v_15 <- eval (concat (sext v_5 16) v_14);
      let v_16 <- eval (concat (sext v_4 16) v_15);
      let v_17 <- eval (concat (sext v_3 16) v_16);
      setRegister (lhs.of_reg xmm_1) v_17;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 8)) <- eval (extract v_2 0 8);
      let (v_4 : expression (bv 8)) <- eval (extract v_2 8 16);
      let (v_5 : expression (bv 8)) <- eval (extract v_2 16 24);
      let (v_6 : expression (bv 8)) <- eval (extract v_2 24 32);
      let (v_7 : expression (bv 8)) <- eval (extract v_2 32 40);
      let (v_8 : expression (bv 8)) <- eval (extract v_2 40 48);
      let (v_9 : expression (bv 8)) <- eval (extract v_2 48 56);
      let (v_10 : expression (bv 8)) <- eval (extract v_2 56 64);
      let (v_11 : expression (bv 8)) <- eval (extract v_2 64 72);
      let (v_12 : expression (bv 8)) <- eval (extract v_2 72 80);
      let (v_13 : expression (bv 8)) <- eval (extract v_2 80 88);
      let (v_14 : expression (bv 8)) <- eval (extract v_2 88 96);
      let (v_15 : expression (bv 8)) <- eval (extract v_2 96 104);
      let (v_16 : expression (bv 8)) <- eval (extract v_2 104 112);
      let (v_17 : expression (bv 8)) <- eval (extract v_2 112 120);
      let (v_18 : expression (bv 8)) <- eval (extract v_2 120 128);
      let v_19 <- eval (concat (sext v_17 16) (sext v_18 16));
      let v_20 <- eval (concat (sext v_16 16) v_19);
      let v_21 <- eval (concat (sext v_15 16) v_20);
      let v_22 <- eval (concat (sext v_14 16) v_21);
      let v_23 <- eval (concat (sext v_13 16) v_22);
      let v_24 <- eval (concat (sext v_12 16) v_23);
      let v_25 <- eval (concat (sext v_11 16) v_24);
      let v_26 <- eval (concat (sext v_10 16) v_25);
      let v_27 <- eval (concat (sext v_9 16) v_26);
      let v_28 <- eval (concat (sext v_8 16) v_27);
      let v_29 <- eval (concat (sext v_7 16) v_28);
      let v_30 <- eval (concat (sext v_6 16) v_29);
      let v_31 <- eval (concat (sext v_5 16) v_30);
      let v_32 <- eval (concat (sext v_4 16) v_31);
      let v_33 <- eval (concat (sext v_3 16) v_32);
      setRegister (lhs.of_reg ymm_1) v_33;
      pure ()
     action
