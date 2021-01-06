def punpckhbw : instruction :=
  definst "punpckhbw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 8)) <- eval (extract v_5 0 8);
      let v_7 <- eval (concat v_4 v_6);
      let (v_8 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_9 : expression (bv 8)) <- eval (extract v_5 8 16);
      let v_10 <- eval (concat v_8 v_9);
      let (v_11 : expression (bv 8)) <- eval (extract v_3 16 24);
      let (v_12 : expression (bv 8)) <- eval (extract v_5 16 24);
      let v_13 <- eval (concat v_11 v_12);
      let (v_14 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_15 : expression (bv 8)) <- eval (extract v_5 24 32);
      let v_16 <- eval (concat v_14 v_15);
      let (v_17 : expression (bv 8)) <- eval (extract v_3 32 40);
      let (v_18 : expression (bv 8)) <- eval (extract v_5 32 40);
      let v_19 <- eval (concat v_17 v_18);
      let (v_20 : expression (bv 8)) <- eval (extract v_3 40 48);
      let (v_21 : expression (bv 8)) <- eval (extract v_5 40 48);
      let v_22 <- eval (concat v_20 v_21);
      let (v_23 : expression (bv 8)) <- eval (extract v_3 48 56);
      let (v_24 : expression (bv 8)) <- eval (extract v_5 48 56);
      let v_25 <- eval (concat v_23 v_24);
      let (v_26 : expression (bv 8)) <- eval (extract v_3 56 64);
      let (v_27 : expression (bv 8)) <- eval (extract v_5 56 64);
      let v_28 <- eval (concat v_26 v_27);
      let v_29 <- eval (concat v_25 v_28);
      let v_30 <- eval (concat v_22 v_29);
      let v_31 <- eval (concat v_19 v_30);
      let v_32 <- eval (concat v_16 v_31);
      let v_33 <- eval (concat v_13 v_32);
      let v_34 <- eval (concat v_10 v_33);
      let v_35 <- eval (concat v_7 v_34);
      setRegister (lhs.of_reg xmm_1) v_35;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 8)) <- eval (extract v_2 0 8);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 8)) <- eval (extract v_4 0 8);
      let v_6 <- eval (concat v_3 v_5);
      let (v_7 : expression (bv 8)) <- eval (extract v_2 8 16);
      let (v_8 : expression (bv 8)) <- eval (extract v_4 8 16);
      let v_9 <- eval (concat v_7 v_8);
      let (v_10 : expression (bv 8)) <- eval (extract v_2 16 24);
      let (v_11 : expression (bv 8)) <- eval (extract v_4 16 24);
      let v_12 <- eval (concat v_10 v_11);
      let (v_13 : expression (bv 8)) <- eval (extract v_2 24 32);
      let (v_14 : expression (bv 8)) <- eval (extract v_4 24 32);
      let v_15 <- eval (concat v_13 v_14);
      let (v_16 : expression (bv 8)) <- eval (extract v_2 32 40);
      let (v_17 : expression (bv 8)) <- eval (extract v_4 32 40);
      let v_18 <- eval (concat v_16 v_17);
      let (v_19 : expression (bv 8)) <- eval (extract v_2 40 48);
      let (v_20 : expression (bv 8)) <- eval (extract v_4 40 48);
      let v_21 <- eval (concat v_19 v_20);
      let (v_22 : expression (bv 8)) <- eval (extract v_2 48 56);
      let (v_23 : expression (bv 8)) <- eval (extract v_4 48 56);
      let v_24 <- eval (concat v_22 v_23);
      let (v_25 : expression (bv 8)) <- eval (extract v_2 56 64);
      let (v_26 : expression (bv 8)) <- eval (extract v_4 56 64);
      let v_27 <- eval (concat v_25 v_26);
      let v_28 <- eval (concat v_24 v_27);
      let v_29 <- eval (concat v_21 v_28);
      let v_30 <- eval (concat v_18 v_29);
      let v_31 <- eval (concat v_15 v_30);
      let v_32 <- eval (concat v_12 v_31);
      let v_33 <- eval (concat v_9 v_32);
      let v_34 <- eval (concat v_6 v_33);
      setRegister (lhs.of_reg xmm_1) v_34;
      pure ()
     action
